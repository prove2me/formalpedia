-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1467_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:09:27.532176+00:00
-- url     : https://prove2.me/submissions/6d1b47f9-3117-489b-878b-11ff6a622027

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
theorem support_rectangle_w1467_s0_0 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-433655309/2500000000 : ℝ)*x 0 + (5948327637/10000000000 : ℝ)*x 1 + (4835601007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433655309/2500000000 : ℝ)^4431 ≤ (512285170361/5000000000000 : ℝ)^3407 := by
    have hnat : (433655309 : ℕ)^4431*5000000000000^3407 ≤ 512285170361^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433655309 2500000000 512285170361 5000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5948327637/10000000000 : ℝ)^4431 ≤ (25442368357707/50000000000000 : ℝ)^3407 := by
    have hnat : (5948327637 : ℕ)^4431*50000000000000^3407 ≤ 25442368357707^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5948327637 10000000000 25442368357707 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4835601007/10000000000 : ℝ)^4431 ≤ (1554782394499/4000000000000 : ℝ)^3407 := by
    have hnat : (4835601007 : ℕ)^4431*4000000000000^3407 ≤ 1554782394499^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4835601007 10000000000 1554782394499 4000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-433655309/2500000000 : ℝ), (5948327637/10000000000 : ℝ), (4835601007/10000000000 : ℝ)] ![(512285170361/5000000000000 : ℝ), (25442368357707/50000000000000 : ℝ), (1554782394499/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-433655309/2500000000 : ℝ)|^4431 ≤ (512285170361/5000000000000 : ℝ)^3407
        have hw : |(-433655309/2500000000 : ℝ)|=(433655309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5948327637/10000000000 : ℝ)|^4431 ≤ (25442368357707/50000000000000 : ℝ)^3407
        have hw : |(5948327637/10000000000 : ℝ)|=(5948327637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4835601007/10000000000 : ℝ)|^4431 ≤ (1554782394499/4000000000000 : ℝ)^3407
        have hw : |(4835601007/10000000000 : ℝ)|=(4835601007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s0_1 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (85747413/156250000 : ℝ)*x 0 + (-2362045233/10000000000 : ℝ)*x 1 + (4835600981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85747413/156250000 : ℝ)^4431 ≤ (45822203597771/100000000000000 : ℝ)^3407 := by
    have hnat : (85747413 : ℕ)^4431*100000000000000^3407 ≤ 45822203597771^3407*156250000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85747413 156250000 45822203597771 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2362045233/10000000000 : ℝ)^4431 ≤ (3061647358141/20000000000000 : ℝ)^3407 := by
    have hnat : (2362045233 : ℕ)^4431*20000000000000^3407 ≤ 3061647358141^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2362045233 10000000000 3061647358141 20000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4835600981/10000000000 : ℝ)^4431 ≤ (38869559590667/100000000000000 : ℝ)^3407 := by
    have hnat : (4835600981 : ℕ)^4431*100000000000000^3407 ≤ 38869559590667^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4835600981 10000000000 38869559590667 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(85747413/156250000 : ℝ), (-2362045233/10000000000 : ℝ), (4835600981/10000000000 : ℝ)] ![(45822203597771/100000000000000 : ℝ), (3061647358141/20000000000000 : ℝ), (38869559590667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(85747413/156250000 : ℝ)|^4431 ≤ (45822203597771/100000000000000 : ℝ)^3407
        have hw : |(85747413/156250000 : ℝ)|=(85747413/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2362045233/10000000000 : ℝ)|^4431 ≤ (3061647358141/20000000000000 : ℝ)^3407
        have hw : |(-2362045233/10000000000 : ℝ)|=(2362045233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4835600981/10000000000 : ℝ)|^4431 ≤ (38869559590667/100000000000000 : ℝ)^3407
        have hw : |(4835600981/10000000000 : ℝ)|=(4835600981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s0_2 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (548783447/1000000000 : ℝ)*x 0 + (2417800479/5000000000 : ℝ)*x 1 + (-2362045213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548783447/1000000000 : ℝ)^4431 ≤ (45822204010427/100000000000000 : ℝ)^3407 := by
    have hnat : (548783447 : ℕ)^4431*100000000000000^3407 ≤ 45822204010427^3407*1000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548783447 1000000000 45822204010427 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2417800479/5000000000 : ℝ)^4431 ≤ (19434779675111/50000000000000 : ℝ)^3407 := by
    have hnat : (2417800479 : ℕ)^4431*50000000000000^3407 ≤ 19434779675111^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417800479 5000000000 19434779675111 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2362045213/10000000000 : ℝ)^4431 ≤ (15308236622129/100000000000000 : ℝ)^3407 := by
    have hnat : (2362045213 : ℕ)^4431*100000000000000^3407 ≤ 15308236622129^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2362045213 10000000000 15308236622129 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(548783447/1000000000 : ℝ), (2417800479/5000000000 : ℝ), (-2362045213/10000000000 : ℝ)] ![(45822204010427/100000000000000 : ℝ), (19434779675111/50000000000000 : ℝ), (15308236622129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(548783447/1000000000 : ℝ)|^4431 ≤ (45822204010427/100000000000000 : ℝ)^3407
        have hw : |(548783447/1000000000 : ℝ)|=(548783447/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2417800479/5000000000 : ℝ)|^4431 ≤ (19434779675111/50000000000000 : ℝ)^3407
        have hw : |(2417800479/5000000000 : ℝ)|=(2417800479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2362045213/10000000000 : ℝ)|^4431 ≤ (15308236622129/100000000000000 : ℝ)^3407
        have hw : |(-2362045213/10000000000 : ℝ)|=(2362045213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s0_3 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (831501661/2000000000 : ℝ)*x 0 + (3091845961/10000000000 : ℝ)*x 1 + (5535250537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (831501661/2000000000 : ℝ)^4431 ≤ (31935262895883/100000000000000 : ℝ)^3407 := by
    have hnat : (831501661 : ℕ)^4431*100000000000000^3407 ≤ 31935262895883^3407*2000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831501661 2000000000 31935262895883 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091845961/10000000000 : ℝ)^4431 ≤ (10863478640487/50000000000000 : ℝ)^3407 := by
    have hnat : (3091845961 : ℕ)^4431*50000000000000^3407 ≤ 10863478640487^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091845961 10000000000 10863478640487 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5535250537/10000000000 : ℝ)^4431 ≤ (2316888990591/5000000000000 : ℝ)^3407 := by
    have hnat : (5535250537 : ℕ)^4431*5000000000000^3407 ≤ 2316888990591^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5535250537 10000000000 2316888990591 5000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(831501661/2000000000 : ℝ), (3091845961/10000000000 : ℝ), (5535250537/10000000000 : ℝ)] ![(31935262895883/100000000000000 : ℝ), (10863478640487/50000000000000 : ℝ), (2316888990591/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(831501661/2000000000 : ℝ)|^4431 ≤ (31935262895883/100000000000000 : ℝ)^3407
        have hw : |(831501661/2000000000 : ℝ)|=(831501661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091845961/10000000000 : ℝ)|^4431 ≤ (10863478640487/50000000000000 : ℝ)^3407
        have hw : |(3091845961/10000000000 : ℝ)|=(3091845961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5535250537/10000000000 : ℝ)|^4431 ≤ (2316888990591/5000000000000 : ℝ)^3407
        have hw : |(5535250537/10000000000 : ℝ)|=(5535250537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s0_4 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-869272601/5000000000 : ℝ)*x 0 + (30401303/62500000 : ℝ)*x 1 + (2959345109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869272601/5000000000 : ℝ)^4431 ≤ (2568964257711/25000000000000 : ℝ)^3407 := by
    have hnat : (869272601 : ℕ)^4431*25000000000000^3407 ≤ 2568964257711^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869272601 5000000000 2568964257711 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30401303/62500000 : ℝ)^4431 ≤ (39168892232703/100000000000000 : ℝ)^3407 := by
    have hnat : (30401303 : ℕ)^4431*100000000000000^3407 ≤ 39168892232703^3407*62500000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30401303 62500000 39168892232703 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2959345109/5000000000 : ℝ)^4431 ≤ (3159703169849/6250000000000 : ℝ)^3407 := by
    have hnat : (2959345109 : ℕ)^4431*6250000000000^3407 ≤ 3159703169849^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2959345109 5000000000 3159703169849 6250000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-869272601/5000000000 : ℝ), (30401303/62500000 : ℝ), (2959345109/5000000000 : ℝ)] ![(2568964257711/25000000000000 : ℝ), (39168892232703/100000000000000 : ℝ), (3159703169849/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-869272601/5000000000 : ℝ)|^4431 ≤ (2568964257711/25000000000000 : ℝ)^3407
        have hw : |(-869272601/5000000000 : ℝ)|=(869272601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(30401303/62500000 : ℝ)|^4431 ≤ (39168892232703/100000000000000 : ℝ)^3407
        have hw : |(30401303/62500000 : ℝ)|=(30401303/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2959345109/5000000000 : ℝ)|^4431 ≤ (3159703169849/6250000000000 : ℝ)^3407
        have hw : |(2959345109/5000000000 : ℝ)|=(2959345109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s0_5 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5184101851/10000000000 : ℝ)*x 0 + (-1278955831/10000000000 : ℝ)*x 1 + (1183738057/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5184101851/10000000000 : ℝ)^4431 ≤ (5318956965253/12500000000000 : ℝ)^3407 := by
    have hnat : (5184101851 : ℕ)^4431*12500000000000^3407 ≤ 5318956965253^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184101851 10000000000 5318956965253 12500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1278955831/10000000000 : ℝ)^4431 ≤ (1378618560559/20000000000000 : ℝ)^3407 := by
    have hnat : (1278955831 : ℕ)^4431*20000000000000^3407 ≤ 1378618560559^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1278955831 10000000000 1378618560559 20000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1183738057/2000000000 : ℝ)^4431 ≤ (50555251461879/100000000000000 : ℝ)^3407 := by
    have hnat : (1183738057 : ℕ)^4431*100000000000000^3407 ≤ 50555251461879^3407*2000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183738057 2000000000 50555251461879 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5184101851/10000000000 : ℝ), (-1278955831/10000000000 : ℝ), (1183738057/2000000000 : ℝ)] ![(5318956965253/12500000000000 : ℝ), (1378618560559/20000000000000 : ℝ), (50555251461879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5184101851/10000000000 : ℝ)|^4431 ≤ (5318956965253/12500000000000 : ℝ)^3407
        have hw : |(5184101851/10000000000 : ℝ)|=(5184101851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1278955831/10000000000 : ℝ)|^4431 ≤ (1378618560559/20000000000000 : ℝ)^3407
        have hw : |(-1278955831/10000000000 : ℝ)|=(1278955831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1183738057/2000000000 : ℝ)|^4431 ≤ (50555251461879/100000000000000 : ℝ)^3407
        have hw : |(1183738057/2000000000 : ℝ)|=(1183738057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s0_6 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5184101889/10000000000 : ℝ)*x 0 + (2959345063/5000000000 : ℝ)*x 1 + (-639478013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5184101889/10000000000 : ℝ)^4431 ≤ (42551656127679/100000000000000 : ℝ)^3407 := by
    have hnat : (5184101889 : ℕ)^4431*100000000000000^3407 ≤ 42551656127679^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184101889 10000000000 42551656127679 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2959345063/5000000000 : ℝ)^4431 ≤ (50555249695567/100000000000000 : ℝ)^3407 := by
    have hnat : (2959345063 : ℕ)^4431*100000000000000^3407 ≤ 50555249695567^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2959345063 5000000000 50555249695567 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (639478013/5000000000 : ℝ)^4431 ≤ (1723273542413/25000000000000 : ℝ)^3407 := by
    have hnat : (639478013 : ℕ)^4431*25000000000000^3407 ≤ 1723273542413^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639478013 5000000000 1723273542413 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5184101889/10000000000 : ℝ), (2959345063/5000000000 : ℝ), (-639478013/5000000000 : ℝ)] ![(42551656127679/100000000000000 : ℝ), (50555249695567/100000000000000 : ℝ), (1723273542413/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5184101889/10000000000 : ℝ)|^4431 ≤ (42551656127679/100000000000000 : ℝ)^3407
        have hw : |(5184101889/10000000000 : ℝ)|=(5184101889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2959345063/5000000000 : ℝ)|^4431 ≤ (50555249695567/100000000000000 : ℝ)^3407
        have hw : |(2959345063/5000000000 : ℝ)|=(2959345063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-639478013/5000000000 : ℝ)|^4431 ≤ (1723273542413/25000000000000 : ℝ)^3407
        have hw : |(-639478013/5000000000 : ℝ)|=(639478013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s0_7 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2083062599/5000000000 : ℝ)*x 0 + (2736216053/5000000000 : ℝ)*x 1 + (789231503/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083062599/5000000000 : ℝ)^4431 ≤ (8005343188317/25000000000000 : ℝ)^3407 := by
    have hnat : (2083062599 : ℕ)^4431*25000000000000^3407 ≤ 8005343188317^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083062599 5000000000 8005343188317 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2736216053/5000000000 : ℝ)^4431 ≤ (11413753662553/25000000000000 : ℝ)^3407 := by
    have hnat : (2736216053 : ℕ)^4431*25000000000000^3407 ≤ 11413753662553^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736216053 5000000000 11413753662553 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (789231503/2500000000 : ℝ)^4431 ≤ (22323612573873/100000000000000 : ℝ)^3407 := by
    have hnat : (789231503 : ℕ)^4431*100000000000000^3407 ≤ 22323612573873^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      789231503 2500000000 22323612573873 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2083062599/5000000000 : ℝ), (2736216053/5000000000 : ℝ), (789231503/2500000000 : ℝ)] ![(8005343188317/25000000000000 : ℝ), (11413753662553/25000000000000 : ℝ), (22323612573873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2083062599/5000000000 : ℝ)|^4431 ≤ (8005343188317/25000000000000 : ℝ)^3407
        have hw : |(2083062599/5000000000 : ℝ)|=(2083062599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2736216053/5000000000 : ℝ)|^4431 ≤ (11413753662553/25000000000000 : ℝ)^3407
        have hw : |(2736216053/5000000000 : ℝ)|=(2736216053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(789231503/2500000000 : ℝ)|^4431 ≤ (22323612573873/100000000000000 : ℝ)^3407
        have hw : |(789231503/2500000000 : ℝ)|=(789231503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1467_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2229/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (163/625 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4429/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4429 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4429*1^1024 ≤ 0^1024*1^4429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4429 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4429/1024 : ℝ) ≤ (950170940732575507/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4429 ≤ (950170940732575507/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4429*50000000000000000000^1024 ≤ 950170940732575507^1024*5^4429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 950170940732575507 50000000000000000000 4429 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (950170940732575507/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4429 := by
      have hnat : (1 : ℕ)^1024*1^4429 ≤ 1^4429*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50950170940732575507/50000000000000000000 : ℝ) ≤ (10043619154570059/10000000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (50950170940732575507/50000000000000000000 : ℝ)^1024 ≤ (10043619154570059/10000000000000000 : ℝ)^4429 := by
      have hnat : (50950170940732575507 : ℕ)^1024*10000000000000000^4429 ≤ 10043619154570059^4429*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50950170940732575507 50000000000000000000 10043619154570059 10000000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10043619154570059/10000000000000000 : ℝ)) (X := (50950170940732575507/50000000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25950170940732575507/25000000000000000000 : ℝ) ≤ (5043619154570059/5000000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (25950170940732575507/25000000000000000000 : ℝ)^1024 ≤ (5043619154570059/5000000000000000 : ℝ)^4429 := by
      have hnat : (25950170940732575507 : ℕ)^1024*5000000000000000^4429 ≤ 5043619154570059^4429*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25950170940732575507 25000000000000000000 5043619154570059 5000000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5043619154570059/5000000000000000 : ℝ)) (X := (25950170940732575507/25000000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(43619154570059/4000000000000000 : ℝ)*(0 : ℝ))^(4429/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(43619154570059/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(950170940732575507/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(43619154570059/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4429/1024 : ℝ) := by
    rw [show (1 : ℝ)+(43619154570059/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10043619154570059/10000000000000000 : ℝ) by norm_num, show 1+(950170940732575507/50000000000000000000 : ℝ)+(0 : ℝ)=(50950170940732575507/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(950170940732575507/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(43619154570059/4000000000000000 : ℝ)*(2/5 : ℝ))^(4429/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(43619154570059/4000000000000000 : ℝ)*(2/5 : ℝ)=(5043619154570059/5000000000000000 : ℝ) by norm_num, show 1+2*(950170940732575507/50000000000000000000 : ℝ)=(25950170940732575507/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(43619154570059/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (43619154570059/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(43619154570059/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (43619154570059/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(43619154570059/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (43619154570059/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-433655309/2500000000 : ℝ)*X 0 0+(5948327637/10000000000 : ℝ)*X 0 1+(4835601007/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((85747413/156250000 : ℝ)*X 1 0+(-2362045233/10000000000 : ℝ)*X 1 1+(4835600981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((548783447/1000000000 : ℝ)*X 2 0+(2417800479/5000000000 : ℝ)*X 2 1+(-2362045213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((831501661/2000000000 : ℝ)*X 0 0+(3091845961/10000000000 : ℝ)*X 0 1+(5535250537/10000000000 : ℝ)*X 0 2+(831501661/2000000000 : ℝ)*X 1 0+(3091845961/10000000000 : ℝ)*X 1 1+(5535250537/10000000000 : ℝ)*X 1 2+(831501661/2000000000 : ℝ)*X 2 0+(3091845961/10000000000 : ℝ)*X 2 1+(5535250537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-869272601/5000000000 : ℝ)*X 0 0+(30401303/62500000 : ℝ)*X 0 1+(2959345109/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5184101851/10000000000 : ℝ)*X 1 0+(-1278955831/10000000000 : ℝ)*X 1 1+(1183738057/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5184101889/10000000000 : ℝ)*X 2 0+(2959345063/5000000000 : ℝ)*X 2 1+(-639478013/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2083062599/5000000000 : ℝ)*X 0 0+(2736216053/5000000000 : ℝ)*X 0 1+(789231503/2500000000 : ℝ)*X 0 2+(2083062599/5000000000 : ℝ)*X 1 0+(2736216053/5000000000 : ℝ)*X 1 1+(789231503/2500000000 : ℝ)*X 1 2+(2083062599/5000000000 : ℝ)*X 2 0+(2736216053/5000000000 : ℝ)*X 2 1+(789231503/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (425665553741901722541873/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12544393/25000000000000 : ℝ)*(base1) + (19381597/2000000000000 : ℝ)*(base19) + (195060561/20000000000000 : ℝ)*(base23) + (57996347/50000000000000 : ℝ)*(upper3) + (24669893/20000000000000 : ℝ)*(upper5) + (653983878818351/100000000000000 : ℝ)*(major0) + (653983878818351/100000000000000 : ℝ)*(major1) + (653983878818351/100000000000000 : ℝ)*(major2) + (898696405025693/100000000000000 : ℝ)*(sp0) + (35947947600201/4000000000000 : ℝ)*(sp1) + (89869868378207/10000000000000 : ℝ)*(sp2) + (40926642828561/10000000000000 : ℝ)*(sp3) + (1652118377/50000000000000 : ℝ)*(sp4) + (11825601/800000000000 : ℝ)*(sp7) + (409267956663307/100000000000000 : ℝ)*(f.failure) + (7189597272679/800000000000 : ℝ)*(f.sum) + (427456375552709/200000000000000000000000000000 : ℝ)*base65 + (115236035952709/400000000000000000000000000000 : ℝ)*base67 + (1647157352847291/400000000000000000000000000000 : ℝ)*base70 + (632565724352709/400000000000000000000000000000 : ℝ)*base71 + (680502637352709/200000000000000000000000000000 : ℝ)*base73 + (1246111073647291/400000000000000000000000000000 : ℝ)*base76 + (673807115647291/400000000000000000000000000000 : ℝ)*base78 + (946272643647291/400000000000000000000000000000 : ℝ)*base80 + (162811732352709/200000000000000000000000000000 : ℝ)*base81 + (1353599/1000000000000000000000 : ℝ)*base89 + (1353599/1000000000000000000000 : ℝ)*base91 + (1353599/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18672454871196619559601/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (424716449/25000000000000 : ℝ)*(base19) + (857450129/50000000000000 : ℝ)*(base23) + (30935071/20000000000000 : ℝ)*(base32) + (16025549/6250000000000 : ℝ)*(upper3) + (39702959/25000000000000 : ℝ)*(upper5) + (43131359957587/6250000000000 : ℝ)*(major0) + (43131359957587/6250000000000 : ℝ)*(major1) + (43131359957587/6250000000000 : ℝ)*(major2) + (2046483099/50000000000000 : ℝ)*(sp1) + (1061999093/25000000000000 : ℝ)*(sp2) + (94833247580097/10000000000000 : ℝ)*(sp4) + (59270417748061/6250000000000 : ℝ)*(sp5) + (948326512904339/100000000000000 : ℝ)*(sp6) + (107967659800097/25000000000000 : ℝ)*(sp7) + (13495962308617/3125000000000 : ℝ)*(f.failure) + (94833247580097/10000000000000 : ℝ)*(f.sum) + (21775824037633/12500000000000000000000000000 : ℝ)*base65 + (27620391887633/25000000000000000000000000000 : ℝ)*base67 + (75457357187633/25000000000000000000000000000 : ℝ)*base69 + (7324563312367/25000000000000000000000000000 : ℝ)*base72 + (58690910862633/12500000000000000000000000000 : ℝ)*base73 + (3274183737633/25000000000000000000000000000 : ℝ)*base75 + (130724559212633/25000000000000000000000000000 : ℝ)*base77 + (133136504637633/25000000000000000000000000000 : ℝ)*base79 + (24395852512633/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (219269/31250000000000000000 : ℝ)*base89 + (219269/31250000000000000000 : ℝ)*base91 + (219269/31250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1467_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2229/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (163/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1467_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1467_s1_0 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1900618367/10000000000 : ℝ)*x 0 + (224093431/400000000 : ℝ)*x 1 + (1268773693/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1900618367/10000000000 : ℝ)^4431 ≤ (11538816206609/100000000000000 : ℝ)^3407 := by
    have hnat : (1900618367 : ℕ)^4431*100000000000000^3407 ≤ 11538816206609^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1900618367 10000000000 11538816206609 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224093431/400000000 : ℝ)^4431 ≤ (11767373961799/25000000000000 : ℝ)^3407 := by
    have hnat : (224093431 : ℕ)^4431*25000000000000^3407 ≤ 11767373961799^3407*400000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224093431 400000000 11767373961799 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1268773693/2500000000 : ℝ)^4431 ≤ (2586980495947/6250000000000 : ℝ)^3407 := by
    have hnat : (1268773693 : ℕ)^4431*6250000000000^3407 ≤ 2586980495947^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268773693 2500000000 2586980495947 6250000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1900618367/10000000000 : ℝ), (224093431/400000000 : ℝ), (1268773693/2500000000 : ℝ)] ![(11538816206609/100000000000000 : ℝ), (11767373961799/25000000000000 : ℝ), (2586980495947/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1900618367/10000000000 : ℝ)|^4431 ≤ (11538816206609/100000000000000 : ℝ)^3407
        have hw : |(-1900618367/10000000000 : ℝ)|=(1900618367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224093431/400000000 : ℝ)|^4431 ≤ (11767373961799/25000000000000 : ℝ)^3407
        have hw : |(224093431/400000000 : ℝ)|=(224093431/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1268773693/2500000000 : ℝ)|^4431 ≤ (2586980495947/6250000000000 : ℝ)^3407
        have hw : |(1268773693/2500000000 : ℝ)|=(1268773693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s1_1 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (337190157/625000000 : ℝ)*x 0 + (-2179911549/10000000000 : ℝ)*x 1 + (2537548049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337190157/625000000 : ℝ)^4431 ≤ (44817112556197/100000000000000 : ℝ)^3407 := by
    have hnat : (337190157 : ℕ)^4431*100000000000000^3407 ≤ 44817112556197^3407*625000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337190157 625000000 44817112556197 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2179911549/10000000000 : ℝ)^4431 ≤ (2758237084323/20000000000000 : ℝ)^3407 := by
    have hnat : (2179911549 : ℕ)^4431*20000000000000^3407 ≤ 2758237084323^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179911549 10000000000 2758237084323 20000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2537548049/5000000000 : ℝ)^4431 ≤ (4139170200023/10000000000000 : ℝ)^3407 := by
    have hnat : (2537548049 : ℕ)^4431*10000000000000^3407 ≤ 4139170200023^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2537548049 5000000000 4139170200023 10000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(337190157/625000000 : ℝ), (-2179911549/10000000000 : ℝ), (2537548049/5000000000 : ℝ)] ![(44817112556197/100000000000000 : ℝ), (2758237084323/20000000000000 : ℝ), (4139170200023/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(337190157/625000000 : ℝ)|^4431 ≤ (44817112556197/100000000000000 : ℝ)^3407
        have hw : |(337190157/625000000 : ℝ)|=(337190157/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2179911549/10000000000 : ℝ)|^4431 ≤ (2758237084323/20000000000000 : ℝ)^3407
        have hw : |(-2179911549/10000000000 : ℝ)|=(2179911549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2537548049/5000000000 : ℝ)|^4431 ≤ (4139170200023/10000000000000 : ℝ)^3407
        have hw : |(2537548049/5000000000 : ℝ)|=(2537548049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s1_2 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348760907/2500000000 : ℝ)*x 0 + (5075094891/10000000000 : ℝ)*x 1 + (-54497791/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348760907/2500000000 : ℝ)^4431 ≤ (2801070288331/6250000000000 : ℝ)^3407 := by
    have hnat : (1348760907 : ℕ)^4431*6250000000000^3407 ≤ 2801070288331^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348760907 2500000000 2801070288331 6250000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5075094891/10000000000 : ℝ)^4431 ≤ (20695844598701/50000000000000 : ℝ)^3407 := by
    have hnat : (5075094891 : ℕ)^4431*50000000000000^3407 ≤ 20695844598701^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075094891 10000000000 20695844598701 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54497791/250000000 : ℝ)^4431 ≤ (344779654259/2500000000000 : ℝ)^3407 := by
    have hnat : (54497791 : ℕ)^4431*2500000000000^3407 ≤ 344779654259^3407*250000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54497791 250000000 344779654259 2500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348760907/2500000000 : ℝ), (5075094891/10000000000 : ℝ), (-54497791/250000000 : ℝ)] ![(2801070288331/6250000000000 : ℝ), (20695844598701/50000000000000 : ℝ), (344779654259/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348760907/2500000000 : ℝ)|^4431 ≤ (2801070288331/6250000000000 : ℝ)^3407
        have hw : |(1348760907/2500000000 : ℝ)|=(1348760907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5075094891/10000000000 : ℝ)|^4431 ≤ (20695844598701/50000000000000 : ℝ)^3407
        have hw : |(5075094891/10000000000 : ℝ)|=(5075094891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-54497791/250000000 : ℝ)|^4431 ≤ (344779654259/2500000000000 : ℝ)^3407
        have hw : |(-54497791/250000000 : ℝ)|=(54497791/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s1_3 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (85319589/200000000 : ℝ)*x 0 + (930380663/2500000000 : ℝ)*x 1 + (975854659/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85319589/200000000 : ℝ)^4431 ≤ (16511558275499/50000000000000 : ℝ)^3407 := by
    have hnat : (85319589 : ℕ)^4431*50000000000000^3407 ≤ 16511558275499^3407*200000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85319589 200000000 16511558275499 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (930380663/2500000000 : ℝ)^4431 ≤ (27650148512713/100000000000000 : ℝ)^3407 := by
    have hnat : (930380663 : ℕ)^4431*100000000000000^3407 ≤ 27650148512713^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930380663 2500000000 27650148512713 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (975854659/2000000000 : ℝ)^4431 ≤ (4915841865011/12500000000000 : ℝ)^3407 := by
    have hnat : (975854659 : ℕ)^4431*12500000000000^3407 ≤ 4915841865011^3407*2000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975854659 2000000000 4915841865011 12500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(85319589/200000000 : ℝ), (930380663/2500000000 : ℝ), (975854659/2000000000 : ℝ)] ![(16511558275499/50000000000000 : ℝ), (27650148512713/100000000000000 : ℝ), (4915841865011/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(85319589/200000000 : ℝ)|^4431 ≤ (16511558275499/50000000000000 : ℝ)^3407
        have hw : |(85319589/200000000 : ℝ)|=(85319589/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(930380663/2500000000 : ℝ)|^4431 ≤ (27650148512713/100000000000000 : ℝ)^3407
        have hw : |(930380663/2500000000 : ℝ)|=(930380663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(975854659/2000000000 : ℝ)|^4431 ≤ (4915841865011/12500000000000 : ℝ)^3407
        have hw : |(975854659/2000000000 : ℝ)|=(975854659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s1_4 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1901019807/10000000000 : ℝ)*x 0 + (508137949/1000000000 : ℝ)*x 1 + (5595942689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1901019807/10000000000 : ℝ)^4431 ≤ (11541985995789/100000000000000 : ℝ)^3407 := by
    have hnat : (1901019807 : ℕ)^4431*100000000000000^3407 ≤ 11541985995789^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901019807 10000000000 11541985995789 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508137949/1000000000 : ℝ)^4431 ≤ (5182295408307/12500000000000 : ℝ)^3407 := by
    have hnat : (508137949 : ℕ)^4431*12500000000000^3407 ≤ 5182295408307^3407*1000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508137949 1000000000 5182295408307 12500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5595942689/10000000000 : ℝ)^4431 ≤ (46999650726579/100000000000000 : ℝ)^3407 := by
    have hnat : (5595942689 : ℕ)^4431*100000000000000^3407 ≤ 46999650726579^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5595942689 10000000000 46999650726579 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1901019807/10000000000 : ℝ), (508137949/1000000000 : ℝ), (5595942689/10000000000 : ℝ)] ![(11541985995789/100000000000000 : ℝ), (5182295408307/12500000000000 : ℝ), (46999650726579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1901019807/10000000000 : ℝ)|^4431 ≤ (11541985995789/100000000000000 : ℝ)^3407
        have hw : |(-1901019807/10000000000 : ℝ)|=(1901019807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(508137949/1000000000 : ℝ)|^4431 ≤ (5182295408307/12500000000000 : ℝ)^3407
        have hw : |(508137949/1000000000 : ℝ)|=(508137949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5595942689/10000000000 : ℝ)|^4431 ≤ (46999650726579/100000000000000 : ℝ)^3407
        have hw : |(5595942689/10000000000 : ℝ)|=(5595942689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s1_5 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256974937/10000000000 : ℝ)*x 0 + (-1659064701/10000000000 : ℝ)*x 1 + (2797971351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256974937/10000000000 : ℝ)^4431 ≤ (21665611140967/50000000000000 : ℝ)^3407 := by
    have hnat : (5256974937 : ℕ)^4431*50000000000000^3407 ≤ 21665611140967^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256974937 10000000000 21665611140967 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1659064701/10000000000 : ℝ)^4431 ≤ (2417281708649/25000000000000 : ℝ)^3407 := by
    have hnat : (1659064701 : ℕ)^4431*25000000000000^3407 ≤ 2417281708649^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1659064701 10000000000 2417281708649 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2797971351/5000000000 : ℝ)^4431 ≤ (46999650868581/100000000000000 : ℝ)^3407 := by
    have hnat : (2797971351 : ℕ)^4431*100000000000000^3407 ≤ 46999650868581^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2797971351 5000000000 46999650868581 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256974937/10000000000 : ℝ), (-1659064701/10000000000 : ℝ), (2797971351/5000000000 : ℝ)] ![(21665611140967/50000000000000 : ℝ), (2417281708649/25000000000000 : ℝ), (46999650868581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256974937/10000000000 : ℝ)|^4431 ≤ (21665611140967/50000000000000 : ℝ)^3407
        have hw : |(5256974937/10000000000 : ℝ)|=(5256974937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1659064701/10000000000 : ℝ)|^4431 ≤ (2417281708649/25000000000000 : ℝ)^3407
        have hw : |(-1659064701/10000000000 : ℝ)|=(1659064701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2797971351/5000000000 : ℝ)|^4431 ≤ (46999650868581/100000000000000 : ℝ)^3407
        have hw : |(2797971351/5000000000 : ℝ)|=(2797971351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s1_6 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314243751/2500000000 : ℝ)*x 0 + (2797971331/5000000000 : ℝ)*x 1 + (-207383083/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314243751/2500000000 : ℝ)^4431 ≤ (21665611500087/50000000000000 : ℝ)^3407 := by
    have hnat : (1314243751 : ℕ)^4431*50000000000000^3407 ≤ 21665611500087^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314243751 2500000000 21665611500087 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2797971331/5000000000 : ℝ)^4431 ≤ (11749912607913/25000000000000 : ℝ)^3407 := by
    have hnat : (2797971331 : ℕ)^4431*25000000000000^3407 ≤ 11749912607913^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2797971331 5000000000 11749912607913 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207383083/1250000000 : ℝ)^4431 ≤ (4834563277073/50000000000000 : ℝ)^3407 := by
    have hnat : (207383083 : ℕ)^4431*50000000000000^3407 ≤ 4834563277073^3407*1250000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207383083 1250000000 4834563277073 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314243751/2500000000 : ℝ), (2797971331/5000000000 : ℝ), (-207383083/1250000000 : ℝ)] ![(21665611500087/50000000000000 : ℝ), (11749912607913/25000000000000 : ℝ), (4834563277073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314243751/2500000000 : ℝ)|^4431 ≤ (21665611500087/50000000000000 : ℝ)^3407
        have hw : |(1314243751/2500000000 : ℝ)|=(1314243751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2797971331/5000000000 : ℝ)|^4431 ≤ (11749912607913/25000000000000 : ℝ)^3407
        have hw : |(2797971331/5000000000 : ℝ)|=(2797971331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-207383083/1250000000 : ℝ)|^4431 ≤ (4834563277073/50000000000000 : ℝ)^3407
        have hw : |(-207383083/1250000000 : ℝ)|=(207383083/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s1_7 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1066715369/2500000000 : ℝ)*x 0 + (4865473939/10000000000 : ℝ)*x 1 + (373555909/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066715369/2500000000 : ℝ)^4431 ≤ (33031996772431/100000000000000 : ℝ)^3407 := by
    have hnat : (1066715369 : ℕ)^4431*100000000000000^3407 ≤ 33031996772431^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066715369 2500000000 33031996772431 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4865473939/10000000000 : ℝ)^4431 ≤ (2448884095323/6250000000000 : ℝ)^3407 := by
    have hnat : (4865473939 : ℕ)^4431*6250000000000^3407 ≤ 2448884095323^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4865473939 10000000000 2448884095323 6250000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (373555909/1000000000 : ℝ)^4431 ≤ (1736616105367/6250000000000 : ℝ)^3407 := by
    have hnat : (373555909 : ℕ)^4431*6250000000000^3407 ≤ 1736616105367^3407*1000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373555909 1000000000 1736616105367 6250000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1066715369/2500000000 : ℝ), (4865473939/10000000000 : ℝ), (373555909/1000000000 : ℝ)] ![(33031996772431/100000000000000 : ℝ), (2448884095323/6250000000000 : ℝ), (1736616105367/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1066715369/2500000000 : ℝ)|^4431 ≤ (33031996772431/100000000000000 : ℝ)^3407
        have hw : |(1066715369/2500000000 : ℝ)|=(1066715369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4865473939/10000000000 : ℝ)|^4431 ≤ (2448884095323/6250000000000 : ℝ)^3407
        have hw : |(4865473939/10000000000 : ℝ)|=(4865473939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(373555909/1000000000 : ℝ)|^4431 ≤ (1736616105367/6250000000000 : ℝ)^3407
        have hw : |(373555909/1000000000 : ℝ)|=(373555909/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1467_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (163/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2229/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (771/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9427/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (163/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2229/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (163/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2229/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (163/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2229/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (163/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2229/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (163/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2229/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (163/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2229/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2229/100000 : ℝ) ^ (4429/1024 : ℝ) ≤ (716561402811/10000000000000000000 : ℝ) := by
    have hpowers : (2229/100000 : ℝ)^4429 ≤ (716561402811/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2229 : ℕ)^4429*10000000000000000000^1024 ≤ 716561402811^1024*100000^4429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2229 100000 716561402811 10000000000000000000 4429 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2229/100000 : ℝ)) (X := (716561402811/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (163/625 : ℝ) ^ (4429/1024 : ℝ) ≤ (149412287879597901/50000000000000000000 : ℝ) := by
    have hpowers : (163/625 : ℝ)^4429 ≤ (149412287879597901/50000000000000000000 : ℝ)^1024 := by
      have hnat : (163 : ℕ)^4429*50000000000000000000^1024 ≤ 149412287879597901^1024*625^4429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        163 625 149412287879597901 50000000000000000000 4429 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (163/625 : ℝ)) (X := (149412287879597901/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000000716561402811/5000000000000000000 : ℝ) ≤ (10000000331342893/10000000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (5000000716561402811/5000000000000000000 : ℝ)^1024 ≤ (10000000331342893/10000000000000000 : ℝ)^4429 := by
      have hnat : (5000000716561402811 : ℕ)^1024*10000000000000000^4429 ≤ 10000000331342893^4429*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000000716561402811 5000000000000000000 10000000331342893 10000000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000331342893/10000000000000000 : ℝ)) (X := (5000000716561402811/5000000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12537353967671652989/12500000000000000000 : ℝ) ≤ (625431323116827/625000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (12537353967671652989/12500000000000000000 : ℝ)^1024 ≤ (625431323116827/625000000000000 : ℝ)^4429 := by
      have hnat : (12537353967671652989 : ℕ)^1024*625000000000000^4429 ≤ 625431323116827^4429*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12537353967671652989 12500000000000000000 625431323116827 625000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625431323116827/625000000000000 : ℝ)) (X := (12537353967671652989/12500000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25149412287879597901/25000000000000000000 : ℝ) ≤ (10013802008395571/10000000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (25149412287879597901/25000000000000000000 : ℝ)^1024 ≤ (10013802008395571/10000000000000000 : ℝ)^4429 := by
      have hnat : (25149412287879597901 : ℕ)^1024*10000000000000000^4429 ≤ 10013802008395571^4429*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25149412287879597901 25000000000000000000 10013802008395571 10000000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013802008395571/10000000000000000 : ℝ)) (X := (25149412287879597901/25000000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(716561402811/10000000000000000000 : ℝ) ≤ ((238479243964708921681/238510000000000000000 : ℝ)+2*(6900838526339/2385100000000000 : ℝ)*(2229/100000 : ℝ))^(4429/1024 : ℝ) := by
    rw [show (238479243964708921681/238510000000000000000 : ℝ)+2*(6900838526339/2385100000000000 : ℝ)*(2229/100000 : ℝ)=(10000000331342893/10000000000000000 : ℝ) by norm_num, show 1+2*(716561402811/10000000000000000000 : ℝ)=(5000000716561402811/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(149412287879597901/50000000000000000000 : ℝ)+(716561402811/10000000000000000000 : ℝ) ≤ ((238479243964708921681/238510000000000000000 : ℝ)+(6900838526339/2385100000000000 : ℝ)*((163/625 : ℝ)+(2229/100000 : ℝ)))^(4429/1024 : ℝ) := by
    rw [show (238479243964708921681/238510000000000000000 : ℝ)+(6900838526339/2385100000000000 : ℝ)*((163/625 : ℝ)+(2229/100000 : ℝ))=(625431323116827/625000000000000 : ℝ) by norm_num, show 1+(149412287879597901/50000000000000000000 : ℝ)+(716561402811/10000000000000000000 : ℝ)=(12537353967671652989/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(149412287879597901/50000000000000000000 : ℝ) ≤ ((238479243964708921681/238510000000000000000 : ℝ)+2*(6900838526339/2385100000000000 : ℝ)*(163/625 : ℝ))^(4429/1024 : ℝ) := by
    rw [show (238479243964708921681/238510000000000000000 : ℝ)+2*(6900838526339/2385100000000000 : ℝ)*(163/625 : ℝ)=(10013802008395571/10000000000000000 : ℝ) by norm_num, show 1+2*(149412287879597901/50000000000000000000 : ℝ)=(25149412287879597901/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (238479243964708921681/238510000000000000000 : ℝ)*(X 1 0+X 2 0)+(6900838526339/2385100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (2229/100000 : ℝ)) (hi := (163/625 : ℝ)) (c := (238479243964708921681/238510000000000000000 : ℝ)) (alpha := (6900838526339/2385100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (238479243964708921681/238510000000000000000 : ℝ)*(X 0 1+X 2 1)+(6900838526339/2385100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (2229/100000 : ℝ)) (hi := (163/625 : ℝ)) (c := (238479243964708921681/238510000000000000000 : ℝ)) (alpha := (6900838526339/2385100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (238479243964708921681/238510000000000000000 : ℝ)*(X 0 2+X 1 2)+(6900838526339/2385100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (2229/100000 : ℝ)) (hi := (163/625 : ℝ)) (c := (238479243964708921681/238510000000000000000 : ℝ)) (alpha := (6900838526339/2385100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1900618367/10000000000 : ℝ)*X 0 0+(224093431/400000000 : ℝ)*X 0 1+(1268773693/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((337190157/625000000 : ℝ)*X 1 0+(-2179911549/10000000000 : ℝ)*X 1 1+(2537548049/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1348760907/2500000000 : ℝ)*X 2 0+(5075094891/10000000000 : ℝ)*X 2 1+(-54497791/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((85319589/200000000 : ℝ)*X 0 0+(930380663/2500000000 : ℝ)*X 0 1+(975854659/2000000000 : ℝ)*X 0 2+(85319589/200000000 : ℝ)*X 1 0+(930380663/2500000000 : ℝ)*X 1 1+(975854659/2000000000 : ℝ)*X 1 2+(85319589/200000000 : ℝ)*X 2 0+(930380663/2500000000 : ℝ)*X 2 1+(975854659/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1901019807/10000000000 : ℝ)*X 0 0+(508137949/1000000000 : ℝ)*X 0 1+(5595942689/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5256974937/10000000000 : ℝ)*X 1 0+(-1659064701/10000000000 : ℝ)*X 1 1+(2797971351/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1314243751/2500000000 : ℝ)*X 2 0+(2797971331/5000000000 : ℝ)*X 2 1+(-207383083/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1066715369/2500000000 : ℝ)*X 0 0+(4865473939/10000000000 : ℝ)*X 0 1+(373555909/1000000000 : ℝ)*X 0 2+(1066715369/2500000000 : ℝ)*X 1 0+(4865473939/10000000000 : ℝ)*X 1 1+(373555909/1000000000 : ℝ)*X 1 2+(1066715369/2500000000 : ℝ)*X 2 0+(4865473939/10000000000 : ℝ)*X 2 1+(373555909/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18758009218850710700758211823/2981375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1036564671/100000000000000 : ℝ)*(base19) + (87947353/6250000000000 : ℝ)*(base23) + (88619939/100000000000000 : ℝ)*(upper3) + (11733959/100000000000000 : ℝ)*(upper4) + (115905531/100000000000000 : ℝ)*(upper5) + (690110764164461/50000000000000 : ℝ)*(major0) + (690110764164461/50000000000000 : ℝ)*(major1) + (690110764164461/50000000000000 : ℝ)*(major2) + (1896677060066553/100000000000000 : ℝ)*(sp0) + (18966889520223/1000000000000 : ℝ)*(sp1) + (1896688581429323/100000000000000 : ℝ)*(sp2) + (17274962838899/2000000000000 : ℝ)*(sp3) + (12928520417/100000000000000 : ℝ)*(sp4) + (2358200777/50000000000000 : ℝ)*(sp7) + (107969107293313/12500000000000 : ℝ)*(f.failure) + (189668998858697/10000000000000 : ℝ)*(f.sum) + (19161350679153/29813750000000000000000000000 : ℝ)*base66 + (1850203881680433867/518500000000000000000000000000000 : ℝ)*base67 + (1194266775637566133/518500000000000000000000000000000 : ℝ)*base70 + (1921074391740066133/518500000000000000000000000000000 : ℝ)*base72 + (25863912834783/7453437500000000000000000000 : ℝ)*base73 + (3132545859801066133/518500000000000000000000000000000 : ℝ)*base76 + (2601080009254066133/518500000000000000000000000000000 : ℝ)*base78 + (2241802208247566133/518500000000000000000000000000000 : ℝ)*base80 + (72081137096777/29813750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (360259/125000000000000000000 : ℝ)*base90 + (360259/125000000000000000000 : ℝ)*base92 + (360259/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (335250506083590951841659/59627500000000000000000000000 : ℝ) := by norm_num
    linear_combination (53372619/5000000000000 : ℝ)*(base19) + (582756231/50000000000000 : ℝ)*(base23) + (146942399/100000000000000 : ℝ)*(upper3) + (3560121/12500000000000 : ℝ)*(lower4) + (24634643/20000000000000 : ℝ)*(upper5) + (707104544393467/50000000000000 : ℝ)*(major0) + (707104544393467/50000000000000 : ℝ)*(major1) + (707104544393467/50000000000000 : ℝ)*(major2) + (6253206927/100000000000000 : ℝ)*(sp1) + (349046503/5000000000000 : ℝ)*(sp2) + (1943395464668611/100000000000000 : ℝ)*(sp4) + (1943388144009303/100000000000000 : ℝ)*(sp5) + (194338731822609/10000000000000 : ℝ)*(sp6) + (885022525491441/100000000000000 : ℝ)*(sp7) + (885022525491441/100000000000000 : ℝ)*(f.failure) + (1943395464668611/100000000000000 : ℝ)*(f.sum) + (308950648240319/119255000000000000000000000000 : ℝ)*base66 + (2188679952482049651/518500000000000000000000000000000 : ℝ)*base68 + (2279784582687950349/518500000000000000000000000000000 : ℝ)*base69 + (252883680220950349/518500000000000000000000000000000 : ℝ)*base71 + (584142762839489/119255000000000000000000000000 : ℝ)*base74 + (3413229433587450349/518500000000000000000000000000000 : ℝ)*base75 + (3067379033621549651/518500000000000000000000000000000 : ℝ)*base78 + (1952548130507049651/518500000000000000000000000000000 : ℝ)*base80 + (75572186129869/29813750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (3816563/1000000000000000000000 : ℝ)*base90 + (3816563/1000000000000000000000 : ℝ)*base92 + (3816563/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1467_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (163/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2229/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (771/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9427/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1467_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1467_s2_0 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1930806649/10000000000 : ℝ)*x 0 + (2736928993/5000000000 : ℝ)*x 1 + (64801407/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1930806649/10000000000 : ℝ)^4431 ≤ (11777743599267/100000000000000 : ℝ)^3407 := by
    have hnat : (1930806649 : ℕ)^4431*100000000000000^3407 ≤ 11777743599267^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930806649 10000000000 11777743599267 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2736928993/5000000000 : ℝ)^4431 ≤ (45670486338329/100000000000000 : ℝ)^3407 := by
    have hnat : (2736928993 : ℕ)^4431*100000000000000^3407 ≤ 45670486338329^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736928993 5000000000 45670486338329 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64801407/125000000 : ℝ)^4431 ≤ (5318971255233/12500000000000 : ℝ)^3407 := by
    have hnat : (64801407 : ℕ)^4431*12500000000000^3407 ≤ 5318971255233^3407*125000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64801407 125000000 5318971255233 12500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1930806649/10000000000 : ℝ), (2736928993/5000000000 : ℝ), (64801407/125000000 : ℝ)] ![(11777743599267/100000000000000 : ℝ), (45670486338329/100000000000000 : ℝ), (5318971255233/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1930806649/10000000000 : ℝ)|^4431 ≤ (11777743599267/100000000000000 : ℝ)^3407
        have hw : |(-1930806649/10000000000 : ℝ)|=(1930806649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2736928993/5000000000 : ℝ)|^4431 ≤ (45670486338329/100000000000000 : ℝ)^3407
        have hw : |(2736928993/5000000000 : ℝ)|=(2736928993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(64801407/125000000 : ℝ)|^4431 ≤ (5318971255233/12500000000000 : ℝ)^3407
        have hw : |(64801407/125000000 : ℝ)|=(64801407/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s2_1 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362888537/10000000000 : ℝ)*x 0 + (-2080411411/10000000000 : ℝ)*x 1 + (2592056939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362888537/10000000000 : ℝ)^4431 ≤ (22235018672801/50000000000000 : ℝ)^3407 := by
    have hnat : (5362888537 : ℕ)^4431*50000000000000^3407 ≤ 22235018672801^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362888537 10000000000 22235018672801 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080411411/10000000000 : ℝ)^4431 ≤ (3244544631657/25000000000000 : ℝ)^3407 := by
    have hnat : (2080411411 : ℕ)^4431*25000000000000^3407 ≤ 3244544631657^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080411411 10000000000 3244544631657 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2592056939/5000000000 : ℝ)^4431 ≤ (1702071364467/4000000000000 : ℝ)^3407 := by
    have hnat : (2592056939 : ℕ)^4431*4000000000000^3407 ≤ 1702071364467^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592056939 5000000000 1702071364467 4000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362888537/10000000000 : ℝ), (-2080411411/10000000000 : ℝ), (2592056939/5000000000 : ℝ)] ![(22235018672801/50000000000000 : ℝ), (3244544631657/25000000000000 : ℝ), (1702071364467/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362888537/10000000000 : ℝ)|^4431 ≤ (22235018672801/50000000000000 : ℝ)^3407
        have hw : |(5362888537/10000000000 : ℝ)|=(5362888537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2080411411/10000000000 : ℝ)|^4431 ≤ (3244544631657/25000000000000 : ℝ)^3407
        have hw : |(-2080411411/10000000000 : ℝ)|=(2080411411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2592056939/5000000000 : ℝ)|^4431 ≤ (1702071364467/4000000000000 : ℝ)^3407
        have hw : |(2592056939/5000000000 : ℝ)|=(2592056939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s2_2 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681444709/5000000000 : ℝ)*x 0 + (1036822627/2000000000 : ℝ)*x 1 + (-2080411217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681444709/5000000000 : ℝ)^4431 ≤ (4447004684671/10000000000000 : ℝ)^3407 := by
    have hnat : (2681444709 : ℕ)^4431*10000000000000^3407 ≤ 4447004684671^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681444709 5000000000 4447004684671 10000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036822627/2000000000 : ℝ)^4431 ≤ (42551776180059/100000000000000 : ℝ)^3407 := by
    have hnat : (1036822627 : ℕ)^4431*100000000000000^3407 ≤ 42551776180059^3407*2000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036822627 2000000000 42551776180059 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2080411217/10000000000 : ℝ)^4431 ≤ (648908847633/5000000000000 : ℝ)^3407 := by
    have hnat : (2080411217 : ℕ)^4431*5000000000000^3407 ≤ 648908847633^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080411217 10000000000 648908847633 5000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681444709/5000000000 : ℝ), (1036822627/2000000000 : ℝ), (-2080411217/10000000000 : ℝ)] ![(4447004684671/10000000000000 : ℝ), (42551776180059/100000000000000 : ℝ), (648908847633/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681444709/5000000000 : ℝ)|^4431 ≤ (4447004684671/10000000000000 : ℝ)^3407
        have hw : |(2681444709/5000000000 : ℝ)|=(2681444709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036822627/2000000000 : ℝ)|^4431 ≤ (42551776180059/100000000000000 : ℝ)^3407
        have hw : |(1036822627/2000000000 : ℝ)|=(1036822627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2080411217/10000000000 : ℝ)|^4431 ≤ (648908847633/5000000000000 : ℝ)^3407
        have hw : |(-2080411217/10000000000 : ℝ)|=(2080411217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s2_3 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4287468447/10000000000 : ℝ)*x 0 + (3979741061/10000000000 : ℝ)*x 1 + (576997963/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4287468447/10000000000 : ℝ)^4431 ≤ (33239624233349/100000000000000 : ℝ)^3407 := by
    have hnat : (4287468447 : ℕ)^4431*100000000000000^3407 ≤ 33239624233349^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4287468447 10000000000 33239624233349 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3979741061/10000000000 : ℝ)^4431 ≤ (15085444588079/50000000000000 : ℝ)^3407 := by
    have hnat : (3979741061 : ℕ)^4431*50000000000000^3407 ≤ 15085444588079^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979741061 10000000000 15085444588079 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (576997963/1250000000 : ℝ)^4431 ≤ (3658948657341/10000000000000 : ℝ)^3407 := by
    have hnat : (576997963 : ℕ)^4431*10000000000000^3407 ≤ 3658948657341^3407*1250000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576997963 1250000000 3658948657341 10000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4287468447/10000000000 : ℝ), (3979741061/10000000000 : ℝ), (576997963/1250000000 : ℝ)] ![(33239624233349/100000000000000 : ℝ), (15085444588079/50000000000000 : ℝ), (3658948657341/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4287468447/10000000000 : ℝ)|^4431 ≤ (33239624233349/100000000000000 : ℝ)^3407
        have hw : |(4287468447/10000000000 : ℝ)|=(4287468447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3979741061/10000000000 : ℝ)|^4431 ≤ (15085444588079/50000000000000 : ℝ)^3407
        have hw : |(3979741061/10000000000 : ℝ)|=(3979741061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(576997963/1250000000 : ℝ)|^4431 ≤ (3658948657341/10000000000000 : ℝ)^3407
        have hw : |(576997963/1250000000 : ℝ)|=(576997963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s2_4 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1930873087/10000000000 : ℝ)*x 0 + (2593010277/5000000000 : ℝ)*x 1 + (5471932147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1930873087/10000000000 : ℝ)^4431 ≤ (11778270673423/100000000000000 : ℝ)^3407 := by
    have hnat : (1930873087 : ℕ)^4431*100000000000000^3407 ≤ 11778270673423^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930873087 10000000000 11778270673423 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593010277/5000000000 : ℝ)^4431 ≤ (42572139235971/100000000000000 : ℝ)^3407 := by
    have hnat : (2593010277 : ℕ)^4431*100000000000000^3407 ≤ 42572139235971^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593010277 5000000000 42572139235971 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5471932147/10000000000 : ℝ)^4431 ≤ (22824795034917/50000000000000 : ℝ)^3407 := by
    have hnat : (5471932147 : ℕ)^4431*50000000000000^3407 ≤ 22824795034917^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471932147 10000000000 22824795034917 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1930873087/10000000000 : ℝ), (2593010277/5000000000 : ℝ), (5471932147/10000000000 : ℝ)] ![(11778270673423/100000000000000 : ℝ), (42572139235971/100000000000000 : ℝ), (22824795034917/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1930873087/10000000000 : ℝ)|^4431 ≤ (11778270673423/100000000000000 : ℝ)^3407
        have hw : |(-1930873087/10000000000 : ℝ)|=(1930873087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593010277/5000000000 : ℝ)|^4431 ≤ (42572139235971/100000000000000 : ℝ)^3407
        have hw : |(2593010277/5000000000 : ℝ)|=(2593010277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5471932147/10000000000 : ℝ)|^4431 ≤ (22824795034917/50000000000000 : ℝ)^3407
        have hw : |(5471932147/10000000000 : ℝ)|=(5471932147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s2_5 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287352743/10000000000 : ℝ)*x 0 + (-14004633/78125000 : ℝ)*x 1 + (1367983057/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287352743/10000000000 : ℝ)^4431 ≤ (5457144334243/12500000000000 : ℝ)^3407 := by
    have hnat : (5287352743 : ℕ)^4431*12500000000000^3407 ≤ 5457144334243^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287352743 10000000000 5457144334243 12500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14004633/78125000 : ℝ)^4431 ≤ (10693254365951/100000000000000 : ℝ)^3407 := by
    have hnat : (14004633 : ℕ)^4431*100000000000000^3407 ≤ 10693254365951^3407*78125000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14004633 78125000 10693254365951 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1367983057/2500000000 : ℝ)^4431 ≤ (11412397737169/25000000000000 : ℝ)^3407 := by
    have hnat : (1367983057 : ℕ)^4431*25000000000000^3407 ≤ 11412397737169^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367983057 2500000000 11412397737169 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287352743/10000000000 : ℝ), (-14004633/78125000 : ℝ), (1367983057/2500000000 : ℝ)] ![(5457144334243/12500000000000 : ℝ), (10693254365951/100000000000000 : ℝ), (11412397737169/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287352743/10000000000 : ℝ)|^4431 ≤ (5457144334243/12500000000000 : ℝ)^3407
        have hw : |(5287352743/10000000000 : ℝ)|=(5287352743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-14004633/78125000 : ℝ)|^4431 ≤ (10693254365951/100000000000000 : ℝ)^3407
        have hw : |(-14004633/78125000 : ℝ)|=(14004633/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1367983057/2500000000 : ℝ)|^4431 ≤ (11412397737169/25000000000000 : ℝ)^3407
        have hw : |(1367983057/2500000000 : ℝ)|=(1367983057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s2_6 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287353101/10000000000 : ℝ)*x 0 + (5471932239/10000000000 : ℝ)*x 1 + (-1792592513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287353101/10000000000 : ℝ)^4431 ≤ (8731431703671/20000000000000 : ℝ)^3407 := by
    have hnat : (5287353101 : ℕ)^4431*20000000000000^3407 ≤ 8731431703671^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287353101 10000000000 8731431703671 20000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5471932239/10000000000 : ℝ)^4431 ≤ (1825983642721/4000000000000 : ℝ)^3407 := by
    have hnat : (5471932239 : ℕ)^4431*4000000000000^3407 ≤ 1825983642721^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471932239 10000000000 1825983642721 4000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1792592513/10000000000 : ℝ)^4431 ≤ (534662520077/5000000000000 : ℝ)^3407 := by
    have hnat : (1792592513 : ℕ)^4431*5000000000000^3407 ≤ 534662520077^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792592513 10000000000 534662520077 5000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287353101/10000000000 : ℝ), (5471932239/10000000000 : ℝ), (-1792592513/10000000000 : ℝ)] ![(8731431703671/20000000000000 : ℝ), (1825983642721/4000000000000 : ℝ), (534662520077/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287353101/10000000000 : ℝ)|^4431 ≤ (8731431703671/20000000000000 : ℝ)^3407
        have hw : |(5287353101/10000000000 : ℝ)|=(5287353101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5471932239/10000000000 : ℝ)|^4431 ≤ (1825983642721/4000000000000 : ℝ)^3407
        have hw : |(5471932239/10000000000 : ℝ)|=(5471932239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1792592513/10000000000 : ℝ)|^4431 ≤ (534662520077/5000000000000 : ℝ)^3407
        have hw : |(-1792592513/10000000000 : ℝ)|=(1792592513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s2_7 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2143807861/5000000000 : ℝ)*x 0 + (2305897179/5000000000 : ℝ)*x 1 + (3983969491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143807861/5000000000 : ℝ)^4431 ≤ (8310277299451/25000000000000 : ℝ)^3407 := by
    have hnat : (2143807861 : ℕ)^4431*25000000000000^3407 ≤ 8310277299451^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143807861 5000000000 8310277299451 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2305897179/5000000000 : ℝ)^4431 ≤ (9136575996873/25000000000000 : ℝ)^3407 := by
    have hnat : (2305897179 : ℕ)^4431*25000000000000^3407 ≤ 9136575996873^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2305897179 5000000000 9136575996873 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3983969491/10000000000 : ℝ)^4431 ≤ (3776573350831/12500000000000 : ℝ)^3407 := by
    have hnat : (3983969491 : ℕ)^4431*12500000000000^3407 ≤ 3776573350831^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3983969491 10000000000 3776573350831 12500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2143807861/5000000000 : ℝ), (2305897179/5000000000 : ℝ), (3983969491/10000000000 : ℝ)] ![(8310277299451/25000000000000 : ℝ), (9136575996873/25000000000000 : ℝ), (3776573350831/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2143807861/5000000000 : ℝ)|^4431 ≤ (8310277299451/25000000000000 : ℝ)^3407
        have hw : |(2143807861/5000000000 : ℝ)|=(2143807861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2305897179/5000000000 : ℝ)|^4431 ≤ (9136575996873/25000000000000 : ℝ)^3407
        have hw : |(2305897179/5000000000 : ℝ)|=(2305897179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3983969491/10000000000 : ℝ)|^4431 ≤ (3776573350831/12500000000000 : ℝ)^3407
        have hw : |(3983969491/10000000000 : ℝ)|=(3983969491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1467_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9427/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (771/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10067/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8097/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9427/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (771/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9427/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (771/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9427/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (771/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9427/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (771/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9427/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (771/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9427/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (771/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (771/10000 : ℝ) ^ (4429/1024 : ℝ) ≤ (1535652011225429/100000000000000000000 : ℝ) := by
    have hpowers : (771/10000 : ℝ)^4429 ≤ (1535652011225429/100000000000000000000 : ℝ)^1024 := by
      have hnat : (771 : ℕ)^4429*100000000000000000000^1024 ≤ 1535652011225429^1024*10000^4429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        771 10000 1535652011225429 100000000000000000000 4429 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (771/10000 : ℝ)) (X := (1535652011225429/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9427/50000 : ℝ) ^ (4429/1024 : ℝ) ≤ (73447772066272317/100000000000000000000 : ℝ) := by
    have hpowers : (9427/50000 : ℝ)^4429 ≤ (73447772066272317/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9427 : ℕ)^4429*100000000000000000000^1024 ≤ 73447772066272317^1024*50000^4429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9427 50000 73447772066272317 100000000000000000000 4429 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9427/50000 : ℝ)) (X := (73447772066272317/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001535652011225429/50000000000000000000 : ℝ) ≤ (10000071008764721/10000000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (50001535652011225429/50000000000000000000 : ℝ)^1024 ≤ (10000071008764721/10000000000000000 : ℝ)^4429 := by
      have hnat : (50001535652011225429 : ℕ)^1024*10000000000000000^4429 ≤ 10000071008764721^4429*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001535652011225429 50000000000000000000 10000071008764721 10000000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000071008764721/10000000000000000 : ℝ)) (X := (50001535652011225429/50000000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50037491712038748873/50000000000000000000 : ℝ) ≤ (1250216642877849/1250000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (50037491712038748873/50000000000000000000 : ℝ)^1024 ≤ (1250216642877849/1250000000000000 : ℝ)^4429 := by
      have hnat : (50037491712038748873 : ℕ)^1024*1250000000000000^4429 ≤ 1250216642877849^4429*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037491712038748873 50000000000000000000 1250216642877849 1250000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250216642877849/1250000000000000 : ℝ)) (X := (50037491712038748873/50000000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50073447772066272317/50000000000000000000 : ℝ) ≤ (10003395277280863/10000000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (50073447772066272317/50000000000000000000 : ℝ)^1024 ≤ (10003395277280863/10000000000000000 : ℝ)^4429 := by
      have hnat : (50073447772066272317 : ℕ)^1024*10000000000000000^4429 ≤ 10003395277280863^4429*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50073447772066272317 50000000000000000000 10003395277280863 10000000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003395277280863/10000000000000000 : ℝ)) (X := (50073447772066272317/50000000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1535652011225429/100000000000000000000 : ℝ) ≤ ((3979112900407664143/3980000000000000000 : ℝ)+2*(237447751153/159200000000000 : ℝ)*(771/10000 : ℝ))^(4429/1024 : ℝ) := by
    rw [show (3979112900407664143/3980000000000000000 : ℝ)+2*(237447751153/159200000000000 : ℝ)*(771/10000 : ℝ)=(10000071008764721/10000000000000000 : ℝ) by norm_num, show 1+2*(1535652011225429/100000000000000000000 : ℝ)=(50001535652011225429/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(73447772066272317/100000000000000000000 : ℝ)+(1535652011225429/100000000000000000000 : ℝ) ≤ ((3979112900407664143/3980000000000000000 : ℝ)+(237447751153/159200000000000 : ℝ)*((9427/50000 : ℝ)+(771/10000 : ℝ)))^(4429/1024 : ℝ) := by
    rw [show (3979112900407664143/3980000000000000000 : ℝ)+(237447751153/159200000000000 : ℝ)*((9427/50000 : ℝ)+(771/10000 : ℝ))=(1250216642877849/1250000000000000 : ℝ) by norm_num, show 1+(73447772066272317/100000000000000000000 : ℝ)+(1535652011225429/100000000000000000000 : ℝ)=(50037491712038748873/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(73447772066272317/100000000000000000000 : ℝ) ≤ ((3979112900407664143/3980000000000000000 : ℝ)+2*(237447751153/159200000000000 : ℝ)*(9427/50000 : ℝ))^(4429/1024 : ℝ) := by
    rw [show (3979112900407664143/3980000000000000000 : ℝ)+2*(237447751153/159200000000000 : ℝ)*(9427/50000 : ℝ)=(10003395277280863/10000000000000000 : ℝ) by norm_num, show 1+2*(73447772066272317/100000000000000000000 : ℝ)=(50073447772066272317/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3979112900407664143/3980000000000000000 : ℝ)*(X 1 0+X 2 0)+(237447751153/159200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (771/10000 : ℝ)) (hi := (9427/50000 : ℝ)) (c := (3979112900407664143/3980000000000000000 : ℝ)) (alpha := (237447751153/159200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3979112900407664143/3980000000000000000 : ℝ)*(X 0 1+X 2 1)+(237447751153/159200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (771/10000 : ℝ)) (hi := (9427/50000 : ℝ)) (c := (3979112900407664143/3980000000000000000 : ℝ)) (alpha := (237447751153/159200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3979112900407664143/3980000000000000000 : ℝ)*(X 0 2+X 1 2)+(237447751153/159200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (771/10000 : ℝ)) (hi := (9427/50000 : ℝ)) (c := (3979112900407664143/3980000000000000000 : ℝ)) (alpha := (237447751153/159200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1930806649/10000000000 : ℝ)*X 0 0+(2736928993/5000000000 : ℝ)*X 0 1+(64801407/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5362888537/10000000000 : ℝ)*X 1 0+(-2080411411/10000000000 : ℝ)*X 1 1+(2592056939/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2681444709/5000000000 : ℝ)*X 2 0+(1036822627/2000000000 : ℝ)*X 2 1+(-2080411217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4287468447/10000000000 : ℝ)*X 0 0+(3979741061/10000000000 : ℝ)*X 0 1+(576997963/1250000000 : ℝ)*X 0 2+(4287468447/10000000000 : ℝ)*X 1 0+(3979741061/10000000000 : ℝ)*X 1 1+(576997963/1250000000 : ℝ)*X 1 2+(4287468447/10000000000 : ℝ)*X 2 0+(3979741061/10000000000 : ℝ)*X 2 1+(576997963/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1930873087/10000000000 : ℝ)*X 0 0+(2593010277/5000000000 : ℝ)*X 0 1+(5471932147/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287352743/10000000000 : ℝ)*X 1 0+(-14004633/78125000 : ℝ)*X 1 1+(1367983057/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5287353101/10000000000 : ℝ)*X 2 0+(5471932239/10000000000 : ℝ)*X 2 1+(-1792592513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2143807861/5000000000 : ℝ)*X 0 0+(2305897179/5000000000 : ℝ)*X 0 1+(3983969491/10000000000 : ℝ)*X 0 2+(2143807861/5000000000 : ℝ)*X 1 0+(2305897179/5000000000 : ℝ)*X 1 1+(3983969491/10000000000 : ℝ)*X 1 2+(2143807861/5000000000 : ℝ)*X 2 0+(2305897179/5000000000 : ℝ)*X 2 1+(3983969491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (354873258297999855549795099/49750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1123484837/100000000000000 : ℝ)*(base19) + (1405176733/100000000000000 : ℝ)*(base23) + (14226547/10000000000000 : ℝ)*(upper3) + (15299637/10000000000000 : ℝ)*(upper4) + (91854349/50000000000000 : ℝ)*(upper5) + (1255777083373731/50000000000000 : ℝ)*(major0) + (1255777083373731/50000000000000 : ℝ)*(major1) + (1255777083373731/50000000000000 : ℝ)*(major2) + (3451329230042469/100000000000000 : ℝ)*(sp0) + (690271553368791/20000000000000 : ℝ)*(sp1) + (3451357485152059/100000000000000 : ℝ)*(sp2) + (1571737568564221/100000000000000 : ℝ)*(sp3) + (29660286323/100000000000000 : ℝ)*(sp4) + (5818415439/50000000000000 : ℝ)*(sp7) + (1571749205395099/100000000000000 : ℝ)*(f.failure) + (431419861291099/12500000000000 : ℝ)*(f.sum) + (613827057737/3980000000000000000000000000 : ℝ)*base66 + (892094260376097467/199000000000000000000000000000000 : ℝ)*base68 + (1210450206154097467/199000000000000000000000000000000 : ℝ)*base70 + (1785644419097467/199000000000000000000000000000000 : ℝ)*base72 + (396364152157/3980000000000000000000000000 : ℝ)*base74 + (291706991414902533/199000000000000000000000000000000 : ℝ)*base75 + (876344441992097467/199000000000000000000000000000000 : ℝ)*base78 + (469478873587097467/199000000000000000000000000000000 : ℝ)*base80 + (9735663316577/3980000000000000000000000000 : ℝ)*base82 + (7028657/1000000000000000000000 : ℝ)*base90 + (7028657/1000000000000000000000 : ℝ)*base92 + (7028657/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31687444094399770037208957/3980000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (828705681/100000000000000 : ℝ)*(base19) + (262594777/20000000000000 : ℝ)*(base23) + (155763989/100000000000000 : ℝ)*(upper3) + (70413581/100000000000000 : ℝ)*(lower4) + (22979017/12500000000000 : ℝ)*(upper5) + (101807742870267/4000000000000 : ℝ)*(major0) + (101807742870267/4000000000000 : ℝ)*(major1) + (101807742870267/4000000000000 : ℝ)*(major2) + (2152486157/25000000000000 : ℝ)*(sp1) + (4152256779/25000000000000 : ℝ)*(sp2) + (349758588384363/10000000000000 : ℝ)*(sp4) + (87439411129833/2500000000000 : ℝ)*(sp5) + (874391990460657/25000000000000 : ℝ)*(sp6) + (159280099428073/10000000000000 : ℝ)*(sp7) + (159280099428073/10000000000000 : ℝ)*(f.failure) + (349758588384363/10000000000000 : ℝ)*(f.sum) + (1140572269851/318400000000000000000000000 : ℝ)*base65 + (56448740081811181/15920000000000000000000000000000 : ℝ)*base67 + (140180144376211181/15920000000000000000000000000000 : ℝ)*base69 + (29713477001491181/15920000000000000000000000000000 : ℝ)*base71 + (8563493828471/1592000000000000000000000000 : ℝ)*base73 + (278580811890931181/15920000000000000000000000000000 : ℝ)*base75 + (20084950364908819/15920000000000000000000000000000 : ℝ)*base78 + (89522830908371181/15920000000000000000000000000000 : ℝ)*base79 + (10729835621607/1592000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (710939/100000000000000000000 : ℝ)*base90 + (710939/100000000000000000000 : ℝ)*base92 + (710939/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1467_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9427/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (771/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10067/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8097/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1467_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1467_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10067/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8097/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1467_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1467_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1467_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10067/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8097/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1467_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

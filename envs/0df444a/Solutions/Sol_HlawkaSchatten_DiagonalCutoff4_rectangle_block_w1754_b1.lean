-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1754_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:23:19.465513+00:00
-- url     : https://prove2.me/submissions/aa7e243e-2548-44ff-9074-f88d89fe53b0

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
theorem support_rectangle_w1754_box_0 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-32801023/400000000 : ℝ)*x 0 + (2710500649/5000000000 : ℝ)*x 1 + (542100201/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32801023/400000000 : ℝ)^5839 ≤ (4817618820241/100000000000000 : ℝ)^4815 := by
    have hnat : (32801023 : ℕ)^5839*100000000000000^4815 ≤ 4817618820241^4815*400000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32801023 400000000 4817618820241 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2710500649/5000000000 : ℝ)^5839 ≤ (47591186794597/100000000000000 : ℝ)^4815 := by
    have hnat : (2710500649 : ℕ)^5839*100000000000000^4815 ≤ 47591186794597^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710500649 5000000000 47591186794597 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542100201/1000000000 : ℝ)^5839 ≤ (47591194374597/100000000000000 : ℝ)^4815 := by
    have hnat : (542100201 : ℕ)^5839*100000000000000^4815 ≤ 47591194374597^4815*1000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542100201 1000000000 47591194374597 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-32801023/400000000 : ℝ), (2710500649/5000000000 : ℝ), (542100201/1000000000 : ℝ)] ![(4817618820241/100000000000000 : ℝ), (47591186794597/100000000000000 : ℝ), (47591194374597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-32801023/400000000 : ℝ)|^5839 ≤ (4817618820241/100000000000000 : ℝ)^4815
        have hw : |(-32801023/400000000 : ℝ)|=(32801023/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2710500649/5000000000 : ℝ)|^5839 ≤ (47591186794597/100000000000000 : ℝ)^4815
        have hw : |(2710500649/5000000000 : ℝ)|=(2710500649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542100201/1000000000 : ℝ)|^5839 ≤ (47591194374597/100000000000000 : ℝ)^4815
        have hw : |(542100201/1000000000 : ℝ)|=(542100201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_box_1 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5193997979/10000000000 : ℝ)*x 0 + (-572609991/5000000000 : ℝ)*x 1 + (5421001173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5193997979/10000000000 : ℝ)^5839 ≤ (112963438967/250000000000 : ℝ)^4815 := by
    have hnat : (5193997979 : ℕ)^5839*250000000000^4815 ≤ 112963438967^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193997979 10000000000 112963438967 250000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (572609991/5000000000 : ℝ)^5839 ≤ (902929866501/12500000000000 : ℝ)^4815 := by
    have hnat : (572609991 : ℕ)^5839*12500000000000^4815 ≤ 902929866501^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572609991 5000000000 902929866501 12500000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5421001173/10000000000 : ℝ)^5839 ≤ (47591185463839/100000000000000 : ℝ)^4815 := by
    have hnat : (5421001173 : ℕ)^5839*100000000000000^4815 ≤ 47591185463839^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421001173 10000000000 47591185463839 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5193997979/10000000000 : ℝ), (-572609991/5000000000 : ℝ), (5421001173/10000000000 : ℝ)] ![(112963438967/250000000000 : ℝ), (902929866501/12500000000000 : ℝ), (47591185463839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5193997979/10000000000 : ℝ)|^5839 ≤ (112963438967/250000000000 : ℝ)^4815
        have hw : |(5193997979/10000000000 : ℝ)|=(5193997979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-572609991/5000000000 : ℝ)|^5839 ≤ (902929866501/12500000000000 : ℝ)^4815
        have hw : |(-572609991/5000000000 : ℝ)|=(572609991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5421001173/10000000000 : ℝ)|^5839 ≤ (47591185463839/100000000000000 : ℝ)^4815
        have hw : |(5421001173/10000000000 : ℝ)|=(5421001173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_box_2 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596998649/5000000000 : ℝ)*x 0 + (271050091/500000000 : ℝ)*x 1 + (-572610011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596998649/5000000000 : ℝ)^5839 ≤ (11296342100621/25000000000000 : ℝ)^4815 := by
    have hnat : (2596998649 : ℕ)^5839*25000000000000^4815 ≤ 11296342100621^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596998649 5000000000 11296342100621 25000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271050091/500000000 : ℝ)^5839 ≤ (11897798087961/25000000000000 : ℝ)^4815 := by
    have hnat : (271050091 : ℕ)^5839*25000000000000^4815 ≤ 11897798087961^4815*500000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271050091 500000000 11897798087961 25000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (572610011/5000000000 : ℝ)^5839 ≤ (7223439237963/100000000000000 : ℝ)^4815 := by
    have hnat : (572610011 : ℕ)^5839*100000000000000^4815 ≤ 7223439237963^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572610011 5000000000 7223439237963 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596998649/5000000000 : ℝ), (271050091/500000000 : ℝ), (-572610011/5000000000 : ℝ)] ![(11296342100621/25000000000000 : ℝ), (11897798087961/25000000000000 : ℝ), (7223439237963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596998649/5000000000 : ℝ)|^5839 ≤ (11296342100621/25000000000000 : ℝ)^4815
        have hw : |(2596998649/5000000000 : ℝ)|=(2596998649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271050091/500000000 : ℝ)|^5839 ≤ (11897798087961/25000000000000 : ℝ)^4815
        have hw : |(271050091/500000000 : ℝ)|=(271050091/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-572610011/5000000000 : ℝ)|^5839 ≤ (7223439237963/100000000000000 : ℝ)^4815
        have hw : |(-572610011/5000000000 : ℝ)|=(572610011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_box_3 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (226916849/500000000 : ℝ)*x 0 + (3788360233/10000000000 : ℝ)*x 1 + (947090007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (226916849/500000000 : ℝ)^5839 ≤ (959112186939/2500000000000 : ℝ)^4815 := by
    have hnat : (226916849 : ℕ)^5839*2500000000000^4815 ≤ 959112186939^4815*500000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226916849 500000000 959112186939 2500000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3788360233/10000000000 : ℝ)^5839 ≤ (30817757268181/100000000000000 : ℝ)^4815 := by
    have hnat : (3788360233 : ℕ)^5839*100000000000000^4815 ≤ 30817757268181^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3788360233 10000000000 30817757268181 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (947090007/2500000000 : ℝ)^5839 ≤ (770443881147/2500000000000 : ℝ)^4815 := by
    have hnat : (947090007 : ℕ)^5839*2500000000000^4815 ≤ 770443881147^4815*2500000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947090007 2500000000 770443881147 2500000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(226916849/500000000 : ℝ), (3788360233/10000000000 : ℝ), (947090007/2500000000 : ℝ)] ![(959112186939/2500000000000 : ℝ), (30817757268181/100000000000000 : ℝ), (770443881147/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(226916849/500000000 : ℝ)|^5839 ≤ (959112186939/2500000000000 : ℝ)^4815
        have hw : |(226916849/500000000 : ℝ)|=(226916849/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3788360233/10000000000 : ℝ)|^5839 ≤ (30817757268181/100000000000000 : ℝ)^4815
        have hw : |(3788360233/10000000000 : ℝ)|=(3788360233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(947090007/2500000000 : ℝ)|^5839 ≤ (770443881147/2500000000000 : ℝ)^4815
        have hw : |(947090007/2500000000 : ℝ)|=(947090007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_box_4 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1619882921/10000000000 : ℝ)*x 0 + (512897679/1000000000 : ℝ)*x 1 + (1025795499/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1619882921/10000000000 : ℝ)^5839 ≤ (687456970687/6250000000000 : ℝ)^4815 := by
    have hnat : (1619882921 : ℕ)^5839*6250000000000^4815 ≤ 687456970687^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1619882921 10000000000 687456970687 6250000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512897679/1000000000 : ℝ)^5839 ≤ (22250170260883/50000000000000 : ℝ)^4815 := by
    have hnat : (512897679 : ℕ)^5839*50000000000000^4815 ≤ 22250170260883^4815*1000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512897679 1000000000 22250170260883 50000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025795499/2000000000 : ℝ)^5839 ≤ (22250173969687/50000000000000 : ℝ)^4815 := by
    have hnat : (1025795499 : ℕ)^5839*50000000000000^4815 ≤ 22250173969687^4815*2000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025795499 2000000000 22250173969687 50000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1619882921/10000000000 : ℝ), (512897679/1000000000 : ℝ), (1025795499/2000000000 : ℝ)] ![(687456970687/6250000000000 : ℝ), (22250170260883/50000000000000 : ℝ), (22250173969687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1619882921/10000000000 : ℝ)|^5839 ≤ (687456970687/6250000000000 : ℝ)^4815
        have hw : |(-1619882921/10000000000 : ℝ)|=(1619882921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(512897679/1000000000 : ℝ)|^5839 ≤ (22250170260883/50000000000000 : ℝ)^4815
        have hw : |(512897679/1000000000 : ℝ)|=(512897679/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1025795499/2000000000 : ℝ)|^5839 ≤ (22250173969687/50000000000000 : ℝ)^4815
        have hw : |(1025795499/2000000000 : ℝ)|=(1025795499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_box_5 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1347288671/2500000000 : ℝ)*x 0 + (-1277499247/10000000000 : ℝ)*x 1 + (1282244373/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347288671/2500000000 : ℝ)^5839 ≤ (23626178859/50000000000 : ℝ)^4815 := by
    have hnat : (1347288671 : ℕ)^5839*50000000000^4815 ≤ 23626178859^4815*2500000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347288671 2500000000 23626178859 50000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1277499247/10000000000 : ℝ)^5839 ≤ (2061823590727/25000000000000 : ℝ)^4815 := by
    have hnat : (1277499247 : ℕ)^5839*25000000000000^4815 ≤ 2061823590727^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1277499247 10000000000 2061823590727 25000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1282244373/2500000000 : ℝ)^5839 ≤ (4450034790781/10000000000000 : ℝ)^4815 := by
    have hnat : (1282244373 : ℕ)^5839*10000000000000^4815 ≤ 4450034790781^4815*2500000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282244373 2500000000 4450034790781 10000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1347288671/2500000000 : ℝ), (-1277499247/10000000000 : ℝ), (1282244373/2500000000 : ℝ)] ![(23626178859/50000000000 : ℝ), (2061823590727/25000000000000 : ℝ), (4450034790781/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1347288671/2500000000 : ℝ)|^5839 ≤ (23626178859/50000000000 : ℝ)^4815
        have hw : |(1347288671/2500000000 : ℝ)|=(1347288671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1277499247/10000000000 : ℝ)|^5839 ≤ (2061823590727/25000000000000 : ℝ)^4815
        have hw : |(-1277499247/10000000000 : ℝ)|=(1277499247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1282244373/2500000000 : ℝ)|^5839 ≤ (4450034790781/10000000000000 : ℝ)^4815
        have hw : |(1282244373/2500000000 : ℝ)|=(1282244373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_box_6 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389155227/10000000000 : ℝ)*x 0 + (5128977213/10000000000 : ℝ)*x 1 + (-319374721/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389155227/10000000000 : ℝ)^5839 ≤ (5906545436447/12500000000000 : ℝ)^4815 := by
    have hnat : (5389155227 : ℕ)^5839*12500000000000^4815 ≤ 5906545436447^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389155227 10000000000 5906545436447 12500000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5128977213/10000000000 : ℝ)^5839 ≤ (44500344972331/100000000000000 : ℝ)^4815 := by
    have hnat : (5128977213 : ℕ)^5839*100000000000000^4815 ≤ 44500344972331^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128977213 10000000000 44500344972331 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319374721/2500000000 : ℝ)^5839 ≤ (2061822880267/25000000000000 : ℝ)^4815 := by
    have hnat : (319374721 : ℕ)^5839*25000000000000^4815 ≤ 2061822880267^4815*2500000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319374721 2500000000 2061822880267 25000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389155227/10000000000 : ℝ), (5128977213/10000000000 : ℝ), (-319374721/2500000000 : ℝ)] ![(5906545436447/12500000000000 : ℝ), (44500344972331/100000000000000 : ℝ), (2061822880267/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389155227/10000000000 : ℝ)|^5839 ≤ (5906545436447/12500000000000 : ℝ)^4815
        have hw : |(5389155227/10000000000 : ℝ)|=(5389155227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5128977213/10000000000 : ℝ)|^5839 ≤ (44500344972331/100000000000000 : ℝ)^4815
        have hw : |(5128977213/10000000000 : ℝ)|=(5128977213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-319374721/2500000000 : ℝ)|^5839 ≤ (2061822880267/25000000000000 : ℝ)^4815
        have hw : |(-319374721/2500000000 : ℝ)|=(319374721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_box_7 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (862403929/2500000000 : ℝ)*x 0 + (86612501/200000000 : ℝ)*x 1 + (4330625797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862403929/2500000000 : ℝ)^5839 ≤ (27508632226013/100000000000000 : ℝ)^4815 := by
    have hnat : (862403929 : ℕ)^5839*100000000000000^4815 ≤ 27508632226013^4815*2500000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862403929 2500000000 27508632226013 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86612501/200000000 : ℝ)^5839 ≤ (1812284004569/5000000000000 : ℝ)^4815 := by
    have hnat : (86612501 : ℕ)^5839*5000000000000^4815 ≤ 1812284004569^4815*200000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86612501 200000000 1812284004569 5000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4330625797/10000000000 : ℝ)^5839 ≤ (36245687673113/100000000000000 : ℝ)^4815 := by
    have hnat : (4330625797 : ℕ)^5839*100000000000000^4815 ≤ 36245687673113^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330625797 10000000000 36245687673113 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862403929/2500000000 : ℝ), (86612501/200000000 : ℝ), (4330625797/10000000000 : ℝ)] ![(27508632226013/100000000000000 : ℝ), (1812284004569/5000000000000 : ℝ), (36245687673113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862403929/2500000000 : ℝ)|^5839 ≤ (27508632226013/100000000000000 : ℝ)^4815
        have hw : |(862403929/2500000000 : ℝ)|=(862403929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(86612501/200000000 : ℝ)|^5839 ≤ (1812284004569/5000000000000 : ℝ)^4815
        have hw : |(86612501/200000000 : ℝ)|=(86612501/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4330625797/10000000000 : ℝ)|^5839 ≤ (36245687673113/100000000000000 : ℝ)^4815
        have hw : |(4330625797/10000000000 : ℝ)|=(4330625797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_box_8 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1445828291/10000000000 : ℝ)*x 0 + (4906214393/10000000000 : ℝ)*x 1 + (5482765383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1445828291/10000000000 : ℝ)^5839 ≤ (598935166771/6250000000000 : ℝ)^4815 := by
    have hnat : (1445828291 : ℕ)^5839*6250000000000^4815 ≤ 598935166771^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1445828291 10000000000 598935166771 6250000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4906214393/10000000000 : ℝ)^5839 ≤ (41179210601/97656250000 : ℝ)^4815 := by
    have hnat : (4906214393 : ℕ)^5839*97656250000^4815 ≤ 41179210601^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4906214393 10000000000 41179210601 97656250000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5482765383/10000000000 : ℝ)^5839 ≤ (48249525658381/100000000000000 : ℝ)^4815 := by
    have hnat : (5482765383 : ℕ)^5839*100000000000000^4815 ≤ 48249525658381^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482765383 10000000000 48249525658381 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1445828291/10000000000 : ℝ), (4906214393/10000000000 : ℝ), (5482765383/10000000000 : ℝ)] ![(598935166771/6250000000000 : ℝ), (41179210601/97656250000 : ℝ), (48249525658381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1445828291/10000000000 : ℝ)|^5839 ≤ (598935166771/6250000000000 : ℝ)^4815
        have hw : |(-1445828291/10000000000 : ℝ)|=(1445828291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4906214393/10000000000 : ℝ)|^5839 ≤ (41179210601/97656250000 : ℝ)^4815
        have hw : |(4906214393/10000000000 : ℝ)|=(4906214393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5482765383/10000000000 : ℝ)|^5839 ≤ (48249525658381/100000000000000 : ℝ)^4815
        have hw : |(5482765383/10000000000 : ℝ)|=(5482765383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_box_9 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (161024739/312500000 : ℝ)*x 0 + (-69740919/625000000 : ℝ)*x 1 + (274138267/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (161024739/312500000 : ℝ)^5839 ≤ (22375515226717/50000000000000 : ℝ)^4815 := by
    have hnat : (161024739 : ℕ)^5839*50000000000000^4815 ≤ 22375515226717^4815*312500000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161024739 312500000 22375515226717 50000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69740919/625000000 : ℝ)^5839 ≤ (1399888866473/20000000000000 : ℝ)^4815 := by
    have hnat : (69740919 : ℕ)^5839*20000000000000^4815 ≤ 1399888866473^4815*625000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69740919 625000000 1399888866473 20000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274138267/500000000 : ℝ)^5839 ≤ (6031190649937/12500000000000 : ℝ)^4815 := by
    have hnat : (274138267 : ℕ)^5839*12500000000000^4815 ≤ 6031190649937^4815*500000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274138267 500000000 6031190649937 12500000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(161024739/312500000 : ℝ), (-69740919/625000000 : ℝ), (274138267/500000000 : ℝ)] ![(22375515226717/50000000000000 : ℝ), (1399888866473/20000000000000 : ℝ), (6031190649937/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(161024739/312500000 : ℝ)|^5839 ≤ (22375515226717/50000000000000 : ℝ)^4815
        have hw : |(161024739/312500000 : ℝ)|=(161024739/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-69740919/625000000 : ℝ)|^5839 ≤ (1399888866473/20000000000000 : ℝ)^4815
        have hw : |(-69740919/625000000 : ℝ)|=(69740919/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(274138267/500000000 : ℝ)|^5839 ≤ (6031190649937/12500000000000 : ℝ)^4815
        have hw : |(274138267/500000000 : ℝ)|=(274138267/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_box_10 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152791863/10000000000 : ℝ)*x 0 + (5482765083/10000000000 : ℝ)*x 1 + (-69740923/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152791863/10000000000 : ℝ)^5839 ≤ (44751032717771/100000000000000 : ℝ)^4815 := by
    have hnat : (5152791863 : ℕ)^5839*100000000000000^4815 ≤ 44751032717771^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152791863 10000000000 44751032717771 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5482765083/10000000000 : ℝ)^5839 ≤ (48249522456857/100000000000000 : ℝ)^4815 := by
    have hnat : (5482765083 : ℕ)^5839*100000000000000^4815 ≤ 48249522456857^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482765083 10000000000 48249522456857 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69740923/625000000 : ℝ)^5839 ≤ (1749861204799/25000000000000 : ℝ)^4815 := by
    have hnat : (69740923 : ℕ)^5839*25000000000000^4815 ≤ 1749861204799^4815*625000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69740923 625000000 1749861204799 25000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152791863/10000000000 : ℝ), (5482765083/10000000000 : ℝ), (-69740923/625000000 : ℝ)] ![(44751032717771/100000000000000 : ℝ), (48249522456857/100000000000000 : ℝ), (1749861204799/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152791863/10000000000 : ℝ)|^5839 ≤ (44751032717771/100000000000000 : ℝ)^4815
        have hw : |(5152791863/10000000000 : ℝ)|=(5152791863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5482765083/10000000000 : ℝ)|^5839 ≤ (48249522456857/100000000000000 : ℝ)^4815
        have hw : |(5482765083/10000000000 : ℝ)|=(5482765083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-69740923/625000000 : ℝ)|^5839 ≤ (1749861204799/25000000000000 : ℝ)^4815
        have hw : |(-69740923/625000000 : ℝ)|=(69740923/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_box_11 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4758057099/10000000000 : ℝ)*x 0 + (1836621073/5000000000 : ℝ)*x 1 + (1836621367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4758057099/10000000000 : ℝ)^5839 ≤ (10157083599819/25000000000000 : ℝ)^4815 := by
    have hnat : (4758057099 : ℕ)^5839*25000000000000^4815 ≤ 10157083599819^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4758057099 10000000000 10157083599819 25000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1836621073/5000000000 : ℝ)^5839 ≤ (5937165983/20000000000 : ℝ)^4815 := by
    have hnat : (1836621073 : ℕ)^5839*20000000000^4815 ≤ 5937165983^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1836621073 5000000000 5937165983 20000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1836621367/5000000000 : ℝ)^5839 ≤ (29685835677609/100000000000000 : ℝ)^4815 := by
    have hnat : (1836621367 : ℕ)^5839*100000000000000^4815 ≤ 29685835677609^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1836621367 5000000000 29685835677609 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4758057099/10000000000 : ℝ), (1836621073/5000000000 : ℝ), (1836621367/5000000000 : ℝ)] ![(10157083599819/25000000000000 : ℝ), (5937165983/20000000000 : ℝ), (29685835677609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4758057099/10000000000 : ℝ)|^5839 ≤ (10157083599819/25000000000000 : ℝ)^4815
        have hw : |(4758057099/10000000000 : ℝ)|=(4758057099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1836621073/5000000000 : ℝ)|^5839 ≤ (5937165983/20000000000 : ℝ)^4815
        have hw : |(1836621073/5000000000 : ℝ)|=(1836621073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1836621367/5000000000 : ℝ)|^5839 ≤ (29685835677609/100000000000000 : ℝ)^4815
        have hw : |(1836621367/5000000000 : ℝ)|=(1836621367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_box_12 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-61258601/625000000 : ℝ)*x 0 + (1126167407/2000000000 : ℝ)*x 1 + (2549488733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61258601/625000000 : ℝ)^5839 ≤ (5980883497931/100000000000000 : ℝ)^4815 := by
    have hnat : (61258601 : ℕ)^5839*100000000000000^4815 ≤ 5980883497931^4815*625000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61258601 625000000 5980883497931 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126167407/2000000000 : ℝ)^5839 ≤ (49834215148691/100000000000000 : ℝ)^4815 := by
    have hnat : (1126167407 : ℕ)^5839*100000000000000^4815 ≤ 49834215148691^4815*2000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126167407 2000000000 49834215148691 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2549488733/5000000000 : ℝ)^5839 ≤ (44184901335299/100000000000000 : ℝ)^4815 := by
    have hnat : (2549488733 : ℕ)^5839*100000000000000^4815 ≤ 44184901335299^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2549488733 5000000000 44184901335299 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-61258601/625000000 : ℝ), (1126167407/2000000000 : ℝ), (2549488733/5000000000 : ℝ)] ![(5980883497931/100000000000000 : ℝ), (49834215148691/100000000000000 : ℝ), (44184901335299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-61258601/625000000 : ℝ)|^5839 ≤ (5980883497931/100000000000000 : ℝ)^4815
        have hw : |(-61258601/625000000 : ℝ)|=(61258601/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126167407/2000000000 : ℝ)|^5839 ≤ (49834215148691/100000000000000 : ℝ)^4815
        have hw : |(1126167407/2000000000 : ℝ)|=(1126167407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2549488733/5000000000 : ℝ)|^5839 ≤ (44184901335299/100000000000000 : ℝ)^4815
        have hw : |(2549488733/5000000000 : ℝ)|=(2549488733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_box_13 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2704638831/5000000000 : ℝ)*x 0 + (-1290438843/10000000000 : ℝ)*x 1 + (2549488237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2704638831/5000000000 : ℝ)^5839 ≤ (9493280978937/20000000000000 : ℝ)^4815 := by
    have hnat : (2704638831 : ℕ)^5839*20000000000000^4815 ≤ 9493280978937^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704638831 5000000000 9493280978937 20000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1290438843/10000000000 : ℝ)^5839 ≤ (1043588022811/12500000000000 : ℝ)^4815 := by
    have hnat : (1290438843 : ℕ)^5839*12500000000000^4815 ≤ 1043588022811^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1290438843 10000000000 1043588022811 12500000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2549488237/5000000000 : ℝ)^5839 ≤ (44184890911053/100000000000000 : ℝ)^4815 := by
    have hnat : (2549488237 : ℕ)^5839*100000000000000^4815 ≤ 44184890911053^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2549488237 5000000000 44184890911053 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2704638831/5000000000 : ℝ), (-1290438843/10000000000 : ℝ), (2549488237/5000000000 : ℝ)] ![(9493280978937/20000000000000 : ℝ), (1043588022811/12500000000000 : ℝ), (44184890911053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2704638831/5000000000 : ℝ)|^5839 ≤ (9493280978937/20000000000000 : ℝ)^4815
        have hw : |(2704638831/5000000000 : ℝ)|=(2704638831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1290438843/10000000000 : ℝ)|^5839 ≤ (1043588022811/12500000000000 : ℝ)^4815
        have hw : |(-1290438843/10000000000 : ℝ)|=(1290438843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2549488237/5000000000 : ℝ)|^5839 ≤ (44184890911053/100000000000000 : ℝ)^4815
        have hw : |(2549488237/5000000000 : ℝ)|=(2549488237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_box_14 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5409277413/10000000000 : ℝ)*x 0 + (5098976827/10000000000 : ℝ)*x 1 + (-1290438707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5409277413/10000000000 : ℝ)^5839 ≤ (9493280449007/20000000000000 : ℝ)^4815 := by
    have hnat : (5409277413 : ℕ)^5839*20000000000000^4815 ≤ 9493280449007^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409277413 10000000000 9493280449007 20000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5098976827/10000000000 : ℝ)^5839 ≤ (44184894620487/100000000000000 : ℝ)^4815 := by
    have hnat : (5098976827 : ℕ)^5839*100000000000000^4815 ≤ 44184894620487^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5098976827 10000000000 44184894620487 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1290438707/10000000000 : ℝ)^5839 ≤ (2087175778873/25000000000000 : ℝ)^4815 := by
    have hnat : (1290438707 : ℕ)^5839*25000000000000^4815 ≤ 2087175778873^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1290438707 10000000000 2087175778873 25000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5409277413/10000000000 : ℝ), (5098976827/10000000000 : ℝ), (-1290438707/10000000000 : ℝ)] ![(9493280449007/20000000000000 : ℝ), (44184894620487/100000000000000 : ℝ), (2087175778873/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5409277413/10000000000 : ℝ)|^5839 ≤ (9493280449007/20000000000000 : ℝ)^4815
        have hw : |(5409277413/10000000000 : ℝ)|=(5409277413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5098976827/10000000000 : ℝ)|^5839 ≤ (44184894620487/100000000000000 : ℝ)^4815
        have hw : |(5098976827/10000000000 : ℝ)|=(5098976827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1290438707/10000000000 : ℝ)|^5839 ≤ (2087175778873/25000000000000 : ℝ)^4815
        have hw : |(-1290438707/10000000000 : ℝ)|=(1290438707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_box_15 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (666513477/2000000000 : ℝ)*x 0 + (877221133/2000000000 : ℝ)*x 1 + (438610981/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (666513477/2000000000 : ℝ)^5839 ≤ (26380859223637/100000000000000 : ℝ)^4815 := by
    have hnat : (666513477 : ℕ)^5839*100000000000000^4815 ≤ 26380859223637^4815*2000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      666513477 2000000000 26380859223637 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (877221133/2000000000 : ℝ)^5839 ≤ (18404774643631/50000000000000 : ℝ)^4815 := by
    have hnat : (877221133 : ℕ)^5839*50000000000000^4815 ≤ 18404774643631^4815*2000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877221133 2000000000 18404774643631 50000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (438610981/1000000000 : ℝ)^5839 ≤ (36809591471303/100000000000000 : ℝ)^4815 := by
    have hnat : (438610981 : ℕ)^5839*100000000000000^4815 ≤ 36809591471303^4815*1000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438610981 1000000000 36809591471303 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(666513477/2000000000 : ℝ), (877221133/2000000000 : ℝ), (438610981/1000000000 : ℝ)] ![(26380859223637/100000000000000 : ℝ), (18404774643631/50000000000000 : ℝ), (36809591471303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(666513477/2000000000 : ℝ)|^5839 ≤ (26380859223637/100000000000000 : ℝ)^4815
        have hw : |(666513477/2000000000 : ℝ)|=(666513477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(877221133/2000000000 : ℝ)|^5839 ≤ (18404774643631/50000000000000 : ℝ)^4815
        have hw : |(877221133/2000000000 : ℝ)|=(877221133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(438610981/1000000000 : ℝ)|^5839 ≤ (36809591471303/100000000000000 : ℝ)^4815
        have hw : |(438610981/1000000000 : ℝ)|=(438610981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1754_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216963139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8949/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9089/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(68989/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58309/100000 : ℝ) ∧ (20449/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (92973/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8949/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9089/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8949/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9089/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8949/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9089/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8949/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9089/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8949/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9089/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8949/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9089/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9089/100000 : ℝ) ^ (5823/1024 : ℝ) ≤ (29889415410251/25000000000000000000 : ℝ) := by
    have hpowers : (9089/100000 : ℝ)^5823 ≤ (29889415410251/25000000000000000000 : ℝ)^1024 := by
      have hnat : (9089 : ℕ)^5823*25000000000000000000^1024 ≤ 29889415410251^1024*100000^5823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9089 100000 29889415410251 25000000000000000000 5823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9089/100000 : ℝ)) (X := (29889415410251/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5823 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8949/50000 : ℝ) ^ (5823/1024 : ℝ) ≤ (2818547138249883/50000000000000000000 : ℝ) := by
    have hpowers : (8949/50000 : ℝ)^5823 ≤ (2818547138249883/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8949 : ℕ)^5823*50000000000000000000^1024 ≤ 2818547138249883^1024*50000^5823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8949 50000 2818547138249883 50000000000000000000 5823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8949/50000 : ℝ)) (X := (2818547138249883/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5823 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500029889415410251/12500000000000000000 : ℝ) ≤ (400000168197733/400000000000000 : ℝ) ^ (5823/1024 : ℝ) := by
    have hpowers : (12500029889415410251/12500000000000000000 : ℝ)^1024 ≤ (400000168197733/400000000000000 : ℝ)^5823 := by
      have hnat : (12500029889415410251 : ℕ)^1024*400000000000000^5823 ≤ 400000168197733^5823*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500029889415410251 12500000000000000000 400000168197733 400000000000000 1024 5823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400000168197733/400000000000000 : ℝ)) (X := (12500029889415410251/12500000000000000000 : ℝ)) (by norm_num) 5823 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10000575665193814077/10000000000000000000 : ℝ) ≤ (2500025307709751/2500000000000000 : ℝ) ^ (5823/1024 : ℝ) := by
    have hpowers : (10000575665193814077/10000000000000000000 : ℝ)^1024 ≤ (2500025307709751/2500000000000000 : ℝ)^5823 := by
      have hnat : (10000575665193814077 : ℕ)^1024*2500000000000000^5823 ≤ 2500025307709751^5823*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000575665193814077 10000000000000000000 2500025307709751 2500000000000000 1024 5823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500025307709751/2500000000000000 : ℝ)) (X := (10000575665193814077/10000000000000000000 : ℝ)) (by norm_num) 5823 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25002818547138249883/25000000000000000000 : ℝ) ≤ (10000198256734683/10000000000000000 : ℝ) ^ (5823/1024 : ℝ) := by
    have hpowers : (25002818547138249883/25000000000000000000 : ℝ)^1024 ≤ (10000198256734683/10000000000000000 : ℝ)^5823 := by
      have hnat : (25002818547138249883 : ℕ)^1024*10000000000000000^5823 ≤ 10000198256734683^5823*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002818547138249883 25000000000000000000 10000198256734683 10000000000000000 1024 5823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000198256734683/10000000000000000 : ℝ)) (X := (25002818547138249883/25000000000000000000 : ℝ)) (by norm_num) 5823 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(29889415410251/25000000000000000000 : ℝ) ≤ ((88088273304614097063/88090000000000000000 : ℝ)+2*(97025895679/880900000000000 : ℝ)*(9089/100000 : ℝ))^(5823/1024 : ℝ) := by
    rw [show (88088273304614097063/88090000000000000000 : ℝ)+2*(97025895679/880900000000000 : ℝ)*(9089/100000 : ℝ)=(400000168197733/400000000000000 : ℝ) by norm_num, show 1+2*(29889415410251/25000000000000000000 : ℝ)=(12500029889415410251/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2818547138249883/50000000000000000000 : ℝ)+(29889415410251/25000000000000000000 : ℝ) ≤ ((88088273304614097063/88090000000000000000 : ℝ)+(97025895679/880900000000000 : ℝ)*((8949/50000 : ℝ)+(9089/100000 : ℝ)))^(5823/1024 : ℝ) := by
    rw [show (88088273304614097063/88090000000000000000 : ℝ)+(97025895679/880900000000000 : ℝ)*((8949/50000 : ℝ)+(9089/100000 : ℝ))=(2500025307709751/2500000000000000 : ℝ) by norm_num, show 1+(2818547138249883/50000000000000000000 : ℝ)+(29889415410251/25000000000000000000 : ℝ)=(10000575665193814077/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2818547138249883/50000000000000000000 : ℝ) ≤ ((88088273304614097063/88090000000000000000 : ℝ)+2*(97025895679/880900000000000 : ℝ)*(8949/50000 : ℝ))^(5823/1024 : ℝ) := by
    rw [show (88088273304614097063/88090000000000000000 : ℝ)+2*(97025895679/880900000000000 : ℝ)*(8949/50000 : ℝ)=(10000198256734683/10000000000000000 : ℝ) by norm_num, show 1+2*(2818547138249883/50000000000000000000 : ℝ)=(25002818547138249883/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (88088273304614097063/88090000000000000000 : ℝ)*(X 1 0+X 2 0)+(97025895679/880900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5823/1024 : ℝ)) (lo := (9089/100000 : ℝ)) (hi := (8949/50000 : ℝ)) (c := (88088273304614097063/88090000000000000000 : ℝ)) (alpha := (97025895679/880900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (88088273304614097063/88090000000000000000 : ℝ)*(X 0 1+X 2 1)+(97025895679/880900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5823/1024 : ℝ)) (lo := (9089/100000 : ℝ)) (hi := (8949/50000 : ℝ)) (c := (88088273304614097063/88090000000000000000 : ℝ)) (alpha := (97025895679/880900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (88088273304614097063/88090000000000000000 : ℝ)*(X 0 2+X 1 2)+(97025895679/880900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5823/1024 : ℝ)) (lo := (9089/100000 : ℝ)) (hi := (8949/50000 : ℝ)) (c := (88088273304614097063/88090000000000000000 : ℝ)) (alpha := (97025895679/880900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-32801023/400000000 : ℝ)*X 0 0+(2710500649/5000000000 : ℝ)*X 0 1+(542100201/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5193997979/10000000000 : ℝ)*X 1 0+(-572609991/5000000000 : ℝ)*X 1 1+(5421001173/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2596998649/5000000000 : ℝ)*X 2 0+(271050091/500000000 : ℝ)*X 2 1+(-572610011/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((226916849/500000000 : ℝ)*X 0 0+(3788360233/10000000000 : ℝ)*X 0 1+(947090007/2500000000 : ℝ)*X 0 2+(226916849/500000000 : ℝ)*X 1 0+(3788360233/10000000000 : ℝ)*X 1 1+(947090007/2500000000 : ℝ)*X 1 2+(226916849/500000000 : ℝ)*X 2 0+(3788360233/10000000000 : ℝ)*X 2 1+(947090007/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1619882921/10000000000 : ℝ)*X 0 0+(512897679/1000000000 : ℝ)*X 0 1+(1025795499/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1347288671/2500000000 : ℝ)*X 1 0+(-1277499247/10000000000 : ℝ)*X 1 1+(1282244373/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5389155227/10000000000 : ℝ)*X 2 0+(5128977213/10000000000 : ℝ)*X 2 1+(-319374721/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((862403929/2500000000 : ℝ)*X 0 0+(86612501/200000000 : ℝ)*X 0 1+(4330625797/10000000000 : ℝ)*X 0 2+(862403929/2500000000 : ℝ)*X 1 0+(86612501/200000000 : ℝ)*X 1 1+(4330625797/10000000000 : ℝ)*X 1 2+(862403929/2500000000 : ℝ)*X 2 0+(86612501/200000000 : ℝ)*X 2 1+(4330625797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1445828291/10000000000 : ℝ)*X 0 0+(4906214393/10000000000 : ℝ)*X 0 1+(5482765383/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((161024739/312500000 : ℝ)*X 1 0+(-69740919/625000000 : ℝ)*X 1 1+(274138267/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5152791863/10000000000 : ℝ)*X 2 0+(5482765083/10000000000 : ℝ)*X 2 1+(-69740923/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4758057099/10000000000 : ℝ)*X 0 0+(1836621073/5000000000 : ℝ)*X 0 1+(1836621367/5000000000 : ℝ)*X 0 2+(4758057099/10000000000 : ℝ)*X 1 0+(1836621073/5000000000 : ℝ)*X 1 1+(1836621367/5000000000 : ℝ)*X 1 2+(4758057099/10000000000 : ℝ)*X 2 0+(1836621073/5000000000 : ℝ)*X 2 1+(1836621367/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-61258601/625000000 : ℝ)*X 0 0+(1126167407/2000000000 : ℝ)*X 0 1+(2549488733/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2704638831/5000000000 : ℝ)*X 1 0+(-1290438843/10000000000 : ℝ)*X 1 1+(2549488237/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5409277413/10000000000 : ℝ)*X 2 0+(5098976827/10000000000 : ℝ)*X 2 1+(-1290438707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((666513477/2000000000 : ℝ)*X 0 0+(877221133/2000000000 : ℝ)*X 0 1+(438610981/1000000000 : ℝ)*X 0 2+(666513477/2000000000 : ℝ)*X 1 0+(877221133/2000000000 : ℝ)*X 1 1+(438610981/1000000000 : ℝ)*X 1 2+(666513477/2000000000 : ℝ)*X 2 0+(877221133/2000000000 : ℝ)*X 2 1+(438610981/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-68989/100000 : ℝ) ≤ (-1519260403306256040759750239354577/2202250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2350429/5000000000000 : ℝ)*(lower2) + (4496227/5000000000000 : ℝ)*(lower3) + (866191/2500000000000 : ℝ)*(upper5) + (531672272072031/50000000000000 : ℝ)*(major0) + (531672272072031/50000000000000 : ℝ)*(major1) + (531672272072031/50000000000000 : ℝ)*(major2) + (414895173075733/25000000000000 : ℝ)*(sp4) + (663820353773/40000000000 : ℝ)*(sp5) + (51861634553333/3125000000000 : ℝ)*(sp6) + (490102094106367/100000000000000 : ℝ)*(sp7) + (24424911/12500000000000 : ℝ)*(sp12) + (30003269719/100000000000000 : ℝ)*(sp13) + (8581995563/100000000000000 : ℝ)*(sp14) + (1685293719/100000000000000 : ℝ)*(sp15) + (245051889700043/50000000000000 : ℝ)*(f.failure) + (1659580887702219/100000000000000 : ℝ)*(f.sum) + (231772921843783/44045000000000000000000000000 : ℝ)*base65 + (10616327933763944953/4404500000000000000000000000000000 : ℝ)*base67 + (19535873871799944953/4404500000000000000000000000000000 : ℝ)*base69 + (27570681129523944953/4404500000000000000000000000000000 : ℝ)*base71 + (15382112058519/22022500000000000000000000000 : ℝ)*base73 + (12418548690938944953/4404500000000000000000000000000000 : ℝ)*base75 + (42948277355285444953/4404500000000000000000000000000000 : ℝ)*base77 + (26999883259803444953/4404500000000000000000000000000000 : ℝ)*base79 + (73814079297309/22022500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2285023/5000000000000000000000 : ℝ)*base90 + (2285023/5000000000000000000000 : ℝ)*base92 + (2285023/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58309/100000 : ℝ) ≤ (513667173463103782007011137578757/880900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1880117/25000000000000 : ℝ)*(lower0) + (26244511/50000000000000 : ℝ)*(upper2) + (29894859/50000000000000 : ℝ)*(lower5) + (237852074850287/20000000000000 : ℝ)*(major0) + (237852074850287/20000000000000 : ℝ)*(major1) + (237852074850287/20000000000000 : ℝ)*(major2) + (1810940555706071/100000000000000 : ℝ)*(sp0) + (1810938483655101/100000000000000 : ℝ)*(sp1) + (362188348603383/20000000000000 : ℝ)*(sp2) + (548138662886443/100000000000000 : ℝ)*(sp3) + (2428693823/100000000000000 : ℝ)*(sp6) + (87870939/12500000000000 : ℝ)*(sp7) + (5688055637/100000000000000 : ℝ)*(sp9) + (904001167/25000000000000 : ℝ)*(sp12) + (109627873170791/20000000000000 : ℝ)*(f.failure) + (905472085855369/50000000000000 : ℝ)*(f.sum) + (6922753955951/4404500000000000000000000000 : ℝ)*base65 + (9841725803363892919/1761800000000000000000000000000000 : ℝ)*base68 + (4431352712400092919/1761800000000000000000000000000000 : ℝ)*base70 + (2778426330782107081/1761800000000000000000000000000000 : ℝ)*base71 + (4917551431743/2202250000000000000000000000 : ℝ)*base73 + (3601325876900907081/1761800000000000000000000000000000 : ℝ)*base75 + (4432055623317307081/1761800000000000000000000000000000 : ℝ)*base77 + (10380424143366307081/1761800000000000000000000000000000 : ℝ)*base79 + (94896559181/8809000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1527051/2000000000000000000000 : ℝ)*base90 + (1527051/2000000000000000000000 : ℝ)*base92 + (1527051/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (20449/25000 : ℝ) ≤ (36027963080502406203893631993/44045000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5053059/20000000000000 : ℝ)*(upper0) + (868709/5000000000000 : ℝ)*(lower3) + (2705697/50000000000000 : ℝ)*(upper4) + (1144648430830657/100000000000000 : ℝ)*(major0) + (1144648430830657/100000000000000 : ℝ)*(major1) + (1144648430830657/100000000000000 : ℝ)*(major2) + (309460749/4000000000000 : ℝ)*(sp1) + (945058551/100000000000000 : ℝ)*(sp3) + (273903279/100000000000000 : ℝ)*(sp4) + (1734452454054237/100000000000000 : ℝ)*(sp8) + (346889145127021/20000000000000 : ℝ)*(sp9) + (173445346215383/10000000000000 : ℝ)*(sp10) + (527576428732421/100000000000000 : ℝ)*(sp11) + (146839263/20000000000000 : ℝ)*(sp12) + (131894343447743/25000000000000 : ℝ)*(f.failure) + (173445346215383/10000000000000 : ℝ)*(f.sum) + (132674890053959/22022500000000000000000000000 : ℝ)*base65 + (21900368886600639609/8809000000000000000000000000000000 : ℝ)*base68 + (8466896555147639609/8809000000000000000000000000000000 : ℝ)*base70 + (70576415782758360391/8809000000000000000000000000000000 : ℝ)*base71 + (1280416220131/5505625000000000000000000000 : ℝ)*base73 + (8167107674521360391/8809000000000000000000000000000000 : ℝ)*base75 + (44210854373483360391/8809000000000000000000000000000000 : ℝ)*base77 + (23382609228626639609/8809000000000000000000000000000000 : ℝ)*base80 + (103105780678013/44045000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (21254723/2500000000000000000000 : ℝ)*base90 + (21254723/2500000000000000000000 : ℝ)*base92 + (21254723/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-92973/100000 : ℝ) ≤ (-818977341978829117217915214448089/880900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (88577669/100000000000000 : ℝ)*(lower3) + (66164417/50000000000000 : ℝ)*(lower4) + (44303923/20000000000000 : ℝ)*(upper5) + (240298143742101/20000000000000 : ℝ)*(major0) + (240298143742101/20000000000000 : ℝ)*(major1) + (240298143742101/20000000000000 : ℝ)*(major2) + (1810853537/100000000000000 : ℝ)*(sp4) + (17227792011/50000000000000 : ℝ)*(sp5) + (38476651937/50000000000000 : ℝ)*(sp6) + (8503241411/50000000000000 : ℝ)*(sp7) + (188019337424681/10000000000000 : ℝ)*(sp12) + (940080364758163/50000000000000 : ℝ)*(sp13) + (940059115898237/50000000000000 : ℝ)*(sp14) + (1730498188611/312500000000 : ℝ)*(sp15) + (276888213419171/50000000000000 : ℝ)*(f.failure) + (470048796275087/25000000000000 : ℝ)*(f.sum) + (4547613849161/2202250000000000000000000000 : ℝ)*base65 + (11695299855747449363/1761800000000000000000000000000000 : ℝ)*base67 + (10385723737875249363/1761800000000000000000000000000000 : ℝ)*base69 + (3774444144789849363/1761800000000000000000000000000000 : ℝ)*base71 + (12319869712347/8809000000000000000000000000 : ℝ)*base73 + (5997631615936150637/1761800000000000000000000000000000 : ℝ)*base76 + (3791997603350150637/1761800000000000000000000000000000 : ℝ)*base78 + (1166930025103449363/1761800000000000000000000000000000 : ℝ)*base79 + (7069838270179/8809000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (12937769/5000000000000000000000 : ℝ)*base89 + (12937769/5000000000000000000000 : ℝ)*base91 + (12937769/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1754_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216963139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8949/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9089/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68989/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58309/100000 : ℝ) else (20449/25000 : ℝ) ≤ X j i ∧ X j i ≤ (92973/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1754_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1754_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216963139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8949/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9089/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68989/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58309/100000 : ℝ) else (20449/25000 : ℝ) ≤ X j i ∧ X j i ≤ (92973/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1754_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216963139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8949/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9089/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68989/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58309/100000 : ℝ) else (20449/25000 : ℝ) ≤ X j i ∧ X j i ≤ (92973/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1754_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

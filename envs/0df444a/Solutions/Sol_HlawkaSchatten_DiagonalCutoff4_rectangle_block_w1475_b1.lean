-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1475_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:11:43.955337+00:00
-- url     : https://prove2.me/submissions/4198784c-5f18-494b-a093-0199e25c7a64

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
theorem support_rectangle_w1475_s3_0 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-240415307/1250000000 : ℝ)*x 0 + (2721537927/5000000000 : ℝ)*x 1 + (260553041/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (240415307/1250000000 : ℝ)^4447 ≤ (11745575240357/100000000000000 : ℝ)^3423 := by
    have hnat : (240415307 : ℕ)^4447*100000000000000^3423 ≤ 11745575240357^3423*1250000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240415307 1250000000 11745575240357 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721537927/5000000000 : ℝ)^4447 ≤ (22687753880347/50000000000000 : ℝ)^3423 := by
    have hnat : (2721537927 : ℕ)^4447*50000000000000^3423 ≤ 22687753880347^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721537927 5000000000 22687753880347 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260553041/500000000 : ℝ)^4447 ≤ (42878916983141/100000000000000 : ℝ)^3423 := by
    have hnat : (260553041 : ℕ)^4447*100000000000000^3423 ≤ 42878916983141^3423*500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260553041 500000000 42878916983141 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-240415307/1250000000 : ℝ), (2721537927/5000000000 : ℝ), (260553041/500000000 : ℝ)] ![(11745575240357/100000000000000 : ℝ), (22687753880347/50000000000000 : ℝ), (42878916983141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-240415307/1250000000 : ℝ)|^4447 ≤ (11745575240357/100000000000000 : ℝ)^3423
        have hw : |(-240415307/1250000000 : ℝ)|=(240415307/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721537927/5000000000 : ℝ)|^4447 ≤ (22687753880347/50000000000000 : ℝ)^3423
        have hw : |(2721537927/5000000000 : ℝ)|=(2721537927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260553041/500000000 : ℝ)|^4447 ≤ (42878916983141/100000000000000 : ℝ)^3423
        have hw : |(260553041/500000000 : ℝ)|=(260553041/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s3_1 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677429269/5000000000 : ℝ)*x 0 + (-2042365649/10000000000 : ℝ)*x 1 + (208442433/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677429269/5000000000 : ℝ)^4447 ≤ (44422419646963/100000000000000 : ℝ)^3423 := by
    have hnat : (2677429269 : ℕ)^4447*100000000000000^3423 ≤ 44422419646963^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677429269 5000000000 44422419646963 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2042365649/10000000000 : ℝ)^4447 ≤ (3174665826493/25000000000000 : ℝ)^3423 := by
    have hnat : (2042365649 : ℕ)^4447*25000000000000^3423 ≤ 3174665826493^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042365649 10000000000 3174665826493 25000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208442433/400000000 : ℝ)^4447 ≤ (42878917036591/100000000000000 : ℝ)^3423 := by
    have hnat : (208442433 : ℕ)^4447*100000000000000^3423 ≤ 42878917036591^3423*400000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208442433 400000000 42878917036591 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677429269/5000000000 : ℝ), (-2042365649/10000000000 : ℝ), (208442433/400000000 : ℝ)] ![(44422419646963/100000000000000 : ℝ), (3174665826493/25000000000000 : ℝ), (42878917036591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677429269/5000000000 : ℝ)|^4447 ≤ (44422419646963/100000000000000 : ℝ)^3423
        have hw : |(2677429269/5000000000 : ℝ)|=(2677429269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2042365649/10000000000 : ℝ)|^4447 ≤ (3174665826493/25000000000000 : ℝ)^3423
        have hw : |(-2042365649/10000000000 : ℝ)|=(2042365649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208442433/400000000 : ℝ)|^4447 ≤ (42878917036591/100000000000000 : ℝ)^3423
        have hw : |(208442433/400000000 : ℝ)|=(208442433/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s3_2 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070971713/2000000000 : ℝ)*x 0 + (5211060817/10000000000 : ℝ)*x 1 + (-1021182811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070971713/2000000000 : ℝ)^4447 ≤ (44422419937953/100000000000000 : ℝ)^3423 := by
    have hnat : (1070971713 : ℕ)^4447*100000000000000^3423 ≤ 44422419937953^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070971713 2000000000 44422419937953 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5211060817/10000000000 : ℝ)^4447 ≤ (42878916951071/100000000000000 : ℝ)^3423 := by
    have hnat : (5211060817 : ℕ)^4447*100000000000000^3423 ≤ 42878916951071^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5211060817 10000000000 42878916951071 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1021182811/5000000000 : ℝ)^4447 ≤ (101589304703/800000000000 : ℝ)^3423 := by
    have hnat : (1021182811 : ℕ)^4447*800000000000^3423 ≤ 101589304703^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021182811 5000000000 101589304703 800000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070971713/2000000000 : ℝ), (5211060817/10000000000 : ℝ), (-1021182811/5000000000 : ℝ)] ![(44422419937953/100000000000000 : ℝ), (42878916951071/100000000000000 : ℝ), (101589304703/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070971713/2000000000 : ℝ)|^4447 ≤ (44422419937953/100000000000000 : ℝ)^3423
        have hw : |(1070971713/2000000000 : ℝ)|=(1070971713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5211060817/10000000000 : ℝ)|^4447 ≤ (42878916951071/100000000000000 : ℝ)^3423
        have hw : |(5211060817/10000000000 : ℝ)|=(5211060817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1021182811/5000000000 : ℝ)|^4447 ≤ (101589304703/800000000000 : ℝ)^3423
        have hw : |(-1021182811/5000000000 : ℝ)|=(1021182811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s3_3 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071710203/2500000000 : ℝ)*x 0 + (807466399/2000000000 : ℝ)*x 1 + (4549758589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071710203/2500000000 : ℝ)^4447 ≤ (6654573347461/20000000000000 : ℝ)^3423 := by
    have hnat : (1071710203 : ℕ)^4447*20000000000000^3423 ≤ 6654573347461^3423*2500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071710203 2500000000 6654573347461 20000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (807466399/2000000000 : ℝ)^4447 ≤ (615582859817/2000000000000 : ℝ)^3423 := by
    have hnat : (807466399 : ℕ)^4447*2000000000000^3423 ≤ 615582859817^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807466399 2000000000 615582859817 2000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4549758589/10000000000 : ℝ)^4447 ≤ (35947990255029/100000000000000 : ℝ)^3423 := by
    have hnat : (4549758589 : ℕ)^4447*100000000000000^3423 ≤ 35947990255029^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4549758589 10000000000 35947990255029 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071710203/2500000000 : ℝ), (807466399/2000000000 : ℝ), (4549758589/10000000000 : ℝ)] ![(6654573347461/20000000000000 : ℝ), (615582859817/2000000000000 : ℝ), (35947990255029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071710203/2500000000 : ℝ)|^4447 ≤ (6654573347461/20000000000000 : ℝ)^3423
        have hw : |(1071710203/2500000000 : ℝ)|=(1071710203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(807466399/2000000000 : ℝ)|^4447 ≤ (615582859817/2000000000000 : ℝ)^3423
        have hw : |(807466399/2000000000 : ℝ)|=(807466399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4549758589/10000000000 : ℝ)|^4447 ≤ (35947990255029/100000000000000 : ℝ)^3423
        have hw : |(4549758589/10000000000 : ℝ)|=(4549758589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s3_4 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-961678501/5000000000 : ℝ)*x 0 + (5212296723/10000000000 : ℝ)*x 1 + (5441830559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (961678501/5000000000 : ℝ)^4447 ≤ (11745849322887/100000000000000 : ℝ)^3423 := by
    have hnat : (961678501 : ℕ)^4447*100000000000000^3423 ≤ 11745849322887^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961678501 5000000000 11745849322887 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5212296723/10000000000 : ℝ)^4447 ≤ (1715685170427/4000000000000 : ℝ)^3423 := by
    have hnat : (5212296723 : ℕ)^4447*4000000000000^3423 ≤ 1715685170427^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212296723 10000000000 1715685170427 4000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5441830559/10000000000 : ℝ)^4447 ≤ (11340505350371/25000000000000 : ℝ)^3423 := by
    have hnat : (5441830559 : ℕ)^4447*25000000000000^3423 ≤ 11340505350371^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441830559 10000000000 11340505350371 25000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-961678501/5000000000 : ℝ), (5212296723/10000000000 : ℝ), (5441830559/10000000000 : ℝ)] ![(11745849322887/100000000000000 : ℝ), (1715685170427/4000000000000 : ℝ), (11340505350371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-961678501/5000000000 : ℝ)|^4447 ≤ (11745849322887/100000000000000 : ℝ)^3423
        have hw : |(-961678501/5000000000 : ℝ)|=(961678501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5212296723/10000000000 : ℝ)|^4447 ≤ (1715685170427/4000000000000 : ℝ)^3423
        have hw : |(5212296723/10000000000 : ℝ)|=(5212296723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5441830559/10000000000 : ℝ)|^4447 ≤ (11340505350371/25000000000000 : ℝ)^3423
        have hw : |(5441830559/10000000000 : ℝ)|=(5441830559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s3_5 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294313959/10000000000 : ℝ)*x 0 + (-1811595899/10000000000 : ℝ)*x 1 + (5441830593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294313959/10000000000 : ℝ)^4447 ≤ (68392206709/156250000000 : ℝ)^3423 := by
    have hnat : (5294313959 : ℕ)^4447*156250000000^3423 ≤ 68392206709^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294313959 10000000000 68392206709 156250000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1811595899/10000000000 : ℝ)^4447 ≤ (2716741482329/25000000000000 : ℝ)^3423 := by
    have hnat : (1811595899 : ℕ)^4447*25000000000000^3423 ≤ 2716741482329^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1811595899 10000000000 2716741482329 25000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5441830593/10000000000 : ℝ)^4447 ≤ (22681010884843/50000000000000 : ℝ)^3423 := by
    have hnat : (5441830593 : ℕ)^4447*50000000000000^3423 ≤ 22681010884843^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441830593 10000000000 22681010884843 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294313959/10000000000 : ℝ), (-1811595899/10000000000 : ℝ), (5441830593/10000000000 : ℝ)] ![(68392206709/156250000000 : ℝ), (2716741482329/25000000000000 : ℝ), (22681010884843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294313959/10000000000 : ℝ)|^4447 ≤ (68392206709/156250000000 : ℝ)^3423
        have hw : |(5294313959/10000000000 : ℝ)|=(5294313959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1811595899/10000000000 : ℝ)|^4447 ≤ (2716741482329/25000000000000 : ℝ)^3423
        have hw : |(-1811595899/10000000000 : ℝ)|=(1811595899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5441830593/10000000000 : ℝ)|^4447 ≤ (22681010884843/50000000000000 : ℝ)^3423
        have hw : |(5441830593/10000000000 : ℝ)|=(5441830593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s3_6 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529431399/1000000000 : ℝ)*x 0 + (5441830609/10000000000 : ℝ)*x 1 + (-1811595833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529431399/1000000000 : ℝ)^4447 ≤ (1750840505069/4000000000000 : ℝ)^3423 := by
    have hnat : (529431399 : ℕ)^4447*4000000000000^3423 ≤ 1750840505069^3423*1000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529431399 1000000000 1750840505069 4000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441830609/10000000000 : ℝ)^4447 ≤ (22681010971479/50000000000000 : ℝ)^3423 := by
    have hnat : (5441830609 : ℕ)^4447*50000000000000^3423 ≤ 22681010971479^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441830609 10000000000 22681010971479 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1811595833/10000000000 : ℝ)^4447 ≤ (434678616599/4000000000000 : ℝ)^3423 := by
    have hnat : (1811595833 : ℕ)^4447*4000000000000^3423 ≤ 434678616599^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1811595833 10000000000 434678616599 4000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529431399/1000000000 : ℝ), (5441830609/10000000000 : ℝ), (-1811595833/10000000000 : ℝ)] ![(1750840505069/4000000000000 : ℝ), (22681010971479/50000000000000 : ℝ), (434678616599/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529431399/1000000000 : ℝ)|^4447 ≤ (1750840505069/4000000000000 : ℝ)^3423
        have hw : |(529431399/1000000000 : ℝ)|=(529431399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441830609/10000000000 : ℝ)|^4447 ≤ (22681010971479/50000000000000 : ℝ)^3423
        have hw : |(5441830609/10000000000 : ℝ)|=(5441830609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1811595833/10000000000 : ℝ)|^4447 ≤ (434678616599/4000000000000 : ℝ)^3423
        have hw : |(-1811595833/10000000000 : ℝ)|=(1811595833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s3_7 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (171476691/400000000 : ℝ)*x 0 + (113675731/250000000 : ℝ)*x 1 + (4040082291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171476691/400000000 : ℝ)^4447 ≤ (33273637757203/100000000000000 : ℝ)^3423 := by
    have hnat : (171476691 : ℕ)^4447*100000000000000^3423 ≤ 33273637757203^3423*400000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171476691 400000000 33273637757203 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113675731/250000000 : ℝ)^4447 ≤ (35919976805647/100000000000000 : ℝ)^3423 := by
    have hnat : (113675731 : ℕ)^4447*100000000000000^3423 ≤ 35919976805647^3423*250000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113675731 250000000 35919976805647 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4040082291/10000000000 : ℝ)^4447 ≤ (30806385428771/100000000000000 : ℝ)^3423 := by
    have hnat : (4040082291 : ℕ)^4447*100000000000000^3423 ≤ 30806385428771^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4040082291 10000000000 30806385428771 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(171476691/400000000 : ℝ), (113675731/250000000 : ℝ), (4040082291/10000000000 : ℝ)] ![(33273637757203/100000000000000 : ℝ), (35919976805647/100000000000000 : ℝ), (30806385428771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(171476691/400000000 : ℝ)|^4447 ≤ (33273637757203/100000000000000 : ℝ)^3423
        have hw : |(171476691/400000000 : ℝ)|=(171476691/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(113675731/250000000 : ℝ)|^4447 ≤ (35919976805647/100000000000000 : ℝ)^3423
        have hw : |(113675731/250000000 : ℝ)|=(113675731/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4040082291/10000000000 : ℝ)|^4447 ≤ (30806385428771/100000000000000 : ℝ)^3423
        have hw : |(4040082291/10000000000 : ℝ)|=(4040082291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1475_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3231/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (507/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (10669/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7789/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3231/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (507/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3231/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (507/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3231/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (507/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3231/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (507/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3231/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (507/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3231/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (507/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (507/5000 : ℝ) ^ (4445/1024 : ℝ) ≤ (2423033226361497/50000000000000000000 : ℝ) := by
    have hpowers : (507/5000 : ℝ)^4445 ≤ (2423033226361497/50000000000000000000 : ℝ)^1024 := by
      have hnat : (507 : ℕ)^4445*50000000000000000000^1024 ≤ 2423033226361497^1024*5000^4445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        507 5000 2423033226361497 50000000000000000000 4445 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (507/5000 : ℝ)) (X := (2423033226361497/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3231/20000 : ℝ) ^ (4445/1024 : ℝ) ≤ (3659340151548917/10000000000000000000 : ℝ) := by
    have hpowers : (3231/20000 : ℝ)^4445 ≤ (3659340151548917/10000000000000000000 : ℝ)^1024 := by
      have hnat : (3231 : ℕ)^4445*10000000000000000000^1024 ≤ 3659340151548917^1024*20000^4445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3231 20000 3659340151548917 10000000000000000000 4445 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3231/20000 : ℝ)) (X := (3659340151548917/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002423033226361497/25000000000000000000 : ℝ) ≤ (2000044654101039/2000000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (25002423033226361497/25000000000000000000 : ℝ)^1024 ≤ (2000044654101039/2000000000000000 : ℝ)^4445 := by
      have hnat : (25002423033226361497 : ℕ)^1024*2000000000000000^4445 ≤ 2000044654101039^4445*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002423033226361497 25000000000000000000 2000044654101039 2000000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000044654101039/2000000000000000 : ℝ)) (X := (25002423033226361497/25000000000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010359866992053041/25000000000000000000 : ℝ) ≤ (5000477246907887/5000000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (25010359866992053041/25000000000000000000 : ℝ)^1024 ≤ (5000477246907887/5000000000000000 : ℝ)^4445 := by
      have hnat : (25010359866992053041 : ℕ)^1024*5000000000000000^4445 ≤ 5000477246907887^4445*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010359866992053041 25000000000000000000 5000477246907887 5000000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000477246907887/5000000000000000 : ℝ)) (X := (25010359866992053041/25000000000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003659340151548917/5000000000000000000 : ℝ) ≤ (10001685717126353/10000000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (5003659340151548917/5000000000000000000 : ℝ)^1024 ≤ (10001685717126353/10000000000000000 : ℝ)^4445 := by
      have hnat : (5003659340151548917 : ℕ)^1024*10000000000000000^4445 ≤ 10001685717126353^4445*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003659340151548917 5000000000000000000 10001685717126353 10000000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001685717126353/10000000000000000 : ℝ)) (X := (5003659340151548917/5000000000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2423033226361497/50000000000000000000 : ℝ) ≤ ((4009100917556680387/4010000000000000000 : ℝ)+2*(731223310579/601500000000000 : ℝ)*(507/5000 : ℝ))^(4445/1024 : ℝ) := by
    rw [show (4009100917556680387/4010000000000000000 : ℝ)+2*(731223310579/601500000000000 : ℝ)*(507/5000 : ℝ)=(2000044654101039/2000000000000000 : ℝ) by norm_num, show 1+2*(2423033226361497/50000000000000000000 : ℝ)=(25002423033226361497/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3659340151548917/10000000000000000000 : ℝ)+(2423033226361497/50000000000000000000 : ℝ) ≤ ((4009100917556680387/4010000000000000000 : ℝ)+(731223310579/601500000000000 : ℝ)*((3231/20000 : ℝ)+(507/5000 : ℝ)))^(4445/1024 : ℝ) := by
    rw [show (4009100917556680387/4010000000000000000 : ℝ)+(731223310579/601500000000000 : ℝ)*((3231/20000 : ℝ)+(507/5000 : ℝ))=(5000477246907887/5000000000000000 : ℝ) by norm_num, show 1+(3659340151548917/10000000000000000000 : ℝ)+(2423033226361497/50000000000000000000 : ℝ)=(25010359866992053041/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3659340151548917/10000000000000000000 : ℝ) ≤ ((4009100917556680387/4010000000000000000 : ℝ)+2*(731223310579/601500000000000 : ℝ)*(3231/20000 : ℝ))^(4445/1024 : ℝ) := by
    rw [show (4009100917556680387/4010000000000000000 : ℝ)+2*(731223310579/601500000000000 : ℝ)*(3231/20000 : ℝ)=(10001685717126353/10000000000000000 : ℝ) by norm_num, show 1+2*(3659340151548917/10000000000000000000 : ℝ)=(5003659340151548917/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4009100917556680387/4010000000000000000 : ℝ)*(X 1 0+X 2 0)+(731223310579/601500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (507/5000 : ℝ)) (hi := (3231/20000 : ℝ)) (c := (4009100917556680387/4010000000000000000 : ℝ)) (alpha := (731223310579/601500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4009100917556680387/4010000000000000000 : ℝ)*(X 0 1+X 2 1)+(731223310579/601500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (507/5000 : ℝ)) (hi := (3231/20000 : ℝ)) (c := (4009100917556680387/4010000000000000000 : ℝ)) (alpha := (731223310579/601500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4009100917556680387/4010000000000000000 : ℝ)*(X 0 2+X 1 2)+(731223310579/601500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (507/5000 : ℝ)) (hi := (3231/20000 : ℝ)) (c := (4009100917556680387/4010000000000000000 : ℝ)) (alpha := (731223310579/601500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-240415307/1250000000 : ℝ)*X 0 0+(2721537927/5000000000 : ℝ)*X 0 1+(260553041/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677429269/5000000000 : ℝ)*X 1 0+(-2042365649/10000000000 : ℝ)*X 1 1+(208442433/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070971713/2000000000 : ℝ)*X 2 0+(5211060817/10000000000 : ℝ)*X 2 1+(-1021182811/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1071710203/2500000000 : ℝ)*X 0 0+(807466399/2000000000 : ℝ)*X 0 1+(4549758589/10000000000 : ℝ)*X 0 2+(1071710203/2500000000 : ℝ)*X 1 0+(807466399/2000000000 : ℝ)*X 1 1+(4549758589/10000000000 : ℝ)*X 1 2+(1071710203/2500000000 : ℝ)*X 2 0+(807466399/2000000000 : ℝ)*X 2 1+(4549758589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-961678501/5000000000 : ℝ)*X 0 0+(5212296723/10000000000 : ℝ)*X 0 1+(5441830559/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294313959/10000000000 : ℝ)*X 1 0+(-1811595899/10000000000 : ℝ)*X 1 1+(5441830593/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((529431399/1000000000 : ℝ)*X 2 0+(5441830609/10000000000 : ℝ)*X 2 1+(-1811595833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((171476691/400000000 : ℝ)*X 0 0+(113675731/250000000 : ℝ)*X 0 1+(4040082291/10000000000 : ℝ)*X 0 2+(171476691/400000000 : ℝ)*X 1 0+(113675731/250000000 : ℝ)*X 1 1+(4040082291/10000000000 : ℝ)*X 1 2+(171476691/400000000 : ℝ)*X 2 0+(113675731/250000000 : ℝ)*X 2 1+(4040082291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (752362883736487273369955673/200500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33582479/5000000000000 : ℝ)*(base19) + (80002429/12500000000000 : ℝ)*(base23) + (14287363/50000000000000 : ℝ)*(lower2) + (11019953/12500000000000 : ℝ)*(upper3) + (75611613/100000000000000 : ℝ)*(upper5) + (391349615642237/12500000000000 : ℝ)*(major0) + (391349615642237/12500000000000 : ℝ)*(major1) + (3130796925137897/100000000000000 : ℝ)*(major2) + (1077518842321709/25000000000000 : ℝ)*(sp0) + (538760613608569/12500000000000 : ℝ)*(sp1) + (43100849404987/1000000000000 : ℝ)*(sp2) + (24393792348017/1250000000000 : ℝ)*(sp3) + (2042246259/20000000000000 : ℝ)*(sp4) + (297302199/6250000000000 : ℝ)*(sp7) + (30492314760571/1562500000000 : ℝ)*(f.failure) + (4310085580518131/100000000000000 : ℝ)*(f.sum) + (67290368497651/20050000000000000000000000000 : ℝ)*base66 + (203001387075149657/150375000000000000000000000000000 : ℝ)*base67 + (6709985759200341583/1203000000000000000000000000000000 : ℝ)*base70 + (409865054214975343/150375000000000000000000000000000 : ℝ)*base72 + (21396756442449/20050000000000000000000000000 : ℝ)*base73 + (4102081427125341583/1203000000000000000000000000000000 : ℝ)*base76 + (632664441787922843/150375000000000000000000000000000 : ℝ)*base78 + (2062607059477922843/150375000000000000000000000000000 : ℝ)*base80 + (531838477001/1879687500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1167881/156250000000000000000 : ℝ)*base89 + (1167881/156250000000000000000 : ℝ)*base91 + (394619/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (335241638548959362980933779/50125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (460760669/50000000000000 : ℝ)*(base19) + (23029057/2000000000000 : ℝ)*(base23) + (14158281/10000000000000 : ℝ)*(upper3) + (9998319/12500000000000 : ℝ)*(lower4) + (92434269/100000000000000 : ℝ)*(upper5) + (1582311822091461/50000000000000 : ℝ)*(major0) + (1582311822091461/50000000000000 : ℝ)*(major1) + (1582311822091461/50000000000000 : ℝ)*(major2) + (635427363/5000000000000 : ℝ)*(sp1) + (8686504873/50000000000000 : ℝ)*(sp2) + (1089163459062639/25000000000000 : ℝ)*(sp4) + (2178320103090979/50000000000000 : ℝ)*(sp5) + (4356635311787961/100000000000000 : ℝ)*(sp6) + (986296614589099/50000000000000 : ℝ)*(sp7) + (986296614589099/50000000000000 : ℝ)*(f.failure) + (1089163459062639/25000000000000 : ℝ)*(f.sum) + (1631909580297/313281250000000000000000000 : ℝ)*base66 + (1365749478744335407/200500000000000000000000000000000 : ℝ)*base67 + (877352548487335407/200500000000000000000000000000000 : ℝ)*base69 + (762195225327664593/200500000000000000000000000000000 : ℝ)*base72 + (2684998084437/1253125000000000000000000000 : ℝ)*base73 + (1199237295592335407/200500000000000000000000000000000 : ℝ)*base75 + (659030723433335407/200500000000000000000000000000000 : ℝ)*base77 + (607560183772835407/200500000000000000000000000000000 : ℝ)*base79 + (28602164013379/10025000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (22589511/5000000000000000000000 : ℝ)*base90 + (22589511/5000000000000000000000 : ℝ)*base92 + (22589511/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1475_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3231/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (507/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10669/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7789/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1475_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1475_s4_0 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-480997437/2500000000 : ℝ)*x 0 + (5438770979/10000000000 : ℝ)*x 1 + (1042985189/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (480997437/2500000000 : ℝ)^4447 ≤ (587543484531/5000000000000 : ℝ)^3423 := by
    have hnat : (480997437 : ℕ)^4447*5000000000000^3423 ≤ 587543484531^3423*2500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480997437 2500000000 587543484531 5000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438770979/10000000000 : ℝ)^4447 ≤ (5666111315881/12500000000000 : ℝ)^3423 := by
    have hnat : (5438770979 : ℕ)^4447*12500000000000^3423 ≤ 5666111315881^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438770979 10000000000 5666111315881 12500000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042985189/2000000000 : ℝ)^4447 ≤ (42920239770713/100000000000000 : ℝ)^3423 := by
    have hnat : (1042985189 : ℕ)^4447*100000000000000^3423 ≤ 42920239770713^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042985189 2000000000 42920239770713 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-480997437/2500000000 : ℝ), (5438770979/10000000000 : ℝ), (1042985189/2000000000 : ℝ)] ![(587543484531/5000000000000 : ℝ), (5666111315881/12500000000000 : ℝ), (42920239770713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-480997437/2500000000 : ℝ)|^4447 ≤ (587543484531/5000000000000 : ℝ)^3423
        have hw : |(-480997437/2500000000 : ℝ)|=(480997437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438770979/10000000000 : ℝ)|^4447 ≤ (5666111315881/12500000000000 : ℝ)^3423
        have hw : |(5438770979/10000000000 : ℝ)|=(5438770979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042985189/2000000000 : ℝ)|^4447 ≤ (42920239770713/100000000000000 : ℝ)^3423
        have hw : |(1042985189/2000000000 : ℝ)|=(1042985189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s4_1 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353742403/10000000000 : ℝ)*x 0 + (-1019369051/5000000000 : ℝ)*x 1 + (5214925961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353742403/10000000000 : ℝ)^4447 ≤ (44410390976567/100000000000000 : ℝ)^3423 := by
    have hnat : (5353742403 : ℕ)^4447*100000000000000^3423 ≤ 44410390976567^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353742403 10000000000 44410390976567 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1019369051/5000000000 : ℝ)^4447 ≤ (1266936905843/10000000000000 : ℝ)^3423 := by
    have hnat : (1019369051 : ℕ)^4447*10000000000000^3423 ≤ 1266936905843^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019369051 5000000000 1266936905843 10000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214925961/10000000000 : ℝ)^4447 ≤ (42920239941791/100000000000000 : ℝ)^3423 := by
    have hnat : (5214925961 : ℕ)^4447*100000000000000^3423 ≤ 42920239941791^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214925961 10000000000 42920239941791 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353742403/10000000000 : ℝ), (-1019369051/5000000000 : ℝ), (5214925961/10000000000 : ℝ)] ![(44410390976567/100000000000000 : ℝ), (1266936905843/10000000000000 : ℝ), (42920239941791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353742403/10000000000 : ℝ)|^4447 ≤ (44410390976567/100000000000000 : ℝ)^3423
        have hw : |(5353742403/10000000000 : ℝ)|=(5353742403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1019369051/5000000000 : ℝ)|^4447 ≤ (1266936905843/10000000000000 : ℝ)^3423
        have hw : |(-1019369051/5000000000 : ℝ)|=(1019369051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214925961/10000000000 : ℝ)|^4447 ≤ (42920239941791/100000000000000 : ℝ)^3423
        have hw : |(5214925961/10000000000 : ℝ)|=(5214925961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s4_2 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334608901/625000000 : ℝ)*x 0 + (1303731481/2500000000 : ℝ)*x 1 + (-407747627/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334608901/625000000 : ℝ)^4447 ≤ (8882078223333/20000000000000 : ℝ)^3423 := by
    have hnat : (334608901 : ℕ)^4447*20000000000000^3423 ≤ 8882078223333^3423*625000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334608901 625000000 8882078223333 20000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303731481/2500000000 : ℝ)^4447 ≤ (42920239546173/100000000000000 : ℝ)^3423 := by
    have hnat : (1303731481 : ℕ)^4447*100000000000000^3423 ≤ 42920239546173^3423*2500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303731481 2500000000 42920239546173 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (407747627/2000000000 : ℝ)^4447 ≤ (12669369324851/100000000000000 : ℝ)^3423 := by
    have hnat : (407747627 : ℕ)^4447*100000000000000^3423 ≤ 12669369324851^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407747627 2000000000 12669369324851 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334608901/625000000 : ℝ), (1303731481/2500000000 : ℝ), (-407747627/2000000000 : ℝ)] ![(8882078223333/20000000000000 : ℝ), (42920239546173/100000000000000 : ℝ), (12669369324851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334608901/625000000 : ℝ)|^4447 ≤ (8882078223333/20000000000000 : ℝ)^3423
        have hw : |(334608901/625000000 : ℝ)|=(334608901/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303731481/2500000000 : ℝ)|^4447 ≤ (42920239546173/100000000000000 : ℝ)^3423
        have hw : |(1303731481/2500000000 : ℝ)|=(1303731481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-407747627/2000000000 : ℝ)|^4447 ≤ (12669369324851/100000000000000 : ℝ)^3423
        have hw : |(-407747627/2000000000 : ℝ)|=(407747627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s4_3 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535906921/1250000000 : ℝ)*x 0 + (505788147/1250000000 : ℝ)*x 1 + (4540687667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535906921/1250000000 : ℝ)^4447 ≤ (33277046990439/100000000000000 : ℝ)^3423 := by
    have hnat : (535906921 : ℕ)^4447*100000000000000^3423 ≤ 33277046990439^3423*1250000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535906921 1250000000 33277046990439 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (505788147/1250000000 : ℝ)^4447 ≤ (30868045290841/100000000000000 : ℝ)^3423 := by
    have hnat : (505788147 : ℕ)^4447*100000000000000^3423 ≤ 30868045290841^3423*1250000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505788147 1250000000 30868045290841 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4540687667/10000000000 : ℝ)^4447 ≤ (17927453846037/50000000000000 : ℝ)^3423 := by
    have hnat : (4540687667 : ℕ)^4447*50000000000000^3423 ≤ 17927453846037^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4540687667 10000000000 17927453846037 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535906921/1250000000 : ℝ), (505788147/1250000000 : ℝ), (4540687667/10000000000 : ℝ)] ![(33277046990439/100000000000000 : ℝ), (30868045290841/100000000000000 : ℝ), (17927453846037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535906921/1250000000 : ℝ)|^4447 ≤ (33277046990439/100000000000000 : ℝ)^3423
        have hw : |(535906921/1250000000 : ℝ)|=(535906921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(505788147/1250000000 : ℝ)|^4447 ≤ (30868045290841/100000000000000 : ℝ)^3423
        have hw : |(505788147/1250000000 : ℝ)|=(505788147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4540687667/10000000000 : ℝ)|^4447 ≤ (17927453846037/50000000000000 : ℝ)^3423
        have hw : |(4540687667/10000000000 : ℝ)|=(4540687667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s4_4 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-962010621/5000000000 : ℝ)*x 0 + (5216075879/10000000000 : ℝ)*x 1 + (5437612259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (962010621/5000000000 : ℝ)^4447 ≤ (5875559792467/50000000000000 : ℝ)^3423 := by
    have hnat : (962010621 : ℕ)^4447*50000000000000^3423 ≤ 5875559792467^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962010621 5000000000 5875559792467 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216075879/10000000000 : ℝ)^4447 ≤ (42932535702987/100000000000000 : ℝ)^3423 := by
    have hnat : (5216075879 : ℕ)^4447*100000000000000^3423 ≤ 42932535702987^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216075879 10000000000 42932535702987 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437612259/10000000000 : ℝ)^4447 ≤ (4531634470247/10000000000000 : ℝ)^3423 := by
    have hnat : (5437612259 : ℕ)^4447*10000000000000^3423 ≤ 4531634470247^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437612259 10000000000 4531634470247 10000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-962010621/5000000000 : ℝ), (5216075879/10000000000 : ℝ), (5437612259/10000000000 : ℝ)] ![(5875559792467/50000000000000 : ℝ), (42932535702987/100000000000000 : ℝ), (4531634470247/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-962010621/5000000000 : ℝ)|^4447 ≤ (5875559792467/50000000000000 : ℝ)^3423
        have hw : |(-962010621/5000000000 : ℝ)|=(962010621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216075879/10000000000 : ℝ)|^4447 ≤ (42932535702987/100000000000000 : ℝ)^3423
        have hw : |(5216075879/10000000000 : ℝ)|=(5216075879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437612259/10000000000 : ℝ)|^4447 ≤ (4531634470247/10000000000000 : ℝ)^3423
        have hw : |(5437612259/10000000000 : ℝ)|=(5437612259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s4_5 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330958309/625000000 : ℝ)*x 0 + (-908026039/5000000000 : ℝ)*x 1 + (1359402881/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330958309/625000000 : ℝ)^4447 ≤ (43781957335499/100000000000000 : ℝ)^3423 := by
    have hnat : (330958309 : ℕ)^4447*100000000000000^3423 ≤ 43781957335499^3423*625000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330958309 625000000 43781957335499 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (908026039/5000000000 : ℝ)^4447 ≤ (10901705904439/100000000000000 : ℝ)^3423 := by
    have hnat : (908026039 : ℕ)^4447*100000000000000^3423 ≤ 10901705904439^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908026039 5000000000 10901705904439 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359402881/2500000000 : ℝ)^4447 ≤ (5664542093081/12500000000000 : ℝ)^3423 := by
    have hnat : (1359402881 : ℕ)^4447*12500000000000^3423 ≤ 5664542093081^3423*2500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359402881 2500000000 5664542093081 12500000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330958309/625000000 : ℝ), (-908026039/5000000000 : ℝ), (1359402881/2500000000 : ℝ)] ![(43781957335499/100000000000000 : ℝ), (10901705904439/100000000000000 : ℝ), (5664542093081/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330958309/625000000 : ℝ)|^4447 ≤ (43781957335499/100000000000000 : ℝ)^3423
        have hw : |(330958309/625000000 : ℝ)|=(330958309/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-908026039/5000000000 : ℝ)|^4447 ≤ (10901705904439/100000000000000 : ℝ)^3423
        have hw : |(-908026039/5000000000 : ℝ)|=(908026039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359402881/2500000000 : ℝ)|^4447 ≤ (5664542093081/12500000000000 : ℝ)^3423
        have hw : |(1359402881/2500000000 : ℝ)|=(1359402881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s4_6 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661916573/1250000000 : ℝ)*x 0 + (2718805839/5000000000 : ℝ)*x 1 + (-45401309/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661916573/1250000000 : ℝ)^4447 ≤ (5472744183573/12500000000000 : ℝ)^3423 := by
    have hnat : (661916573 : ℕ)^4447*12500000000000^3423 ≤ 5472744183573^3423*1250000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661916573 1250000000 5472744183573 12500000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718805839/5000000000 : ℝ)^4447 ≤ (45316338412001/100000000000000 : ℝ)^3423 := by
    have hnat : (2718805839 : ℕ)^4447*100000000000000^3423 ≤ 45316338412001^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718805839 5000000000 45316338412001 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45401309/250000000 : ℝ)^4447 ≤ (10901708103693/100000000000000 : ℝ)^3423 := by
    have hnat : (45401309 : ℕ)^4447*100000000000000^3423 ≤ 10901708103693^3423*250000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45401309 250000000 10901708103693 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661916573/1250000000 : ℝ), (2718805839/5000000000 : ℝ), (-45401309/250000000 : ℝ)] ![(5472744183573/12500000000000 : ℝ), (45316338412001/100000000000000 : ℝ), (10901708103693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661916573/1250000000 : ℝ)|^4447 ≤ (5472744183573/12500000000000 : ℝ)^3423
        have hw : |(661916573/1250000000 : ℝ)|=(661916573/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718805839/5000000000 : ℝ)|^4447 ≤ (45316338412001/100000000000000 : ℝ)^3423
        have hw : |(2718805839/5000000000 : ℝ)|=(2718805839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-45401309/250000000 : ℝ)|^4447 ≤ (10901708103693/100000000000000 : ℝ)^3423
        have hw : |(-45401309/250000000 : ℝ)|=(45401309/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s4_7 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4287324901/10000000000 : ℝ)*x 0 + (4538145911/10000000000 : ℝ)*x 1 + (809772981/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4287324901/10000000000 : ℝ)^4447 ≤ (33277748151321/100000000000000 : ℝ)^3423 := by
    have hnat : (4287324901 : ℕ)^4447*100000000000000^3423 ≤ 33277748151321^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4287324901 10000000000 33277748151321 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4538145911/10000000000 : ℝ)^4447 ≤ (35828835070729/100000000000000 : ℝ)^3423 := by
    have hnat : (4538145911 : ℕ)^4447*100000000000000^3423 ≤ 35828835070729^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4538145911 10000000000 35828835070729 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (809772981/2000000000 : ℝ)^4447 ≤ (193083854817/625000000000 : ℝ)^3423 := by
    have hnat : (809772981 : ℕ)^4447*625000000000^3423 ≤ 193083854817^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809772981 2000000000 193083854817 625000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4287324901/10000000000 : ℝ), (4538145911/10000000000 : ℝ), (809772981/2000000000 : ℝ)] ![(33277748151321/100000000000000 : ℝ), (35828835070729/100000000000000 : ℝ), (193083854817/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4287324901/10000000000 : ℝ)|^4447 ≤ (33277748151321/100000000000000 : ℝ)^3423
        have hw : |(4287324901/10000000000 : ℝ)|=(4287324901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4538145911/10000000000 : ℝ)|^4447 ≤ (35828835070729/100000000000000 : ℝ)^3423
        have hw : |(4538145911/10000000000 : ℝ)|=(4538145911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(809772981/2000000000 : ℝ)|^4447 ≤ (193083854817/625000000000 : ℝ)^3423
        have hw : |(809772981/2000000000 : ℝ)|=(809772981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1475_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7789/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10669/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10751/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (484/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7789/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10669/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7789/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10669/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7789/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10669/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7789/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10669/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7789/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10669/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7789/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10669/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10669/100000 : ℝ) ^ (4445/1024 : ℝ) ≤ (755387326881057/12500000000000000000 : ℝ) := by
    have hpowers : (10669/100000 : ℝ)^4445 ≤ (755387326881057/12500000000000000000 : ℝ)^1024 := by
      have hnat : (10669 : ℕ)^4445*12500000000000000000^1024 ≤ 755387326881057^1024*100000^4445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10669 100000 755387326881057 12500000000000000000 4445 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10669/100000 : ℝ)) (X := (755387326881057/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7789/50000 : ℝ) ^ (4445/1024 : ℝ) ≤ (31249162547970327/100000000000000000000 : ℝ) := by
    have hpowers : (7789/50000 : ℝ)^4445 ≤ (31249162547970327/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7789 : ℕ)^4445*100000000000000000000^1024 ≤ 31249162547970327^1024*50000^4445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7789 50000 31249162547970327 100000000000000000000 4445 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7789/50000 : ℝ)) (X := (31249162547970327/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250755387326881057/6250000000000000000 : ℝ) ≤ (10000278418231533/10000000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (6250755387326881057/6250000000000000000 : ℝ)^1024 ≤ (10000278418231533/10000000000000000 : ℝ)^4445 := by
      have hnat : (6250755387326881057 : ℕ)^1024*10000000000000000^4445 ≤ 10000278418231533^4445*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250755387326881057 6250000000000000000 10000278418231533 10000000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000278418231533/10000000000000000 : ℝ)) (X := (6250755387326881057/6250000000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037292261163018783/100000000000000000000 : ℝ) ≤ (62505368644057/62500000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (100037292261163018783/100000000000000000000 : ℝ)^1024 ≤ (62505368644057/62500000000000 : ℝ)^4445 := by
      have hnat : (100037292261163018783 : ℕ)^1024*62500000000000^4445 ≤ 62505368644057^4445*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037292261163018783 100000000000000000000 62505368644057 62500000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62505368644057/62500000000000 : ℝ)) (X := (100037292261163018783/100000000000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031249162547970327/50000000000000000000 : ℝ) ≤ (10001439547866707/10000000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (50031249162547970327/50000000000000000000 : ℝ)^1024 ≤ (10001439547866707/10000000000000000 : ℝ)^4445 := by
      have hnat : (50031249162547970327 : ℕ)^1024*10000000000000000^4445 ≤ 10001439547866707^4445*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031249162547970327 50000000000000000000 10001439547866707 10000000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001439547866707/10000000000000000 : ℝ)) (X := (50031249162547970327/50000000000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(755387326881057/12500000000000000000 : ℝ) ≤ ((49078978663020924091/49090000000000000000 : ℝ)+2*(580564817587/490900000000000 : ℝ)*(10669/100000 : ℝ))^(4445/1024 : ℝ) := by
    rw [show (49078978663020924091/49090000000000000000 : ℝ)+2*(580564817587/490900000000000 : ℝ)*(10669/100000 : ℝ)=(10000278418231533/10000000000000000 : ℝ) by norm_num, show 1+2*(755387326881057/12500000000000000000 : ℝ)=(6250755387326881057/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31249162547970327/100000000000000000000 : ℝ)+(755387326881057/12500000000000000000 : ℝ) ≤ ((49078978663020924091/49090000000000000000 : ℝ)+(580564817587/490900000000000 : ℝ)*((7789/50000 : ℝ)+(10669/100000 : ℝ)))^(4445/1024 : ℝ) := by
    rw [show (49078978663020924091/49090000000000000000 : ℝ)+(580564817587/490900000000000 : ℝ)*((7789/50000 : ℝ)+(10669/100000 : ℝ))=(62505368644057/62500000000000 : ℝ) by norm_num, show 1+(31249162547970327/100000000000000000000 : ℝ)+(755387326881057/12500000000000000000 : ℝ)=(100037292261163018783/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31249162547970327/100000000000000000000 : ℝ) ≤ ((49078978663020924091/49090000000000000000 : ℝ)+2*(580564817587/490900000000000 : ℝ)*(7789/50000 : ℝ))^(4445/1024 : ℝ) := by
    rw [show (49078978663020924091/49090000000000000000 : ℝ)+2*(580564817587/490900000000000 : ℝ)*(7789/50000 : ℝ)=(10001439547866707/10000000000000000 : ℝ) by norm_num, show 1+2*(31249162547970327/100000000000000000000 : ℝ)=(50031249162547970327/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (49078978663020924091/49090000000000000000 : ℝ)*(X 1 0+X 2 0)+(580564817587/490900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (10669/100000 : ℝ)) (hi := (7789/50000 : ℝ)) (c := (49078978663020924091/49090000000000000000 : ℝ)) (alpha := (580564817587/490900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (49078978663020924091/49090000000000000000 : ℝ)*(X 0 1+X 2 1)+(580564817587/490900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (10669/100000 : ℝ)) (hi := (7789/50000 : ℝ)) (c := (49078978663020924091/49090000000000000000 : ℝ)) (alpha := (580564817587/490900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (49078978663020924091/49090000000000000000 : ℝ)*(X 0 2+X 1 2)+(580564817587/490900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (10669/100000 : ℝ)) (hi := (7789/50000 : ℝ)) (c := (49078978663020924091/49090000000000000000 : ℝ)) (alpha := (580564817587/490900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-480997437/2500000000 : ℝ)*X 0 0+(5438770979/10000000000 : ℝ)*X 0 1+(1042985189/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353742403/10000000000 : ℝ)*X 1 0+(-1019369051/5000000000 : ℝ)*X 1 1+(5214925961/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334608901/625000000 : ℝ)*X 2 0+(1303731481/2500000000 : ℝ)*X 2 1+(-407747627/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((535906921/1250000000 : ℝ)*X 0 0+(505788147/1250000000 : ℝ)*X 0 1+(4540687667/10000000000 : ℝ)*X 0 2+(535906921/1250000000 : ℝ)*X 1 0+(505788147/1250000000 : ℝ)*X 1 1+(4540687667/10000000000 : ℝ)*X 1 2+(535906921/1250000000 : ℝ)*X 2 0+(505788147/1250000000 : ℝ)*X 2 1+(4540687667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-962010621/5000000000 : ℝ)*X 0 0+(5216075879/10000000000 : ℝ)*X 0 1+(5437612259/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((330958309/625000000 : ℝ)*X 1 0+(-908026039/5000000000 : ℝ)*X 1 1+(1359402881/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661916573/1250000000 : ℝ)*X 2 0+(2718805839/5000000000 : ℝ)*X 2 1+(-45401309/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4287324901/10000000000 : ℝ)*X 0 0+(4538145911/10000000000 : ℝ)*X 0 1+(809772981/2000000000 : ℝ)*X 0 2+(4287324901/10000000000 : ℝ)*X 1 0+(4538145911/10000000000 : ℝ)*X 1 1+(809772981/2000000000 : ℝ)*X 1 2+(4287324901/10000000000 : ℝ)*X 2 0+(4538145911/10000000000 : ℝ)*X 2 1+(809772981/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13845310437439153320204360801/1227250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2027404803/100000000000000 : ℝ)*(base19) + (944553191/50000000000000 : ℝ)*(base23) + (79849079/100000000000000 : ℝ)*(lower2) + (154157291/50000000000000 : ℝ)*(upper3) + (16957681/10000000000000 : ℝ)*(upper5) + (3245096521945291/100000000000000 : ℝ)*(major0) + (3245096521945291/100000000000000 : ℝ)*(major1) + (811274130486323/25000000000000 : ℝ)*(major2) + (4467408534893079/100000000000000 : ℝ)*(sp0) + (1116859137005001/25000000000000 : ℝ)*(sp1) + (558429585789803/12500000000000 : ℝ)*(sp2) + (2022738675671893/100000000000000 : ℝ)*(sp3) + (1877533233/6250000000000 : ℝ)*(sp4) + (15416741441/100000000000000 : ℝ)*(sp7) + (1011377046206667/50000000000000 : ℝ)*(f.failure) + (2233719287712403/50000000000000 : ℝ)*(f.sum) + (208251408702509/49090000000000000000000000000 : ℝ)*base66 + (51170418630541694519/4909000000000000000000000000000000 : ℝ)*base68 + (12494839983529617607/1227250000000000000000000000000000 : ℝ)*base70 + (41746436594686694519/4909000000000000000000000000000000 : ℝ)*base72 + (6945582071769/49090000000000000000000000000 : ℝ)*base74 + (19217268319037867607/1227250000000000000000000000000000 : ℝ)*base76 + (53311399044193394519/4909000000000000000000000000000000 : ℝ)*base78 + (49992784199707394519/4909000000000000000000000000000000 : ℝ)*base80 + (31173677281503/24545000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (62416537/5000000000000000000000 : ℝ)*base89 + (62416537/5000000000000000000000 : ℝ)*base91 + (12416537/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (463026531710303900928262209/490900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (760954191/50000000000000 : ℝ)*(base19) + (1060527971/100000000000000 : ℝ)*(base23) + (8627797/100000000000000 : ℝ)*(lower4) + (99687807/25000000000000 : ℝ)*(upper5) + (655775245138811/20000000000000 : ℝ)*(major0) + (655775245138811/20000000000000 : ℝ)*(major1) + (655775245138811/20000000000000 : ℝ)*(major2) + (304544361/25000000000000 : ℝ)*(sp0) + (17500285497/100000000000000 : ℝ)*(sp1) + (1008051949/50000000000000 : ℝ)*(sp2) + (4513941330726897/100000000000000 : ℝ)*(sp4) + (2256961763355231/50000000000000 : ℝ)*(sp5) + (564242434034059/12500000000000 : ℝ)*(sp6) + (408761974208621/20000000000000 : ℝ)*(sp7) + (408761974208621/20000000000000 : ℝ)*(f.failure) + (225697127445217/5000000000000 : ℝ)*(f.sum) + (11568983654593/2454500000000000000000000000 : ℝ)*base65 + (7952066142254504199/981800000000000000000000000000000 : ℝ)*base68 + (9048674038615704199/981800000000000000000000000000000 : ℝ)*base70 + (1320437396468504199/981800000000000000000000000000000 : ℝ)*base72 + (2678778351779/613625000000000000000000000 : ℝ)*base73 + (15294921770819304199/981800000000000000000000000000000 : ℝ)*base76 + (7231340533963104199/981800000000000000000000000000000 : ℝ)*base78 + (13278296415006704199/981800000000000000000000000000000 : ℝ)*base80 + (4249472084341/2454500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (123569/2000000000000000000000 : ℝ)*base90 + (123569/2000000000000000000000 : ℝ)*base92 + (123569/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1475_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7789/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10669/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10751/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (484/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1475_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1475_s5_0 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1924084201/10000000000 : ℝ)*x 0 + (2719085533/5000000000 : ℝ)*x 1 + (5215463337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1924084201/10000000000 : ℝ)^4447 ≤ (2937904786781/25000000000000 : ℝ)^3423 := by
    have hnat : (1924084201 : ℕ)^4447*25000000000000^3423 ≤ 2937904786781^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924084201 10000000000 2937904786781 25000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719085533/5000000000 : ℝ)^4447 ≤ (1416324843161/3125000000000 : ℝ)^3423 := by
    have hnat : (2719085533 : ℕ)^4447*3125000000000^3423 ≤ 1416324843161^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719085533 5000000000 1416324843161 3125000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215463337/10000000000 : ℝ)^4447 ≤ (343407886853/800000000000 : ℝ)^3423 := by
    have hnat : (5215463337 : ℕ)^4447*800000000000^3423 ≤ 343407886853^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215463337 10000000000 343407886853 800000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1924084201/10000000000 : ℝ), (2719085533/5000000000 : ℝ), (5215463337/10000000000 : ℝ)] ![(2937904786781/25000000000000 : ℝ), (1416324843161/3125000000000 : ℝ), (343407886853/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1924084201/10000000000 : ℝ)|^4447 ≤ (2937904786781/25000000000000 : ℝ)^3423
        have hw : |(-1924084201/10000000000 : ℝ)|=(1924084201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719085533/5000000000 : ℝ)|^4447 ≤ (1416324843161/3125000000000 : ℝ)^3423
        have hw : |(2719085533/5000000000 : ℝ)|=(2719085533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215463337/10000000000 : ℝ)|^4447 ≤ (343407886853/800000000000 : ℝ)^3423
        have hw : |(5215463337/10000000000 : ℝ)|=(5215463337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s5_1 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353586039/10000000000 : ℝ)*x 0 + (-407647053/2000000000 : ℝ)*x 1 + (5215463207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353586039/10000000000 : ℝ)^4447 ≤ (44408705889947/100000000000000 : ℝ)^3423 := by
    have hnat : (5353586039 : ℕ)^4447*100000000000000^3423 ≤ 44408705889947^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353586039 10000000000 44408705889947 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (407647053/2000000000 : ℝ)^4447 ≤ (12665309629133/100000000000000 : ℝ)^3423 := by
    have hnat : (407647053 : ℕ)^4447*100000000000000^3423 ≤ 12665309629133^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407647053 2000000000 12665309629133 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215463207/10000000000 : ℝ)^4447 ≤ (42925984466573/100000000000000 : ℝ)^3423 := by
    have hnat : (5215463207 : ℕ)^4447*100000000000000^3423 ≤ 42925984466573^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215463207 10000000000 42925984466573 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353586039/10000000000 : ℝ), (-407647053/2000000000 : ℝ), (5215463207/10000000000 : ℝ)] ![(44408705889947/100000000000000 : ℝ), (12665309629133/100000000000000 : ℝ), (42925984466573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353586039/10000000000 : ℝ)|^4447 ≤ (44408705889947/100000000000000 : ℝ)^3423
        have hw : |(5353586039/10000000000 : ℝ)|=(5353586039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-407647053/2000000000 : ℝ)|^4447 ≤ (12665309629133/100000000000000 : ℝ)^3423
        have hw : |(-407647053/2000000000 : ℝ)|=(407647053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215463207/10000000000 : ℝ)|^4447 ≤ (42925984466573/100000000000000 : ℝ)^3423
        have hw : |(5215463207/10000000000 : ℝ)|=(5215463207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s5_2 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070717321/2000000000 : ℝ)*x 0 + (521546241/1000000000 : ℝ)*x 1 + (-407647113/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070717321/2000000000 : ℝ)^4447 ≤ (5551088998691/12500000000000 : ℝ)^3423 := by
    have hnat : (1070717321 : ℕ)^4447*12500000000000^3423 ≤ 5551088998691^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070717321 2000000000 5551088998691 12500000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521546241/1000000000 : ℝ)^4447 ≤ (42925975944487/100000000000000 : ℝ)^3423 := by
    have hnat : (521546241 : ℕ)^4447*100000000000000^3423 ≤ 42925975944487^3423*1000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521546241 1000000000 42925975944487 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (407647113/2000000000 : ℝ)^4447 ≤ (158316400637/1250000000000 : ℝ)^3423 := by
    have hnat : (407647113 : ℕ)^4447*1250000000000^3423 ≤ 158316400637^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407647113 2000000000 158316400637 1250000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070717321/2000000000 : ℝ), (521546241/1000000000 : ℝ), (-407647113/2000000000 : ℝ)] ![(5551088998691/12500000000000 : ℝ), (42925975944487/100000000000000 : ℝ), (158316400637/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070717321/2000000000 : ℝ)|^4447 ≤ (5551088998691/12500000000000 : ℝ)^3423
        have hw : |(1070717321/2000000000 : ℝ)|=(1070717321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521546241/1000000000 : ℝ)|^4447 ≤ (42925975944487/100000000000000 : ℝ)^3423
        have hw : |(521546241/1000000000 : ℝ)|=(521546241/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-407647113/2000000000 : ℝ)|^4447 ≤ (158316400637/1250000000000 : ℝ)^3423
        have hw : |(-407647113/2000000000 : ℝ)|=(407647113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s5_3 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2143655811/5000000000 : ℝ)*x 0 + (1011888659/2500000000 : ℝ)*x 1 + (1134856289/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143655811/5000000000 : ℝ)^4447 ≤ (33277614247511/100000000000000 : ℝ)^3423 := by
    have hnat : (2143655811 : ℕ)^4447*100000000000000^3423 ≤ 33277614247511^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143655811 5000000000 33277614247511 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1011888659/2500000000 : ℝ)^4447 ≤ (308804290683/1000000000000 : ℝ)^3423 := by
    have hnat : (1011888659 : ℕ)^4447*1000000000000^3423 ≤ 308804290683^3423*2500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011888659 2500000000 308804290683 1000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1134856289/2500000000 : ℝ)^4447 ≤ (17920978330929/50000000000000 : ℝ)^3423 := by
    have hnat : (1134856289 : ℕ)^4447*50000000000000^3423 ≤ 17920978330929^3423*2500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134856289 2500000000 17920978330929 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2143655811/5000000000 : ℝ), (1011888659/2500000000 : ℝ), (1134856289/2500000000 : ℝ)] ![(33277614247511/100000000000000 : ℝ), (308804290683/1000000000000 : ℝ), (17920978330929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2143655811/5000000000 : ℝ)|^4447 ≤ (33277614247511/100000000000000 : ℝ)^3423
        have hw : |(2143655811/5000000000 : ℝ)|=(2143655811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1011888659/2500000000 : ℝ)|^4447 ≤ (308804290683/1000000000000 : ℝ)^3423
        have hw : |(1011888659/2500000000 : ℝ)|=(1011888659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1134856289/2500000000 : ℝ)|^4447 ≤ (17920978330929/50000000000000 : ℝ)^3423
        have hw : |(1134856289/2500000000 : ℝ)|=(1134856289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s5_4 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-7516073/39062500 : ℝ)*x 0 + (2608301073/5000000000 : ℝ)*x 1 + (2718511999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7516073/39062500 : ℝ)^4447 ≤ (2937965263691/25000000000000 : ℝ)^3423 := by
    have hnat : (7516073 : ℕ)^4447*25000000000000^3423 ≤ 2937965263691^3423*39062500^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7516073 39062500 2937965263691 25000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608301073/5000000000 : ℝ)^4447 ≤ (5367270400467/12500000000000 : ℝ)^3423 := by
    have hnat : (2608301073 : ℕ)^4447*12500000000000^3423 ≤ 5367270400467^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608301073 5000000000 5367270400467 12500000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718511999/5000000000 : ℝ)^4447 ≤ (22654987861163/50000000000000 : ℝ)^3423 := by
    have hnat : (2718511999 : ℕ)^4447*50000000000000^3423 ≤ 22654987861163^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718511999 5000000000 22654987861163 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7516073/39062500 : ℝ), (2608301073/5000000000 : ℝ), (2718511999/5000000000 : ℝ)] ![(2937965263691/25000000000000 : ℝ), (5367270400467/12500000000000 : ℝ), (22654987861163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7516073/39062500 : ℝ)|^4447 ≤ (2937965263691/25000000000000 : ℝ)^3423
        have hw : |(-7516073/39062500 : ℝ)|=(7516073/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608301073/5000000000 : ℝ)|^4447 ≤ (5367270400467/12500000000000 : ℝ)^3423
        have hw : |(2608301073/5000000000 : ℝ)|=(2608301073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718511999/5000000000 : ℝ)|^4447 ≤ (22654987861163/50000000000000 : ℝ)^3423
        have hw : |(2718511999/5000000000 : ℝ)|=(2718511999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s5_5 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295473159/10000000000 : ℝ)*x 0 + (-363334933/2000000000 : ℝ)*x 1 + (679627991/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295473159/10000000000 : ℝ)^4447 ≤ (1751338538047/4000000000000 : ℝ)^3423 := by
    have hnat : (5295473159 : ℕ)^4447*4000000000000^3423 ≤ 1751338538047^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295473159 10000000000 1751338538047 4000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (363334933/2000000000 : ℝ)^4447 ≤ (10906561569361/100000000000000 : ℝ)^3423 := by
    have hnat : (363334933 : ℕ)^4447*100000000000000^3423 ≤ 10906561569361^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363334933 2000000000 10906561569361 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679627991/1250000000 : ℝ)^4447 ≤ (22654987482231/50000000000000 : ℝ)^3423 := by
    have hnat : (679627991 : ℕ)^4447*50000000000000^3423 ≤ 22654987482231^3423*1250000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679627991 1250000000 22654987482231 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295473159/10000000000 : ℝ), (-363334933/2000000000 : ℝ), (679627991/1250000000 : ℝ)] ![(1751338538047/4000000000000 : ℝ), (10906561569361/100000000000000 : ℝ), (22654987482231/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295473159/10000000000 : ℝ)|^4447 ≤ (1751338538047/4000000000000 : ℝ)^3423
        have hw : |(5295473159/10000000000 : ℝ)|=(5295473159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-363334933/2000000000 : ℝ)|^4447 ≤ (10906561569361/100000000000000 : ℝ)^3423
        have hw : |(-363334933/2000000000 : ℝ)|=(363334933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679627991/1250000000 : ℝ)|^4447 ≤ (22654987482231/50000000000000 : ℝ)^3423
        have hw : |(679627991/1250000000 : ℝ)|=(679627991/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s5_6 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647736547/5000000000 : ℝ)*x 0 + (5437023953/10000000000 : ℝ)*x 1 + (-11354217/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647736547/5000000000 : ℝ)^4447 ≤ (2736466422061/6250000000000 : ℝ)^3423 := by
    have hnat : (2647736547 : ℕ)^4447*6250000000000^3423 ≤ 2736466422061^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647736547 5000000000 2736466422061 6250000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437023953/10000000000 : ℝ)^4447 ≤ (5663746904391/12500000000000 : ℝ)^3423 := by
    have hnat : (5437023953 : ℕ)^4447*12500000000000^3423 ≤ 5663746904391^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437023953 10000000000 5663746904391 12500000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11354217/62500000 : ℝ)^4447 ≤ (5453280999169/50000000000000 : ℝ)^3423 := by
    have hnat : (11354217 : ℕ)^4447*50000000000000^3423 ≤ 5453280999169^3423*62500000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11354217 62500000 5453280999169 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647736547/5000000000 : ℝ), (5437023953/10000000000 : ℝ), (-11354217/62500000 : ℝ)] ![(2736466422061/6250000000000 : ℝ), (5663746904391/12500000000000 : ℝ), (5453280999169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647736547/5000000000 : ℝ)|^4447 ≤ (2736466422061/6250000000000 : ℝ)^3423
        have hw : |(2647736547/5000000000 : ℝ)|=(2647736547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437023953/10000000000 : ℝ)|^4447 ≤ (5663746904391/12500000000000 : ℝ)^3423
        have hw : |(5437023953/10000000000 : ℝ)|=(5437023953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-11354217/62500000 : ℝ)|^4447 ≤ (5453280999169/50000000000000 : ℝ)^3423
        have hw : |(-11354217/62500000 : ℝ)|=(11354217/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s5_7 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4287379637/10000000000 : ℝ)*x 0 + (283556867/625000000 : ℝ)*x 1 + (2025044033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4287379637/10000000000 : ℝ)^4447 ≤ (4159787512969/12500000000000 : ℝ)^3423 := by
    have hnat : (4287379637 : ℕ)^4447*12500000000000^3423 ≤ 4159787512969^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4287379637 10000000000 4159787512969 12500000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283556867/625000000 : ℝ)^4447 ≤ (2238509856703/6250000000000 : ℝ)^3423 := by
    have hnat : (283556867 : ℕ)^4447*6250000000000^3423 ≤ 2238509856703^3423*625000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283556867 625000000 2238509856703 6250000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2025044033/5000000000 : ℝ)^4447 ≤ (1236221686897/4000000000000 : ℝ)^3423 := by
    have hnat : (2025044033 : ℕ)^4447*4000000000000^3423 ≤ 1236221686897^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025044033 5000000000 1236221686897 4000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4287379637/10000000000 : ℝ), (283556867/625000000 : ℝ), (2025044033/5000000000 : ℝ)] ![(4159787512969/12500000000000 : ℝ), (2238509856703/6250000000000 : ℝ), (1236221686897/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4287379637/10000000000 : ℝ)|^4447 ≤ (4159787512969/12500000000000 : ℝ)^3423
        have hw : |(4287379637/10000000000 : ℝ)|=(4287379637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(283556867/625000000 : ℝ)|^4447 ≤ (2238509856703/6250000000000 : ℝ)^3423
        have hw : |(283556867/625000000 : ℝ)|=(283556867/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2025044033/5000000000 : ℝ)|^4447 ≤ (1236221686897/4000000000000 : ℝ)^3423
        have hw : |(2025044033/5000000000 : ℝ)|=(2025044033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1475_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10751/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10763/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3869/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10751/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10751/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10751/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10751/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10751/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10751/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10751/100000 : ℝ) ^ (4445/1024 : ℝ) ≤ (195228657366171/3125000000000000000 : ℝ) := by
    have hpowers : (10751/100000 : ℝ)^4445 ≤ (195228657366171/3125000000000000000 : ℝ)^1024 := by
      have hnat : (10751 : ℕ)^4445*3125000000000000000^1024 ≤ 195228657366171^1024*100000^4445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10751 100000 195228657366171 3125000000000000000 4445 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10751/100000 : ℝ)) (X := (195228657366171/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (484/3125 : ℝ) ^ (4445/1024 : ℝ) ≤ (15236503747990211/50000000000000000000 : ℝ) := by
    have hpowers : (484/3125 : ℝ)^4445 ≤ (15236503747990211/50000000000000000000 : ℝ)^1024 := by
      have hnat : (484 : ℕ)^4445*50000000000000000000^1024 ≤ 15236503747990211^1024*3125^4445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        484 3125 15236503747990211 50000000000000000000 4445 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (484/3125 : ℝ)) (X := (15236503747990211/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562695228657366171/1562500000000000000 : ℝ) ≤ (250007195663757/250000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (1562695228657366171/1562500000000000000 : ℝ)^1024 ≤ (250007195663757/250000000000000 : ℝ)^4445 := by
      have hnat : (1562695228657366171 : ℕ)^1024*250000000000000^4445 ≤ 250007195663757^4445*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562695228657366171 1562500000000000000 250007195663757 250000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250007195663757/250000000000000 : ℝ)) (X := (1562695228657366171/1562500000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018360162265848947/50000000000000000000 : ℝ) ≤ (10000845811027483/10000000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (50018360162265848947/50000000000000000000 : ℝ)^1024 ≤ (10000845811027483/10000000000000000 : ℝ)^4445 := by
      have hnat : (50018360162265848947 : ℕ)^1024*10000000000000000^4445 ≤ 10000845811027483^4445*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018360162265848947 50000000000000000000 10000845811027483 10000000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000845811027483/10000000000000000 : ℝ)) (X := (50018360162265848947/50000000000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015236503747990211/25000000000000000000 : ℝ) ≤ (5000701897752343/5000000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (25015236503747990211/25000000000000000000 : ℝ)^1024 ≤ (5000701897752343/5000000000000000 : ℝ)^4445 := by
      have hnat : (25015236503747990211 : ℕ)^1024*5000000000000000^4445 ≤ 5000701897752343^4445*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015236503747990211 25000000000000000000 5000701897752343 5000000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000701897752343/5000000000000000 : ℝ)) (X := (25015236503747990211/25000000000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(195228657366171/3125000000000000000 : ℝ) ≤ ((23679682826069928727/23685000000000000000 : ℝ)+2*(557984477203/473700000000000 : ℝ)*(10751/100000 : ℝ))^(4445/1024 : ℝ) := by
    rw [show (23679682826069928727/23685000000000000000 : ℝ)+2*(557984477203/473700000000000 : ℝ)*(10751/100000 : ℝ)=(250007195663757/250000000000000 : ℝ) by norm_num, show 1+2*(195228657366171/3125000000000000000 : ℝ)=(1562695228657366171/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15236503747990211/50000000000000000000 : ℝ)+(195228657366171/3125000000000000000 : ℝ) ≤ ((23679682826069928727/23685000000000000000 : ℝ)+(557984477203/473700000000000 : ℝ)*((484/3125 : ℝ)+(10751/100000 : ℝ)))^(4445/1024 : ℝ) := by
    rw [show (23679682826069928727/23685000000000000000 : ℝ)+(557984477203/473700000000000 : ℝ)*((484/3125 : ℝ)+(10751/100000 : ℝ))=(10000845811027483/10000000000000000 : ℝ) by norm_num, show 1+(15236503747990211/50000000000000000000 : ℝ)+(195228657366171/3125000000000000000 : ℝ)=(50018360162265848947/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15236503747990211/50000000000000000000 : ℝ) ≤ ((23679682826069928727/23685000000000000000 : ℝ)+2*(557984477203/473700000000000 : ℝ)*(484/3125 : ℝ))^(4445/1024 : ℝ) := by
    rw [show (23679682826069928727/23685000000000000000 : ℝ)+2*(557984477203/473700000000000 : ℝ)*(484/3125 : ℝ)=(5000701897752343/5000000000000000 : ℝ) by norm_num, show 1+2*(15236503747990211/50000000000000000000 : ℝ)=(25015236503747990211/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23679682826069928727/23685000000000000000 : ℝ)*(X 1 0+X 2 0)+(557984477203/473700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (10751/100000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (23679682826069928727/23685000000000000000 : ℝ)) (alpha := (557984477203/473700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23679682826069928727/23685000000000000000 : ℝ)*(X 0 1+X 2 1)+(557984477203/473700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (10751/100000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (23679682826069928727/23685000000000000000 : ℝ)) (alpha := (557984477203/473700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23679682826069928727/23685000000000000000 : ℝ)*(X 0 2+X 1 2)+(557984477203/473700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (10751/100000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (23679682826069928727/23685000000000000000 : ℝ)) (alpha := (557984477203/473700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1924084201/10000000000 : ℝ)*X 0 0+(2719085533/5000000000 : ℝ)*X 0 1+(5215463337/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353586039/10000000000 : ℝ)*X 1 0+(-407647053/2000000000 : ℝ)*X 1 1+(5215463207/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070717321/2000000000 : ℝ)*X 2 0+(521546241/1000000000 : ℝ)*X 2 1+(-407647113/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2143655811/5000000000 : ℝ)*X 0 0+(1011888659/2500000000 : ℝ)*X 0 1+(1134856289/2500000000 : ℝ)*X 0 2+(2143655811/5000000000 : ℝ)*X 1 0+(1011888659/2500000000 : ℝ)*X 1 1+(1134856289/2500000000 : ℝ)*X 1 2+(2143655811/5000000000 : ℝ)*X 2 0+(1011888659/2500000000 : ℝ)*X 2 1+(1134856289/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-7516073/39062500 : ℝ)*X 0 0+(2608301073/5000000000 : ℝ)*X 0 1+(2718511999/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295473159/10000000000 : ℝ)*X 1 0+(-363334933/2000000000 : ℝ)*X 1 1+(679627991/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647736547/5000000000 : ℝ)*X 2 0+(5437023953/10000000000 : ℝ)*X 2 1+(-11354217/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4287379637/10000000000 : ℝ)*X 0 0+(283556867/625000000 : ℝ)*X 0 1+(2025044033/5000000000 : ℝ)*X 0 2+(4287379637/10000000000 : ℝ)*X 1 0+(283556867/625000000 : ℝ)*X 1 1+(2025044033/5000000000 : ℝ)*X 1 2+(4287379637/10000000000 : ℝ)*X 2 0+(283556867/625000000 : ℝ)*X 2 1+(2025044033/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40044483030727190695429/7895000000000000000000000000 : ℝ) := by norm_num
    linear_combination (640943611/50000000000000 : ℝ)*(base19) + (1671753079/100000000000000 : ℝ)*(base23) + (30135399/100000000000000 : ℝ)*(upper2) + (259779043/100000000000000 : ℝ)*(upper3) + (75563739/100000000000000 : ℝ)*(upper4) + (407705603512901/12500000000000 : ℝ)*(major0) + (407705603512901/12500000000000 : ℝ)*(major1) + (407705603512901/12500000000000 : ℝ)*(major2) + (1122551769363473/25000000000000 : ℝ)*(sp0) + (561277389744561/12500000000000 : ℝ)*(sp1) + (449021872809063/10000000000000 : ℝ)*(sp2) + (508265025323937/25000000000000 : ℝ)*(sp3) + (6661194909/50000000000000 : ℝ)*(sp4) + (8985995879/100000000000000 : ℝ)*(sp7) + (508267271822907/25000000000000 : ℝ)*(f.failure) + (449022039984371/10000000000000 : ℝ)*(f.sum) + (66119283292331/23685000000000000000000000000 : ℝ)*base66 + (103940848338530991/98687500000000000000000000000000 : ℝ)*base68 + (290024335848905991/98687500000000000000000000000000 : ℝ)*base70 + (377237029698656509/98687500000000000000000000000000 : ℝ)*base71 + (478234336577/740156250000000000000000000 : ℝ)*base73 + (485438123898405991/98687500000000000000000000000000 : ℝ)*base76 + (1795599426803531509/98687500000000000000000000000000 : ℝ)*base77 + (785492087911469009/98687500000000000000000000000000 : ℝ)*base79 + (3081947467987/2960625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (30899177/2500000000000000000000 : ℝ)*base89 + (30899177/2500000000000000000000 : ℝ)*base91 + (30899177/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3437632775307391354815039221/394750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (687931509/50000000000000 : ℝ)*(base19) + (355506017/25000000000000 : ℝ)*(base23) + (94353559/50000000000000 : ℝ)*(upper3) + (56190137/100000000000000 : ℝ)*(lower4) + (220670589/100000000000000 : ℝ)*(upper5) + (3295447019354477/100000000000000 : ℝ)*(major0) + (3295447019354477/100000000000000 : ℝ)*(major1) + (3295447019354477/100000000000000 : ℝ)*(major2) + (18384964507/100000000000000 : ℝ)*(sp1) + (17996425043/100000000000000 : ℝ)*(sp2) + (56709435818199/1250000000000 : ℝ)*(sp4) + (907347020925679/20000000000000 : ℝ)*(sp5) + (4536735447006809/100000000000000 : ℝ)*(sp6) + (513534720743429/25000000000000 : ℝ)*(sp7) + (513534720743429/25000000000000 : ℝ)*(f.failure) + (56709435818199/1250000000000 : ℝ)*(f.sum) + (80487991218589/23685000000000000000000000000 : ℝ)*base66 + (430935989899303593/789500000000000000000000000000000 : ℝ)*base67 + (398556428511303593/789500000000000000000000000000000 : ℝ)*base69 + (3160111171478303593/789500000000000000000000000000000 : ℝ)*base71 + (38789569541261/23685000000000000000000000000 : ℝ)*base73 + (13158312306524196407/789500000000000000000000000000000 : ℝ)*base76 + (469354259149803593/789500000000000000000000000000000 : ℝ)*base77 + (3750118074187196407/789500000000000000000000000000000 : ℝ)*base80 + (4878506922673/11842500000000000000000000000 : ℝ)*base81 + (20276119/2500000000000000000000 : ℝ)*base89 + (20276119/2500000000000000000000 : ℝ)*base91 + (20276119/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1475_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10751/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10763/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1475_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1475_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3231/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (507/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10763/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1475_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1475_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1475_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3231/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (507/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10763/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1475_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

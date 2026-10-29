-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1429_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:53:40.869994+00:00
-- url     : https://prove2.me/submissions/fe39930e-c14b-45f3-99bb-a45454b7fc18

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
theorem support_rectangle_w1429_s3_0 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-985036973/5000000000 : ℝ)*x 0 + (5417275577/10000000000 : ℝ)*x 1 + (5238545883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (985036973/5000000000 : ℝ)^4389 ≤ (2403350774049/20000000000000 : ℝ)^3365 := by
    have hnat : (985036973 : ℕ)^4389*20000000000000^3365 ≤ 2403350774049^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985036973 5000000000 2403350774049 20000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417275577/10000000000 : ℝ)^4389 ≤ (44953970096869/100000000000000 : ℝ)^3365 := by
    have hnat : (5417275577 : ℕ)^4389*100000000000000^3365 ≤ 44953970096869^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417275577 10000000000 44953970096869 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238545883/10000000000 : ℝ)^4389 ≤ (10757319003679/25000000000000 : ℝ)^3365 := by
    have hnat : (5238545883 : ℕ)^4389*25000000000000^3365 ≤ 10757319003679^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238545883 10000000000 10757319003679 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-985036973/5000000000 : ℝ), (5417275577/10000000000 : ℝ), (5238545883/10000000000 : ℝ)] ![(2403350774049/20000000000000 : ℝ), (44953970096869/100000000000000 : ℝ), (10757319003679/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-985036973/5000000000 : ℝ)|^4389 ≤ (2403350774049/20000000000000 : ℝ)^3365
        have hw : |(-985036973/5000000000 : ℝ)|=(985036973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417275577/10000000000 : ℝ)|^4389 ≤ (44953970096869/100000000000000 : ℝ)^3365
        have hw : |(5417275577/10000000000 : ℝ)|=(5417275577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238545883/10000000000 : ℝ)|^4389 ≤ (10757319003679/25000000000000 : ℝ)^3365
        have hw : |(5238545883/10000000000 : ℝ)|=(5238545883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s3_1 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668708199/1250000000 : ℝ)*x 0 + (-515310893/2500000000 : ℝ)*x 1 + (2619272937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668708199/1250000000 : ℝ)^4389 ≤ (11055896805679/25000000000000 : ℝ)^3365 := by
    have hnat : (668708199 : ℕ)^4389*25000000000000^3365 ≤ 11055896805679^3365*1250000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668708199 1250000000 11055896805679 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515310893/2500000000 : ℝ)^4389 ≤ (6373568420313/50000000000000 : ℝ)^3365 := by
    have hnat : (515310893 : ℕ)^4389*50000000000000^3365 ≤ 6373568420313^3365*2500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515310893 2500000000 6373568420313 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619272937/5000000000 : ℝ)^4389 ≤ (43029275918293/100000000000000 : ℝ)^3365 := by
    have hnat : (2619272937 : ℕ)^4389*100000000000000^3365 ≤ 43029275918293^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619272937 5000000000 43029275918293 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668708199/1250000000 : ℝ), (-515310893/2500000000 : ℝ), (2619272937/5000000000 : ℝ)] ![(11055896805679/25000000000000 : ℝ), (6373568420313/50000000000000 : ℝ), (43029275918293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668708199/1250000000 : ℝ)|^4389 ≤ (11055896805679/25000000000000 : ℝ)^3365
        have hw : |(668708199/1250000000 : ℝ)|=(668708199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-515310893/2500000000 : ℝ)|^4389 ≤ (6373568420313/50000000000000 : ℝ)^3365
        have hw : |(-515310893/2500000000 : ℝ)|=(515310893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619272937/5000000000 : ℝ)|^4389 ≤ (43029275918293/100000000000000 : ℝ)^3365
        have hw : |(2619272937/5000000000 : ℝ)|=(2619272937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s3_2 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349665629/10000000000 : ℝ)*x 0 + (327409113/625000000 : ℝ)*x 1 + (-206124361/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349665629/10000000000 : ℝ)^4389 ≤ (44223587621657/100000000000000 : ℝ)^3365 := by
    have hnat : (5349665629 : ℕ)^4389*100000000000000^3365 ≤ 44223587621657^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349665629 10000000000 44223587621657 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327409113/625000000 : ℝ)^4389 ≤ (43029275211199/100000000000000 : ℝ)^3365 := by
    have hnat : (327409113 : ℕ)^4389*100000000000000^3365 ≤ 43029275211199^3365*625000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327409113 625000000 43029275211199 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206124361/1000000000 : ℝ)^4389 ≤ (6373568573569/50000000000000 : ℝ)^3365 := by
    have hnat : (206124361 : ℕ)^4389*50000000000000^3365 ≤ 6373568573569^3365*1000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206124361 1000000000 6373568573569 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349665629/10000000000 : ℝ), (327409113/625000000 : ℝ), (-206124361/1000000000 : ℝ)] ![(44223587621657/100000000000000 : ℝ), (43029275211199/100000000000000 : ℝ), (6373568573569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349665629/10000000000 : ℝ)|^4389 ≤ (44223587621657/100000000000000 : ℝ)^3365
        have hw : |(5349665629/10000000000 : ℝ)|=(5349665629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327409113/625000000 : ℝ)|^4389 ≤ (43029275211199/100000000000000 : ℝ)^3365
        have hw : |(327409113/625000000 : ℝ)|=(327409113/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-206124361/1000000000 : ℝ)|^4389 ≤ (6373568573569/50000000000000 : ℝ)^3365
        have hw : |(-206124361/1000000000 : ℝ)|=(206124361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s3_3 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4303727901/10000000000 : ℝ)*x 0 + (822861259/2000000000 : ℝ)*x 1 + (281309877/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4303727901/10000000000 : ℝ)^4389 ≤ (33298177287019/100000000000000 : ℝ)^3365 := by
    have hnat : (4303727901 : ℕ)^4389*100000000000000^3365 ≤ 33298177287019^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303727901 10000000000 33298177287019 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (822861259/2000000000 : ℝ)^4389 ≤ (31399561689439/100000000000000 : ℝ)^3365 := by
    have hnat : (822861259 : ℕ)^4389*100000000000000^3365 ≤ 31399561689439^3365*2000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      822861259 2000000000 31399561689439 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281309877/625000000 : ℝ)^4389 ≤ (35302260998987/100000000000000 : ℝ)^3365 := by
    have hnat : (281309877 : ℕ)^4389*100000000000000^3365 ≤ 35302260998987^3365*625000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281309877 625000000 35302260998987 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4303727901/10000000000 : ℝ), (822861259/2000000000 : ℝ), (281309877/625000000 : ℝ)] ![(33298177287019/100000000000000 : ℝ), (31399561689439/100000000000000 : ℝ), (35302260998987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4303727901/10000000000 : ℝ)|^4389 ≤ (33298177287019/100000000000000 : ℝ)^3365
        have hw : |(4303727901/10000000000 : ℝ)|=(4303727901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(822861259/2000000000 : ℝ)|^4389 ≤ (31399561689439/100000000000000 : ℝ)^3365
        have hw : |(822861259/2000000000 : ℝ)|=(822861259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(281309877/625000000 : ℝ)|^4389 ≤ (35302260998987/100000000000000 : ℝ)^3365
        have hw : |(281309877/625000000 : ℝ)|=(281309877/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s3_4 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-985044471/5000000000 : ℝ)*x 0 + (2619629867/5000000000 : ℝ)*x 1 + (216662317/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (985044471/5000000000 : ℝ)^4389 ≤ (3004218293979/25000000000000 : ℝ)^3365 := by
    have hnat : (985044471 : ℕ)^4389*25000000000000^3365 ≤ 3004218293979^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985044471 5000000000 3004218293979 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619629867/5000000000 : ℝ)^4389 ≤ (43036924058677/100000000000000 : ℝ)^3365 := by
    have hnat : (2619629867 : ℕ)^4389*100000000000000^3365 ≤ 43036924058677^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619629867 5000000000 43036924058677 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216662317/400000000 : ℝ)^4389 ≤ (44946202748549/100000000000000 : ℝ)^3365 := by
    have hnat : (216662317 : ℕ)^4389*100000000000000^3365 ≤ 44946202748549^3365*400000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216662317 400000000 44946202748549 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-985044471/5000000000 : ℝ), (2619629867/5000000000 : ℝ), (216662317/400000000 : ℝ)] ![(3004218293979/25000000000000 : ℝ), (43036924058677/100000000000000 : ℝ), (44946202748549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-985044471/5000000000 : ℝ)|^4389 ≤ (3004218293979/25000000000000 : ℝ)^3365
        have hw : |(-985044471/5000000000 : ℝ)|=(985044471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2619629867/5000000000 : ℝ)|^4389 ≤ (43036924058677/100000000000000 : ℝ)^3365
        have hw : |(2619629867/5000000000 : ℝ)|=(2619629867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216662317/400000000 : ℝ)|^4389 ≤ (44946202748549/100000000000000 : ℝ)^3365
        have hw : |(216662317/400000000 : ℝ)|=(216662317/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s3_5 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651600699/5000000000 : ℝ)*x 0 + (-188323161/1000000000 : ℝ)*x 1 + (84633717/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651600699/5000000000 : ℝ)^4389 ≤ (1366351995769/3125000000000 : ℝ)^3365 := by
    have hnat : (2651600699 : ℕ)^4389*3125000000000^3365 ≤ 1366351995769^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651600699 5000000000 1366351995769 3125000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (188323161/1000000000 : ℝ)^4389 ≤ (11330533772227/100000000000000 : ℝ)^3365 := by
    have hnat : (188323161 : ℕ)^4389*100000000000000^3365 ≤ 11330533772227^3365*1000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188323161 1000000000 11330533772227 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84633717/156250000 : ℝ)^4389 ≤ (702284411689/1562500000000 : ℝ)^3365 := by
    have hnat : (84633717 : ℕ)^4389*1562500000000^3365 ≤ 702284411689^3365*156250000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84633717 156250000 702284411689 1562500000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651600699/5000000000 : ℝ), (-188323161/1000000000 : ℝ), (84633717/156250000 : ℝ)] ![(1366351995769/3125000000000 : ℝ), (11330533772227/100000000000000 : ℝ), (702284411689/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651600699/5000000000 : ℝ)|^4389 ≤ (1366351995769/3125000000000 : ℝ)^3365
        have hw : |(2651600699/5000000000 : ℝ)|=(2651600699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-188323161/1000000000 : ℝ)|^4389 ≤ (11330533772227/100000000000000 : ℝ)^3365
        have hw : |(-188323161/1000000000 : ℝ)|=(188323161/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84633717/156250000 : ℝ)|^4389 ≤ (702284411689/1562500000000 : ℝ)^3365
        have hw : |(84633717/156250000 : ℝ)|=(84633717/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s3_6 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132580027/250000000 : ℝ)*x 0 + (541655823/1000000000 : ℝ)*x 1 + (-941615787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132580027/250000000 : ℝ)^4389 ≤ (21861630222477/50000000000000 : ℝ)^3365 := by
    have hnat : (132580027 : ℕ)^4389*50000000000000^3365 ≤ 21861630222477^3365*250000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132580027 250000000 21861630222477 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541655823/1000000000 : ℝ)^4389 ≤ (44946206049583/100000000000000 : ℝ)^3365 := by
    have hnat : (541655823 : ℕ)^4389*100000000000000^3365 ≤ 44946206049583^3365*1000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541655823 1000000000 44946206049583 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (941615787/5000000000 : ℝ)^4389 ≤ (283263337243/2500000000000 : ℝ)^3365 := by
    have hnat : (941615787 : ℕ)^4389*2500000000000^3365 ≤ 283263337243^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941615787 5000000000 283263337243 2500000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132580027/250000000 : ℝ), (541655823/1000000000 : ℝ), (-941615787/5000000000 : ℝ)] ![(21861630222477/50000000000000 : ℝ), (44946206049583/100000000000000 : ℝ), (283263337243/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132580027/250000000 : ℝ)|^4389 ≤ (21861630222477/50000000000000 : ℝ)^3365
        have hw : |(132580027/250000000 : ℝ)|=(132580027/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541655823/1000000000 : ℝ)|^4389 ≤ (44946206049583/100000000000000 : ℝ)^3365
        have hw : |(541655823/1000000000 : ℝ)|=(541655823/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-941615787/5000000000 : ℝ)|^4389 ≤ (283263337243/2500000000000 : ℝ)^3365
        have hw : |(-941615787/5000000000 : ℝ)|=(941615787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s3_7 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4303760793/10000000000 : ℝ)*x 0 + (2249707223/5000000000 : ℝ)*x 1 + (2057929569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4303760793/10000000000 : ℝ)^4389 ≤ (16649254608681/50000000000000 : ℝ)^3365 := by
    have hnat : (4303760793 : ℕ)^4389*50000000000000^3365 ≤ 16649254608681^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303760793 10000000000 16649254608681 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249707223/5000000000 : ℝ)^4389 ≤ (7057294169933/20000000000000 : ℝ)^3365 := by
    have hnat : (2249707223 : ℕ)^4389*20000000000000^3365 ≤ 7057294169933^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249707223 5000000000 7057294169933 20000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2057929569/5000000000 : ℝ)^4389 ≤ (31415019926523/100000000000000 : ℝ)^3365 := by
    have hnat : (2057929569 : ℕ)^4389*100000000000000^3365 ≤ 31415019926523^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057929569 5000000000 31415019926523 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4303760793/10000000000 : ℝ), (2249707223/5000000000 : ℝ), (2057929569/5000000000 : ℝ)] ![(16649254608681/50000000000000 : ℝ), (7057294169933/20000000000000 : ℝ), (31415019926523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4303760793/10000000000 : ℝ)|^4389 ≤ (16649254608681/50000000000000 : ℝ)^3365
        have hw : |(4303760793/10000000000 : ℝ)|=(4303760793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2249707223/5000000000 : ℝ)|^4389 ≤ (7057294169933/20000000000000 : ℝ)^3365
        have hw : |(2249707223/5000000000 : ℝ)|=(2249707223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2057929569/5000000000 : ℝ)|^4389 ≤ (31415019926523/100000000000000 : ℝ)^3365
        have hw : |(2057929569/5000000000 : ℝ)|=(2057929569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1429_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15799/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (324/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11161/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7473/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15799/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (324/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15799/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (324/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15799/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (324/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15799/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (324/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15799/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (324/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15799/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (324/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (324/3125 : ℝ) ^ (1097/256 : ℝ) ≤ (6054791996399731/100000000000000000000 : ℝ) := by
    have hpowers : (324/3125 : ℝ)^1097 ≤ (6054791996399731/100000000000000000000 : ℝ)^256 := by
      have hnat : (324 : ℕ)^1097*100000000000000000000^256 ≤ 6054791996399731^256*3125^1097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        324 3125 6054791996399731 100000000000000000000 1097 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (324/3125 : ℝ)) (X := (6054791996399731/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hpowhi : (15799/100000 : ℝ) ^ (1097/256 : ℝ) ≤ (36813119277900781/100000000000000000000 : ℝ) := by
    have hpowers : (15799/100000 : ℝ)^1097 ≤ (36813119277900781/100000000000000000000 : ℝ)^256 := by
      have hnat : (15799 : ℕ)^1097*100000000000000000000^256 ≤ 36813119277900781^256*100000^1097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15799 100000 36813119277900781 100000000000000000000 1097 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15799/100000 : ℝ)) (X := (36813119277900781/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006054791996399731/50000000000000000000 : ℝ) ≤ (10000282580639327/10000000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (50006054791996399731/50000000000000000000 : ℝ)^256 ≤ (10000282580639327/10000000000000000 : ℝ)^1097 := by
      have hnat : (50006054791996399731 : ℕ)^256*10000000000000000^1097 ≤ 10000282580639327^1097*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006054791996399731 50000000000000000000 10000282580639327 10000000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000282580639327/10000000000000000 : ℝ)) (X := (50006054791996399731/50000000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126339622227321891/3125000000000000000 : ℝ) ≤ (10001000217179391/10000000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (3126339622227321891/3125000000000000000 : ℝ)^256 ≤ (10001000217179391/10000000000000000 : ℝ)^1097 := by
      have hnat : (3126339622227321891 : ℕ)^256*10000000000000000^1097 ≤ 10001000217179391^1097*3125000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126339622227321891 3125000000000000000 10001000217179391 10000000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001000217179391/10000000000000000 : ℝ)) (X := (3126339622227321891/3125000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036813119277900781/50000000000000000000 : ℝ) ≤ (2000343570743891/2000000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (50036813119277900781/50000000000000000000 : ℝ)^256 ≤ (2000343570743891/2000000000000000 : ℝ)^1097 := by
      have hnat : (50036813119277900781 : ℕ)^256*2000000000000000^1097 ≤ 2000343570743891^1097*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036813119277900781 50000000000000000000 2000343570743891 2000000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000343570743891/2000000000000000 : ℝ)) (X := (50036813119277900781/50000000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6054791996399731/100000000000000000000 : ℝ) ≤ ((54296653784157417833/54310000000000000000 : ℝ)+2*(22426141877/16971875000000 : ℝ)*(324/3125 : ℝ))^(1097/256 : ℝ) := by
    rw [show (54296653784157417833/54310000000000000000 : ℝ)+2*(22426141877/16971875000000 : ℝ)*(324/3125 : ℝ)=(10000282580639327/10000000000000000 : ℝ) by norm_num, show 1+2*(6054791996399731/100000000000000000000 : ℝ)=(50006054791996399731/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36813119277900781/100000000000000000000 : ℝ)+(6054791996399731/100000000000000000000 : ℝ) ≤ ((54296653784157417833/54310000000000000000 : ℝ)+(22426141877/16971875000000 : ℝ)*((15799/100000 : ℝ)+(324/3125 : ℝ)))^(1097/256 : ℝ) := by
    rw [show (54296653784157417833/54310000000000000000 : ℝ)+(22426141877/16971875000000 : ℝ)*((15799/100000 : ℝ)+(324/3125 : ℝ))=(10001000217179391/10000000000000000 : ℝ) by norm_num, show 1+(36813119277900781/100000000000000000000 : ℝ)+(6054791996399731/100000000000000000000 : ℝ)=(3126339622227321891/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36813119277900781/100000000000000000000 : ℝ) ≤ ((54296653784157417833/54310000000000000000 : ℝ)+2*(22426141877/16971875000000 : ℝ)*(15799/100000 : ℝ))^(1097/256 : ℝ) := by
    rw [show (54296653784157417833/54310000000000000000 : ℝ)+2*(22426141877/16971875000000 : ℝ)*(15799/100000 : ℝ)=(2000343570743891/2000000000000000 : ℝ) by norm_num, show 1+2*(36813119277900781/100000000000000000000 : ℝ)=(50036813119277900781/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (54296653784157417833/54310000000000000000 : ℝ)*(X 1 0+X 2 0)+(22426141877/16971875000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (324/3125 : ℝ)) (hi := (15799/100000 : ℝ)) (c := (54296653784157417833/54310000000000000000 : ℝ)) (alpha := (22426141877/16971875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (54296653784157417833/54310000000000000000 : ℝ)*(X 0 1+X 2 1)+(22426141877/16971875000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (324/3125 : ℝ)) (hi := (15799/100000 : ℝ)) (c := (54296653784157417833/54310000000000000000 : ℝ)) (alpha := (22426141877/16971875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (54296653784157417833/54310000000000000000 : ℝ)*(X 0 2+X 1 2)+(22426141877/16971875000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (324/3125 : ℝ)) (hi := (15799/100000 : ℝ)) (c := (54296653784157417833/54310000000000000000 : ℝ)) (alpha := (22426141877/16971875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-985036973/5000000000 : ℝ)*X 0 0+(5417275577/10000000000 : ℝ)*X 0 1+(5238545883/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668708199/1250000000 : ℝ)*X 1 0+(-515310893/2500000000 : ℝ)*X 1 1+(2619272937/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349665629/10000000000 : ℝ)*X 2 0+(327409113/625000000 : ℝ)*X 2 1+(-206124361/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4303727901/10000000000 : ℝ)*X 0 0+(822861259/2000000000 : ℝ)*X 0 1+(281309877/625000000 : ℝ)*X 0 2+(4303727901/10000000000 : ℝ)*X 1 0+(822861259/2000000000 : ℝ)*X 1 1+(281309877/625000000 : ℝ)*X 1 2+(4303727901/10000000000 : ℝ)*X 2 0+(822861259/2000000000 : ℝ)*X 2 1+(281309877/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-985044471/5000000000 : ℝ)*X 0 0+(2619629867/5000000000 : ℝ)*X 0 1+(216662317/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651600699/5000000000 : ℝ)*X 1 0+(-188323161/1000000000 : ℝ)*X 1 1+(84633717/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132580027/250000000 : ℝ)*X 2 0+(541655823/1000000000 : ℝ)*X 2 1+(-941615787/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4303760793/10000000000 : ℝ)*X 0 0+(2249707223/5000000000 : ℝ)*X 0 1+(2057929569/5000000000 : ℝ)*X 0 2+(4303760793/10000000000 : ℝ)*X 1 0+(2249707223/5000000000 : ℝ)*X 1 1+(2057929569/5000000000 : ℝ)*X 1 2+(4303760793/10000000000 : ℝ)*X 2 0+(2249707223/5000000000 : ℝ)*X 2 1+(2057929569/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15720766606939092772951612341/1357750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (127768493/6250000000000 : ℝ)*(base19) + (1031243353/50000000000000 : ℝ)*(base23) + (12499983/4000000000000 : ℝ)*(upper3) + (5485221/50000000000000 : ℝ)*(upper4) + (130095157/50000000000000 : ℝ)*(upper5) + (2045363831551947/50000000000000 : ℝ)*(major0) + (2045363831551947/50000000000000 : ℝ)*(major1) + (2045363831551947/50000000000000 : ℝ)*(major2) + (5595079084054381/100000000000000 : ℝ)*(sp0) + (2797556941299643/50000000000000 : ℝ)*(sp1) + (5595113864408469/100000000000000 : ℝ)*(sp2) + (2586322368536859/100000000000000 : ℝ)*(sp3) + (18421420397/50000000000000 : ℝ)*(sp4) + (1664482431/10000000000000 : ℝ)*(sp7) + (2586339013361169/100000000000000 : ℝ)*(f.failure) + (223804637075807/4000000000000 : ℝ)*(f.sum) + (120737118074891/27155000000000000000000000000 : ℝ)*base65 + (31493937603265470851/2715500000000000000000000000000000 : ℝ)*base67 + (3598282689098970851/2715500000000000000000000000000000 : ℝ)*base69 + (42953899384718970851/2715500000000000000000000000000000 : ℝ)*base71 + (29643045826901/27155000000000000000000000000 : ℝ)*base73 + (87015754096988470851/2715500000000000000000000000000000 : ℝ)*base75 + (28866307131739470851/2715500000000000000000000000000000 : ℝ)*base77 + (33743169094020970851/2715500000000000000000000000000000 : ℝ)*base79 + (34275981219687/13577500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (83820813/10000000000000000000000 : ℝ)*base90 + (83820813/10000000000000000000000 : ℝ)*base92 + (83820813/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (856581913471871133951973377/339437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (98571839/100000000000000 : ℝ)*(base8) + (140960977/50000000000000 : ℝ)*(base21) + (23065309/100000000000000 : ℝ)*(base29) + (3279773/10000000000000 : ℝ)*(upper2) + (128865670622287/3125000000000 : ℝ)*(major0) + (1030925370744623/25000000000000 : ℝ)*(major1) + (1030925370744623/25000000000000 : ℝ)*(major2) + (2253807/200000000000 : ℝ)*(sp1) + (2085905701/50000000000000 : ℝ)*(sp2) + (48280467/100000000000000 : ℝ)*(sp3) + (5640216262131329/100000000000000 : ℝ)*(sp4) + (5640215210734377/100000000000000 : ℝ)*(sp5) + (705026485488063/12500000000000 : ℝ)*(sp6) + (16294915455347/625000000000 : ℝ)*(sp7) + (1303593260567993/50000000000000 : ℝ)*(f.failure) + (5640216360703169/100000000000000 : ℝ)*(f.sum) + (293970975186907/27155000000000000000000000000 : ℝ)*base66 + (10811422484438988041/1357750000000000000000000000000000 : ℝ)*base68 + (2500291030888488041/1357750000000000000000000000000000 : ℝ)*base70 + (28421678965356899679/169718750000000000000000000000000 : ℝ)*base72 + (60347604272193/27155000000000000000000000000 : ℝ)*base74 + (6732757556226538041/1357750000000000000000000000000000 : ℝ)*base76 + (2804545418958975321/169718750000000000000000000000000 : ℝ)*base77 + (3491910057369288041/1357750000000000000000000000000000 : ℝ)*base80 + (19864344527877/6788750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (17/100000000000000 : ℝ)*base85 + (78503061/5000000000000000000000 : ℝ)*base90 + (28503061/5000000000000000000000 : ℝ)*base92 + (28503061/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1429_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15799/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (324/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11161/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7473/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1429_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1429_s4_0 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-123186039/625000000 : ℝ)*x 0 + (2704796161/5000000000 : ℝ)*x 1 + (1311408619/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (123186039/625000000 : ℝ)^4389 ≤ (1202393591789/10000000000000 : ℝ)^3365 := by
    have hnat : (123186039 : ℕ)^4389*10000000000000^3365 ≤ 1202393591789^3365*625000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123186039 625000000 1202393591789 10000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704796161/5000000000 : ℝ)^4389 ≤ (44870828354437/100000000000000 : ℝ)^3365 := by
    have hnat : (2704796161 : ℕ)^4389*100000000000000^3365 ≤ 44870828354437^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704796161 5000000000 44870828354437 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311408619/2500000000 : ℝ)^4389 ≤ (10776308927771/25000000000000 : ℝ)^3365 := by
    have hnat : (1311408619 : ℕ)^4389*25000000000000^3365 ≤ 10776308927771^3365*2500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311408619 2500000000 10776308927771 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-123186039/625000000 : ℝ), (2704796161/5000000000 : ℝ), (1311408619/2500000000 : ℝ)] ![(1202393591789/10000000000000 : ℝ), (44870828354437/100000000000000 : ℝ), (10776308927771/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-123186039/625000000 : ℝ)|^4389 ≤ (1202393591789/10000000000000 : ℝ)^3365
        have hw : |(-123186039/625000000 : ℝ)|=(123186039/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704796161/5000000000 : ℝ)|^4389 ≤ (44870828354437/100000000000000 : ℝ)^3365
        have hw : |(2704796161/5000000000 : ℝ)|=(2704796161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311408619/2500000000 : ℝ)|^4389 ≤ (10776308927771/25000000000000 : ℝ)^3365
        have hw : |(1311408619/2500000000 : ℝ)|=(1311408619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s4_1 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673840943/5000000000 : ℝ)*x 0 + (-256809323/1250000000 : ℝ)*x 1 + (2622817229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673840943/5000000000 : ℝ)^4389 ≤ (44202199692013/100000000000000 : ℝ)^3365 := by
    have hnat : (2673840943 : ℕ)^4389*100000000000000^3365 ≤ 44202199692013^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673840943 5000000000 44202199692013 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256809323/1250000000 : ℝ)^4389 ≤ (1586570597257/12500000000000 : ℝ)^3365 := by
    have hnat : (256809323 : ℕ)^4389*12500000000000^3365 ≤ 1586570597257^3365*1250000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256809323 1250000000 1586570597257 12500000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622817229/5000000000 : ℝ)^4389 ≤ (43105235518161/100000000000000 : ℝ)^3365 := by
    have hnat : (2622817229 : ℕ)^4389*100000000000000^3365 ≤ 43105235518161^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622817229 5000000000 43105235518161 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673840943/5000000000 : ℝ), (-256809323/1250000000 : ℝ), (2622817229/5000000000 : ℝ)] ![(44202199692013/100000000000000 : ℝ), (1586570597257/12500000000000 : ℝ), (43105235518161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673840943/5000000000 : ℝ)|^4389 ≤ (44202199692013/100000000000000 : ℝ)^3365
        have hw : |(2673840943/5000000000 : ℝ)|=(2673840943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-256809323/1250000000 : ℝ)|^4389 ≤ (1586570597257/12500000000000 : ℝ)^3365
        have hw : |(-256809323/1250000000 : ℝ)|=(256809323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622817229/5000000000 : ℝ)|^4389 ≤ (43105235518161/100000000000000 : ℝ)^3365
        have hw : |(2622817229/5000000000 : ℝ)|=(2622817229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s4_2 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347681899/10000000000 : ℝ)*x 0 + (131140861/250000000 : ℝ)*x 1 + (-205447459/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347681899/10000000000 : ℝ)^4389 ≤ (22101099916083/50000000000000 : ℝ)^3365 := by
    have hnat : (5347681899 : ℕ)^4389*50000000000000^3365 ≤ 22101099916083^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347681899 10000000000 22101099916083 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131140861/250000000 : ℝ)^4389 ≤ (21552617662619/50000000000000 : ℝ)^3365 := by
    have hnat : (131140861 : ℕ)^4389*50000000000000^3365 ≤ 21552617662619^3365*250000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131140861 250000000 21552617662619 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (205447459/1000000000 : ℝ)^4389 ≤ (3173141206601/25000000000000 : ℝ)^3365 := by
    have hnat : (205447459 : ℕ)^4389*25000000000000^3365 ≤ 3173141206601^3365*1000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205447459 1000000000 3173141206601 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347681899/10000000000 : ℝ), (131140861/250000000 : ℝ), (-205447459/1000000000 : ℝ)] ![(22101099916083/50000000000000 : ℝ), (21552617662619/50000000000000 : ℝ), (3173141206601/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347681899/10000000000 : ℝ)|^4389 ≤ (22101099916083/50000000000000 : ℝ)^3365
        have hw : |(5347681899/10000000000 : ℝ)|=(5347681899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131140861/250000000 : ℝ)|^4389 ≤ (21552617662619/50000000000000 : ℝ)^3365
        have hw : |(131140861/250000000 : ℝ)|=(131140861/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-205447459/1000000000 : ℝ)|^4389 ≤ (3173141206601/25000000000000 : ℝ)^3365
        have hw : |(-205447459/1000000000 : ℝ)|=(205447459/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s4_3 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (430427951/1000000000 : ℝ)*x 0 + (826043569/2000000000 : ℝ)*x 1 + (4484913543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430427951/1000000000 : ℝ)^4389 ≤ (33303743963479/100000000000000 : ℝ)^3365 := by
    have hnat : (430427951 : ℕ)^4389*100000000000000^3365 ≤ 33303743963479^3365*1000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430427951 1000000000 33303743963479 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (826043569/2000000000 : ℝ)^4389 ≤ (631160839297/2000000000000 : ℝ)^3365 := by
    have hnat : (826043569 : ℕ)^4389*2000000000000^3365 ≤ 631160839297^3365*2000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826043569 2000000000 631160839297 2000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4484913543/10000000000 : ℝ)^4389 ≤ (7027642810781/20000000000000 : ℝ)^3365 := by
    have hnat : (4484913543 : ℕ)^4389*20000000000000^3365 ≤ 7027642810781^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484913543 10000000000 7027642810781 20000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(430427951/1000000000 : ℝ), (826043569/2000000000 : ℝ), (4484913543/10000000000 : ℝ)] ![(33303743963479/100000000000000 : ℝ), (631160839297/2000000000000 : ℝ), (7027642810781/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(430427951/1000000000 : ℝ)|^4389 ≤ (33303743963479/100000000000000 : ℝ)^3365
        have hw : |(430427951/1000000000 : ℝ)|=(430427951/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(826043569/2000000000 : ℝ)|^4389 ≤ (631160839297/2000000000000 : ℝ)^3365
        have hw : |(826043569/2000000000 : ℝ)|=(826043569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4484913543/10000000000 : ℝ)|^4389 ≤ (7027642810781/20000000000000 : ℝ)^3365
        have hw : |(4484913543/10000000000 : ℝ)|=(4484913543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s4_4 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-246373563/1250000000 : ℝ)*x 0 + (655779433/1250000000 : ℝ)*x 1 + (2704494089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (246373563/1250000000 : ℝ)^4389 ≤ (12024030446339/100000000000000 : ℝ)^3365 := by
    have hnat : (246373563 : ℕ)^4389*100000000000000^3365 ≤ 12024030446339^3365*1250000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246373563 1250000000 12024030446339 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655779433/1250000000 : ℝ)^4389 ≤ (8622335438869/20000000000000 : ℝ)^3365 := by
    have hnat : (655779433 : ℕ)^4389*20000000000000^3365 ≤ 8622335438869^3365*1250000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655779433 1250000000 8622335438869 20000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704494089/5000000000 : ℝ)^4389 ≤ (224321461689/500000000000 : ℝ)^3365 := by
    have hnat : (2704494089 : ℕ)^4389*500000000000^3365 ≤ 224321461689^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704494089 5000000000 224321461689 500000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-246373563/1250000000 : ℝ), (655779433/1250000000 : ℝ), (2704494089/5000000000 : ℝ)] ![(12024030446339/100000000000000 : ℝ), (8622335438869/20000000000000 : ℝ), (224321461689/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-246373563/1250000000 : ℝ)|^4389 ≤ (12024030446339/100000000000000 : ℝ)^3365
        have hw : |(-246373563/1250000000 : ℝ)|=(246373563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655779433/1250000000 : ℝ)|^4389 ≤ (8622335438869/20000000000000 : ℝ)^3365
        have hw : |(655779433/1250000000 : ℝ)|=(655779433/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704494089/5000000000 : ℝ)|^4389 ≤ (224321461689/500000000000 : ℝ)^3365
        have hw : |(2704494089/5000000000 : ℝ)|=(2704494089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s4_5 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305057441/10000000000 : ℝ)*x 0 + (-945560421/5000000000 : ℝ)*x 1 + (2704494097/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305057441/10000000000 : ℝ)^4389 ≤ (43743224121371/100000000000000 : ℝ)^3365 := by
    have hnat : (5305057441 : ℕ)^4389*100000000000000^3365 ≤ 43743224121371^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305057441 10000000000 43743224121371 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (945560421/5000000000 : ℝ)^4389 ≤ (2278496669683/20000000000000 : ℝ)^3365 := by
    have hnat : (945560421 : ℕ)^4389*20000000000000^3365 ≤ 2278496669683^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945560421 5000000000 2278496669683 20000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704494097/5000000000 : ℝ)^4389 ≤ (2804018281931/6250000000000 : ℝ)^3365 := by
    have hnat : (2704494097 : ℕ)^4389*6250000000000^3365 ≤ 2804018281931^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704494097 5000000000 2804018281931 6250000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305057441/10000000000 : ℝ), (-945560421/5000000000 : ℝ), (2704494097/5000000000 : ℝ)] ![(43743224121371/100000000000000 : ℝ), (2278496669683/20000000000000 : ℝ), (2804018281931/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305057441/10000000000 : ℝ)|^4389 ≤ (43743224121371/100000000000000 : ℝ)^3365
        have hw : |(5305057441/10000000000 : ℝ)|=(5305057441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-945560421/5000000000 : ℝ)|^4389 ≤ (2278496669683/20000000000000 : ℝ)^3365
        have hw : |(-945560421/5000000000 : ℝ)|=(945560421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704494097/5000000000 : ℝ)|^4389 ≤ (2804018281931/6250000000000 : ℝ)^3365
        have hw : |(2704494097/5000000000 : ℝ)|=(2704494097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s4_6 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305057427/10000000000 : ℝ)*x 0 + (1352247049/2500000000 : ℝ)*x 1 + (-94556043/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305057427/10000000000 : ℝ)^4389 ≤ (8748644794161/20000000000000 : ℝ)^3365 := by
    have hnat : (5305057427 : ℕ)^4389*20000000000000^3365 ≤ 8748644794161^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305057427 10000000000 8748644794161 20000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352247049/2500000000 : ℝ)^4389 ≤ (44864292532533/100000000000000 : ℝ)^3365 := by
    have hnat : (1352247049 : ℕ)^4389*100000000000000^3365 ≤ 44864292532533^3365*2500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352247049 2500000000 44864292532533 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94556043/500000000 : ℝ)^4389 ≤ (11392483489849/100000000000000 : ℝ)^3365 := by
    have hnat : (94556043 : ℕ)^4389*100000000000000^3365 ≤ 11392483489849^3365*500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94556043 500000000 11392483489849 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305057427/10000000000 : ℝ), (1352247049/2500000000 : ℝ), (-94556043/500000000 : ℝ)] ![(8748644794161/20000000000000 : ℝ), (44864292532533/100000000000000 : ℝ), (11392483489849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305057427/10000000000 : ℝ)|^4389 ≤ (8748644794161/20000000000000 : ℝ)^3365
        have hw : |(5305057427/10000000000 : ℝ)|=(5305057427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352247049/2500000000 : ℝ)|^4389 ≤ (44864292532533/100000000000000 : ℝ)^3365
        have hw : |(1352247049/2500000000 : ℝ)|=(1352247049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94556043/500000000 : ℝ)|^4389 ≤ (11392483489849/100000000000000 : ℝ)^3365
        have hw : |(-94556043/500000000 : ℝ)|=(94556043/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s4_7 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076076301/2500000000 : ℝ)*x 0 + (4483613483/10000000000 : ℝ)*x 1 + (1032881193/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076076301/2500000000 : ℝ)^4389 ≤ (33304003265093/100000000000000 : ℝ)^3365 := by
    have hnat : (1076076301 : ℕ)^4389*100000000000000^3365 ≤ 33304003265093^3365*2500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076076301 2500000000 33304003265093 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4483613483/10000000000 : ℝ)^4389 ≤ (35124929396449/100000000000000 : ℝ)^3365 := by
    have hnat : (4483613483 : ℕ)^4389*100000000000000^3365 ≤ 35124929396449^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483613483 10000000000 35124929396449 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032881193/2500000000 : ℝ)^4389 ≤ (31571067328011/100000000000000 : ℝ)^3365 := by
    have hnat : (1032881193 : ℕ)^4389*100000000000000^3365 ≤ 31571067328011^3365*2500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032881193 2500000000 31571067328011 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076076301/2500000000 : ℝ), (4483613483/10000000000 : ℝ), (1032881193/2500000000 : ℝ)] ![(33304003265093/100000000000000 : ℝ), (35124929396449/100000000000000 : ℝ), (31571067328011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076076301/2500000000 : ℝ)|^4389 ≤ (33304003265093/100000000000000 : ℝ)^3365
        have hw : |(1076076301/2500000000 : ℝ)|=(1076076301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4483613483/10000000000 : ℝ)|^4389 ≤ (35124929396449/100000000000000 : ℝ)^3365
        have hw : |(4483613483/10000000000 : ℝ)|=(4483613483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032881193/2500000000 : ℝ)|^4389 ≤ (31571067328011/100000000000000 : ℝ)^3365
        have hw : |(1032881193/2500000000 : ℝ)|=(1032881193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1429_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7473/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11161/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11313/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7393/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7473/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11161/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7473/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11161/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7473/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11161/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7473/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11161/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7473/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11161/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7473/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11161/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11161/100000 : ℝ) ^ (1097/256 : ℝ) ≤ (4151729274162209/50000000000000000000 : ℝ) := by
    have hpowers : (11161/100000 : ℝ)^1097 ≤ (4151729274162209/50000000000000000000 : ℝ)^256 := by
      have hnat : (11161 : ℕ)^1097*50000000000000000000^256 ≤ 4151729274162209^256*100000^1097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11161 100000 4151729274162209 50000000000000000000 1097 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11161/100000 : ℝ)) (X := (4151729274162209/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7473/50000 : ℝ) ^ (1097/256 : ℝ) ≤ (29020878162689903/100000000000000000000 : ℝ) := by
    have hpowers : (7473/50000 : ℝ)^1097 ≤ (29020878162689903/100000000000000000000 : ℝ)^256 := by
      have hnat : (7473 : ℕ)^1097*100000000000000000000^256 ≤ 29020878162689903^256*50000^1097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7473 50000 29020878162689903 100000000000000000000 1097 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7473/50000 : ℝ)) (X := (29020878162689903/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004151729274162209/25000000000000000000 : ℝ) ≤ (10000387520526191/10000000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (25004151729274162209/25000000000000000000 : ℝ)^256 ≤ (10000387520526191/10000000000000000 : ℝ)^1097 := by
      have hnat : (25004151729274162209 : ℕ)^256*10000000000000000^1097 ≤ 10000387520526191^1097*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004151729274162209 25000000000000000000 10000387520526191 10000000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000387520526191/10000000000000000 : ℝ)) (X := (25004151729274162209/25000000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037324336711014321/100000000000000000000 : ℝ) ≤ (10000870890013777/10000000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (100037324336711014321/100000000000000000000 : ℝ)^256 ≤ (10000870890013777/10000000000000000 : ℝ)^1097 := by
      have hnat : (100037324336711014321 : ℕ)^256*10000000000000000^1097 ≤ 10000870890013777^1097*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037324336711014321 100000000000000000000 10000870890013777 10000000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000870890013777/10000000000000000 : ℝ)) (X := (100037324336711014321/100000000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029020878162689903/50000000000000000000 : ℝ) ≤ (10001354259501363/10000000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (50029020878162689903/50000000000000000000 : ℝ)^256 ≤ (10001354259501363/10000000000000000 : ℝ)^1097 := by
      have hnat : (50029020878162689903 : ℕ)^256*10000000000000000^1097 ≤ 10001354259501363^1097*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029020878162689903 50000000000000000000 10001354259501363 10000000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001354259501363/10000000000000000 : ℝ)) (X := (50029020878162689903/50000000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4151729274162209/50000000000000000000 : ℝ) ≤ ((37840676991489738243/37850000000000000000 : ℝ)+2*(241684743793/189250000000000 : ℝ)*(11161/100000 : ℝ))^(1097/256 : ℝ) := by
    rw [show (37840676991489738243/37850000000000000000 : ℝ)+2*(241684743793/189250000000000 : ℝ)*(11161/100000 : ℝ)=(10000387520526191/10000000000000000 : ℝ) by norm_num, show 1+2*(4151729274162209/50000000000000000000 : ℝ)=(25004151729274162209/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29020878162689903/100000000000000000000 : ℝ)+(4151729274162209/50000000000000000000 : ℝ) ≤ ((37840676991489738243/37850000000000000000 : ℝ)+(241684743793/189250000000000 : ℝ)*((7473/50000 : ℝ)+(11161/100000 : ℝ)))^(1097/256 : ℝ) := by
    rw [show (37840676991489738243/37850000000000000000 : ℝ)+(241684743793/189250000000000 : ℝ)*((7473/50000 : ℝ)+(11161/100000 : ℝ))=(10000870890013777/10000000000000000 : ℝ) by norm_num, show 1+(29020878162689903/100000000000000000000 : ℝ)+(4151729274162209/50000000000000000000 : ℝ)=(100037324336711014321/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29020878162689903/100000000000000000000 : ℝ) ≤ ((37840676991489738243/37850000000000000000 : ℝ)+2*(241684743793/189250000000000 : ℝ)*(7473/50000 : ℝ))^(1097/256 : ℝ) := by
    rw [show (37840676991489738243/37850000000000000000 : ℝ)+2*(241684743793/189250000000000 : ℝ)*(7473/50000 : ℝ)=(10001354259501363/10000000000000000 : ℝ) by norm_num, show 1+2*(29020878162689903/100000000000000000000 : ℝ)=(50029020878162689903/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37840676991489738243/37850000000000000000 : ℝ)*(X 1 0+X 2 0)+(241684743793/189250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (11161/100000 : ℝ)) (hi := (7473/50000 : ℝ)) (c := (37840676991489738243/37850000000000000000 : ℝ)) (alpha := (241684743793/189250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37840676991489738243/37850000000000000000 : ℝ)*(X 0 1+X 2 1)+(241684743793/189250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (11161/100000 : ℝ)) (hi := (7473/50000 : ℝ)) (c := (37840676991489738243/37850000000000000000 : ℝ)) (alpha := (241684743793/189250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37840676991489738243/37850000000000000000 : ℝ)*(X 0 2+X 1 2)+(241684743793/189250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (11161/100000 : ℝ)) (hi := (7473/50000 : ℝ)) (c := (37840676991489738243/37850000000000000000 : ℝ)) (alpha := (241684743793/189250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-123186039/625000000 : ℝ)*X 0 0+(2704796161/5000000000 : ℝ)*X 0 1+(1311408619/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673840943/5000000000 : ℝ)*X 1 0+(-256809323/1250000000 : ℝ)*X 1 1+(2622817229/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347681899/10000000000 : ℝ)*X 2 0+(131140861/250000000 : ℝ)*X 2 1+(-205447459/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((430427951/1000000000 : ℝ)*X 0 0+(826043569/2000000000 : ℝ)*X 0 1+(4484913543/10000000000 : ℝ)*X 0 2+(430427951/1000000000 : ℝ)*X 1 0+(826043569/2000000000 : ℝ)*X 1 1+(4484913543/10000000000 : ℝ)*X 1 2+(430427951/1000000000 : ℝ)*X 2 0+(826043569/2000000000 : ℝ)*X 2 1+(4484913543/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-246373563/1250000000 : ℝ)*X 0 0+(655779433/1250000000 : ℝ)*X 0 1+(2704494089/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305057441/10000000000 : ℝ)*X 1 0+(-945560421/5000000000 : ℝ)*X 1 1+(2704494097/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305057427/10000000000 : ℝ)*X 2 0+(1352247049/2500000000 : ℝ)*X 2 1+(-94556043/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1076076301/2500000000 : ℝ)*X 0 0+(4483613483/10000000000 : ℝ)*X 0 1+(1032881193/2500000000 : ℝ)*X 0 2+(1076076301/2500000000 : ℝ)*X 1 0+(4483613483/10000000000 : ℝ)*X 1 1+(1032881193/2500000000 : ℝ)*X 1 2+(1076076301/2500000000 : ℝ)*X 2 0+(4483613483/10000000000 : ℝ)*X 2 1+(1032881193/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1956399963686202740582418669/378500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (496376447/50000000000000 : ℝ)*(base19) + (474661949/50000000000000 : ℝ)*(base23) + (6230673/20000000000000 : ℝ)*(lower2) + (132274779/100000000000000 : ℝ)*(upper3) + (42193137/50000000000000 : ℝ)*(upper5) + (891850742646139/20000000000000 : ℝ)*(major0) + (891850742646139/20000000000000 : ℝ)*(major1) + (891850742646139/20000000000000 : ℝ)*(major2) + (1219829928609243/20000000000000 : ℝ)*(sp0) + (6099168774583633/100000000000000 : ℝ)*(sp1) + (609916881801263/10000000000000 : ℝ)*(sp2) + (704831814048243/25000000000000 : ℝ)*(sp3) + (20124290313/100000000000000 : ℝ)*(sp4) + (511531887/5000000000000 : ℝ)*(sp7) + (2819337486830713/100000000000000 : ℝ)*(f.failure) + (6099169767336527/100000000000000 : ℝ)*(f.sum) + (9011377626787/1892500000000000000000000000 : ℝ)*base65 + (5060850144275993777/757000000000000000000000000000000 : ℝ)*base67 + (6152581702080006223/757000000000000000000000000000000 : ℝ)*base70 + (7943945737203993777/757000000000000000000000000000000 : ℝ)*base71 + (11317223623687/1892500000000000000000000000 : ℝ)*base73 + (11148352117899993777/757000000000000000000000000000000 : ℝ)*base75 + (3993758850479993777/757000000000000000000000000000000 : ℝ)*base77 + (3293065549390006223/757000000000000000000000000000000 : ℝ)*base80 + (5661500076147/1892500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (30963499/10000000000000000000000 : ℝ)*base89 + (30963499/10000000000000000000000 : ℝ)*base91 + (30963499/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (274757346071758929167942619/29570312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (795273797/50000000000000 : ℝ)*(base19) + (340469639/20000000000000 : ℝ)*(base23) + (204947477/100000000000000 : ℝ)*(upper3) + (2819789/5000000000000 : ℝ)*(lower4) + (167406753/100000000000000 : ℝ)*(upper5) + (140382526097661/3125000000000 : ℝ)*(major0) + (140382526097661/3125000000000 : ℝ)*(major1) + (140382526097661/3125000000000 : ℝ)*(major2) + (32757479119/100000000000000 : ℝ)*(sp1) + (35459446717/100000000000000 : ℝ)*(sp2) + (6144287955797231/100000000000000 : ℝ)*(sp4) + (3072126803885259/50000000000000 : ℝ)*(sp5) + (6144250794002319/100000000000000 : ℝ)*(sp6) + (1420096702365501/50000000000000 : ℝ)*(sp7) + (1420096702365501/50000000000000 : ℝ)*(f.failure) + (6144287955797231/100000000000000 : ℝ)*(f.sum) + (3180420771379/591406250000000000000000000 : ℝ)*base66 + (233726582661962123/118281250000000000000000000000000 : ℝ)*base67 + (680755026648037877/118281250000000000000000000000000 : ℝ)*base70 + (81882937245850377/118281250000000000000000000000000 : ℝ)*base72 + (13047118910311/9462500000000000000000000000 : ℝ)*base73 + (3439193462606162877/118281250000000000000000000000000 : ℝ)*base76 + (1132952116068975377/118281250000000000000000000000000 : ℝ)*base78 + (1592838696047412877/118281250000000000000000000000000 : ℝ)*base80 + (5485507739939/9462500000000000000000000000 : ℝ)*base82 + (41423223/5000000000000000000000 : ℝ)*base89 + (41423223/5000000000000000000000 : ℝ)*base91 + (41423223/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1429_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7473/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11161/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11313/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7393/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1429_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1429_s5_0 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-985554223/5000000000 : ℝ)*x 0 + (108168017/200000000 : ℝ)*x 1 + (262336961/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (985554223/5000000000 : ℝ)^4389 ≤ (12024984827363/100000000000000 : ℝ)^3365 := by
    have hnat : (985554223 : ℕ)^4389*100000000000000^3365 ≤ 12024984827363^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985554223 5000000000 12024984827363 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108168017/200000000 : ℝ)^4389 ≤ (2242896923019/5000000000000 : ℝ)^3365 := by
    have hnat : (108168017 : ℕ)^4389*5000000000000^3365 ≤ 2242896923019^3365*200000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108168017 200000000 2242896923019 5000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262336961/500000000 : ℝ)^4389 ≤ (21558538351421/50000000000000 : ℝ)^3365 := by
    have hnat : (262336961 : ℕ)^4389*50000000000000^3365 ≤ 21558538351421^3365*500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262336961 500000000 21558538351421 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-985554223/5000000000 : ℝ), (108168017/200000000 : ℝ), (262336961/500000000 : ℝ)] ![(12024984827363/100000000000000 : ℝ), (2242896923019/5000000000000 : ℝ), (21558538351421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-985554223/5000000000 : ℝ)|^4389 ≤ (12024984827363/100000000000000 : ℝ)^3365
        have hw : |(-985554223/5000000000 : ℝ)|=(985554223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108168017/200000000 : ℝ)|^4389 ≤ (2242896923019/5000000000000 : ℝ)^3365
        have hw : |(108168017/200000000 : ℝ)|=(108168017/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262336961/500000000 : ℝ)|^4389 ≤ (21558538351421/50000000000000 : ℝ)^3365
        have hw : |(262336961/500000000 : ℝ)|=(262336961/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s5_1 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336843667/2500000000 : ℝ)*x 0 + (-410683257/2000000000 : ℝ)*x 1 + (5246739037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336843667/2500000000 : ℝ)^4389 ≤ (11049721901339/25000000000000 : ℝ)^3365 := by
    have hnat : (1336843667 : ℕ)^4389*25000000000000^3365 ≤ 11049721901339^3365*2500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336843667 2500000000 11049721901339 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (410683257/2000000000 : ℝ)^4389 ≤ (6342018818283/50000000000000 : ℝ)^3365 := by
    have hnat : (410683257 : ℕ)^4389*50000000000000^3365 ≤ 6342018818283^3365*2000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410683257 2000000000 6342018818283 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246739037/10000000000 : ℝ)^4389 ≤ (2694817171333/6250000000000 : ℝ)^3365 := by
    have hnat : (5246739037 : ℕ)^4389*6250000000000^3365 ≤ 2694817171333^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246739037 10000000000 2694817171333 6250000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336843667/2500000000 : ℝ), (-410683257/2000000000 : ℝ), (5246739037/10000000000 : ℝ)] ![(11049721901339/25000000000000 : ℝ), (6342018818283/50000000000000 : ℝ), (2694817171333/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336843667/2500000000 : ℝ)|^4389 ≤ (11049721901339/25000000000000 : ℝ)^3365
        have hw : |(1336843667/2500000000 : ℝ)|=(1336843667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-410683257/2000000000 : ℝ)|^4389 ≤ (6342018818283/50000000000000 : ℝ)^3365
        have hw : |(-410683257/2000000000 : ℝ)|=(410683257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246739037/10000000000 : ℝ)|^4389 ≤ (2694817171333/6250000000000 : ℝ)^3365
        have hw : |(5246739037/10000000000 : ℝ)|=(5246739037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s5_2 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673687289/5000000000 : ℝ)*x 0 + (5246739229/10000000000 : ℝ)*x 1 + (-41068323/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673687289/5000000000 : ℝ)^4389 ≤ (44198886635083/100000000000000 : ℝ)^3365 := by
    have hnat : (2673687289 : ℕ)^4389*100000000000000^3365 ≤ 44198886635083^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673687289 5000000000 44198886635083 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246739229/10000000000 : ℝ)^4389 ≤ (4311707679931/10000000000000 : ℝ)^3365 := by
    have hnat : (5246739229 : ℕ)^4389*10000000000000^3365 ≤ 4311707679931^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246739229 10000000000 4311707679931 10000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41068323/200000000 : ℝ)^4389 ≤ (6342018274451/50000000000000 : ℝ)^3365 := by
    have hnat : (41068323 : ℕ)^4389*50000000000000^3365 ≤ 6342018274451^3365*200000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41068323 200000000 6342018274451 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673687289/5000000000 : ℝ), (5246739229/10000000000 : ℝ), (-41068323/200000000 : ℝ)] ![(44198886635083/100000000000000 : ℝ), (4311707679931/10000000000000 : ℝ), (6342018274451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673687289/5000000000 : ℝ)|^4389 ≤ (44198886635083/100000000000000 : ℝ)^3365
        have hw : |(2673687289/5000000000 : ℝ)|=(2673687289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246739229/10000000000 : ℝ)|^4389 ≤ (4311707679931/10000000000000 : ℝ)^3365
        have hw : |(5246739229/10000000000 : ℝ)|=(5246739229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41068323/200000000 : ℝ)|^4389 ≤ (6342018274451/50000000000000 : ℝ)^3365
        have hw : |(-41068323/200000000 : ℝ)|=(41068323/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s5_3 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (860872183/2000000000 : ℝ)*x 0 + (2066345829/5000000000 : ℝ)*x 1 + (4482420157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860872183/2000000000 : ℝ)^4389 ≤ (33304565497279/100000000000000 : ℝ)^3365 := by
    have hnat : (860872183 : ℕ)^4389*100000000000000^3365 ≤ 33304565497279^3365*2000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860872183 2000000000 33304565497279 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2066345829/5000000000 : ℝ)^4389 ≤ (31582698045493/100000000000000 : ℝ)^3365 := by
    have hnat : (2066345829 : ℕ)^4389*100000000000000^3365 ≤ 31582698045493^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066345829 5000000000 31582698045493 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4482420157/10000000000 : ℝ)^4389 ≤ (35112736431649/100000000000000 : ℝ)^3365 := by
    have hnat : (4482420157 : ℕ)^4389*100000000000000^3365 ≤ 35112736431649^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482420157 10000000000 35112736431649 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(860872183/2000000000 : ℝ), (2066345829/5000000000 : ℝ), (4482420157/10000000000 : ℝ)] ![(33304565497279/100000000000000 : ℝ), (31582698045493/100000000000000 : ℝ), (35112736431649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(860872183/2000000000 : ℝ)|^4389 ≤ (33304565497279/100000000000000 : ℝ)^3365
        have hw : |(860872183/2000000000 : ℝ)|=(860872183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2066345829/5000000000 : ℝ)|^4389 ≤ (31582698045493/100000000000000 : ℝ)^3365
        have hw : |(2066345829/5000000000 : ℝ)|=(2066345829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4482420157/10000000000 : ℝ)|^4389 ≤ (35112736431649/100000000000000 : ℝ)^3365
        have hw : |(4482420157/10000000000 : ℝ)|=(4482420157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s5_4 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-394223881/2000000000 : ℝ)*x 0 + (262366191/500000000 : ℝ)*x 1 + (5407813543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (394223881/2000000000 : ℝ)^4389 ≤ (12025072029239/100000000000000 : ℝ)^3365 := by
    have hnat : (394223881 : ℕ)^4389*100000000000000^3365 ≤ 12025072029239^3365*2000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394223881 2000000000 12025072029239 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262366191/500000000 : ℝ)^4389 ≤ (21561671467747/50000000000000 : ℝ)^3365 := by
    have hnat : (262366191 : ℕ)^4389*50000000000000^3365 ≤ 21561671467747^3365*500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262366191 500000000 21561671467747 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407813543/10000000000 : ℝ)^4389 ≤ (22425792510051/50000000000000 : ℝ)^3365 := by
    have hnat : (5407813543 : ℕ)^4389*50000000000000^3365 ≤ 22425792510051^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407813543 10000000000 22425792510051 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-394223881/2000000000 : ℝ), (262366191/500000000 : ℝ), (5407813543/10000000000 : ℝ)] ![(12025072029239/100000000000000 : ℝ), (21561671467747/50000000000000 : ℝ), (22425792510051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-394223881/2000000000 : ℝ)|^4389 ≤ (12025072029239/100000000000000 : ℝ)^3365
        have hw : |(-394223881/2000000000 : ℝ)|=(394223881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262366191/500000000 : ℝ)|^4389 ≤ (21561671467747/50000000000000 : ℝ)^3365
        have hw : |(262366191/500000000 : ℝ)|=(262366191/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407813543/10000000000 : ℝ)|^4389 ≤ (22425792510051/50000000000000 : ℝ)^3365
        have hw : |(5407813543/10000000000 : ℝ)|=(5407813543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s5_5 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652673611/5000000000 : ℝ)*x 0 + (-1892341501/10000000000 : ℝ)*x 1 + (540781343/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652673611/5000000000 : ℝ)^4389 ≤ (10936585168971/25000000000000 : ℝ)^3365 := by
    have hnat : (2652673611 : ℕ)^4389*25000000000000^3365 ≤ 10936585168971^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652673611 5000000000 10936585168971 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1892341501/10000000000 : ℝ)^4389 ≤ (712629719581/6250000000000 : ℝ)^3365 := by
    have hnat : (1892341501 : ℕ)^4389*6250000000000^3365 ≤ 712629719581^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1892341501 10000000000 712629719581 6250000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540781343/1000000000 : ℝ)^4389 ≤ (44851583797697/100000000000000 : ℝ)^3365 := by
    have hnat : (540781343 : ℕ)^4389*100000000000000^3365 ≤ 44851583797697^3365*1000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540781343 1000000000 44851583797697 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652673611/5000000000 : ℝ), (-1892341501/10000000000 : ℝ), (540781343/1000000000 : ℝ)] ![(10936585168971/25000000000000 : ℝ), (712629719581/6250000000000 : ℝ), (44851583797697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652673611/5000000000 : ℝ)|^4389 ≤ (10936585168971/25000000000000 : ℝ)^3365
        have hw : |(2652673611/5000000000 : ℝ)|=(2652673611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1892341501/10000000000 : ℝ)|^4389 ≤ (712629719581/6250000000000 : ℝ)^3365
        have hw : |(-1892341501/10000000000 : ℝ)|=(1892341501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540781343/1000000000 : ℝ)|^4389 ≤ (44851583797697/100000000000000 : ℝ)^3365
        have hw : |(540781343/1000000000 : ℝ)|=(540781343/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s5_6 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061069597/2000000000 : ℝ)*x 0 + (5407813059/10000000000 : ℝ)*x 1 + (-1892340967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061069597/2000000000 : ℝ)^4389 ≤ (5468293610239/12500000000000 : ℝ)^3365 := by
    have hnat : (1061069597 : ℕ)^4389*12500000000000^3365 ≤ 5468293610239^3365*2000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061069597 2000000000 5468293610239 12500000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407813059/10000000000 : ℝ)^4389 ≤ (8970315956863/20000000000000 : ℝ)^3365 := by
    have hnat : (5407813059 : ℕ)^4389*20000000000000^3365 ≤ 8970315956863^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407813059 10000000000 8970315956863 20000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1892340967/10000000000 : ℝ)^4389 ≤ (5701035658307/50000000000000 : ℝ)^3365 := by
    have hnat : (1892340967 : ℕ)^4389*50000000000000^3365 ≤ 5701035658307^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1892340967 10000000000 5701035658307 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061069597/2000000000 : ℝ), (5407813059/10000000000 : ℝ), (-1892340967/10000000000 : ℝ)] ![(5468293610239/12500000000000 : ℝ), (8970315956863/20000000000000 : ℝ), (5701035658307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061069597/2000000000 : ℝ)|^4389 ≤ (5468293610239/12500000000000 : ℝ)^3365
        have hw : |(1061069597/2000000000 : ℝ)|=(1061069597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407813059/10000000000 : ℝ)|^4389 ≤ (8970315956863/20000000000000 : ℝ)^3365
        have hw : |(5407813059/10000000000 : ℝ)|=(5407813059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1892340967/10000000000 : ℝ)|^4389 ≤ (5701035658307/50000000000000 : ℝ)^3365
        have hw : |(-1892340967/10000000000 : ℝ)|=(1892340967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s5_7 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (430438591/1000000000 : ℝ)*x 0 + (1120288933/2500000000 : ℝ)*x 1 + (4133962309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430438591/1000000000 : ℝ)^4389 ≤ (33304817746091/100000000000000 : ℝ)^3365 := by
    have hnat : (430438591 : ℕ)^4389*100000000000000^3365 ≤ 33304817746091^3365*1000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430438591 1000000000 33304817746091 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120288933/2500000000 : ℝ)^4389 ≤ (35099818081297/100000000000000 : ℝ)^3365 := by
    have hnat : (1120288933 : ℕ)^4389*100000000000000^3365 ≤ 35099818081297^3365*2500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120288933 2500000000 35099818081297 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4133962309/10000000000 : ℝ)^4389 ≤ (6319072831561/20000000000000 : ℝ)^3365 := by
    have hnat : (4133962309 : ℕ)^4389*20000000000000^3365 ≤ 6319072831561^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133962309 10000000000 6319072831561 20000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(430438591/1000000000 : ℝ), (1120288933/2500000000 : ℝ), (4133962309/10000000000 : ℝ)] ![(33304817746091/100000000000000 : ℝ), (35099818081297/100000000000000 : ℝ), (6319072831561/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(430438591/1000000000 : ℝ)|^4389 ≤ (33304817746091/100000000000000 : ℝ)^3365
        have hw : |(430438591/1000000000 : ℝ)|=(430438591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1120288933/2500000000 : ℝ)|^4389 ≤ (35099818081297/100000000000000 : ℝ)^3365
        have hw : |(1120288933/2500000000 : ℝ)|=(1120288933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4133962309/10000000000 : ℝ)|^4389 ≤ (6319072831561/20000000000000 : ℝ)^3365
        have hw : |(4133962309/10000000000 : ℝ)|=(4133962309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1429_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7393/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11313/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1417/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14761/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7393/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11313/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7393/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11313/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7393/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11313/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7393/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11313/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7393/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11313/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7393/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11313/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11313/100000 : ℝ) ^ (1097/256 : ℝ) ≤ (8798992334683531/100000000000000000000 : ℝ) := by
    have hpowers : (11313/100000 : ℝ)^1097 ≤ (8798992334683531/100000000000000000000 : ℝ)^256 := by
      have hnat : (11313 : ℕ)^1097*100000000000000000000^256 ≤ 8798992334683531^256*100000^1097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11313 100000 8798992334683531 100000000000000000000 1097 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11313/100000 : ℝ)) (X := (8798992334683531/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7393/50000 : ℝ) ^ (1097/256 : ℝ) ≤ (27712808877579343/100000000000000000000 : ℝ) := by
    have hpowers : (7393/50000 : ℝ)^1097 ≤ (27712808877579343/100000000000000000000 : ℝ)^256 := by
      have hnat : (7393 : ℕ)^1097*100000000000000000000^256 ≤ 27712808877579343^256*50000^1097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7393 50000 27712808877579343 100000000000000000000 1097 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7393/50000 : ℝ)) (X := (27712808877579343/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008798992334683531/50000000000000000000 : ℝ) ≤ (10000410645415743/10000000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (50008798992334683531/50000000000000000000 : ℝ)^256 ≤ (10000410645415743/10000000000000000 : ℝ)^1097 := by
      have hnat : (50008798992334683531 : ℕ)^256*10000000000000000^1097 ≤ 10000410645415743^1097*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008798992334683531 50000000000000000000 10000410645415743 10000000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000410645415743/10000000000000000 : ℝ)) (X := (50008798992334683531/50000000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018255900606131437/50000000000000000000 : ℝ) ≤ (10000851933748087/10000000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (50018255900606131437/50000000000000000000 : ℝ)^256 ≤ (10000851933748087/10000000000000000 : ℝ)^1097 := by
      have hnat : (50018255900606131437 : ℕ)^256*10000000000000000^1097 ≤ 10000851933748087^1097*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018255900606131437 50000000000000000000 10000851933748087 10000000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000851933748087/10000000000000000 : ℝ)) (X := (50018255900606131437/50000000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027712808877579343/50000000000000000000 : ℝ) ≤ (10001293222080431/10000000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (50027712808877579343/50000000000000000000 : ℝ)^256 ≤ (10001293222080431/10000000000000000 : ℝ)^1097 := by
      have hnat : (50027712808877579343 : ℕ)^256*10000000000000000^1097 ≤ 10001293222080431^1097*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027712808877579343 50000000000000000000 10001293222080431 10000000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001293222080431/10000000000000000 : ℝ)) (X := (50027712808877579343/50000000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8798992334683531/100000000000000000000 : ℝ) ≤ ((6944288316344252019/6946000000000000000 : ℝ)+2*(55161041543/43412500000000 : ℝ)*(11313/100000 : ℝ))^(1097/256 : ℝ) := by
    rw [show (6944288316344252019/6946000000000000000 : ℝ)+2*(55161041543/43412500000000 : ℝ)*(11313/100000 : ℝ)=(10000410645415743/10000000000000000 : ℝ) by norm_num, show 1+2*(8798992334683531/100000000000000000000 : ℝ)=(50008798992334683531/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27712808877579343/100000000000000000000 : ℝ)+(8798992334683531/100000000000000000000 : ℝ) ≤ ((6944288316344252019/6946000000000000000 : ℝ)+(55161041543/43412500000000 : ℝ)*((7393/50000 : ℝ)+(11313/100000 : ℝ)))^(1097/256 : ℝ) := by
    rw [show (6944288316344252019/6946000000000000000 : ℝ)+(55161041543/43412500000000 : ℝ)*((7393/50000 : ℝ)+(11313/100000 : ℝ))=(10000851933748087/10000000000000000 : ℝ) by norm_num, show 1+(27712808877579343/100000000000000000000 : ℝ)+(8798992334683531/100000000000000000000 : ℝ)=(50018255900606131437/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27712808877579343/100000000000000000000 : ℝ) ≤ ((6944288316344252019/6946000000000000000 : ℝ)+2*(55161041543/43412500000000 : ℝ)*(7393/50000 : ℝ))^(1097/256 : ℝ) := by
    rw [show (6944288316344252019/6946000000000000000 : ℝ)+2*(55161041543/43412500000000 : ℝ)*(7393/50000 : ℝ)=(10001293222080431/10000000000000000 : ℝ) by norm_num, show 1+2*(27712808877579343/100000000000000000000 : ℝ)=(50027712808877579343/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6944288316344252019/6946000000000000000 : ℝ)*(X 1 0+X 2 0)+(55161041543/43412500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (11313/100000 : ℝ)) (hi := (7393/50000 : ℝ)) (c := (6944288316344252019/6946000000000000000 : ℝ)) (alpha := (55161041543/43412500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6944288316344252019/6946000000000000000 : ℝ)*(X 0 1+X 2 1)+(55161041543/43412500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (11313/100000 : ℝ)) (hi := (7393/50000 : ℝ)) (c := (6944288316344252019/6946000000000000000 : ℝ)) (alpha := (55161041543/43412500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6944288316344252019/6946000000000000000 : ℝ)*(X 0 2+X 1 2)+(55161041543/43412500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (11313/100000 : ℝ)) (hi := (7393/50000 : ℝ)) (c := (6944288316344252019/6946000000000000000 : ℝ)) (alpha := (55161041543/43412500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-985554223/5000000000 : ℝ)*X 0 0+(108168017/200000000 : ℝ)*X 0 1+(262336961/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336843667/2500000000 : ℝ)*X 1 0+(-410683257/2000000000 : ℝ)*X 1 1+(5246739037/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673687289/5000000000 : ℝ)*X 2 0+(5246739229/10000000000 : ℝ)*X 2 1+(-41068323/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((860872183/2000000000 : ℝ)*X 0 0+(2066345829/5000000000 : ℝ)*X 0 1+(4482420157/10000000000 : ℝ)*X 0 2+(860872183/2000000000 : ℝ)*X 1 0+(2066345829/5000000000 : ℝ)*X 1 1+(4482420157/10000000000 : ℝ)*X 1 2+(860872183/2000000000 : ℝ)*X 2 0+(2066345829/5000000000 : ℝ)*X 2 1+(4482420157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-394223881/2000000000 : ℝ)*X 0 0+(262366191/500000000 : ℝ)*X 0 1+(5407813543/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652673611/5000000000 : ℝ)*X 1 0+(-1892341501/10000000000 : ℝ)*X 1 1+(540781343/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061069597/2000000000 : ℝ)*X 2 0+(5407813059/10000000000 : ℝ)*X 2 1+(-1892340967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((430438591/1000000000 : ℝ)*X 0 0+(1120288933/2500000000 : ℝ)*X 0 1+(4133962309/10000000000 : ℝ)*X 0 2+(430438591/1000000000 : ℝ)*X 1 0+(1120288933/2500000000 : ℝ)*X 1 1+(4133962309/10000000000 : ℝ)*X 1 2+(430438591/1000000000 : ℝ)*X 2 0+(1120288933/2500000000 : ℝ)*X 2 1+(4133962309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21335298249686245795029813/1887500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (987187189/50000000000000 : ℝ)*(base19) + (880040197/50000000000000 : ℝ)*(base23) + (14729629/25000000000000 : ℝ)*(lower2) + (181299959/100000000000000 : ℝ)*(upper3) + (7978889/3125000000000 : ℝ)*(upper5) + (1130654396021907/25000000000000 : ℝ)*(major0) + (1130654396021907/25000000000000 : ℝ)*(major1) + (1130654396021907/25000000000000 : ℝ)*(major2) + (3092897941140947/50000000000000 : ℝ)*(sp0) + (3092916943822379/50000000000000 : ℝ)*(sp1) + (3092917050969371/50000000000000 : ℝ)*(sp2) + (1429690173531279/50000000000000 : ℝ)*(sp3) + (19989868621/50000000000000 : ℝ)*(sp4) + (4645577811/25000000000000 : ℝ)*(sp7) + (1429699464686901/50000000000000 : ℝ)*(f.failure) + (96653685344049/1562500000000 : ℝ)*(f.sum) + (6929819245427/4341250000000000000000000000 : ℝ)*base66 + (1568047174095659767/173650000000000000000000000000000 : ℝ)*base68 + (1447243900778059767/173650000000000000000000000000000 : ℝ)*base70 + (1067201822708959767/173650000000000000000000000000000 : ℝ)*base72 + (19396233149899/8682500000000000000000000000 : ℝ)*base74 + (504718058382059767/173650000000000000000000000000000 : ℝ)*base76 + (257415913409240233/173650000000000000000000000000000 : ℝ)*base77 + (1545367716215359767/173650000000000000000000000000000 : ℝ)*base80 + (9678915724901/8682500000000000000000000000 : ℝ)*base81 + (47804577/5000000000000000000000 : ℝ)*base90 + (47804577/5000000000000000000000 : ℝ)*base92 + (47804577/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (765789675562285414535247/138920000000000000000000000000 : ℝ) := by norm_num
    linear_combination (715456127/50000000000000 : ℝ)*(base19) + (339802651/10000000000000 : ℝ)*(base23) + (25905109/100000000000000 : ℝ)*(upper3) + (39144501/10000000000000 : ℝ)*(lower4) + (1822233957997/40000000000 : ℝ)*(major0) + (1822233957997/40000000000 : ℝ)*(major1) + (1822233957997/40000000000 : ℝ)*(major2) + (8703851141/25000000000000 : ℝ)*(sp1) + (38437349147/50000000000000 : ℝ)*(sp2) + (942304113/100000000000000 : ℝ)*(sp3) + (6230927284346641/100000000000000 : ℝ)*(sp4) + (6230891038029823/100000000000000 : ℝ)*(sp5) + (6230847011621837/100000000000000 : ℝ)*(sp6) + (180015086224117/6250000000000 : ℝ)*(sp7) + (45003786279531/1562500000000 : ℝ)*(f.failure) + (6230927284346641/100000000000000 : ℝ)*(f.sum) + (1769284586663/347300000000000000000000000 : ℝ)*base66 + (2086231702073577/277840000000000000000000000000 : ℝ)*base68 + (2211083822129737/277840000000000000000000000000 : ℝ)*base70 + (4626271958948377/277840000000000000000000000000 : ℝ)*base72 + (53455547287/694600000000000000000000000 : ℝ)*base74 + (3694840746748537/277840000000000000000000000000 : ℝ)*base76 + (2890919971323337/277840000000000000000000000000 : ℝ)*base78 + (4617647525841337/277840000000000000000000000000 : ℝ)*base80 + (1830764118883/347300000000000000000000000 : ℝ)*base82 + (1003087/156250000000000000000 : ℝ)*base90 + (1003087/156250000000000000000 : ℝ)*base92 + (1003087/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1429_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7393/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11313/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1417/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1429_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1429_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15799/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (324/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1417/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1429_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1429_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1429_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15799/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (324/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1417/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1429_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

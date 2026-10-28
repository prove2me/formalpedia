-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1143_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:32:36.462804+00:00
-- url     : https://prove2.me/submissions/595e41e3-23bb-4be3-9ed9-9a527a080fc3

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
theorem support_rectangle_w1143_s0_0 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-945747131/5000000000 : ℝ)*x 0 + (47297649/78125000 : ℝ)*x 1 + (4780598787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (945747131/5000000000 : ℝ)^521 ≤ (2749163811941/25000000000000 : ℝ)^393 := by
    have hnat : (945747131 : ℕ)^521*25000000000000^393 ≤ 2749163811941^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945747131 5000000000 2749163811941 25000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47297649/78125000 : ℝ)^521 ≤ (6426479433147/12500000000000 : ℝ)^393 := by
    have hnat : (47297649 : ℕ)^521*12500000000000^393 ≤ 6426479433147^393*78125000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47297649 78125000 6426479433147 12500000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4780598787/10000000000 : ℝ)^521 ≤ (37591509267303/100000000000000 : ℝ)^393 := by
    have hnat : (4780598787 : ℕ)^521*100000000000000^393 ≤ 37591509267303^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4780598787 10000000000 37591509267303 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-945747131/5000000000 : ℝ), (47297649/78125000 : ℝ), (4780598787/10000000000 : ℝ)] ![(2749163811941/25000000000000 : ℝ), (6426479433147/12500000000000 : ℝ), (37591509267303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-945747131/5000000000 : ℝ)|^521 ≤ (2749163811941/25000000000000 : ℝ)^393
        have hw : |(-945747131/5000000000 : ℝ)|=(945747131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(47297649/78125000 : ℝ)|^521 ≤ (6426479433147/12500000000000 : ℝ)^393
        have hw : |(47297649/78125000 : ℝ)|=(47297649/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4780598787/10000000000 : ℝ)|^521 ≤ (37591509267303/100000000000000 : ℝ)^393
        have hw : |(4780598787/10000000000 : ℝ)|=(4780598787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s0_1 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5516737389/10000000000 : ℝ)*x 0 + (-2622305419/10000000000 : ℝ)*x 1 + (119514969/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5516737389/10000000000 : ℝ)^521 ≤ (22725754438773/50000000000000 : ℝ)^393 := by
    have hnat : (5516737389 : ℕ)^521*50000000000000^393 ≤ 22725754438773^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516737389 10000000000 22725754438773 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622305419/10000000000 : ℝ)^521 ≤ (16956982117693/100000000000000 : ℝ)^393 := by
    have hnat : (2622305419 : ℕ)^521*100000000000000^393 ≤ 16956982117693^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622305419 10000000000 16956982117693 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119514969/250000000 : ℝ)^521 ≤ (37591508985843/100000000000000 : ℝ)^393 := by
    have hnat : (119514969 : ℕ)^521*100000000000000^393 ≤ 37591508985843^393*250000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119514969 250000000 37591508985843 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5516737389/10000000000 : ℝ), (-2622305419/10000000000 : ℝ), (119514969/250000000 : ℝ)] ![(22725754438773/50000000000000 : ℝ), (16956982117693/100000000000000 : ℝ), (37591508985843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5516737389/10000000000 : ℝ)|^521 ≤ (22725754438773/50000000000000 : ℝ)^393
        have hw : |(5516737389/10000000000 : ℝ)|=(5516737389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2622305419/10000000000 : ℝ)|^521 ≤ (16956982117693/100000000000000 : ℝ)^393
        have hw : |(-2622305419/10000000000 : ℝ)|=(2622305419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(119514969/250000000 : ℝ)|^521 ≤ (37591508985843/100000000000000 : ℝ)^393
        have hw : |(119514969/250000000 : ℝ)|=(119514969/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s0_2 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2758368641/5000000000 : ℝ)*x 0 + (478059881/1000000000 : ℝ)*x 1 + (-327788187/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2758368641/5000000000 : ℝ)^521 ≤ (45451507708867/100000000000000 : ℝ)^393 := by
    have hnat : (2758368641 : ℕ)^521*100000000000000^393 ≤ 45451507708867^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758368641 5000000000 45451507708867 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (478059881/1000000000 : ℝ)^521 ≤ (7518301901413/20000000000000 : ℝ)^393 := by
    have hnat : (478059881 : ℕ)^521*20000000000000^393 ≤ 7518301901413^393*1000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478059881 1000000000 7518301901413 20000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327788187/1250000000 : ℝ)^521 ≤ (847849138889/5000000000000 : ℝ)^393 := by
    have hnat : (327788187 : ℕ)^521*5000000000000^393 ≤ 847849138889^393*1250000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327788187 1250000000 847849138889 5000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2758368641/5000000000 : ℝ), (478059881/1000000000 : ℝ), (-327788187/1250000000 : ℝ)] ![(45451507708867/100000000000000 : ℝ), (7518301901413/20000000000000 : ℝ), (847849138889/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2758368641/5000000000 : ℝ)|^521 ≤ (45451507708867/100000000000000 : ℝ)^393
        have hw : |(2758368641/5000000000 : ℝ)|=(2758368641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(478059881/1000000000 : ℝ)|^521 ≤ (7518301901413/20000000000000 : ℝ)^393
        have hw : |(478059881/1000000000 : ℝ)|=(478059881/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-327788187/1250000000 : ℝ)|^521 ≤ (847849138889/5000000000000 : ℝ)^393
        have hw : |(-327788187/1250000000 : ℝ)|=(327788187/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s0_3 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (840181987/2000000000 : ℝ)*x 0 + (97532257/312500000 : ℝ)*x 1 + (5655125089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840181987/2000000000 : ℝ)^521 ≤ (15835668676911/50000000000000 : ℝ)^393 := by
    have hnat : (840181987 : ℕ)^521*50000000000000^393 ≤ 15835668676911^393*2000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840181987 2000000000 15835668676911 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97532257/312500000 : ℝ)^521 ≤ (4271902361693/20000000000000 : ℝ)^393 := by
    have hnat : (97532257 : ℕ)^521*20000000000000^393 ≤ 4271902361693^393*312500000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97532257 312500000 4271902361693 20000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5655125089/10000000000 : ℝ)^521 ≤ (293557192649/625000000000 : ℝ)^393 := by
    have hnat : (5655125089 : ℕ)^521*625000000000^393 ≤ 293557192649^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5655125089 10000000000 293557192649 625000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(840181987/2000000000 : ℝ), (97532257/312500000 : ℝ), (5655125089/10000000000 : ℝ)] ![(15835668676911/50000000000000 : ℝ), (4271902361693/20000000000000 : ℝ), (293557192649/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(840181987/2000000000 : ℝ)|^521 ≤ (15835668676911/50000000000000 : ℝ)^393
        have hw : |(840181987/2000000000 : ℝ)|=(840181987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(97532257/312500000 : ℝ)|^521 ≤ (4271902361693/20000000000000 : ℝ)^393
        have hw : |(97532257/312500000 : ℝ)|=(97532257/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5655125089/10000000000 : ℝ)|^521 ≤ (293557192649/625000000000 : ℝ)^393
        have hw : |(5655125089/10000000000 : ℝ)|=(5655125089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s0_4 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1896636913/10000000000 : ℝ)*x 0 + (4813451013/10000000000 : ℝ)*x 1 + (94063933/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1896636913/10000000000 : ℝ)^521 ≤ (11036308602561/100000000000000 : ℝ)^393 := by
    have hnat : (1896636913 : ℕ)^521*100000000000000^393 ≤ 11036308602561^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896636913 10000000000 11036308602561 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4813451013/10000000000 : ℝ)^521 ≤ (2370897369699/6250000000000 : ℝ)^393 := by
    have hnat : (4813451013 : ℕ)^521*6250000000000^393 ≤ 2370897369699^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4813451013 10000000000 2370897369699 6250000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94063933/156250000 : ℝ)^521 ≤ (3189333341399/6250000000000 : ℝ)^393 := by
    have hnat : (94063933 : ℕ)^521*6250000000000^393 ≤ 3189333341399^393*156250000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94063933 156250000 3189333341399 6250000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1896636913/10000000000 : ℝ), (4813451013/10000000000 : ℝ), (94063933/156250000 : ℝ)] ![(11036308602561/100000000000000 : ℝ), (2370897369699/6250000000000 : ℝ), (3189333341399/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1896636913/10000000000 : ℝ)|^521 ≤ (11036308602561/100000000000000 : ℝ)^393
        have hw : |(-1896636913/10000000000 : ℝ)|=(1896636913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4813451013/10000000000 : ℝ)|^521 ≤ (2370897369699/6250000000000 : ℝ)^393
        have hw : |(4813451013/10000000000 : ℝ)|=(4813451013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(94063933/156250000 : ℝ)|^521 ≤ (3189333341399/6250000000000 : ℝ)^393
        have hw : |(94063933/156250000 : ℝ)|=(94063933/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s0_5 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (646336729/1250000000 : ℝ)*x 0 + (-1382812643/10000000000 : ℝ)*x 1 + (752511447/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646336729/1250000000 : ℝ)^521 ≤ (10427777506771/25000000000000 : ℝ)^393 := by
    have hnat : (646336729 : ℕ)^521*25000000000000^393 ≤ 10427777506771^393*1250000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646336729 1250000000 10427777506771 25000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1382812643/10000000000 : ℝ)^521 ≤ (725955802091/10000000000000 : ℝ)^393 := by
    have hnat : (1382812643 : ℕ)^521*10000000000000^393 ≤ 725955802091^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382812643 10000000000 725955802091 10000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (752511447/1250000000 : ℝ)^521 ≤ (51029331934111/100000000000000 : ℝ)^393 := by
    have hnat : (752511447 : ℕ)^521*100000000000000^393 ≤ 51029331934111^393*1250000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752511447 1250000000 51029331934111 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646336729/1250000000 : ℝ), (-1382812643/10000000000 : ℝ), (752511447/1250000000 : ℝ)] ![(10427777506771/25000000000000 : ℝ), (725955802091/10000000000000 : ℝ), (51029331934111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646336729/1250000000 : ℝ)|^521 ≤ (10427777506771/25000000000000 : ℝ)^393
        have hw : |(646336729/1250000000 : ℝ)|=(646336729/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1382812643/10000000000 : ℝ)|^521 ≤ (725955802091/10000000000000 : ℝ)^393
        have hw : |(-1382812643/10000000000 : ℝ)|=(1382812643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(752511447/1250000000 : ℝ)|^521 ≤ (51029331934111/100000000000000 : ℝ)^393
        have hw : |(752511447/1250000000 : ℝ)|=(752511447/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s0_6 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2585346917/5000000000 : ℝ)*x 0 + (6020091603/10000000000 : ℝ)*x 1 + (-1382812597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585346917/5000000000 : ℝ)^521 ≤ (41711110048473/100000000000000 : ℝ)^393 := by
    have hnat : (2585346917 : ℕ)^521*100000000000000^393 ≤ 41711110048473^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585346917 5000000000 41711110048473 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6020091603/10000000000 : ℝ)^521 ≤ (25514666118759/50000000000000 : ℝ)^393 := by
    have hnat : (6020091603 : ℕ)^521*50000000000000^393 ≤ 25514666118759^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6020091603 10000000000 25514666118759 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1382812597/10000000000 : ℝ)^521 ≤ (7259557700763/100000000000000 : ℝ)^393 := by
    have hnat : (1382812597 : ℕ)^521*100000000000000^393 ≤ 7259557700763^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382812597 10000000000 7259557700763 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585346917/5000000000 : ℝ), (6020091603/10000000000 : ℝ), (-1382812597/10000000000 : ℝ)] ![(41711110048473/100000000000000 : ℝ), (25514666118759/50000000000000 : ℝ), (7259557700763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585346917/5000000000 : ℝ)|^521 ≤ (41711110048473/100000000000000 : ℝ)^393
        have hw : |(2585346917/5000000000 : ℝ)|=(2585346917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6020091603/10000000000 : ℝ)|^521 ≤ (25514666118759/50000000000000 : ℝ)^393
        have hw : |(6020091603/10000000000 : ℝ)|=(6020091603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1382812597/10000000000 : ℝ)|^521 ≤ (7259557700763/100000000000000 : ℝ)^393
        have hw : |(-1382812597/10000000000 : ℝ)|=(1382812597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s0_7 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (421114329/1000000000 : ℝ)*x 0 + (2794876703/5000000000 : ℝ)*x 1 + (127548097/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421114329/1000000000 : ℝ)^521 ≤ (317736568519/1000000000000 : ℝ)^393 := by
    have hnat : (421114329 : ℕ)^521*1000000000000^393 ≤ 317736568519^393*1000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421114329 1000000000 317736568519 1000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2794876703/5000000000 : ℝ)^521 ≤ (23125360077569/50000000000000 : ℝ)^393 := by
    have hnat : (2794876703 : ℕ)^521*50000000000000^393 ≤ 23125360077569^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2794876703 5000000000 23125360077569 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127548097/400000000 : ℝ)^521 ≤ (439512459573/2000000000000 : ℝ)^393 := by
    have hnat : (127548097 : ℕ)^521*2000000000000^393 ≤ 439512459573^393*400000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127548097 400000000 439512459573 2000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(421114329/1000000000 : ℝ), (2794876703/5000000000 : ℝ), (127548097/400000000 : ℝ)] ![(317736568519/1000000000000 : ℝ), (23125360077569/50000000000000 : ℝ), (439512459573/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(421114329/1000000000 : ℝ)|^521 ≤ (317736568519/1000000000000 : ℝ)^393
        have hw : |(421114329/1000000000 : ℝ)|=(421114329/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2794876703/5000000000 : ℝ)|^521 ≤ (23125360077569/50000000000000 : ℝ)^393
        have hw : |(2794876703/5000000000 : ℝ)|=(2794876703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(127548097/400000000 : ℝ)|^521 ≤ (439512459573/2000000000000 : ℝ)^393
        have hw : |(127548097/400000000 : ℝ)|=(127548097/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1143_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7474661/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (209/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27811/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8335/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8335 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8335*1^2048 ≤ 0^2048*1^8335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8335 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8335/2048 : ℝ) ≤ (600335635823132581/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8335 ≤ (600335635823132581/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8335*25000000000000000000^2048 ≤ 600335635823132581^2048*5^8335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 600335635823132581 25000000000000000000 8335 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (600335635823132581/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8335/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8335 := by
      have hnat : (1 : ℕ)^2048*1^8335 ≤ 1^8335*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25600335635823132581/25000000000000000000 : ℝ) ≤ (125730957592943/125000000000000 : ℝ) ^ (8335/2048 : ℝ) := by
    have hpowers : (25600335635823132581/25000000000000000000 : ℝ)^2048 ≤ (125730957592943/125000000000000 : ℝ)^8335 := by
      have hnat : (25600335635823132581 : ℕ)^2048*125000000000000^8335 ≤ 125730957592943^8335*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25600335635823132581 25000000000000000000 125730957592943 125000000000000 2048 8335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125730957592943/125000000000000 : ℝ)) (X := (25600335635823132581/25000000000000000000 : ℝ)) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (13100335635823132581/12500000000000000000 : ℝ) ≤ (63230957592943/62500000000000 : ℝ) ^ (8335/2048 : ℝ) := by
    have hpowers : (13100335635823132581/12500000000000000000 : ℝ)^2048 ≤ (63230957592943/62500000000000 : ℝ)^8335 := by
      have hnat : (13100335635823132581 : ℕ)^2048*62500000000000^8335 ≤ 63230957592943^8335*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13100335635823132581 12500000000000000000 63230957592943 62500000000000 2048 8335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (63230957592943/62500000000000 : ℝ)) (X := (13100335635823132581/12500000000000000000 : ℝ)) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(730957592943/50000000000000 : ℝ)*(0 : ℝ))^(8335/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(730957592943/50000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(600335635823132581/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(730957592943/50000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8335/2048 : ℝ) := by
    rw [show (1 : ℝ)+(730957592943/50000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(125730957592943/125000000000000 : ℝ) by norm_num, show 1+(600335635823132581/25000000000000000000 : ℝ)+(0 : ℝ)=(25600335635823132581/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(600335635823132581/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(730957592943/50000000000000 : ℝ)*(2/5 : ℝ))^(8335/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(730957592943/50000000000000 : ℝ)*(2/5 : ℝ)=(63230957592943/62500000000000 : ℝ) by norm_num, show 1+2*(600335635823132581/25000000000000000000 : ℝ)=(13100335635823132581/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(730957592943/50000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8335/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (730957592943/50000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(730957592943/50000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8335/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (730957592943/50000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(730957592943/50000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8335/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (730957592943/50000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-945747131/5000000000 : ℝ)*X 0 0+(47297649/78125000 : ℝ)*X 0 1+(4780598787/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5516737389/10000000000 : ℝ)*X 1 0+(-2622305419/10000000000 : ℝ)*X 1 1+(119514969/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2758368641/5000000000 : ℝ)*X 2 0+(478059881/1000000000 : ℝ)*X 2 1+(-327788187/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((840181987/2000000000 : ℝ)*X 0 0+(97532257/312500000 : ℝ)*X 0 1+(5655125089/10000000000 : ℝ)*X 0 2+(840181987/2000000000 : ℝ)*X 1 0+(97532257/312500000 : ℝ)*X 1 1+(5655125089/10000000000 : ℝ)*X 1 2+(840181987/2000000000 : ℝ)*X 2 0+(97532257/312500000 : ℝ)*X 2 1+(5655125089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1896636913/10000000000 : ℝ)*X 0 0+(4813451013/10000000000 : ℝ)*X 0 1+(94063933/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((646336729/1250000000 : ℝ)*X 1 0+(-1382812643/10000000000 : ℝ)*X 1 1+(752511447/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2585346917/5000000000 : ℝ)*X 2 0+(6020091603/10000000000 : ℝ)*X 2 1+(-1382812597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((421114329/1000000000 : ℝ)*X 0 0+(2794876703/5000000000 : ℝ)*X 0 1+(127548097/400000000 : ℝ)*X 0 2+(421114329/1000000000 : ℝ)*X 1 0+(2794876703/5000000000 : ℝ)*X 1 1+(127548097/400000000 : ℝ)*X 1 2+(421114329/1000000000 : ℝ)*X 2 0+(2794876703/5000000000 : ℝ)*X 2 1+(127548097/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (656096733314002916223/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (23776827/100000000000000 : ℝ)*(base1) + (256923779/50000000000000 : ℝ)*(base19) + (471214799/100000000000000 : ℝ)*(base23) + (13701313/50000000000000 : ℝ)*(base24) + (3586897/3125000000000 : ℝ)*(upper3) + (147482530261171/25000000000000 : ℝ)*(major0) + (147482530261171/25000000000000 : ℝ)*(major1) + (147482530261171/25000000000000 : ℝ)*(major2) + (157047816563829/20000000000000 : ℝ)*(sp0) + (98154959265579/12500000000000 : ℝ)*(sp1) + (392619844677383/50000000000000 : ℝ)*(sp2) + (98654767233169/25000000000000 : ℝ)*(sp3) + (1128929873/100000000000000 : ℝ)*(sp4) + (891424013/100000000000000 : ℝ)*(sp7) + (394619984133517/100000000000000 : ℝ)*(f.failure) + (785240187972191/100000000000000 : ℝ)*(f.sum) + (1082863635939/312500000000000000000000000 : ℝ)*base65 + (6679253402503/1250000000000000000000000000 : ℝ)*base67 + (1886634791253/1250000000000000000000000000 : ℝ)*base69 + (8030515668753/1250000000000000000000000000 : ℝ)*base71 + (1608478457503/625000000000000000000000000 : ℝ)*base73 + (13360676505003/1250000000000000000000000000 : ℝ)*base75 + (4385115463753/1250000000000000000000000000 : ℝ)*base77 + (11277648813753/1250000000000000000000000000 : ℝ)*base79 + (790285730157/156250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1687263/500000000000000000000 : ℝ)*base90 + (1687263/500000000000000000000 : ℝ)*base92 + (1687263/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (522983460995539291107/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (9657841/20000000000000 : ℝ)*(base1) + (41141909/5000000000000 : ℝ)*(base19) + (51399521/6250000000000 : ℝ)*(base23) + (84957223/100000000000000 : ℝ)*(upper3) + (49686523/50000000000000 : ℝ)*(upper5) + (77826972799603/12500000000000 : ℝ)*(major0) + (77826972799603/12500000000000 : ℝ)*(major1) + (77826972799603/12500000000000 : ℝ)*(major2) + (815588961/50000000000000 : ℝ)*(sp1) + (809863323/50000000000000 : ℝ)*(sp2) + (82874720717727/10000000000000 : ℝ)*(sp4) + (828744704871963/100000000000000 : ℝ)*(sp5) + (828744716769083/100000000000000 : ℝ)*(sp6) + (416484246046567/100000000000000 : ℝ)*(sp7) + (104121073583943/25000000000000 : ℝ)*(f.failure) + (165749431777613/20000000000000 : ℝ)*(f.sum) + (382467901629/312500000000000000000000000 : ℝ)*base65 + (1220953681629/625000000000000000000000000 : ℝ)*base67 + (40889496127/312500000000000000000000000 : ℝ)*base69 + (960196436629/625000000000000000000000000 : ℝ)*base71 + (300278456383/625000000000000000000000000 : ℝ)*base73 + (529633681373/312500000000000000000000000 : ℝ)*base76 + (1794951111629/625000000000000000000000000 : ℝ)*base77 + (2141999716127/312500000000000000000000000 : ℝ)*base79 + (582164000871/312500000000000000000000000 : ℝ)*base82 + (1031677/125000000000000000000 : ℝ)*base90 + (1031677/125000000000000000000 : ℝ)*base92 + (1031677/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1143_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7474661/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (209/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27811/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1143_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1143_s1_0 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2096088427/10000000000 : ℝ)*x 0 + (5701231737/10000000000 : ℝ)*x 1 + (5002485811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096088427/10000000000 : ℝ)^521 ≤ (3150161999161/25000000000000 : ℝ)^393 := by
    have hnat : (2096088427 : ℕ)^521*25000000000000^393 ≤ 3150161999161^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096088427 10000000000 3150161999161 25000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5701231737/10000000000 : ℝ)^521 ≤ (9495498193101/20000000000000 : ℝ)^393 := by
    have hnat : (5701231737 : ℕ)^521*20000000000000^393 ≤ 9495498193101^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5701231737 10000000000 9495498193101 20000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5002485811/10000000000 : ℝ)^521 ≤ (1996093051037/5000000000000 : ℝ)^393 := by
    have hnat : (5002485811 : ℕ)^521*5000000000000^393 ≤ 1996093051037^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5002485811 10000000000 1996093051037 5000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2096088427/10000000000 : ℝ), (5701231737/10000000000 : ℝ), (5002485811/10000000000 : ℝ)] ![(3150161999161/25000000000000 : ℝ), (9495498193101/20000000000000 : ℝ), (1996093051037/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2096088427/10000000000 : ℝ)|^521 ≤ (3150161999161/25000000000000 : ℝ)^393
        have hw : |(-2096088427/10000000000 : ℝ)|=(2096088427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5701231737/10000000000 : ℝ)|^521 ≤ (9495498193101/20000000000000 : ℝ)^393
        have hw : |(5701231737/10000000000 : ℝ)|=(5701231737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5002485811/10000000000 : ℝ)|^521 ≤ (1996093051037/5000000000000 : ℝ)^393
        have hw : |(5002485811/10000000000 : ℝ)|=(5002485811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s1_1 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1083813177/2000000000 : ℝ)*x 0 + (-247315027/1000000000 : ℝ)*x 1 + (2501242549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083813177/2000000000 : ℝ)^521 ≤ (44387806704013/100000000000000 : ℝ)^393 := by
    have hnat : (1083813177 : ℕ)^521*100000000000000^393 ≤ 44387806704013^393*2000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083813177 2000000000 44387806704013 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (247315027/1000000000 : ℝ)^521 ≤ (7845169900109/50000000000000 : ℝ)^393 := by
    have hnat : (247315027 : ℕ)^521*50000000000000^393 ≤ 7845169900109^393*1000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247315027 1000000000 7845169900109 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2501242549/5000000000 : ℝ)^521 ≤ (39921853477471/100000000000000 : ℝ)^393 := by
    have hnat : (2501242549 : ℕ)^521*100000000000000^393 ≤ 39921853477471^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2501242549 5000000000 39921853477471 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083813177/2000000000 : ℝ), (-247315027/1000000000 : ℝ), (2501242549/5000000000 : ℝ)] ![(44387806704013/100000000000000 : ℝ), (7845169900109/50000000000000 : ℝ), (39921853477471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083813177/2000000000 : ℝ)|^521 ≤ (44387806704013/100000000000000 : ℝ)^393
        have hw : |(1083813177/2000000000 : ℝ)|=(1083813177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-247315027/1000000000 : ℝ)|^521 ≤ (7845169900109/50000000000000 : ℝ)^393
        have hw : |(-247315027/1000000000 : ℝ)|=(247315027/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2501242549/5000000000 : ℝ)|^521 ≤ (39921853477471/100000000000000 : ℝ)^393
        have hw : |(2501242549/5000000000 : ℝ)|=(2501242549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s1_2 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5419067837/10000000000 : ℝ)*x 0 + (5002483363/10000000000 : ℝ)*x 1 + (-2473149933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5419067837/10000000000 : ℝ)^521 ≤ (22193913950259/50000000000000 : ℝ)^393 := by
    have hnat : (5419067837 : ℕ)^521*50000000000000^393 ≤ 22193913950259^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419067837 10000000000 22193913950259 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5002483363/10000000000 : ℝ)^521 ≤ (39921835121831/100000000000000 : ℝ)^393 := by
    have hnat : (5002483363 : ℕ)^521*100000000000000^393 ≤ 39921835121831^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5002483363 10000000000 39921835121831 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2473149933/10000000000 : ℝ)^521 ≤ (7845168482923/50000000000000 : ℝ)^393 := by
    have hnat : (2473149933 : ℕ)^521*50000000000000^393 ≤ 7845168482923^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2473149933 10000000000 7845168482923 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5419067837/10000000000 : ℝ), (5002483363/10000000000 : ℝ), (-2473149933/10000000000 : ℝ)] ![(22193913950259/50000000000000 : ℝ), (39921835121831/100000000000000 : ℝ), (7845168482923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5419067837/10000000000 : ℝ)|^521 ≤ (22193913950259/50000000000000 : ℝ)^393
        have hw : |(5419067837/10000000000 : ℝ)|=(5419067837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5002483363/10000000000 : ℝ)|^521 ≤ (39921835121831/100000000000000 : ℝ)^393
        have hw : |(5002483363/10000000000 : ℝ)|=(5002483363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2473149933/10000000000 : ℝ)|^521 ≤ (7845168482923/50000000000000 : ℝ)^393
        have hw : |(-2473149933/10000000000 : ℝ)|=(2473149933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s1_3 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2158678219/5000000000 : ℝ)*x 0 + (229827729/625000000 : ℝ)*x 1 + (2533825259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158678219/5000000000 : ℝ)^521 ≤ (16420201190793/50000000000000 : ℝ)^393 := by
    have hnat : (2158678219 : ℕ)^521*50000000000000^393 ≤ 16420201190793^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158678219 5000000000 16420201190793 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229827729/625000000 : ℝ)^521 ≤ (1327343023819/5000000000000 : ℝ)^393 := by
    have hnat : (229827729 : ℕ)^521*5000000000000^393 ≤ 1327343023819^393*625000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229827729 625000000 1327343023819 5000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2533825259/5000000000 : ℝ)^521 ≤ (40612737128397/100000000000000 : ℝ)^393 := by
    have hnat : (2533825259 : ℕ)^521*100000000000000^393 ≤ 40612737128397^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2533825259 5000000000 40612737128397 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158678219/5000000000 : ℝ), (229827729/625000000 : ℝ), (2533825259/5000000000 : ℝ)] ![(16420201190793/50000000000000 : ℝ), (1327343023819/5000000000000 : ℝ), (40612737128397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158678219/5000000000 : ℝ)|^521 ≤ (16420201190793/50000000000000 : ℝ)^393
        have hw : |(2158678219/5000000000 : ℝ)|=(2158678219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229827729/625000000 : ℝ)|^521 ≤ (1327343023819/5000000000000 : ℝ)^393
        have hw : |(229827729/625000000 : ℝ)|=(229827729/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2533825259/5000000000 : ℝ)|^521 ≤ (40612737128397/100000000000000 : ℝ)^393
        have hw : |(2533825259/5000000000 : ℝ)|=(2533825259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s1_4 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-131056109/625000000 : ℝ)*x 0 + (5012022781/10000000000 : ℝ)*x 1 + (35571891/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131056109/625000000 : ℝ)^521 ≤ (19698590961/156250000000 : ℝ)^393 := by
    have hnat : (131056109 : ℕ)^521*156250000000^393 ≤ 19698590961^393*625000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131056109 625000000 19698590961 156250000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5012022781/10000000000 : ℝ)^521 ≤ (4002278985491/10000000000000 : ℝ)^393 := by
    have hnat : (5012022781 : ℕ)^521*10000000000000^393 ≤ 4002278985491^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5012022781 10000000000 4002278985491 10000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35571891/62500000 : ℝ)^521 ≤ (23685055953987/50000000000000 : ℝ)^393 := by
    have hnat : (35571891 : ℕ)^521*50000000000000^393 ≤ 23685055953987^393*62500000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35571891 62500000 23685055953987 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-131056109/625000000 : ℝ), (5012022781/10000000000 : ℝ), (35571891/62500000 : ℝ)] ![(19698590961/156250000000 : ℝ), (4002278985491/10000000000000 : ℝ), (23685055953987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-131056109/625000000 : ℝ)|^521 ≤ (19698590961/156250000000 : ℝ)^393
        have hw : |(-131056109/625000000 : ℝ)|=(131056109/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5012022781/10000000000 : ℝ)|^521 ≤ (4002278985491/10000000000000 : ℝ)^393
        have hw : |(5012022781/10000000000 : ℝ)|=(5012022781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35571891/62500000 : ℝ)|^521 ≤ (23685055953987/50000000000000 : ℝ)^393
        have hw : |(35571891/62500000 : ℝ)|=(35571891/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s1_5 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5239910891/10000000000 : ℝ)*x 0 + (-892064293/5000000000 : ℝ)*x 1 + (5691506249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5239910891/10000000000 : ℝ)^521 ≤ (42452939586323/100000000000000 : ℝ)^393 := by
    have hnat : (5239910891 : ℕ)^521*100000000000000^393 ≤ 42452939586323^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239910891 10000000000 42452939586323 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (892064293/5000000000 : ℝ)^521 ≤ (5088453898263/50000000000000 : ℝ)^393 := by
    have hnat : (892064293 : ℕ)^521*50000000000000^393 ≤ 5088453898263^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892064293 5000000000 5088453898263 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5691506249/10000000000 : ℝ)^521 ≤ (11842538152859/25000000000000 : ℝ)^393 := by
    have hnat : (5691506249 : ℕ)^521*25000000000000^393 ≤ 11842538152859^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5691506249 10000000000 11842538152859 25000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5239910891/10000000000 : ℝ), (-892064293/5000000000 : ℝ), (5691506249/10000000000 : ℝ)] ![(42452939586323/100000000000000 : ℝ), (5088453898263/50000000000000 : ℝ), (11842538152859/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5239910891/10000000000 : ℝ)|^521 ≤ (42452939586323/100000000000000 : ℝ)^393
        have hw : |(5239910891/10000000000 : ℝ)|=(5239910891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-892064293/5000000000 : ℝ)|^521 ≤ (5088453898263/50000000000000 : ℝ)^393
        have hw : |(-892064293/5000000000 : ℝ)|=(892064293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5691506249/10000000000 : ℝ)|^521 ≤ (11842538152859/25000000000000 : ℝ)^393
        have hw : |(5691506249/10000000000 : ℝ)|=(5691506249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s1_6 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2619954711/5000000000 : ℝ)*x 0 + (5691508159/10000000000 : ℝ)*x 1 + (-892063943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2619954711/5000000000 : ℝ)^521 ≤ (10613230952091/25000000000000 : ℝ)^393 := by
    have hnat : (2619954711 : ℕ)^521*25000000000000^393 ≤ 10613230952091^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619954711 5000000000 10613230952091 25000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5691508159/10000000000 : ℝ)^521 ≤ (1184254342147/2500000000000 : ℝ)^393 := by
    have hnat : (5691508159 : ℕ)^521*2500000000000^393 ≤ 1184254342147^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5691508159 10000000000 1184254342147 2500000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (892063943/5000000000 : ℝ)^521 ≤ (10176902503149/100000000000000 : ℝ)^393 := by
    have hnat : (892063943 : ℕ)^521*100000000000000^393 ≤ 10176902503149^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892063943 5000000000 10176902503149 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2619954711/5000000000 : ℝ), (5691508159/10000000000 : ℝ), (-892063943/5000000000 : ℝ)] ![(10613230952091/25000000000000 : ℝ), (1184254342147/2500000000000 : ℝ), (10176902503149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2619954711/5000000000 : ℝ)|^521 ≤ (10613230952091/25000000000000 : ℝ)^393
        have hw : |(2619954711/5000000000 : ℝ)|=(2619954711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5691508159/10000000000 : ℝ)|^521 ≤ (1184254342147/2500000000000 : ℝ)^393
        have hw : |(5691508159/10000000000 : ℝ)|=(5691508159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-892063943/5000000000 : ℝ)|^521 ≤ (10176902503149/100000000000000 : ℝ)^393
        have hw : |(-892063943/5000000000 : ℝ)|=(892063943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s1_7 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4318956521/10000000000 : ℝ)*x 0 + (5048673159/10000000000 : ℝ)*x 1 + (1848297549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318956521/10000000000 : ℝ)^521 ≤ (32856538700083/100000000000000 : ℝ)^393 := by
    have hnat : (4318956521 : ℕ)^521*100000000000000^393 ≤ 32856538700083^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318956521 10000000000 32856538700083 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5048673159/10000000000 : ℝ)^521 ≤ (40411238824527/100000000000000 : ℝ)^393 := by
    have hnat : (5048673159 : ℕ)^521*100000000000000^393 ≤ 40411238824527^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5048673159 10000000000 40411238824527 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1848297549/5000000000 : ℝ)^521 ≤ (6683055615687/25000000000000 : ℝ)^393 := by
    have hnat : (1848297549 : ℕ)^521*25000000000000^393 ≤ 6683055615687^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1848297549 5000000000 6683055615687 25000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318956521/10000000000 : ℝ), (5048673159/10000000000 : ℝ), (1848297549/5000000000 : ℝ)] ![(32856538700083/100000000000000 : ℝ), (40411238824527/100000000000000 : ℝ), (6683055615687/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318956521/10000000000 : ℝ)|^521 ≤ (32856538700083/100000000000000 : ℝ)^393
        have hw : |(4318956521/10000000000 : ℝ)|=(4318956521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5048673159/10000000000 : ℝ)|^521 ≤ (40411238824527/100000000000000 : ℝ)^393
        have hw : |(5048673159/10000000000 : ℝ)|=(5048673159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1848297549/5000000000 : ℝ)|^521 ≤ (6683055615687/25000000000000 : ℝ)^393
        have hw : |(1848297549/5000000000 : ℝ)|=(1848297549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s1_8 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (6067053/10000000000 : ℝ)*x 0 + (1098065511/2000000000 : ℝ)*x 1 + (6355420387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6067053/10000000000 : ℝ)^521 ≤ (5434936487/100000000000000 : ℝ)^393 := by
    have hnat : (6067053 : ℕ)^521*100000000000000^393 ≤ 5434936487^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6067053 10000000000 5434936487 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098065511/2000000000 : ℝ)^521 ≤ (9032655963397/20000000000000 : ℝ)^393 := by
    have hnat : (1098065511 : ℕ)^521*20000000000000^393 ≤ 9032655963397^393*2000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098065511 2000000000 9032655963397 20000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6355420387/10000000000 : ℝ)^521 ≤ (54831285232871/100000000000000 : ℝ)^393 := by
    have hnat : (6355420387 : ℕ)^521*100000000000000^393 ≤ 54831285232871^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6355420387 10000000000 54831285232871 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6067053/10000000000 : ℝ), (1098065511/2000000000 : ℝ), (6355420387/10000000000 : ℝ)] ![(5434936487/100000000000000 : ℝ), (9032655963397/20000000000000 : ℝ), (54831285232871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6067053/10000000000 : ℝ)|^521 ≤ (5434936487/100000000000000 : ℝ)^393
        have hw : |(6067053/10000000000 : ℝ)|=(6067053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1098065511/2000000000 : ℝ)|^521 ≤ (9032655963397/20000000000000 : ℝ)^393
        have hw : |(1098065511/2000000000 : ℝ)|=(1098065511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6355420387/10000000000 : ℝ)|^521 ≤ (54831285232871/100000000000000 : ℝ)^393
        have hw : |(6355420387/10000000000 : ℝ)|=(6355420387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s1_9 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (245013271/2500000000 : ℝ)*x 0 + (-4408857761/10000000000 : ℝ)*x 1 + (1388319311/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (245013271/2500000000 : ℝ)^521 ≤ (4599385915019/100000000000000 : ℝ)^393 := by
    have hnat : (245013271 : ℕ)^521*100000000000000^393 ≤ 4599385915019^393*2500000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245013271 2500000000 4599385915019 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4408857761/10000000000 : ℝ)^521 ≤ (33766277485043/100000000000000 : ℝ)^393 := by
    have hnat : (4408857761 : ℕ)^521*100000000000000^393 ≤ 33766277485043^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4408857761 10000000000 33766277485043 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1388319311/2000000000 : ℝ)^521 ≤ (3852146036467/6250000000000 : ℝ)^393 := by
    have hnat : (1388319311 : ℕ)^521*6250000000000^393 ≤ 3852146036467^393*2000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1388319311 2000000000 3852146036467 6250000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(245013271/2500000000 : ℝ), (-4408857761/10000000000 : ℝ), (1388319311/2000000000 : ℝ)] ![(4599385915019/100000000000000 : ℝ), (33766277485043/100000000000000 : ℝ), (3852146036467/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(245013271/2500000000 : ℝ)|^521 ≤ (4599385915019/100000000000000 : ℝ)^393
        have hw : |(245013271/2500000000 : ℝ)|=(245013271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4408857761/10000000000 : ℝ)|^521 ≤ (33766277485043/100000000000000 : ℝ)^393
        have hw : |(-4408857761/10000000000 : ℝ)|=(4408857761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1388319311/2000000000 : ℝ)|^521 ≤ (3852146036467/6250000000000 : ℝ)^393
        have hw : |(1388319311/2000000000 : ℝ)|=(1388319311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s1_10 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (980045103/10000000000 : ℝ)*x 0 + (694157781/1000000000 : ℝ)*x 1 + (-4408884383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (980045103/10000000000 : ℝ)^521 ≤ (4599336261257/100000000000000 : ℝ)^393 := by
    have hnat : (980045103 : ℕ)^521*100000000000000^393 ≤ 4599336261257^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980045103 10000000000 4599336261257 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (694157781/1000000000 : ℝ)^521 ≤ (15408528984657/25000000000000 : ℝ)^393 := by
    have hnat : (694157781 : ℕ)^521*25000000000000^393 ≤ 15408528984657^393*1000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694157781 1000000000 15408528984657 25000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4408884383/10000000000 : ℝ)^521 ≤ (16883273891691/50000000000000 : ℝ)^393 := by
    have hnat : (4408884383 : ℕ)^521*50000000000000^393 ≤ 16883273891691^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4408884383 10000000000 16883273891691 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(980045103/10000000000 : ℝ), (694157781/1000000000 : ℝ), (-4408884383/10000000000 : ℝ)] ![(4599336261257/100000000000000 : ℝ), (15408528984657/25000000000000 : ℝ), (16883273891691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(980045103/10000000000 : ℝ)|^521 ≤ (4599336261257/100000000000000 : ℝ)^393
        have hw : |(980045103/10000000000 : ℝ)|=(980045103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(694157781/1000000000 : ℝ)|^521 ≤ (15408528984657/25000000000000 : ℝ)^393
        have hw : |(694157781/1000000000 : ℝ)|=(694157781/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4408884383/10000000000 : ℝ)|^521 ≤ (16883273891691/50000000000000 : ℝ)^393
        have hw : |(-4408884383/10000000000 : ℝ)|=(4408884383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s1_11 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1915798529/10000000000 : ℝ)*x 0 + (90808433/156250000 : ℝ)*x 1 + (627583253/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1915798529/10000000000 : ℝ)^521 ≤ (11184365713693/100000000000000 : ℝ)^393 := by
    have hnat : (1915798529 : ℕ)^521*100000000000000^393 ≤ 11184365713693^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915798529 10000000000 11184365713693 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90808433/156250000 : ℝ)^521 ≤ (24350659877953/50000000000000 : ℝ)^393 := by
    have hnat : (90808433 : ℕ)^521*50000000000000^393 ≤ 24350659877953^393*156250000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90808433 156250000 24350659877953 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627583253/1250000000 : ℝ)^521 ≤ (10028578628453/25000000000000 : ℝ)^393 := by
    have hnat : (627583253 : ℕ)^521*25000000000000^393 ≤ 10028578628453^393*1250000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627583253 1250000000 10028578628453 25000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1915798529/10000000000 : ℝ), (90808433/156250000 : ℝ), (627583253/1250000000 : ℝ)] ![(11184365713693/100000000000000 : ℝ), (24350659877953/50000000000000 : ℝ), (10028578628453/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1915798529/10000000000 : ℝ)|^521 ≤ (11184365713693/100000000000000 : ℝ)^393
        have hw : |(1915798529/10000000000 : ℝ)|=(1915798529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(90808433/156250000 : ℝ)|^521 ≤ (24350659877953/50000000000000 : ℝ)^393
        have hw : |(90808433/156250000 : ℝ)|=(90808433/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(627583253/1250000000 : ℝ)|^521 ≤ (10028578628453/25000000000000 : ℝ)^393
        have hw : |(627583253/1250000000 : ℝ)|=(627583253/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1143_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7474661/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27811/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (209/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1131/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1277/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27811/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (209/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27811/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (209/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27811/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (209/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27811/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (209/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27811/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (209/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27811/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (209/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (209/50000 : ℝ) ^ (8335/2048 : ℝ) ≤ (2082598827/10000000000000000000 : ℝ) := by
    have hpowers : (209/50000 : ℝ)^8335 ≤ (2082598827/10000000000000000000 : ℝ)^2048 := by
      have hnat : (209 : ℕ)^8335*10000000000000000000^2048 ≤ 2082598827^2048*50000^8335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        209 50000 2082598827 10000000000000000000 8335 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (209/50000 : ℝ)) (X := (2082598827/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27811/100000 : ℝ) ^ (8335/2048 : ℝ) ≤ (109418126563555571/20000000000000000000 : ℝ) := by
    have hpowers : (27811/100000 : ℝ)^8335 ≤ (109418126563555571/20000000000000000000 : ℝ)^2048 := by
      have hnat : (27811 : ℕ)^8335*20000000000000000000^2048 ≤ 109418126563555571^2048*100000^8335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27811 100000 109418126563555571 20000000000000000000 8335 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27811/100000 : ℝ)) (X := (109418126563555571/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000000002082598827/5000000000000000000 : ℝ) ≤ (2000000000204687/2000000000000000 : ℝ) ^ (8335/2048 : ℝ) := by
    have hpowers : (5000000002082598827/5000000000000000000 : ℝ)^2048 ≤ (2000000000204687/2000000000000000 : ℝ)^8335 := by
      have hnat : (5000000002082598827 : ℕ)^2048*2000000000000000^8335 ≤ 2000000000204687^8335*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000000002082598827 5000000000000000000 2000000000204687 2000000000000000 2048 8335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000000204687/2000000000000000 : ℝ)) (X := (5000000002082598827/5000000000000000000 : ℝ)) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (804376725229150129/800000000000000000 : ℝ) ≤ (10013414963337561/10000000000000000 : ℝ) ^ (8335/2048 : ℝ) := by
    have hpowers : (804376725229150129/800000000000000000 : ℝ)^2048 ≤ (10013414963337561/10000000000000000 : ℝ)^8335 := by
      have hnat : (804376725229150129 : ℕ)^2048*10000000000000000^8335 ≤ 10013414963337561^8335*800000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        804376725229150129 800000000000000000 10013414963337561 10000000000000000 2048 8335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013414963337561/10000000000000000 : ℝ)) (X := (804376725229150129/800000000000000000 : ℝ)) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10109418126563555571/10000000000000000000 : ℝ) ≤ (10026829925651687/10000000000000000 : ℝ) ^ (8335/2048 : ℝ) := by
    have hpowers : (10109418126563555571/10000000000000000000 : ℝ)^2048 ≤ (10026829925651687/10000000000000000 : ℝ)^8335 := by
      have hnat : (10109418126563555571 : ℕ)^2048*10000000000000000^8335 ≤ 10026829925651687^8335*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10109418126563555571 10000000000000000000 10026829925651687 10000000000000000 2048 8335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10026829925651687/10000000000000000 : ℝ)) (X := (10109418126563555571/10000000000000000000 : ℝ)) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2082598827/10000000000000000000 : ℝ) ≤ ((273918785119540345619/273930000000000000000 : ℝ)+2*(6707481157063/1369650000000000 : ℝ)*(209/50000 : ℝ))^(8335/2048 : ℝ) := by
    rw [show (273918785119540345619/273930000000000000000 : ℝ)+2*(6707481157063/1369650000000000 : ℝ)*(209/50000 : ℝ)=(2000000000204687/2000000000000000 : ℝ) by norm_num, show 1+2*(2082598827/10000000000000000000 : ℝ)=(5000000002082598827/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(109418126563555571/20000000000000000000 : ℝ)+(2082598827/10000000000000000000 : ℝ) ≤ ((273918785119540345619/273930000000000000000 : ℝ)+(6707481157063/1369650000000000 : ℝ)*((27811/100000 : ℝ)+(209/50000 : ℝ)))^(8335/2048 : ℝ) := by
    rw [show (273918785119540345619/273930000000000000000 : ℝ)+(6707481157063/1369650000000000 : ℝ)*((27811/100000 : ℝ)+(209/50000 : ℝ))=(10013414963337561/10000000000000000 : ℝ) by norm_num, show 1+(109418126563555571/20000000000000000000 : ℝ)+(2082598827/10000000000000000000 : ℝ)=(804376725229150129/800000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(109418126563555571/20000000000000000000 : ℝ) ≤ ((273918785119540345619/273930000000000000000 : ℝ)+2*(6707481157063/1369650000000000 : ℝ)*(27811/100000 : ℝ))^(8335/2048 : ℝ) := by
    rw [show (273918785119540345619/273930000000000000000 : ℝ)+2*(6707481157063/1369650000000000 : ℝ)*(27811/100000 : ℝ)=(10026829925651687/10000000000000000 : ℝ) by norm_num, show 1+2*(109418126563555571/20000000000000000000 : ℝ)=(10109418126563555571/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (273918785119540345619/273930000000000000000 : ℝ)*(X 1 0+X 2 0)+(6707481157063/1369650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8335/2048 : ℝ)) (lo := (209/50000 : ℝ)) (hi := (27811/100000 : ℝ)) (c := (273918785119540345619/273930000000000000000 : ℝ)) (alpha := (6707481157063/1369650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (273918785119540345619/273930000000000000000 : ℝ)*(X 0 1+X 2 1)+(6707481157063/1369650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8335/2048 : ℝ)) (lo := (209/50000 : ℝ)) (hi := (27811/100000 : ℝ)) (c := (273918785119540345619/273930000000000000000 : ℝ)) (alpha := (6707481157063/1369650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (273918785119540345619/273930000000000000000 : ℝ)*(X 0 2+X 1 2)+(6707481157063/1369650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8335/2048 : ℝ)) (lo := (209/50000 : ℝ)) (hi := (27811/100000 : ℝ)) (c := (273918785119540345619/273930000000000000000 : ℝ)) (alpha := (6707481157063/1369650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2096088427/10000000000 : ℝ)*X 0 0+(5701231737/10000000000 : ℝ)*X 0 1+(5002485811/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1083813177/2000000000 : ℝ)*X 1 0+(-247315027/1000000000 : ℝ)*X 1 1+(2501242549/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5419067837/10000000000 : ℝ)*X 2 0+(5002483363/10000000000 : ℝ)*X 2 1+(-2473149933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2158678219/5000000000 : ℝ)*X 0 0+(229827729/625000000 : ℝ)*X 0 1+(2533825259/5000000000 : ℝ)*X 0 2+(2158678219/5000000000 : ℝ)*X 1 0+(229827729/625000000 : ℝ)*X 1 1+(2533825259/5000000000 : ℝ)*X 1 2+(2158678219/5000000000 : ℝ)*X 2 0+(229827729/625000000 : ℝ)*X 2 1+(2533825259/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-131056109/625000000 : ℝ)*X 0 0+(5012022781/10000000000 : ℝ)*X 0 1+(35571891/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5239910891/10000000000 : ℝ)*X 1 0+(-892064293/5000000000 : ℝ)*X 1 1+(5691506249/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2619954711/5000000000 : ℝ)*X 2 0+(5691508159/10000000000 : ℝ)*X 2 1+(-892063943/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4318956521/10000000000 : ℝ)*X 0 0+(5048673159/10000000000 : ℝ)*X 0 1+(1848297549/5000000000 : ℝ)*X 0 2+(4318956521/10000000000 : ℝ)*X 1 0+(5048673159/10000000000 : ℝ)*X 1 1+(1848297549/5000000000 : ℝ)*X 1 2+(4318956521/10000000000 : ℝ)*X 2 0+(5048673159/10000000000 : ℝ)*X 2 1+(1848297549/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((6067053/10000000000 : ℝ)*X 0 0+(1098065511/2000000000 : ℝ)*X 0 1+(6355420387/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((245013271/2500000000 : ℝ)*X 1 0+(-4408857761/10000000000 : ℝ)*X 1 1+(1388319311/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((980045103/10000000000 : ℝ)*X 2 0+(694157781/1000000000 : ℝ)*X 2 1+(-4408884383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1915798529/10000000000 : ℝ)*X 0 0+(90808433/156250000 : ℝ)*X 0 1+(627583253/1250000000 : ℝ)*X 0 2+(1915798529/10000000000 : ℝ)*X 1 0+(90808433/156250000 : ℝ)*X 1 1+(627583253/1250000000 : ℝ)*X 1 2+(1915798529/10000000000 : ℝ)*X 2 0+(90808433/156250000 : ℝ)*X 2 1+(627583253/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (644845283167131726173176469/49625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (268795049175527/25000000000000 : ℝ)*(major0) + (268795049175527/25000000000000 : ℝ)*(major1) + (268795049175527/25000000000000 : ℝ)*(major2) + (1431139018585169/100000000000000 : ℝ)*(sp0) + (715569336068507/50000000000000 : ℝ)*(sp1) + (715568325435189/50000000000000 : ℝ)*(sp2) + (179803692568349/25000000000000 : ℝ)*(sp3) + (3975184089/100000000000000 : ℝ)*(sp4) + (1911730201/50000000000000 : ℝ)*(sp5) + (1054789471/20000000000000 : ℝ)*(sp6) + (271108871/100000000000000 : ℝ)*(sp8) + (769280713/100000000000000 : ℝ)*(sp9) + (335015099/25000000000000 : ℝ)*(sp10) + (1925107243/100000000000000 : ℝ)*(sp11) + (719216695380639/100000000000000 : ℝ)*(f.failure) + (1431143264878129/100000000000000 : ℝ)*(f.sum) + (300176567683127/136965000000000000000000000000 : ℝ)*base66 + (2423913743563916213/6848250000000000000000000000000000 : ℝ)*base67 + (3641660097945333787/6848250000000000000000000000000000 : ℝ)*base70 + (910683114919916213/6848250000000000000000000000000000 : ℝ)*base71 + (330545301596867/136965000000000000000000000000 : ℝ)*base74 + (5304108457979583787/6848250000000000000000000000000000 : ℝ)*base76 + (5712829963579916213/6848250000000000000000000000000000 : ℝ)*base77 + (5617780362529916213/6848250000000000000000000000000000 : ℝ)*base79 + (69356971045039/17120625000000000000000000000 : ℝ)*base82 + (2488379/500000000000000000000 : ℝ)*base89 + (2488379/500000000000000000000 : ℝ)*base91 + (2488379/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1965507199708199743421872537/1141375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12996503/25000000000000 : ℝ)*(upper3) + (16146353/10000000000000 : ℝ)*(lower4) + (552828800914277/50000000000000 : ℝ)*(major0) + (552828800914277/50000000000000 : ℝ)*(major1) + (552828800914277/50000000000000 : ℝ)*(major2) + (3471872731/100000000000000 : ℝ)*(sp1) + (6526692859/100000000000000 : ℝ)*(sp2) + (160799387/20000000000000 : ℝ)*(sp3) + (45990859714461/3125000000000 : ℝ)*(sp4) + (735853915128043/50000000000000 : ℝ)*(sp5) + (1471704775435959/100000000000000 : ℝ)*(sp6) + (739602182191657/100000000000000 : ℝ)*(sp7) + (758253213/20000000000000 : ℝ)*(sp8) + (857937953/100000000000000 : ℝ)*(sp11) + (369801922063273/50000000000000 : ℝ)*(f.failure) + (735855651064409/50000000000000 : ℝ)*(f.sum) + (688838857739039/136965000000000000000000000000 : ℝ)*base65 + (49141996926052702463/13696500000000000000000000000000000 : ℝ)*base67 + (82985875343382202463/13696500000000000000000000000000000 : ℝ)*base69 + (71953787510799202463/13696500000000000000000000000000000 : ℝ)*base71 + (440059308975359/136965000000000000000000000000 : ℝ)*base73 + (71200971509701702463/13696500000000000000000000000000000 : ℝ)*base75 + (91471030498280797537/13696500000000000000000000000000000 : ℝ)*base78 + (8126185315041202463/13696500000000000000000000000000000 : ℝ)*base79 + (1023248691936149/136965000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1225453/250000000000000000000 : ℝ)*base89 + (1225453/250000000000000000000 : ℝ)*base91 + (1225453/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1143_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7474661/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27811/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (209/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1131/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1277/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1143_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1143_s2_0 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-107463487/500000000 : ℝ)*x 0 + (5510608181/10000000000 : ℝ)*x 1 + (41274327/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107463487/500000000 : ℝ)^521 ≤ (6513107591847/50000000000000 : ℝ)^393 := by
    have hnat : (107463487 : ℕ)^521*50000000000000^393 ≤ 6513107591847^393*500000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107463487 500000000 6513107591847 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5510608181/10000000000 : ℝ)^521 ≤ (45384576396507/100000000000000 : ℝ)^393 := by
    have hnat : (5510608181 : ℕ)^521*100000000000000^393 ≤ 45384576396507^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510608181 10000000000 45384576396507 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41274327/80000000 : ℝ)^521 ≤ (1299662762443/3125000000000 : ℝ)^393 := by
    have hnat : (41274327 : ℕ)^521*3125000000000^393 ≤ 1299662762443^393*80000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41274327 80000000 1299662762443 3125000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107463487/500000000 : ℝ), (5510608181/10000000000 : ℝ), (41274327/80000000 : ℝ)] ![(6513107591847/50000000000000 : ℝ), (45384576396507/100000000000000 : ℝ), (1299662762443/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107463487/500000000 : ℝ)|^521 ≤ (6513107591847/50000000000000 : ℝ)^393
        have hw : |(-107463487/500000000 : ℝ)|=(107463487/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5510608181/10000000000 : ℝ)|^521 ≤ (45384576396507/100000000000000 : ℝ)^393
        have hw : |(5510608181/10000000000 : ℝ)|=(5510608181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41274327/80000000 : ℝ)|^521 ≤ (1299662762443/3125000000000 : ℝ)^393
        have hw : |(41274327/80000000 : ℝ)|=(41274327/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s2_1 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (671727229/1250000000 : ℝ)*x 0 + (-93276489/400000000 : ℝ)*x 1 + (2579646473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671727229/1250000000 : ℝ)^521 ≤ (43897133578917/100000000000000 : ℝ)^393 := by
    have hnat : (671727229 : ℕ)^521*100000000000000^393 ≤ 43897133578917^393*1250000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671727229 1250000000 43897133578917 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93276489/400000000 : ℝ)^521 ≤ (14513635884537/100000000000000 : ℝ)^393 := by
    have hnat : (93276489 : ℕ)^521*100000000000000^393 ≤ 14513635884537^393*400000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93276489 400000000 14513635884537 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2579646473/5000000000 : ℝ)^521 ≤ (8317846105987/20000000000000 : ℝ)^393 := by
    have hnat : (2579646473 : ℕ)^521*20000000000000^393 ≤ 8317846105987^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2579646473 5000000000 8317846105987 20000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671727229/1250000000 : ℝ), (-93276489/400000000 : ℝ), (2579646473/5000000000 : ℝ)] ![(43897133578917/100000000000000 : ℝ), (14513635884537/100000000000000 : ℝ), (8317846105987/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671727229/1250000000 : ℝ)|^521 ≤ (43897133578917/100000000000000 : ℝ)^393
        have hw : |(671727229/1250000000 : ℝ)|=(671727229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-93276489/400000000 : ℝ)|^521 ≤ (14513635884537/100000000000000 : ℝ)^393
        have hw : |(-93276489/400000000 : ℝ)|=(93276489/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2579646473/5000000000 : ℝ)|^521 ≤ (8317846105987/20000000000000 : ℝ)^393
        have hw : |(2579646473/5000000000 : ℝ)|=(2579646473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s2_2 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5373817841/10000000000 : ℝ)*x 0 + (5159292781/10000000000 : ℝ)*x 1 + (-2331912427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373817841/10000000000 : ℝ)^521 ≤ (43897133676381/100000000000000 : ℝ)^393 := by
    have hnat : (5373817841 : ℕ)^521*100000000000000^393 ≤ 43897133676381^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373817841 10000000000 43897133676381 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5159292781/10000000000 : ℝ)^521 ≤ (41589228766661/100000000000000 : ℝ)^393 := by
    have hnat : (5159292781 : ℕ)^521*100000000000000^393 ≤ 41589228766661^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5159292781 10000000000 41589228766661 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2331912427/10000000000 : ℝ)^521 ≤ (14513637551249/100000000000000 : ℝ)^393 := by
    have hnat : (2331912427 : ℕ)^521*100000000000000^393 ≤ 14513637551249^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2331912427 10000000000 14513637551249 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373817841/10000000000 : ℝ), (5159292781/10000000000 : ℝ), (-2331912427/10000000000 : ℝ)] ![(43897133676381/100000000000000 : ℝ), (41589228766661/100000000000000 : ℝ), (14513637551249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373817841/10000000000 : ℝ)|^521 ≤ (43897133676381/100000000000000 : ℝ)^393
        have hw : |(5373817841/10000000000 : ℝ)|=(5373817841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5159292781/10000000000 : ℝ)|^521 ≤ (41589228766661/100000000000000 : ℝ)^393
        have hw : |(5159292781/10000000000 : ℝ)|=(5159292781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2331912427/10000000000 : ℝ)|^521 ≤ (14513637551249/100000000000000 : ℝ)^393
        have hw : |(-2331912427/10000000000 : ℝ)|=(2331912427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s2_3 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (544230061/1250000000 : ℝ)*x 0 + (4018207319/10000000000 : ℝ)*x 1 + (117931909/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544230061/1250000000 : ℝ)^521 ≤ (415110191807/1250000000000 : ℝ)^393 := by
    have hnat : (544230061 : ℕ)^521*1250000000000^393 ≤ 415110191807^393*1250000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544230061 1250000000 415110191807 1250000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4018207319/10000000000 : ℝ)^521 ≤ (29858347926867/100000000000000 : ℝ)^393 := by
    have hnat : (4018207319 : ℕ)^521*100000000000000^393 ≤ 29858347926867^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4018207319 10000000000 29858347926867 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117931909/250000000 : ℝ)^521 ≤ (36932836712539/100000000000000 : ℝ)^393 := by
    have hnat : (117931909 : ℕ)^521*100000000000000^393 ≤ 36932836712539^393*250000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117931909 250000000 36932836712539 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544230061/1250000000 : ℝ), (4018207319/10000000000 : ℝ), (117931909/250000000 : ℝ)] ![(415110191807/1250000000000 : ℝ), (29858347926867/100000000000000 : ℝ), (36932836712539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544230061/1250000000 : ℝ)|^521 ≤ (415110191807/1250000000000 : ℝ)^393
        have hw : |(544230061/1250000000 : ℝ)|=(544230061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4018207319/10000000000 : ℝ)|^521 ≤ (29858347926867/100000000000000 : ℝ)^393
        have hw : |(4018207319/10000000000 : ℝ)|=(4018207319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(117931909/250000000 : ℝ)|^521 ≤ (36932836712539/100000000000000 : ℝ)^393
        have hw : |(117931909/250000000 : ℝ)|=(117931909/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s2_4 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1074686049/5000000000 : ℝ)*x 0 + (258085589/500000000 : ℝ)*x 1 + (2754081491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074686049/5000000000 : ℝ)^521 ≤ (1628379701407/12500000000000 : ℝ)^393 := by
    have hnat : (1074686049 : ℕ)^521*12500000000000^393 ≤ 1628379701407^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074686049 5000000000 1628379701407 12500000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258085589/500000000 : ℝ)^521 ≤ (41615081395433/100000000000000 : ℝ)^393 := by
    have hnat : (258085589 : ℕ)^521*100000000000000^393 ≤ 41615081395433^393*500000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258085589 500000000 41615081395433 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2754081491/5000000000 : ℝ)^521 ≤ (22678940488519/50000000000000 : ℝ)^393 := by
    have hnat : (2754081491 : ℕ)^521*50000000000000^393 ≤ 22678940488519^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754081491 5000000000 22678940488519 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1074686049/5000000000 : ℝ), (258085589/500000000 : ℝ), (2754081491/5000000000 : ℝ)] ![(1628379701407/12500000000000 : ℝ), (41615081395433/100000000000000 : ℝ), (22678940488519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1074686049/5000000000 : ℝ)|^521 ≤ (1628379701407/12500000000000 : ℝ)^393
        have hw : |(-1074686049/5000000000 : ℝ)|=(1074686049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(258085589/500000000 : ℝ)|^521 ≤ (41615081395433/100000000000000 : ℝ)^393
        have hw : |(258085589/500000000 : ℝ)|=(258085589/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2754081491/5000000000 : ℝ)|^521 ≤ (22678940488519/50000000000000 : ℝ)^393
        have hw : |(2754081491/5000000000 : ℝ)|=(2754081491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s2_5 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5284673571/10000000000 : ℝ)*x 0 + (-991520047/5000000000 : ℝ)*x 1 + (5508163667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284673571/10000000000 : ℝ)^521 ≤ (21467192870249/50000000000000 : ℝ)^393 := by
    have hnat : (5284673571 : ℕ)^521*50000000000000^393 ≤ 21467192870249^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284673571 10000000000 21467192870249 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (991520047/5000000000 : ℝ)^521 ≤ (2926931445117/25000000000000 : ℝ)^393 := by
    have hnat : (991520047 : ℕ)^521*25000000000000^393 ≤ 2926931445117^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991520047 5000000000 2926931445117 25000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5508163667/10000000000 : ℝ)^521 ≤ (22678944227487/50000000000000 : ℝ)^393 := by
    have hnat : (5508163667 : ℕ)^521*50000000000000^393 ≤ 22678944227487^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508163667 10000000000 22678944227487 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284673571/10000000000 : ℝ), (-991520047/5000000000 : ℝ), (5508163667/10000000000 : ℝ)] ![(21467192870249/50000000000000 : ℝ), (2926931445117/25000000000000 : ℝ), (22678944227487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284673571/10000000000 : ℝ)|^521 ≤ (21467192870249/50000000000000 : ℝ)^393
        have hw : |(5284673571/10000000000 : ℝ)|=(5284673571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-991520047/5000000000 : ℝ)|^521 ≤ (2926931445117/25000000000000 : ℝ)^393
        have hw : |(-991520047/5000000000 : ℝ)|=(991520047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5508163667/10000000000 : ℝ)|^521 ≤ (22678944227487/50000000000000 : ℝ)^393
        have hw : |(5508163667/10000000000 : ℝ)|=(5508163667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s2_6 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5284672051/10000000000 : ℝ)*x 0 + (5508163453/10000000000 : ℝ)*x 1 + (-991521243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284672051/10000000000 : ℝ)^521 ≤ (1717374774779/4000000000000 : ℝ)^393 := by
    have hnat : (5284672051 : ℕ)^521*4000000000000^393 ≤ 1717374774779^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284672051 10000000000 1717374774779 4000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5508163453/10000000000 : ℝ)^521 ≤ (45357886118801/100000000000000 : ℝ)^393 := by
    have hnat : (5508163453 : ℕ)^521*100000000000000^393 ≤ 45357886118801^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508163453 10000000000 45357886118801 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (991521243/5000000000 : ℝ)^521 ≤ (11707744502263/100000000000000 : ℝ)^393 := by
    have hnat : (991521243 : ℕ)^521*100000000000000^393 ≤ 11707744502263^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991521243 5000000000 11707744502263 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284672051/10000000000 : ℝ), (5508163453/10000000000 : ℝ), (-991521243/5000000000 : ℝ)] ![(1717374774779/4000000000000 : ℝ), (45357886118801/100000000000000 : ℝ), (11707744502263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284672051/10000000000 : ℝ)|^521 ≤ (1717374774779/4000000000000 : ℝ)^393
        have hw : |(5284672051/10000000000 : ℝ)|=(5284672051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5508163453/10000000000 : ℝ)|^521 ≤ (45357886118801/100000000000000 : ℝ)^393
        have hw : |(5508163453/10000000000 : ℝ)|=(5508163453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-991521243/5000000000 : ℝ)|^521 ≤ (11707744502263/100000000000000 : ℝ)^393
        have hw : |(-991521243/5000000000 : ℝ)|=(991521243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s2_7 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4354043249/10000000000 : ℝ)*x 0 + (4712460861/10000000000 : ℝ)*x 1 + (2011535569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354043249/10000000000 : ℝ)^521 ≤ (33210865627323/100000000000000 : ℝ)^393 := by
    have hnat : (4354043249 : ℕ)^521*100000000000000^393 ≤ 33210865627323^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354043249 10000000000 33210865627323 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4712460861/10000000000 : ℝ)^521 ≤ (2305178980783/6250000000000 : ℝ)^393 := by
    have hnat : (4712460861 : ℕ)^521*6250000000000^393 ≤ 2305178980783^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4712460861 10000000000 2305178980783 6250000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011535569/5000000000 : ℝ)^521 ≤ (5981254132217/20000000000000 : ℝ)^393 := by
    have hnat : (2011535569 : ℕ)^521*20000000000000^393 ≤ 5981254132217^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011535569 5000000000 5981254132217 20000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354043249/10000000000 : ℝ), (4712460861/10000000000 : ℝ), (2011535569/5000000000 : ℝ)] ![(33210865627323/100000000000000 : ℝ), (2305178980783/6250000000000 : ℝ), (5981254132217/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354043249/10000000000 : ℝ)|^521 ≤ (33210865627323/100000000000000 : ℝ)^393
        have hw : |(4354043249/10000000000 : ℝ)|=(4354043249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4712460861/10000000000 : ℝ)|^521 ≤ (2305178980783/6250000000000 : ℝ)^393
        have hw : |(4712460861/10000000000 : ℝ)|=(4712460861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2011535569/5000000000 : ℝ)|^521 ≤ (5981254132217/20000000000000 : ℝ)^393
        have hw : |(2011535569/5000000000 : ℝ)|=(2011535569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1143_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7474661/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1277/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1131/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (363/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16499/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1277/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1131/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1277/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1131/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1277/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1131/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1277/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1131/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1277/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1131/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1277/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1131/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1131/20000 : ℝ) ^ (8335/2048 : ℝ) ≤ (836796815243917/100000000000000000000 : ℝ) := by
    have hpowers : (1131/20000 : ℝ)^8335 ≤ (836796815243917/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1131 : ℕ)^8335*100000000000000000000^2048 ≤ 836796815243917^2048*20000^8335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1131 20000 836796815243917 100000000000000000000 8335 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1131/20000 : ℝ)) (X := (836796815243917/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1277/6250 : ℝ) ^ (8335/2048 : ℝ) ≤ (155986321181019603/100000000000000000000 : ℝ) := by
    have hpowers : (1277/6250 : ℝ)^8335 ≤ (155986321181019603/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1277 : ℕ)^8335*100000000000000000000^2048 ≤ 155986321181019603^2048*6250^8335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1277 6250 155986321181019603 100000000000000000000 8335 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1277/6250 : ℝ)) (X := (155986321181019603/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000836796815243917/50000000000000000000 : ℝ) ≤ (10000041121753107/10000000000000000 : ℝ) ^ (8335/2048 : ℝ) := by
    have hpowers : (50000836796815243917/50000000000000000000 : ℝ)^2048 ≤ (10000041121753107/10000000000000000 : ℝ)^8335 := by
      have hnat : (50000836796815243917 : ℕ)^2048*10000000000000000^8335 ≤ 10000041121753107^8335*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000836796815243917 50000000000000000000 10000041121753107 10000000000000000 2048 8335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000041121753107/10000000000000000 : ℝ)) (X := (50000836796815243917/50000000000000000000 : ℝ)) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (625980144487476647/625000000000000000 : ℝ) ≤ (2500962759332623/2500000000000000 : ℝ) ^ (8335/2048 : ℝ) := by
    have hpowers : (625980144487476647/625000000000000000 : ℝ)^2048 ≤ (2500962759332623/2500000000000000 : ℝ)^8335 := by
      have hnat : (625980144487476647 : ℕ)^2048*2500000000000000^8335 ≤ 2500962759332623^8335*625000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625980144487476647 625000000000000000 2500962759332623 2500000000000000 2048 8335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500962759332623/2500000000000000 : ℝ)) (X := (625980144487476647/625000000000000000 : ℝ)) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50155986321181019603/50000000000000000000 : ℝ) ≤ (10007660952907877/10000000000000000 : ℝ) ^ (8335/2048 : ℝ) := by
    have hpowers : (50155986321181019603/50000000000000000000 : ℝ)^2048 ≤ (10007660952907877/10000000000000000 : ℝ)^8335 := by
      have hnat : (50155986321181019603 : ℕ)^2048*10000000000000000^8335 ≤ 10007660952907877^8335*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50155986321181019603 50000000000000000000 10007660952907877 10000000000000000 2048 8335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007660952907877/10000000000000000 : ℝ)) (X := (50155986321181019603/50000000000000000000 : ℝ)) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(836796815243917/100000000000000000000 : ℝ) ≤ ((147727517510965437789/147770000000000000000 : ℝ)+2*(761983115477/295540000000000 : ℝ)*(1131/20000 : ℝ))^(8335/2048 : ℝ) := by
    rw [show (147727517510965437789/147770000000000000000 : ℝ)+2*(761983115477/295540000000000 : ℝ)*(1131/20000 : ℝ)=(10000041121753107/10000000000000000 : ℝ) by norm_num, show 1+2*(836796815243917/100000000000000000000 : ℝ)=(50000836796815243917/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(155986321181019603/100000000000000000000 : ℝ)+(836796815243917/100000000000000000000 : ℝ) ≤ ((147727517510965437789/147770000000000000000 : ℝ)+(761983115477/295540000000000 : ℝ)*((1277/6250 : ℝ)+(1131/20000 : ℝ)))^(8335/2048 : ℝ) := by
    rw [show (147727517510965437789/147770000000000000000 : ℝ)+(761983115477/295540000000000 : ℝ)*((1277/6250 : ℝ)+(1131/20000 : ℝ))=(2500962759332623/2500000000000000 : ℝ) by norm_num, show 1+(155986321181019603/100000000000000000000 : ℝ)+(836796815243917/100000000000000000000 : ℝ)=(625980144487476647/625000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(155986321181019603/100000000000000000000 : ℝ) ≤ ((147727517510965437789/147770000000000000000 : ℝ)+2*(761983115477/295540000000000 : ℝ)*(1277/6250 : ℝ))^(8335/2048 : ℝ) := by
    rw [show (147727517510965437789/147770000000000000000 : ℝ)+2*(761983115477/295540000000000 : ℝ)*(1277/6250 : ℝ)=(10007660952907877/10000000000000000 : ℝ) by norm_num, show 1+2*(155986321181019603/100000000000000000000 : ℝ)=(50155986321181019603/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (147727517510965437789/147770000000000000000 : ℝ)*(X 1 0+X 2 0)+(761983115477/295540000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8335/2048 : ℝ)) (lo := (1131/20000 : ℝ)) (hi := (1277/6250 : ℝ)) (c := (147727517510965437789/147770000000000000000 : ℝ)) (alpha := (761983115477/295540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (147727517510965437789/147770000000000000000 : ℝ)*(X 0 1+X 2 1)+(761983115477/295540000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8335/2048 : ℝ)) (lo := (1131/20000 : ℝ)) (hi := (1277/6250 : ℝ)) (c := (147727517510965437789/147770000000000000000 : ℝ)) (alpha := (761983115477/295540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (147727517510965437789/147770000000000000000 : ℝ)*(X 0 2+X 1 2)+(761983115477/295540000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8335/2048 : ℝ)) (lo := (1131/20000 : ℝ)) (hi := (1277/6250 : ℝ)) (c := (147727517510965437789/147770000000000000000 : ℝ)) (alpha := (761983115477/295540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-107463487/500000000 : ℝ)*X 0 0+(5510608181/10000000000 : ℝ)*X 0 1+(41274327/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((671727229/1250000000 : ℝ)*X 1 0+(-93276489/400000000 : ℝ)*X 1 1+(2579646473/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5373817841/10000000000 : ℝ)*X 2 0+(5159292781/10000000000 : ℝ)*X 2 1+(-2331912427/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544230061/1250000000 : ℝ)*X 0 0+(4018207319/10000000000 : ℝ)*X 0 1+(117931909/250000000 : ℝ)*X 0 2+(544230061/1250000000 : ℝ)*X 1 0+(4018207319/10000000000 : ℝ)*X 1 1+(117931909/250000000 : ℝ)*X 1 2+(544230061/1250000000 : ℝ)*X 2 0+(4018207319/10000000000 : ℝ)*X 2 1+(117931909/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1074686049/5000000000 : ℝ)*X 0 0+(258085589/500000000 : ℝ)*X 0 1+(2754081491/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5284673571/10000000000 : ℝ)*X 1 0+(-991520047/5000000000 : ℝ)*X 1 1+(5508163667/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5284672051/10000000000 : ℝ)*X 2 0+(5508163453/10000000000 : ℝ)*X 2 1+(-991521243/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4354043249/10000000000 : ℝ)*X 0 0+(4712460861/10000000000 : ℝ)*X 0 1+(2011535569/5000000000 : ℝ)*X 0 2+(4354043249/10000000000 : ℝ)*X 1 0+(4712460861/10000000000 : ℝ)*X 1 1+(2011535569/5000000000 : ℝ)*X 1 2+(4354043249/10000000000 : ℝ)*X 2 0+(4712460861/10000000000 : ℝ)*X 2 1+(2011535569/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12714548083533208122613200321/1847125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (423306827/100000000000000 : ℝ)*(base19) + (68803887/25000000000000 : ℝ)*(base23) + (59600257/100000000000000 : ℝ)*(upper2) + (243693371/100000000000000 : ℝ)*(upper3) + (14174363/10000000000000 : ℝ)*(upper4) + (1069236649585337/50000000000000 : ℝ)*(major0) + (1069236649585337/50000000000000 : ℝ)*(major1) + (1069236649585337/50000000000000 : ℝ)*(major2) + (35580609832797/1250000000000 : ℝ)*(sp0) + (711616037260211/25000000000000 : ℝ)*(sp1) + (1423232148566061/50000000000000 : ℝ)*(sp2) + (357619178970703/25000000000000 : ℝ)*(sp3) + (1578572391/10000000000000 : ℝ)*(sp4) + (158770729/3125000000000 : ℝ)*(sp7) + (71524089827307/5000000000000 : ℝ)*(f.failure) + (284646457234767/10000000000000 : ℝ)*(f.sum) + (38540292598051/7388500000000000000000000000 : ℝ)*base65 + (6131683297664085699/1055500000000000000000000000000000 : ℝ)*base67 + (2668065950020085699/1055500000000000000000000000000000 : ℝ)*base69 + (6089517824794085699/1055500000000000000000000000000000 : ℝ)*base71 + (13093491862513/7388500000000000000000000000 : ℝ)*base73 + (4672510976601914301/1055500000000000000000000000000000 : ℝ)*base76 + (6982198089927085699/1055500000000000000000000000000000 : ℝ)*base77 + (7463543889493085699/1055500000000000000000000000000000 : ℝ)*base79 + (2087506435779/1847125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (132073/25000000000000000000 : ℝ)*base90 + (132073/25000000000000000000 : ℝ)*base92 + (132073/25000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34945293315398551274115458901/7388500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40508813/6250000000000 : ℝ)*(base19) + (234683389/100000000000000 : ℝ)*(base23) + (353278169/100000000000000 : ℝ)*(upper2) + (126263209/100000000000000 : ℝ)*(upper3) + (15621709/25000000000000 : ℝ)*(upper5) + (2168482267861199/100000000000000 : ℝ)*(major0) + (2168482267861199/100000000000000 : ℝ)*(major1) + (2168482267861199/100000000000000 : ℝ)*(major2) + (4531182293/100000000000000 : ℝ)*(sp0) + (14924452097/100000000000000 : ℝ)*(sp1) + (144320212560561/5000000000000 : ℝ)*(sp4) + (360799151225051/12500000000000 : ℝ)*(sp5) + (721602136927531/25000000000000 : ℝ)*(sp6) + (181319449459079/12500000000000 : ℝ)*(sp7) + (181319449459079/12500000000000 : ℝ)*(f.failure) + (1443204391196757/50000000000000 : ℝ)*(f.sum) + (21546131838247/14777000000000000000000000000 : ℝ)*base65 + (21566606866891135573/2111000000000000000000000000000000 : ℝ)*base67 + (31288895798985135573/2111000000000000000000000000000000 : ℝ)*base69 + (20901419673586135573/2111000000000000000000000000000000 : ℝ)*base71 + (2380507005587/3694250000000000000000000000 : ℝ)*base73 + (21302072540372135573/2111000000000000000000000000000000 : ℝ)*base75 + (28666662134214135573/2111000000000000000000000000000000 : ℝ)*base77 + (32323022572062135573/2111000000000000000000000000000000 : ℝ)*base79 + (16241795227219/14777000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (477781/62500000000000000000 : ℝ)*base90 + (477781/62500000000000000000 : ℝ)*base92 + (477781/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1143_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7474661/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1277/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1131/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (363/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16499/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1143_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1143_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7474661/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (363/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16499/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1143_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1143_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1143_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7474661/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (363/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16499/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1143_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

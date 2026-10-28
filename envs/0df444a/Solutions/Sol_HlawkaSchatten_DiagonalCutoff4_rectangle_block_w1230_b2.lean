-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1230_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:14:52.177037+00:00
-- url     : https://prove2.me/submissions/8fa80a6b-da2c-4191-8409-827bef3fc738

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
theorem support_rectangle_w1230_s6_0 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-212548233/1000000000 : ℝ)*x 0 + (1347906889/2500000000 : ℝ)*x 1 + (5266856957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212548233/1000000000 : ℝ)^8423 ≤ (12924088509393/100000000000000 : ℝ)^6375 := by
    have hnat : (212548233 : ℕ)^8423*100000000000000^6375 ≤ 12924088509393^6375*1000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212548233 1000000000 12924088509393 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347906889/2500000000 : ℝ)^8423 ≤ (22105665107453/50000000000000 : ℝ)^6375 := by
    have hnat : (1347906889 : ℕ)^8423*50000000000000^6375 ≤ 22105665107453^6375*2500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347906889 2500000000 22105665107453 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266856957/10000000000 : ℝ)^8423 ≤ (8572916251011/20000000000000 : ℝ)^6375 := by
    have hnat : (5266856957 : ℕ)^8423*20000000000000^6375 ≤ 8572916251011^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266856957 10000000000 8572916251011 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-212548233/1000000000 : ℝ), (1347906889/2500000000 : ℝ), (5266856957/10000000000 : ℝ)] ![(12924088509393/100000000000000 : ℝ), (22105665107453/50000000000000 : ℝ), (8572916251011/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-212548233/1000000000 : ℝ)|^8423 ≤ (12924088509393/100000000000000 : ℝ)^6375
        have hw : |(-212548233/1000000000 : ℝ)|=(212548233/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347906889/2500000000 : ℝ)|^8423 ≤ (22105665107453/50000000000000 : ℝ)^6375
        have hw : |(1347906889/2500000000 : ℝ)|=(1347906889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266856957/10000000000 : ℝ)|^8423 ≤ (8572916251011/20000000000000 : ℝ)^6375
        have hw : |(5266856957/10000000000 : ℝ)|=(5266856957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s6_1 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344423509/10000000000 : ℝ)*x 0 + (-136796877/625000000 : ℝ)*x 1 + (82294637/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344423509/10000000000 : ℝ)^8423 ≤ (10925157174543/25000000000000 : ℝ)^6375 := by
    have hnat : (5344423509 : ℕ)^8423*25000000000000^6375 ≤ 10925157174543^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344423509 10000000000 10925157174543 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136796877/625000000 : ℝ)^8423 ≤ (671739603503/5000000000000 : ℝ)^6375 := by
    have hnat : (136796877 : ℕ)^8423*5000000000000^6375 ≤ 671739603503^6375*625000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136796877 625000000 671739603503 5000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82294637/156250000 : ℝ)^8423 ≤ (42864579222719/100000000000000 : ℝ)^6375 := by
    have hnat : (82294637 : ℕ)^8423*100000000000000^6375 ≤ 42864579222719^6375*156250000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82294637 156250000 42864579222719 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344423509/10000000000 : ℝ), (-136796877/625000000 : ℝ), (82294637/156250000 : ℝ)] ![(10925157174543/25000000000000 : ℝ), (671739603503/5000000000000 : ℝ), (42864579222719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344423509/10000000000 : ℝ)|^8423 ≤ (10925157174543/25000000000000 : ℝ)^6375
        have hw : |(5344423509/10000000000 : ℝ)|=(5344423509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-136796877/625000000 : ℝ)|^8423 ≤ (671739603503/5000000000000 : ℝ)^6375
        have hw : |(-136796877/625000000 : ℝ)|=(136796877/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82294637/156250000 : ℝ)|^8423 ≤ (42864579222719/100000000000000 : ℝ)^6375
        have hw : |(82294637/156250000 : ℝ)|=(82294637/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s6_2 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336105851/2500000000 : ℝ)*x 0 + (5266856837/10000000000 : ℝ)*x 1 + (-2188750081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336105851/2500000000 : ℝ)^8423 ≤ (43700627563781/100000000000000 : ℝ)^6375 := by
    have hnat : (1336105851 : ℕ)^8423*100000000000000^6375 ≤ 43700627563781^6375*2500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336105851 2500000000 43700627563781 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266856837/10000000000 : ℝ)^8423 ≤ (42864579964683/100000000000000 : ℝ)^6375 := by
    have hnat : (5266856837 : ℕ)^8423*100000000000000^6375 ≤ 42864579964683^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266856837 10000000000 42864579964683 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2188750081/10000000000 : ℝ)^8423 ≤ (268695849349/2000000000000 : ℝ)^6375 := by
    have hnat : (2188750081 : ℕ)^8423*2000000000000^6375 ≤ 268695849349^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188750081 10000000000 268695849349 2000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336105851/2500000000 : ℝ), (5266856837/10000000000 : ℝ), (-2188750081/10000000000 : ℝ)] ![(43700627563781/100000000000000 : ℝ), (42864579964683/100000000000000 : ℝ), (268695849349/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336105851/2500000000 : ℝ)|^8423 ≤ (43700627563781/100000000000000 : ℝ)^6375
        have hw : |(1336105851/2500000000 : ℝ)|=(1336105851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266856837/10000000000 : ℝ)|^8423 ≤ (42864579964683/100000000000000 : ℝ)^6375
        have hw : |(5266856837/10000000000 : ℝ)|=(5266856837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2188750081/10000000000 : ℝ)|^8423 ≤ (268695849349/2000000000000 : ℝ)^6375
        have hw : |(-2188750081/10000000000 : ℝ)|=(2188750081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s6_3 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4352411151/10000000000 : ℝ)*x 0 + (4227936951/10000000000 : ℝ)*x 1 + (4480456943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352411151/10000000000 : ℝ)^8423 ≤ (16658662618377/50000000000000 : ℝ)^6375 := by
    have hnat : (4352411151 : ℕ)^8423*50000000000000^6375 ≤ 16658662618377^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352411151 10000000000 16658662618377 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227936951/10000000000 : ℝ)^8423 ≤ (3206420311319/10000000000000 : ℝ)^6375 := by
    have hnat : (4227936951 : ℕ)^8423*10000000000000^6375 ≤ 3206420311319^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227936951 10000000000 3206420311319 10000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4480456943/10000000000 : ℝ)^8423 ≤ (17309235819123/50000000000000 : ℝ)^6375 := by
    have hnat : (4480456943 : ℕ)^8423*50000000000000^6375 ≤ 17309235819123^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480456943 10000000000 17309235819123 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352411151/10000000000 : ℝ), (4227936951/10000000000 : ℝ), (4480456943/10000000000 : ℝ)] ![(16658662618377/50000000000000 : ℝ), (3206420311319/10000000000000 : ℝ), (17309235819123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352411151/10000000000 : ℝ)|^8423 ≤ (16658662618377/50000000000000 : ℝ)^6375
        have hw : |(4352411151/10000000000 : ℝ)|=(4352411151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227936951/10000000000 : ℝ)|^8423 ≤ (3206420311319/10000000000000 : ℝ)^6375
        have hw : |(4227936951/10000000000 : ℝ)|=(4227936951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4480456943/10000000000 : ℝ)|^8423 ≤ (17309235819123/50000000000000 : ℝ)^6375
        have hw : |(4480456943/10000000000 : ℝ)|=(4480456943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s6_4 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2125486941/10000000000 : ℝ)*x 0 + (526717247/1000000000 : ℝ)*x 1 + (5391310983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125486941/10000000000 : ℝ)^8423 ≤ (6462062776971/50000000000000 : ℝ)^6375 := by
    have hnat : (2125486941 : ℕ)^8423*50000000000000^6375 ≤ 6462062776971^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125486941 10000000000 6462062776971 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526717247/1000000000 : ℝ)^8423 ≤ (8573594806091/20000000000000 : ℝ)^6375 := by
    have hnat : (526717247 : ℕ)^8423*20000000000000^6375 ≤ 8573594806091^6375*1000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526717247 1000000000 8573594806091 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391310983/10000000000 : ℝ)^8423 ≤ (1768316016189/4000000000000 : ℝ)^6375 := by
    have hnat : (5391310983 : ℕ)^8423*4000000000000^6375 ≤ 1768316016189^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391310983 10000000000 1768316016189 4000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2125486941/10000000000 : ℝ), (526717247/1000000000 : ℝ), (5391310983/10000000000 : ℝ)] ![(6462062776971/50000000000000 : ℝ), (8573594806091/20000000000000 : ℝ), (1768316016189/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2125486941/10000000000 : ℝ)|^8423 ≤ (6462062776971/50000000000000 : ℝ)^6375
        have hw : |(-2125486941/10000000000 : ℝ)|=(2125486941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526717247/1000000000 : ℝ)|^8423 ≤ (8573594806091/20000000000000 : ℝ)^6375
        have hw : |(526717247/1000000000 : ℝ)|=(526717247/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391310983/10000000000 : ℝ)|^8423 ≤ (1768316016189/4000000000000 : ℝ)^6375
        have hw : |(5391310983/10000000000 : ℝ)|=(5391310983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s6_5 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312613181/10000000000 : ℝ)*x 0 + (-2064295993/10000000000 : ℝ)*x 1 + (5391311279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312613181/10000000000 : ℝ)^8423 ≤ (43357287747777/100000000000000 : ℝ)^6375 := by
    have hnat : (5312613181 : ℕ)^8423*100000000000000^6375 ≤ 43357287747777^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312613181 10000000000 43357287747777 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064295993/10000000000 : ℝ)^8423 ≤ (12434808626963/100000000000000 : ℝ)^6375 := by
    have hnat : (2064295993 : ℕ)^8423*100000000000000^6375 ≤ 12434808626963^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064295993 10000000000 12434808626963 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391311279/10000000000 : ℝ)^8423 ≤ (22103951805807/50000000000000 : ℝ)^6375 := by
    have hnat : (5391311279 : ℕ)^8423*50000000000000^6375 ≤ 22103951805807^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391311279 10000000000 22103951805807 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312613181/10000000000 : ℝ), (-2064295993/10000000000 : ℝ), (5391311279/10000000000 : ℝ)] ![(43357287747777/100000000000000 : ℝ), (12434808626963/100000000000000 : ℝ), (22103951805807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312613181/10000000000 : ℝ)|^8423 ≤ (43357287747777/100000000000000 : ℝ)^6375
        have hw : |(5312613181/10000000000 : ℝ)|=(5312613181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2064295993/10000000000 : ℝ)|^8423 ≤ (12434808626963/100000000000000 : ℝ)^6375
        have hw : |(-2064295993/10000000000 : ℝ)|=(2064295993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391311279/10000000000 : ℝ)|^8423 ≤ (22103951805807/50000000000000 : ℝ)^6375
        have hw : |(5391311279/10000000000 : ℝ)|=(5391311279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s6_6 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328153261/2500000000 : ℝ)*x 0 + (673913909/1250000000 : ℝ)*x 1 + (-2064296189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328153261/2500000000 : ℝ)^8423 ≤ (43357286270503/100000000000000 : ℝ)^6375 := by
    have hnat : (1328153261 : ℕ)^8423*100000000000000^6375 ≤ 43357286270503^6375*2500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328153261 2500000000 43357286270503 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673913909/1250000000 : ℝ)^8423 ≤ (1768316141431/4000000000000 : ℝ)^6375 := by
    have hnat : (673913909 : ℕ)^8423*4000000000000^6375 ≤ 1768316141431^6375*1250000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673913909 1250000000 1768316141431 4000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064296189/10000000000 : ℝ)^8423 ≤ (1243481018691/10000000000000 : ℝ)^6375 := by
    have hnat : (2064296189 : ℕ)^8423*10000000000000^6375 ≤ 1243481018691^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064296189 10000000000 1243481018691 10000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328153261/2500000000 : ℝ), (673913909/1250000000 : ℝ), (-2064296189/10000000000 : ℝ)] ![(43357286270503/100000000000000 : ℝ), (1768316141431/4000000000000 : ℝ), (1243481018691/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328153261/2500000000 : ℝ)|^8423 ≤ (43357286270503/100000000000000 : ℝ)^6375
        have hw : |(1328153261/2500000000 : ℝ)|=(1328153261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673913909/1250000000 : ℝ)|^8423 ≤ (1768316141431/4000000000000 : ℝ)^6375
        have hw : |(673913909/1250000000 : ℝ)|=(673913909/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2064296189/10000000000 : ℝ)|^8423 ≤ (1243481018691/10000000000000 : ℝ)^6375
        have hw : |(-2064296189/10000000000 : ℝ)|=(2064296189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s6_7 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088105129/2500000000 : ℝ)*x 0 + (895963697/2000000000 : ℝ)*x 1 + (264286121/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088105129/2500000000 : ℝ)^8423 ≤ (16658709977621/50000000000000 : ℝ)^6375 := by
    have hnat : (1088105129 : ℕ)^8423*50000000000000^6375 ≤ 16658709977621^6375*2500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088105129 2500000000 16658709977621 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895963697/2000000000 : ℝ)^8423 ≤ (6922390786991/20000000000000 : ℝ)^6375 := by
    have hnat : (895963697 : ℕ)^8423*20000000000000^6375 ≤ 6922390786991^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895963697 2000000000 6922390786991 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264286121/625000000 : ℝ)^8423 ≤ (8017656524897/25000000000000 : ℝ)^6375 := by
    have hnat : (264286121 : ℕ)^8423*25000000000000^6375 ≤ 8017656524897^6375*625000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264286121 625000000 8017656524897 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088105129/2500000000 : ℝ), (895963697/2000000000 : ℝ), (264286121/625000000 : ℝ)] ![(16658709977621/50000000000000 : ℝ), (6922390786991/20000000000000 : ℝ), (8017656524897/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088105129/2500000000 : ℝ)|^8423 ≤ (16658709977621/50000000000000 : ℝ)^6375
        have hw : |(1088105129/2500000000 : ℝ)|=(1088105129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895963697/2000000000 : ℝ)|^8423 ≤ (6922390786991/20000000000000 : ℝ)^6375
        have hw : |(895963697/2000000000 : ℝ)|=(895963697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264286121/625000000 : ℝ)|^8423 ≤ (8017656524897/25000000000000 : ℝ)^6375
        have hw : |(264286121/625000000 : ℝ)|=(264286121/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1230_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (113/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5719/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (573/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14103/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (113/800 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5719/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (113/800 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5719/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (113/800 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5719/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (113/800 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5719/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (113/800 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5719/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (113/800 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5719/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5719/50000 : ℝ) ^ (4211/1024 : ℝ) ≤ (670839574106539/5000000000000000000 : ℝ) := by
    have hpowers : (5719/50000 : ℝ)^4211 ≤ (670839574106539/5000000000000000000 : ℝ)^1024 := by
      have hnat : (5719 : ℕ)^4211*5000000000000000000^1024 ≤ 670839574106539^1024*50000^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5719 50000 670839574106539 5000000000000000000 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5719/50000 : ℝ)) (X := (670839574106539/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (113/800 : ℝ) ^ (4211/1024 : ℝ) ≤ (6390333751140963/20000000000000000000 : ℝ) := by
    have hpowers : (113/800 : ℝ)^4211 ≤ (6390333751140963/20000000000000000000 : ℝ)^1024 := by
      have hnat : (113 : ℕ)^4211*20000000000000000000^1024 ≤ 6390333751140963^1024*800^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113 800 6390333751140963 20000000000000000000 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (113/800 : ℝ)) (X := (6390333751140963/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500670839574106539/2500000000000000000 : ℝ) ≤ (10000652453081593/10000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (2500670839574106539/2500000000000000000 : ℝ)^1024 ≤ (10000652453081593/10000000000000000 : ℝ)^4211 := by
      have hnat : (2500670839574106539 : ℕ)^1024*10000000000000000^4211 ≤ 10000652453081593^4211*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500670839574106539 2500000000000000000 10000652453081593 10000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000652453081593/10000000000000000 : ℝ)) (X := (2500670839574106539/2500000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009073692047567119/20000000000000000000 : ℝ) ≤ (10001103047484939/10000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (20009073692047567119/20000000000000000000 : ℝ)^1024 ≤ (10001103047484939/10000000000000000 : ℝ)^4211 := by
      have hnat : (20009073692047567119 : ℕ)^1024*10000000000000000^4211 ≤ 10001103047484939^4211*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009073692047567119 20000000000000000000 10001103047484939 10000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001103047484939/10000000000000000 : ℝ)) (X := (20009073692047567119/20000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006390333751140963/10000000000000000000 : ℝ) ≤ (2000310728377657/2000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (10006390333751140963/10000000000000000000 : ℝ)^1024 ≤ (2000310728377657/2000000000000000 : ℝ)^4211 := by
      have hnat : (10006390333751140963 : ℕ)^1024*2000000000000000^4211 ≤ 2000310728377657^4211*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006390333751140963 10000000000000000000 2000310728377657 2000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000310728377657/2000000000000000 : ℝ)) (X := (10006390333751140963/10000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(670839574106539/5000000000000000000 : ℝ) ≤ ((5372289068771859459/5374000000000000000 : ℝ)+2*(225297201673/134350000000000 : ℝ)*(5719/50000 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (5372289068771859459/5374000000000000000 : ℝ)+2*(225297201673/134350000000000 : ℝ)*(5719/50000 : ℝ)=(10000652453081593/10000000000000000 : ℝ) by norm_num, show 1+2*(670839574106539/5000000000000000000 : ℝ)=(2500670839574106539/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6390333751140963/20000000000000000000 : ℝ)+(670839574106539/5000000000000000000 : ℝ) ≤ ((5372289068771859459/5374000000000000000 : ℝ)+(225297201673/134350000000000 : ℝ)*((113/800 : ℝ)+(5719/50000 : ℝ)))^(4211/1024 : ℝ) := by
    rw [show (5372289068771859459/5374000000000000000 : ℝ)+(225297201673/134350000000000 : ℝ)*((113/800 : ℝ)+(5719/50000 : ℝ))=(10001103047484939/10000000000000000 : ℝ) by norm_num, show 1+(6390333751140963/20000000000000000000 : ℝ)+(670839574106539/5000000000000000000 : ℝ)=(20009073692047567119/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6390333751140963/20000000000000000000 : ℝ) ≤ ((5372289068771859459/5374000000000000000 : ℝ)+2*(225297201673/134350000000000 : ℝ)*(113/800 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (5372289068771859459/5374000000000000000 : ℝ)+2*(225297201673/134350000000000 : ℝ)*(113/800 : ℝ)=(2000310728377657/2000000000000000 : ℝ) by norm_num, show 1+2*(6390333751140963/20000000000000000000 : ℝ)=(10006390333751140963/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5372289068771859459/5374000000000000000 : ℝ)*(X 1 0+X 2 0)+(225297201673/134350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (5719/50000 : ℝ)) (hi := (113/800 : ℝ)) (c := (5372289068771859459/5374000000000000000 : ℝ)) (alpha := (225297201673/134350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5372289068771859459/5374000000000000000 : ℝ)*(X 0 1+X 2 1)+(225297201673/134350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (5719/50000 : ℝ)) (hi := (113/800 : ℝ)) (c := (5372289068771859459/5374000000000000000 : ℝ)) (alpha := (225297201673/134350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5372289068771859459/5374000000000000000 : ℝ)*(X 0 2+X 1 2)+(225297201673/134350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (5719/50000 : ℝ)) (hi := (113/800 : ℝ)) (c := (5372289068771859459/5374000000000000000 : ℝ)) (alpha := (225297201673/134350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-212548233/1000000000 : ℝ)*X 0 0+(1347906889/2500000000 : ℝ)*X 0 1+(5266856957/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344423509/10000000000 : ℝ)*X 1 0+(-136796877/625000000 : ℝ)*X 1 1+(82294637/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336105851/2500000000 : ℝ)*X 2 0+(5266856837/10000000000 : ℝ)*X 2 1+(-2188750081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4352411151/10000000000 : ℝ)*X 0 0+(4227936951/10000000000 : ℝ)*X 0 1+(4480456943/10000000000 : ℝ)*X 0 2+(4352411151/10000000000 : ℝ)*X 1 0+(4227936951/10000000000 : ℝ)*X 1 1+(4480456943/10000000000 : ℝ)*X 1 2+(4352411151/10000000000 : ℝ)*X 2 0+(4227936951/10000000000 : ℝ)*X 2 1+(4480456943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2125486941/10000000000 : ℝ)*X 0 0+(526717247/1000000000 : ℝ)*X 0 1+(5391310983/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312613181/10000000000 : ℝ)*X 1 0+(-2064295993/10000000000 : ℝ)*X 1 1+(5391311279/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328153261/2500000000 : ℝ)*X 2 0+(673913909/1250000000 : ℝ)*X 2 1+(-2064296189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1088105129/2500000000 : ℝ)*X 0 0+(895963697/2000000000 : ℝ)*X 0 1+(264286121/625000000 : ℝ)*X 0 2+(1088105129/2500000000 : ℝ)*X 1 0+(895963697/2000000000 : ℝ)*X 1 1+(264286121/625000000 : ℝ)*X 1 2+(1088105129/2500000000 : ℝ)*X 2 0+(895963697/2000000000 : ℝ)*X 2 1+(264286121/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (418451141827214578771457949/134350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (276535749/100000000000000 : ℝ)*(base19) + (116038239/100000000000000 : ℝ)*(base23) + (205897/1000000000000 : ℝ)*(lower3) + (2243251/20000000000000 : ℝ)*(lower4) + (15949233/100000000000000 : ℝ)*(lower5) + (2993699994655321/50000000000000 : ℝ)*(major0) + (2993699994655321/50000000000000 : ℝ)*(major1) + (2993699994655321/50000000000000 : ℝ)*(major2) + (1602942131011119/20000000000000 : ℝ)*(sp0) + (1602942075703969/20000000000000 : ℝ)*(sp1) + (8014706503079783/100000000000000 : ℝ)*(sp2) + (1980043210434651/50000000000000 : ℝ)*(sp3) + (4035937573/100000000000000 : ℝ)*(sp6) + (2798875219/100000000000000 : ℝ)*(sp7) + (3960089219744521/100000000000000 : ℝ)*(f.failure) + (1602942131011119/20000000000000 : ℝ)*(f.sum) + (61587328515943/3358750000000000000000000000 : ℝ)*base65 + (8228522085457951339/268700000000000000000000000000000 : ℝ)*base67 + (1371841142130351339/268700000000000000000000000000000 : ℝ)*base69 + (1792340647494151339/268700000000000000000000000000000 : ℝ)*base71 + (1862232183137/13435000000000000000000000000 : ℝ)*base73 + (4135948222488851339/268700000000000000000000000000000 : ℝ)*base75 + (5233606418634851339/268700000000000000000000000000000 : ℝ)*base77 + (5450359320997051339/268700000000000000000000000000000 : ℝ)*base79 + (12687455343191/6717500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (120281677/10000000000000000000000 : ℝ)*base90 + (120281677/10000000000000000000000 : ℝ)*base92 + (120281677/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (951033898128562482519694557/67175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (134263229/50000000000000 : ℝ)*(base19) + (53724511/25000000000000 : ℝ)*(base23) + (143504681/100000000000000 : ℝ)*(upper3) + (5125193/5000000000000 : ℝ)*(lower4) + (42884909/50000000000000 : ℝ)*(upper5) + (1504469695431447/25000000000000 : ℝ)*(major0) + (1504469695431447/25000000000000 : ℝ)*(major1) + (1504469695431447/25000000000000 : ℝ)*(major2) + (8786096717/50000000000000 : ℝ)*(sp1) + (1108558139/10000000000000 : ℝ)*(sp2) + (4027754541040919/50000000000000 : ℝ)*(sp4) + (4027745620680973/50000000000000 : ℝ)*(sp5) + (2013874445400601/25000000000000 : ℝ)*(sp6) + (1990124004725581/50000000000000 : ℝ)*(sp7) + (1990124004725581/50000000000000 : ℝ)*(f.failure) + (4027754541040919/50000000000000 : ℝ)*(f.sum) + (37015409620071/6717500000000000000000000000 : ℝ)*base66 + (561260478034252827/134350000000000000000000000000000 : ℝ)*base68 + (1399545223772852827/134350000000000000000000000000000 : ℝ)*base70 + (1064382458533152827/134350000000000000000000000000000 : ℝ)*base72 + (1555193019213/839687500000000000000000000 : ℝ)*base73 + (801019129923052827/134350000000000000000000000000000 : ℝ)*base76 + (1373193887590552827/134350000000000000000000000000000 : ℝ)*base78 + (1037982839916552827/134350000000000000000000000000000 : ℝ)*base80 + (5383835039881/6717500000000000000000000000 : ℝ)*base82 + (28635103/5000000000000000000000 : ℝ)*base89 + (28635103/5000000000000000000000 : ℝ)*base91 + (28635103/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1230_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (113/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5719/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (573/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1230_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1230_s7_0 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2125497219/10000000000 : ℝ)*x 0 + (539142027/1000000000 : ℝ)*x 1 + (5267054681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125497219/10000000000 : ℝ)^8423 ≤ (2584841625397/20000000000000 : ℝ)^6375 := by
    have hnat : (2125497219 : ℕ)^8423*20000000000000^6375 ≤ 2584841625397^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125497219 10000000000 2584841625397 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539142027/1000000000 : ℝ)^8423 ≤ (44209084432897/100000000000000 : ℝ)^6375 := by
    have hnat : (539142027 : ℕ)^8423*100000000000000^6375 ≤ 44209084432897^6375*1000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539142027 1000000000 44209084432897 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267054681/10000000000 : ℝ)^8423 ≤ (21433353706883/50000000000000 : ℝ)^6375 := by
    have hnat : (5267054681 : ℕ)^8423*50000000000000^6375 ≤ 21433353706883^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267054681 10000000000 21433353706883 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2125497219/10000000000 : ℝ), (539142027/1000000000 : ℝ), (5267054681/10000000000 : ℝ)] ![(2584841625397/20000000000000 : ℝ), (44209084432897/100000000000000 : ℝ), (21433353706883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2125497219/10000000000 : ℝ)|^8423 ≤ (2584841625397/20000000000000 : ℝ)^6375
        have hw : |(-2125497219/10000000000 : ℝ)|=(2125497219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539142027/1000000000 : ℝ)|^8423 ≤ (44209084432897/100000000000000 : ℝ)^6375
        have hw : |(539142027/1000000000 : ℝ)|=(539142027/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267054681/10000000000 : ℝ)|^8423 ≤ (21433353706883/50000000000000 : ℝ)^6375
        have hw : |(5267054681/10000000000 : ℝ)|=(5267054681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s7_1 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068874357/2000000000 : ℝ)*x 0 + (-1094278089/5000000000 : ℝ)*x 1 + (658381867/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068874357/2000000000 : ℝ)^8423 ≤ (10925017471821/25000000000000 : ℝ)^6375 := by
    have hnat : (1068874357 : ℕ)^8423*25000000000000^6375 ≤ 10925017471821^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068874357 2000000000 10925017471821 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094278089/5000000000 : ℝ)^8423 ≤ (209894061477/1562500000000 : ℝ)^6375 := by
    have hnat : (1094278089 : ℕ)^8423*1562500000000^6375 ≤ 209894061477^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094278089 5000000000 209894061477 1562500000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658381867/1250000000 : ℝ)^8423 ≤ (133958469237/312500000000 : ℝ)^6375 := by
    have hnat : (658381867 : ℕ)^8423*312500000000^6375 ≤ 133958469237^6375*1250000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658381867 1250000000 133958469237 312500000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068874357/2000000000 : ℝ), (-1094278089/5000000000 : ℝ), (658381867/1250000000 : ℝ)] ![(10925017471821/25000000000000 : ℝ), (209894061477/1562500000000 : ℝ), (133958469237/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068874357/2000000000 : ℝ)|^8423 ≤ (10925017471821/25000000000000 : ℝ)^6375
        have hw : |(1068874357/2000000000 : ℝ)|=(1068874357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1094278089/5000000000 : ℝ)|^8423 ≤ (209894061477/1562500000000 : ℝ)^6375
        have hw : |(-1094278089/5000000000 : ℝ)|=(1094278089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658381867/1250000000 : ℝ)|^8423 ≤ (133958469237/312500000000 : ℝ)^6375
        have hw : |(658381867/1250000000 : ℝ)|=(658381867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s7_2 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068874351/2000000000 : ℝ)*x 0 + (1316763719/2500000000 : ℝ)*x 1 + (-2188556299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068874351/2000000000 : ℝ)^8423 ≤ (21850034781587/50000000000000 : ℝ)^6375 := by
    have hnat : (1068874351 : ℕ)^8423*50000000000000^6375 ≤ 21850034781587^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068874351 2000000000 21850034781587 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316763719/2500000000 : ℝ)^8423 ≤ (21433354755323/50000000000000 : ℝ)^6375 := by
    have hnat : (1316763719 : ℕ)^8423*50000000000000^6375 ≤ 21433354755323^6375*2500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316763719 2500000000 21433354755323 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2188556299/10000000000 : ℝ)^8423 ≤ (13433220915811/100000000000000 : ℝ)^6375 := by
    have hnat : (2188556299 : ℕ)^8423*100000000000000^6375 ≤ 13433220915811^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188556299 10000000000 13433220915811 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068874351/2000000000 : ℝ), (1316763719/2500000000 : ℝ), (-2188556299/10000000000 : ℝ)] ![(21850034781587/50000000000000 : ℝ), (21433354755323/50000000000000 : ℝ), (13433220915811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068874351/2000000000 : ℝ)|^8423 ≤ (21850034781587/50000000000000 : ℝ)^6375
        have hw : |(1068874351/2000000000 : ℝ)|=(1068874351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316763719/2500000000 : ℝ)|^8423 ≤ (21433354755323/50000000000000 : ℝ)^6375
        have hw : |(1316763719/2500000000 : ℝ)|=(1316763719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2188556299/10000000000 : ℝ)|^8423 ≤ (13433220915811/100000000000000 : ℝ)^6375
        have hw : |(-2188556299/10000000000 : ℝ)|=(2188556299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s7_3 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870484363/2000000000 : ℝ)*x 0 + (1057086407/2500000000 : ℝ)*x 1 + (2240022617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870484363/2000000000 : ℝ)^8423 ≤ (6663486618691/20000000000000 : ℝ)^6375 := by
    have hnat : (870484363 : ℕ)^8423*20000000000000^6375 ≤ 6663486618691^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870484363 2000000000 6663486618691 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057086407/2500000000 : ℝ)^8423 ≤ (32068298222509/100000000000000 : ℝ)^6375 := by
    have hnat : (1057086407 : ℕ)^8423*100000000000000^6375 ≤ 32068298222509^6375*2500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057086407 2500000000 32068298222509 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2240022617/5000000000 : ℝ)^8423 ≤ (34614268669657/100000000000000 : ℝ)^6375 := by
    have hnat : (2240022617 : ℕ)^8423*100000000000000^6375 ≤ 34614268669657^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240022617 5000000000 34614268669657 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870484363/2000000000 : ℝ), (1057086407/2500000000 : ℝ), (2240022617/5000000000 : ℝ)] ![(6663486618691/20000000000000 : ℝ), (32068298222509/100000000000000 : ℝ), (34614268669657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870484363/2000000000 : ℝ)|^8423 ≤ (6663486618691/20000000000000 : ℝ)^6375
        have hw : |(870484363/2000000000 : ℝ)|=(870484363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1057086407/2500000000 : ℝ)|^8423 ≤ (32068298222509/100000000000000 : ℝ)^6375
        have hw : |(1057086407/2500000000 : ℝ)|=(1057086407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2240022617/5000000000 : ℝ)|^8423 ≤ (34614268669657/100000000000000 : ℝ)^6375
        have hw : |(2240022617/5000000000 : ℝ)|=(2240022617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s7_4 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2125501659/10000000000 : ℝ)*x 0 + (1053473597/2000000000 : ℝ)*x 1 + (5391106009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125501659/10000000000 : ℝ)^8423 ≤ (807765237363/6250000000000 : ℝ)^6375 := by
    have hnat : (2125501659 : ℕ)^8423*6250000000000^6375 ≤ 807765237363^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125501659 10000000000 807765237363 6250000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053473597/2000000000 : ℝ)^8423 ≤ (42870076475743/100000000000000 : ℝ)^6375 := by
    have hnat : (1053473597 : ℕ)^8423*100000000000000^6375 ≤ 42870076475743^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053473597 2000000000 42870076475743 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391106009/10000000000 : ℝ)^8423 ≤ (44205679713169/100000000000000 : ℝ)^6375 := by
    have hnat : (5391106009 : ℕ)^8423*100000000000000^6375 ≤ 44205679713169^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391106009 10000000000 44205679713169 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2125501659/10000000000 : ℝ), (1053473597/2000000000 : ℝ), (5391106009/10000000000 : ℝ)] ![(807765237363/6250000000000 : ℝ), (42870076475743/100000000000000 : ℝ), (44205679713169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2125501659/10000000000 : ℝ)|^8423 ≤ (807765237363/6250000000000 : ℝ)^6375
        have hw : |(-2125501659/10000000000 : ℝ)|=(2125501659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053473597/2000000000 : ℝ)|^8423 ≤ (42870076475743/100000000000000 : ℝ)^6375
        have hw : |(1053473597/2000000000 : ℝ)|=(1053473597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391106009/10000000000 : ℝ)|^8423 ≤ (44205679713169/100000000000000 : ℝ)^6375
        have hw : |(5391106009/10000000000 : ℝ)|=(5391106009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s7_5 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664083183/1250000000 : ℝ)*x 0 + (-2064505773/10000000000 : ℝ)*x 1 + (539110513/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664083183/1250000000 : ℝ)^8423 ≤ (5419731439681/12500000000000 : ℝ)^6375 := by
    have hnat : (664083183 : ℕ)^8423*12500000000000^6375 ≤ 5419731439681^6375*1250000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664083183 1250000000 5419731439681 12500000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064505773/10000000000 : ℝ)^8423 ≤ (12436478274949/100000000000000 : ℝ)^6375 := by
    have hnat : (2064505773 : ℕ)^8423*100000000000000^6375 ≤ 12436478274949^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064505773 10000000000 12436478274949 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539110513/1000000000 : ℝ)^8423 ≤ (2762854386883/6250000000000 : ℝ)^6375 := by
    have hnat : (539110513 : ℕ)^8423*6250000000000^6375 ≤ 2762854386883^6375*1000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539110513 1000000000 2762854386883 6250000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664083183/1250000000 : ℝ), (-2064505773/10000000000 : ℝ), (539110513/1000000000 : ℝ)] ![(5419731439681/12500000000000 : ℝ), (12436478274949/100000000000000 : ℝ), (2762854386883/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664083183/1250000000 : ℝ)|^8423 ≤ (5419731439681/12500000000000 : ℝ)^6375
        have hw : |(664083183/1250000000 : ℝ)|=(664083183/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2064505773/10000000000 : ℝ)|^8423 ≤ (12436478274949/100000000000000 : ℝ)^6375
        have hw : |(-2064505773/10000000000 : ℝ)|=(2064505773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539110513/1000000000 : ℝ)|^8423 ≤ (2762854386883/6250000000000 : ℝ)^6375
        have hw : |(539110513/1000000000 : ℝ)|=(539110513/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s7_6 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656332499/5000000000 : ℝ)*x 0 + (26955529/50000000 : ℝ)*x 1 + (-2064505493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656332499/5000000000 : ℝ)^8423 ≤ (338733175723/781250000000 : ℝ)^6375 := by
    have hnat : (2656332499 : ℕ)^8423*781250000000^6375 ≤ 338733175723^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656332499 5000000000 338733175723 781250000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26955529/50000000 : ℝ)^8423 ≤ (22102838724437/50000000000000 : ℝ)^6375 := by
    have hnat : (26955529 : ℕ)^8423*50000000000000^6375 ≤ 22102838724437^6375*50000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26955529 50000000 22102838724437 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064505493/10000000000 : ℝ)^8423 ≤ (621823802319/5000000000000 : ℝ)^6375 := by
    have hnat : (2064505493 : ℕ)^8423*5000000000000^6375 ≤ 621823802319^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064505493 10000000000 621823802319 5000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656332499/5000000000 : ℝ), (26955529/50000000 : ℝ), (-2064505493/10000000000 : ℝ)] ![(338733175723/781250000000 : ℝ), (22102838724437/50000000000000 : ℝ), (621823802319/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656332499/5000000000 : ℝ)|^8423 ≤ (338733175723/781250000000 : ℝ)^6375
        have hw : |(2656332499/5000000000 : ℝ)|=(2656332499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(26955529/50000000 : ℝ)|^8423 ≤ (22102838724437/50000000000000 : ℝ)^6375
        have hw : |(26955529/50000000 : ℝ)|=(26955529/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2064505493/10000000000 : ℝ)|^8423 ≤ (621823802319/5000000000000 : ℝ)^6375
        have hw : |(-2064505493/10000000000 : ℝ)|=(2064505493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s7_7 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2176214889/5000000000 : ℝ)*x 0 + (4479411181/10000000000 : ℝ)*x 1 + (4228983501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176214889/5000000000 : ℝ)^8423 ≤ (33317513632043/100000000000000 : ℝ)^6375 := by
    have hnat : (2176214889 : ℕ)^8423*100000000000000^6375 ≤ 33317513632043^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176214889 5000000000 33317513632043 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4479411181/10000000000 : ℝ)^8423 ≤ (6921559224983/20000000000000 : ℝ)^6375 := by
    have hnat : (4479411181 : ℕ)^8423*20000000000000^6375 ≤ 6921559224983^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479411181 10000000000 6921559224983 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4228983501/10000000000 : ℝ)^8423 ≤ (8018672555709/25000000000000 : ℝ)^6375 := by
    have hnat : (4228983501 : ℕ)^8423*25000000000000^6375 ≤ 8018672555709^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228983501 10000000000 8018672555709 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176214889/5000000000 : ℝ), (4479411181/10000000000 : ℝ), (4228983501/10000000000 : ℝ)] ![(33317513632043/100000000000000 : ℝ), (6921559224983/20000000000000 : ℝ), (8018672555709/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176214889/5000000000 : ℝ)|^8423 ≤ (33317513632043/100000000000000 : ℝ)^6375
        have hw : |(2176214889/5000000000 : ℝ)|=(2176214889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4479411181/10000000000 : ℝ)|^8423 ≤ (6921559224983/20000000000000 : ℝ)^6375
        have hw : |(4479411181/10000000000 : ℝ)|=(4479411181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4228983501/10000000000 : ℝ)|^8423 ≤ (8018672555709/25000000000000 : ℝ)^6375
        have hw : |(4228983501/10000000000 : ℝ)|=(4228983501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1230_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (573/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (1433/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7049/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14103/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (573/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14103/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (573/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14103/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (573/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14103/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (573/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14103/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (573/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14103/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (573/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (573/5000 : ℝ) ^ (4211/1024 : ℝ) ≤ (13523231822688679/100000000000000000000 : ℝ) := by
    have hpowers : (573/5000 : ℝ)^4211 ≤ (13523231822688679/100000000000000000000 : ℝ)^1024 := by
      have hnat : (573 : ℕ)^4211*100000000000000000000^1024 ≤ 13523231822688679^1024*5000^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        573 5000 13523231822688679 100000000000000000000 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (573/5000 : ℝ)) (X := (13523231822688679/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14103/100000 : ℝ) ^ (4211/1024 : ℝ) ≤ (31747513617104313/100000000000000000000 : ℝ) := by
    have hpowers : (14103/100000 : ℝ)^4211 ≤ (31747513617104313/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14103 : ℕ)^4211*100000000000000000000^1024 ≤ 31747513617104313^1024*100000^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14103 100000 31747513617104313 100000000000000000000 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14103/100000 : ℝ)) (X := (31747513617104313/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013523231822688679/50000000000000000000 : ℝ) ≤ (10000657628702161/10000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (50013523231822688679/50000000000000000000 : ℝ)^1024 ≤ (10000657628702161/10000000000000000 : ℝ)^4211 := by
      have hnat : (50013523231822688679 : ℕ)^1024*10000000000000000^4211 ≤ 10000657628702161^4211*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013523231822688679 50000000000000000000 10000657628702161 10000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000657628702161/10000000000000000 : ℝ)) (X := (50013523231822688679/50000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126414710794993531/3125000000000000000 : ℝ) ≤ (2500275168035761/2500000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (3126414710794993531/3125000000000000000 : ℝ)^1024 ≤ (2500275168035761/2500000000000000 : ℝ)^4211 := by
      have hnat : (3126414710794993531 : ℕ)^1024*2500000000000000^4211 ≤ 2500275168035761^4211*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126414710794993531 3125000000000000000 2500275168035761 2500000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500275168035761/2500000000000000 : ℝ)) (X := (3126414710794993531/3125000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031747513617104313/50000000000000000000 : ℝ) ≤ (10001543715583927/10000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (50031747513617104313/50000000000000000000 : ℝ)^1024 ≤ (10001543715583927/10000000000000000 : ℝ)^4211 := by
      have hnat : (50031747513617104313 : ℕ)^1024*10000000000000000^4211 ≤ 10001543715583927^4211*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031747513617104313 50000000000000000000 10001543715583927 10000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001543715583927/10000000000000000 : ℝ)) (X := (50031747513617104313/50000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13523231822688679/100000000000000000000 : ℝ) ≤ ((8807194518998257721/8810000000000000000 : ℝ)+2*(147681146961/88100000000000 : ℝ)*(573/5000 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (8807194518998257721/8810000000000000000 : ℝ)+2*(147681146961/88100000000000 : ℝ)*(573/5000 : ℝ)=(10000657628702161/10000000000000000 : ℝ) by norm_num, show 1+2*(13523231822688679/100000000000000000000 : ℝ)=(50013523231822688679/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31747513617104313/100000000000000000000 : ℝ)+(13523231822688679/100000000000000000000 : ℝ) ≤ ((8807194518998257721/8810000000000000000 : ℝ)+(147681146961/88100000000000 : ℝ)*((14103/100000 : ℝ)+(573/5000 : ℝ)))^(4211/1024 : ℝ) := by
    rw [show (8807194518998257721/8810000000000000000 : ℝ)+(147681146961/88100000000000 : ℝ)*((14103/100000 : ℝ)+(573/5000 : ℝ))=(2500275168035761/2500000000000000 : ℝ) by norm_num, show 1+(31747513617104313/100000000000000000000 : ℝ)+(13523231822688679/100000000000000000000 : ℝ)=(3126414710794993531/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31747513617104313/100000000000000000000 : ℝ) ≤ ((8807194518998257721/8810000000000000000 : ℝ)+2*(147681146961/88100000000000 : ℝ)*(14103/100000 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (8807194518998257721/8810000000000000000 : ℝ)+2*(147681146961/88100000000000 : ℝ)*(14103/100000 : ℝ)=(10001543715583927/10000000000000000 : ℝ) by norm_num, show 1+2*(31747513617104313/100000000000000000000 : ℝ)=(50031747513617104313/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8807194518998257721/8810000000000000000 : ℝ)*(X 1 0+X 2 0)+(147681146961/88100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (573/5000 : ℝ)) (hi := (14103/100000 : ℝ)) (c := (8807194518998257721/8810000000000000000 : ℝ)) (alpha := (147681146961/88100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8807194518998257721/8810000000000000000 : ℝ)*(X 0 1+X 2 1)+(147681146961/88100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (573/5000 : ℝ)) (hi := (14103/100000 : ℝ)) (c := (8807194518998257721/8810000000000000000 : ℝ)) (alpha := (147681146961/88100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8807194518998257721/8810000000000000000 : ℝ)*(X 0 2+X 1 2)+(147681146961/88100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (573/5000 : ℝ)) (hi := (14103/100000 : ℝ)) (c := (8807194518998257721/8810000000000000000 : ℝ)) (alpha := (147681146961/88100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2125497219/10000000000 : ℝ)*X 0 0+(539142027/1000000000 : ℝ)*X 0 1+(5267054681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068874357/2000000000 : ℝ)*X 1 0+(-1094278089/5000000000 : ℝ)*X 1 1+(658381867/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068874351/2000000000 : ℝ)*X 2 0+(1316763719/2500000000 : ℝ)*X 2 1+(-2188556299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((870484363/2000000000 : ℝ)*X 0 0+(1057086407/2500000000 : ℝ)*X 0 1+(2240022617/5000000000 : ℝ)*X 0 2+(870484363/2000000000 : ℝ)*X 1 0+(1057086407/2500000000 : ℝ)*X 1 1+(2240022617/5000000000 : ℝ)*X 1 2+(870484363/2000000000 : ℝ)*X 2 0+(1057086407/2500000000 : ℝ)*X 2 1+(2240022617/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2125501659/10000000000 : ℝ)*X 0 0+(1053473597/2000000000 : ℝ)*X 0 1+(5391106009/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664083183/1250000000 : ℝ)*X 1 0+(-2064505773/10000000000 : ℝ)*X 1 1+(539110513/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656332499/5000000000 : ℝ)*X 2 0+(26955529/50000000 : ℝ)*X 2 1+(-2064505493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2176214889/5000000000 : ℝ)*X 0 0+(4479411181/10000000000 : ℝ)*X 0 1+(4228983501/10000000000 : ℝ)*X 0 2+(2176214889/5000000000 : ℝ)*X 1 0+(4479411181/10000000000 : ℝ)*X 1 1+(4228983501/10000000000 : ℝ)*X 1 2+(2176214889/5000000000 : ℝ)*X 2 0+(4479411181/10000000000 : ℝ)*X 2 1+(4228983501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1590577537122792050595304989/440500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2444333/250000000000 : ℝ)*(base19) + (929910993/100000000000000 : ℝ)*(base23) + (59081859/100000000000000 : ℝ)*(lower2) + (20777889/10000000000000 : ℝ)*(upper3) + (28823287/50000000000000 : ℝ)*(lower4) + (6006960609730499/100000000000000 : ℝ)*(major0) + (6006960609730499/100000000000000 : ℝ)*(major1) + (6006960609730499/100000000000000 : ℝ)*(major2) + (8040857327293737/100000000000000 : ℝ)*(sp0) + (8040893432570989/100000000000000 : ℝ)*(sp1) + (2010223370098299/25000000000000 : ℝ)*(sp2) + (39730062709117/1000000000000 : ℝ)*(sp3) + (9270752613/25000000000000 : ℝ)*(sp4) + (816715343/4000000000000 : ℝ)*(sp7) + (993256672198819/25000000000000 : ℝ)*(f.failure) + (8040894410304189/100000000000000 : ℝ)*(f.sum) + (1029198835761/1101250000000000000000000000 : ℝ)*base65 + (13790906240024832779/881000000000000000000000000000000 : ℝ)*base67 + (6888936434669832779/881000000000000000000000000000000 : ℝ)*base69 + (12303206180294832779/881000000000000000000000000000000 : ℝ)*base71 + (3943205709913/2202500000000000000000000000 : ℝ)*base74 + (2776417211610832779/881000000000000000000000000000000 : ℝ)*base75 + (12853449165479832779/881000000000000000000000000000000 : ℝ)*base77 + (10973472216858832779/881000000000000000000000000000000 : ℝ)*base79 + (3281315113723/550625000000000000000000000 : ℝ)*base81 + (14002097/2500000000000000000000 : ℝ)*base89 + (14002097/2500000000000000000000 : ℝ)*base91 + (14002097/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3352055453178610000443/881000000000000000000000000 : ℝ) := by norm_num
    linear_combination (161232079/100000000000000 : ℝ)*(base8) + (371211093/100000000000000 : ℝ)*(upper2) + (22748339/6250000000000 : ℝ)*(lower3) + (11418137/25000000000000 : ℝ)*(upper4) + (301869762097557/5000000000000 : ℝ)*(major0) + (301869762097557/5000000000000 : ℝ)*(major1) + (301869762097557/5000000000000 : ℝ)*(major2) + (5229292863/25000000000000 : ℝ)*(sp0) + (16105589681/100000000000000 : ℝ)*(sp2) + (117279587/25000000000000 : ℝ)*(sp3) + (505100812993153/6250000000000 : ℝ)*(sp4) + (4040817043146989/50000000000000 : ℝ)*(sp5) + (8081617980704297/100000000000000 : ℝ)*(sp6) + (998288950415567/25000000000000 : ℝ)*(sp7) + (499144533847577/12500000000000 : ℝ)*(f.failure) + (4040817043146989/50000000000000 : ℝ)*(f.sum) + (1425507902171/220250000000000000000000000 : ℝ)*base65 + (1192119669471587597/44050000000000000000000000000000 : ℝ)*base67 + (304436307794987597/44050000000000000000000000000000 : ℝ)*base69 + (966938817141612403/44050000000000000000000000000000 : ℝ)*base72 + (203449909999/88100000000000000000000000 : ℝ)*base74 + (334335760856187597/44050000000000000000000000000000 : ℝ)*base75 + (268489980016062403/44050000000000000000000000000000 : ℝ)*base78 + (52174681204212403/44050000000000000000000000000000 : ℝ)*base80 + (757492630419/110125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (15546851/1250000000000000000000 : ℝ)*base89 + (15546851/1250000000000000000000 : ℝ)*base91 + (15546851/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1230_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (573/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1433/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1230_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1230_s8_0 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-66421987/312500000 : ℝ)*x 0 + (5391376843/10000000000 : ℝ)*x 1 + (65838671/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66421987/312500000 : ℝ)^8423 ≤ (6462129631603/50000000000000 : ℝ)^6375 := by
    have hnat : (66421987 : ℕ)^8423*50000000000000^6375 ≤ 6462129631603^6375*312500000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66421987 312500000 6462129631603 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391376843/10000000000 : ℝ)^8423 ≤ (11052153484691/25000000000000 : ℝ)^6375 := by
    have hnat : (5391376843 : ℕ)^8423*25000000000000^6375 ≤ 11052153484691^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391376843 10000000000 11052153484691 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65838671/125000000 : ℝ)^8423 ≤ (42867126779459/100000000000000 : ℝ)^6375 := by
    have hnat : (65838671 : ℕ)^8423*100000000000000^6375 ≤ 42867126779459^6375*125000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65838671 125000000 42867126779459 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66421987/312500000 : ℝ), (5391376843/10000000000 : ℝ), (65838671/125000000 : ℝ)] ![(6462129631603/50000000000000 : ℝ), (11052153484691/25000000000000 : ℝ), (42867126779459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66421987/312500000 : ℝ)|^8423 ≤ (6462129631603/50000000000000 : ℝ)^6375
        have hw : |(-66421987/312500000 : ℝ)|=(66421987/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391376843/10000000000 : ℝ)|^8423 ≤ (11052153484691/25000000000000 : ℝ)^6375
        have hw : |(5391376843/10000000000 : ℝ)|=(5391376843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65838671/125000000 : ℝ)|^8423 ≤ (42867126779459/100000000000000 : ℝ)^6375
        have hw : |(65838671/125000000 : ℝ)|=(65838671/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s8_1 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672179791/5000000000 : ℝ)*x 0 + (-2188519523/10000000000 : ℝ)*x 1 + (2633547421/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672179791/5000000000 : ℝ)^8423 ≤ (21849969024957/50000000000000 : ℝ)^6375 := by
    have hnat : (2672179791 : ℕ)^8423*50000000000000^6375 ≤ 21849969024957^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672179791 5000000000 21849969024957 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2188519523/10000000000 : ℝ)^8423 ≤ (2686584534273/20000000000000 : ℝ)^6375 := by
    have hnat : (2188519523 : ℕ)^8423*20000000000000^6375 ≤ 2686584534273^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188519523 10000000000 2686584534273 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633547421/5000000000 : ℝ)^8423 ≤ (21433569637371/50000000000000 : ℝ)^6375 := by
    have hnat : (2633547421 : ℕ)^8423*50000000000000^6375 ≤ 21433569637371^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633547421 5000000000 21433569637371 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672179791/5000000000 : ℝ), (-2188519523/10000000000 : ℝ), (2633547421/5000000000 : ℝ)] ![(21849969024957/50000000000000 : ℝ), (2686584534273/20000000000000 : ℝ), (21433569637371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672179791/5000000000 : ℝ)|^8423 ≤ (21849969024957/50000000000000 : ℝ)^6375
        have hw : |(2672179791/5000000000 : ℝ)|=(2672179791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2188519523/10000000000 : ℝ)|^8423 ≤ (2686584534273/20000000000000 : ℝ)^6375
        have hw : |(-2188519523/10000000000 : ℝ)|=(2188519523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633547421/5000000000 : ℝ)|^8423 ≤ (21433569637371/50000000000000 : ℝ)^6375
        have hw : |(2633547421/5000000000 : ℝ)|=(2633547421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s8_2 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344359539/10000000000 : ℝ)*x 0 + (263354719/500000000 : ℝ)*x 1 + (-8548907/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344359539/10000000000 : ℝ)^8423 ≤ (10924984396339/25000000000000 : ℝ)^6375 := by
    have hnat : (5344359539 : ℕ)^8423*25000000000000^6375 ≤ 10924984396339^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344359539 10000000000 10924984396339 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263354719/500000000 : ℝ)^8423 ≤ (21433567153369/50000000000000 : ℝ)^6375 := by
    have hnat : (263354719 : ℕ)^8423*50000000000000^6375 ≤ 21433567153369^6375*500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263354719 500000000 21433567153369 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8548907/39062500 : ℝ)^8423 ≤ (13432928096779/100000000000000 : ℝ)^6375 := by
    have hnat : (8548907 : ℕ)^8423*100000000000000^6375 ≤ 13432928096779^6375*39062500^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8548907 39062500 13432928096779 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344359539/10000000000 : ℝ), (263354719/500000000 : ℝ), (-8548907/39062500 : ℝ)] ![(10924984396339/25000000000000 : ℝ), (21433567153369/50000000000000 : ℝ), (13432928096779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344359539/10000000000 : ℝ)|^8423 ≤ (10924984396339/25000000000000 : ℝ)^6375
        have hw : |(5344359539/10000000000 : ℝ)|=(5344359539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263354719/500000000 : ℝ)|^8423 ≤ (21433567153369/50000000000000 : ℝ)^6375
        have hw : |(263354719/500000000 : ℝ)|=(263354719/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8548907/39062500 : ℝ)|^8423 ≤ (13432928096779/100000000000000 : ℝ)^6375
        have hw : |(-8548907/39062500 : ℝ)|=(8548907/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s8_3 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4352423917/10000000000 : ℝ)*x 0 + (845685859/2000000000 : ℝ)*x 1 + (69999391/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352423917/10000000000 : ℝ)^8423 ≤ (33317454353291/100000000000000 : ℝ)^6375 := by
    have hnat : (4352423917 : ℕ)^8423*100000000000000^6375 ≤ 33317454353291^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352423917 10000000000 33317454353291 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845685859/2000000000 : ℝ)^8423 ≤ (3206913661547/10000000000000 : ℝ)^6375 := by
    have hnat : (845685859 : ℕ)^8423*10000000000000^6375 ≤ 3206913661547^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845685859 2000000000 3206913661547 10000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69999391/156250000 : ℝ)^8423 ≤ (2163338063721/6250000000000 : ℝ)^6375 := by
    have hnat : (69999391 : ℕ)^8423*6250000000000^6375 ≤ 2163338063721^6375*156250000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69999391 156250000 2163338063721 6250000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352423917/10000000000 : ℝ), (845685859/2000000000 : ℝ), (69999391/156250000 : ℝ)] ![(33317454353291/100000000000000 : ℝ), (3206913661547/10000000000000 : ℝ), (2163338063721/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352423917/10000000000 : ℝ)|^8423 ≤ (33317454353291/100000000000000 : ℝ)^6375
        have hw : |(4352423917/10000000000 : ℝ)|=(4352423917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845685859/2000000000 : ℝ)|^8423 ≤ (3206913661547/10000000000000 : ℝ)^6375
        have hw : |(845685859/2000000000 : ℝ)|=(845685859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(69999391/156250000 : ℝ)|^8423 ≤ (2163338063721/6250000000000 : ℝ)^6375
        have hw : |(69999391/156250000 : ℝ)|=(69999391/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s8_4 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2125508859/10000000000 : ℝ)*x 0 + (164606447/312500000 : ℝ)*x 1 + (1078212527/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125508859/10000000000 : ℝ)^8423 ≤ (12924301642437/100000000000000 : ℝ)^6375 := by
    have hnat : (2125508859 : ℕ)^8423*100000000000000^6375 ≤ 12924301642437^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125508859 10000000000 12924301642437 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164606447/312500000 : ℝ)^8423 ≤ (42870488537097/100000000000000 : ℝ)^6375 := by
    have hnat : (164606447 : ℕ)^8423*100000000000000^6375 ≤ 42870488537097^6375*312500000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164606447 312500000 42870488537097 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078212527/2000000000 : ℝ)^8423 ≤ (8841041960409/20000000000000 : ℝ)^6375 := by
    have hnat : (1078212527 : ℕ)^8423*20000000000000^6375 ≤ 8841041960409^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078212527 2000000000 8841041960409 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2125508859/10000000000 : ℝ), (164606447/312500000 : ℝ), (1078212527/2000000000 : ℝ)] ![(12924301642437/100000000000000 : ℝ), (42870488537097/100000000000000 : ℝ), (8841041960409/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2125508859/10000000000 : ℝ)|^8423 ≤ (12924301642437/100000000000000 : ℝ)^6375
        have hw : |(-2125508859/10000000000 : ℝ)|=(2125508859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164606447/312500000 : ℝ)|^8423 ≤ (42870488537097/100000000000000 : ℝ)^6375
        have hw : |(164606447/312500000 : ℝ)|=(164606447/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078212527/2000000000 : ℝ)|^8423 ≤ (8841041960409/20000000000000 : ℝ)^6375
        have hw : |(1078212527/2000000000 : ℝ)|=(1078212527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s8_5 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312673617/10000000000 : ℝ)*x 0 + (67388279/125000000 : ℝ)*x 1 + (-2064553/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312673617/10000000000 : ℝ)^8423 ≤ (43357939431733/100000000000000 : ℝ)^6375 := by
    have hnat : (5312673617 : ℕ)^8423*100000000000000^6375 ≤ 43357939431733^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312673617 10000000000 43357939431733 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67388279/125000000 : ℝ)^8423 ≤ (552565079867/1250000000000 : ℝ)^6375 := by
    have hnat : (67388279 : ℕ)^8423*1250000000000^6375 ≤ 552565079867^6375*125000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67388279 125000000 552565079867 1250000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064553/10000000 : ℝ)^8423 ≤ (12436854164177/100000000000000 : ℝ)^6375 := by
    have hnat : (2064553 : ℕ)^8423*100000000000000^6375 ≤ 12436854164177^6375*10000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064553 10000000 12436854164177 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312673617/10000000000 : ℝ), (67388279/125000000 : ℝ), (-2064553/10000000 : ℝ)] ![(43357939431733/100000000000000 : ℝ), (552565079867/1250000000000 : ℝ), (12436854164177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312673617/10000000000 : ℝ)|^8423 ≤ (43357939431733/100000000000000 : ℝ)^6375
        have hw : |(5312673617/10000000000 : ℝ)|=(5312673617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67388279/125000000 : ℝ)|^8423 ≤ (552565079867/1250000000000 : ℝ)^6375
        have hw : |(67388279/125000000 : ℝ)|=(67388279/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2064553/10000000 : ℝ)|^8423 ≤ (12436854164177/100000000000000 : ℝ)^6375
        have hw : |(-2064553/10000000 : ℝ)|=(2064553/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s8_6 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088108053/2500000000 : ℝ)*x 0 + (4479327993/10000000000 : ℝ)*x 1 + (528633223/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088108053/2500000000 : ℝ)^8423 ≤ (1332701529991/4000000000000 : ℝ)^6375 := by
    have hnat : (1088108053 : ℕ)^8423*4000000000000^6375 ≤ 1332701529991^6375*2500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088108053 2500000000 1332701529991 4000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4479327993/10000000000 : ℝ)^8423 ≤ (3460694694637/10000000000000 : ℝ)^6375 := by
    have hnat : (4479327993 : ℕ)^8423*10000000000000^6375 ≤ 3460694694637^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479327993 10000000000 3460694694637 10000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528633223/1250000000 : ℝ)^8423 ≤ (32075514787209/100000000000000 : ℝ)^6375 := by
    have hnat : (528633223 : ℕ)^8423*100000000000000^6375 ≤ 32075514787209^6375*1250000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528633223 1250000000 32075514787209 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088108053/2500000000 : ℝ), (4479327993/10000000000 : ℝ), (528633223/1250000000 : ℝ)] ![(1332701529991/4000000000000 : ℝ), (3460694694637/10000000000000 : ℝ), (32075514787209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088108053/2500000000 : ℝ)|^8423 ≤ (1332701529991/4000000000000 : ℝ)^6375
        have hw : |(1088108053/2500000000 : ℝ)|=(1088108053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4479327993/10000000000 : ℝ)|^8423 ≤ (3460694694637/10000000000000 : ℝ)^6375
        have hw : |(4479327993/10000000000 : ℝ)|=(4479327993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528633223/1250000000 : ℝ)|^8423 ≤ (32075514787209/100000000000000 : ℝ)^6375
        have hw : |(528633223/1250000000 : ℝ)|=(528633223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1230_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1433/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2293/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7049/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7049/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1433/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7049/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1433/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7049/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1433/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7049/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1433/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7049/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1433/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7049/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1433/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1433/12500 : ℝ) ^ (4211/1024 : ℝ) ≤ (6771326533166649/50000000000000000000 : ℝ) := by
    have hpowers : (1433/12500 : ℝ)^4211 ≤ (6771326533166649/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1433 : ℕ)^4211*50000000000000000000^1024 ≤ 6771326533166649^1024*12500^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1433 12500 6771326533166649 50000000000000000000 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1433/12500 : ℝ)) (X := (6771326533166649/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7049/50000 : ℝ) ^ (4211/1024 : ℝ) ≤ (990664148032197/3125000000000000000 : ℝ) := by
    have hpowers : (7049/50000 : ℝ)^4211 ≤ (990664148032197/3125000000000000000 : ℝ)^1024 := by
      have hnat : (7049 : ℕ)^4211*3125000000000000000^1024 ≤ 990664148032197^1024*50000^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7049 50000 990664148032197 3125000000000000000 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7049/50000 : ℝ)) (X := (990664148032197/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006771326533166649/25000000000000000000 : ℝ) ≤ (2000131714610351/2000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (25006771326533166649/25000000000000000000 : ℝ)^1024 ≤ (2000131714610351/2000000000000000 : ℝ)^4211 := by
      have hnat : (25006771326533166649 : ℕ)^1024*2000000000000000^4211 ≤ 2000131714610351^4211*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006771326533166649 25000000000000000000 2000131714610351 2000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000131714610351/2000000000000000 : ℝ)) (X := (25006771326533166649/25000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022621952901681801/50000000000000000000 : ℝ) ≤ (5000550009849987/5000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (50022621952901681801/50000000000000000000 : ℝ)^1024 ≤ (5000550009849987/5000000000000000 : ℝ)^4211 := by
      have hnat : (50022621952901681801 : ℕ)^1024*5000000000000000^4211 ≤ 5000550009849987^4211*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022621952901681801 50000000000000000000 5000550009849987 5000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000550009849987/5000000000000000 : ℝ)) (X := (50022621952901681801/50000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563490664148032197/1562500000000000000 : ℝ) ≤ (10001541466348193/10000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (1563490664148032197/1562500000000000000 : ℝ)^1024 ≤ (10001541466348193/10000000000000000 : ℝ)^4211 := by
      have hnat : (1563490664148032197 : ℕ)^1024*10000000000000000^4211 ≤ 10001541466348193^4211*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563490664148032197 1562500000000000000 10001541466348193 10000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001541466348193/10000000000000000 : ℝ)) (X := (1563490664148032197/1562500000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6771326533166649/50000000000000000000 : ℝ) ≤ ((13165806596333978719/13170000000000000000 : ℝ)+2*(441446648219/263400000000000 : ℝ)*(1433/12500 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (13165806596333978719/13170000000000000000 : ℝ)+2*(441446648219/263400000000000 : ℝ)*(1433/12500 : ℝ)=(2000131714610351/2000000000000000 : ℝ) by norm_num, show 1+2*(6771326533166649/50000000000000000000 : ℝ)=(25006771326533166649/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(990664148032197/3125000000000000000 : ℝ)+(6771326533166649/50000000000000000000 : ℝ) ≤ ((13165806596333978719/13170000000000000000 : ℝ)+(441446648219/263400000000000 : ℝ)*((7049/50000 : ℝ)+(1433/12500 : ℝ)))^(4211/1024 : ℝ) := by
    rw [show (13165806596333978719/13170000000000000000 : ℝ)+(441446648219/263400000000000 : ℝ)*((7049/50000 : ℝ)+(1433/12500 : ℝ))=(5000550009849987/5000000000000000 : ℝ) by norm_num, show 1+(990664148032197/3125000000000000000 : ℝ)+(6771326533166649/50000000000000000000 : ℝ)=(50022621952901681801/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(990664148032197/3125000000000000000 : ℝ) ≤ ((13165806596333978719/13170000000000000000 : ℝ)+2*(441446648219/263400000000000 : ℝ)*(7049/50000 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (13165806596333978719/13170000000000000000 : ℝ)+2*(441446648219/263400000000000 : ℝ)*(7049/50000 : ℝ)=(10001541466348193/10000000000000000 : ℝ) by norm_num, show 1+2*(990664148032197/3125000000000000000 : ℝ)=(1563490664148032197/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13165806596333978719/13170000000000000000 : ℝ)*(X 1 0+X 2 0)+(441446648219/263400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (1433/12500 : ℝ)) (hi := (7049/50000 : ℝ)) (c := (13165806596333978719/13170000000000000000 : ℝ)) (alpha := (441446648219/263400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13165806596333978719/13170000000000000000 : ℝ)*(X 0 1+X 2 1)+(441446648219/263400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (1433/12500 : ℝ)) (hi := (7049/50000 : ℝ)) (c := (13165806596333978719/13170000000000000000 : ℝ)) (alpha := (441446648219/263400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13165806596333978719/13170000000000000000 : ℝ)*(X 0 2+X 1 2)+(441446648219/263400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (1433/12500 : ℝ)) (hi := (7049/50000 : ℝ)) (c := (13165806596333978719/13170000000000000000 : ℝ)) (alpha := (441446648219/263400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-66421987/312500000 : ℝ)*X 0 0+(5391376843/10000000000 : ℝ)*X 0 1+(65838671/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672179791/5000000000 : ℝ)*X 1 0+(-2188519523/10000000000 : ℝ)*X 1 1+(2633547421/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344359539/10000000000 : ℝ)*X 2 0+(263354719/500000000 : ℝ)*X 2 1+(-8548907/39062500 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4352423917/10000000000 : ℝ)*X 0 0+(845685859/2000000000 : ℝ)*X 0 1+(69999391/156250000 : ℝ)*X 0 2+(4352423917/10000000000 : ℝ)*X 1 0+(845685859/2000000000 : ℝ)*X 1 1+(69999391/156250000 : ℝ)*X 1 2+(4352423917/10000000000 : ℝ)*X 2 0+(845685859/2000000000 : ℝ)*X 2 1+(69999391/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2125508859/10000000000 : ℝ)*X 0 0+(164606447/312500000 : ℝ)*X 0 1+(1078212527/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312673617/10000000000 : ℝ)*X 2 0+(67388279/125000000 : ℝ)*X 2 1+(-2064553/10000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s8_5 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1088108053/2500000000 : ℝ)*X 0 0+(4479327993/10000000000 : ℝ)*X 0 1+(528633223/1250000000 : ℝ)*X 0 2+(1088108053/2500000000 : ℝ)*X 1 0+(4479327993/10000000000 : ℝ)*X 1 1+(528633223/1250000000 : ℝ)*X 1 2+(1088108053/2500000000 : ℝ)*X 2 0+(4479327993/10000000000 : ℝ)*X 2 1+(528633223/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s8_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (119515494073807697581250757/27437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42714599/50000000000000 : ℝ)*(base23) + (138224001/100000000000000 : ℝ)*(upper2) + (512178897/100000000000000 : ℝ)*(upper3) + (3016277/100000000000000 : ℝ)*(upper4) + (751369450491597/12500000000000 : ℝ)*(major0) + (751369450491597/12500000000000 : ℝ)*(major1) + (751369450491597/12500000000000 : ℝ)*(major2) + (2011551991146569/25000000000000 : ℝ)*(sp0) + (4023121034725049/50000000000000 : ℝ)*(sp1) + (8046224641159561/100000000000000 : ℝ)*(sp2) + (397565111424923/10000000000000 : ℝ)*(sp3) + (34104863823/100000000000000 : ℝ)*(sp4) + (8671430669/50000000000000 : ℝ)*(sp5) + (17878968937/100000000000000 : ℝ)*(sp6) + (3975668993218167/100000000000000 : ℝ)*(f.failure) + (4023121034725049/50000000000000 : ℝ)*(f.sum) + (128544432197211/2195000000000000000000000000 : ℝ)*base66 + (667091623430033081/54875000000000000000000000000000 : ℝ)*base67 + (224373333927783081/54875000000000000000000000000000 : ℝ)*base69 + (4317538180910091919/54875000000000000000000000000000 : ℝ)*base72 + (5809824088109/2195000000000000000000000000 : ℝ)*base73 + (1273621459376658081/54875000000000000000000000000000 : ℝ)*base75 + (191826216943966919/54875000000000000000000000000000 : ℝ)*base78 + (1223019027590033081/54875000000000000000000000000000 : ℝ)*base79 + (2332755076551/548750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (94940979/10000000000000000000000 : ℝ)*base90 + (94940979/10000000000000000000000 : ℝ)*base92 + (94940979/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1230_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1433/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2293/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1230_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1230_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (113/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5719/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2293/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1230_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1230_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1230_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (113/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5719/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2293/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1230_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

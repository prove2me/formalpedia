-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1665_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:19:03.810387+00:00
-- url     : https://prove2.me/submissions/a0a3ed04-1a72-4dc2-b2cb-21c153e5b9fc

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
theorem support_rectangle_w1665_s3_0 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-787512787/5000000000 : ℝ)*x 0 + (5443179287/10000000000 : ℝ)*x 1 + (2592381079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (787512787/5000000000 : ℝ)^4979 ≤ (9760119218853/100000000000000 : ℝ)^3955 := by
    have hnat : (787512787 : ℕ)^4979*100000000000000^3955 ≤ 9760119218853^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      787512787 5000000000 9760119218853 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443179287/10000000000 : ℝ)^4979 ≤ (23250458368433/50000000000000 : ℝ)^3955 := by
    have hnat : (5443179287 : ℕ)^4979*50000000000000^3955 ≤ 23250458368433^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443179287 10000000000 23250458368433 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2592381079/5000000000 : ℝ)^4979 ≤ (43738964034641/100000000000000 : ℝ)^3955 := by
    have hnat : (2592381079 : ℕ)^4979*100000000000000^3955 ≤ 43738964034641^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592381079 5000000000 43738964034641 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-787512787/5000000000 : ℝ), (5443179287/10000000000 : ℝ), (2592381079/5000000000 : ℝ)] ![(9760119218853/100000000000000 : ℝ), (23250458368433/50000000000000 : ℝ), (43738964034641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-787512787/5000000000 : ℝ)|^4979 ≤ (9760119218853/100000000000000 : ℝ)^3955
        have hw : |(-787512787/5000000000 : ℝ)|=(787512787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443179287/10000000000 : ℝ)|^4979 ≤ (23250458368433/50000000000000 : ℝ)^3955
        have hw : |(5443179287/10000000000 : ℝ)|=(5443179287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2592381079/5000000000 : ℝ)|^4979 ≤ (43738964034641/100000000000000 : ℝ)^3955
        have hw : |(2592381079/5000000000 : ℝ)|=(2592381079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s3_1 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668184743/1250000000 : ℝ)*x 0 + (-853989733/5000000000 : ℝ)*x 1 + (5184762221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668184743/1250000000 : ℝ)^4979 ≤ (9090521118391/20000000000000 : ℝ)^3955 := by
    have hnat : (668184743 : ℕ)^4979*20000000000000^3955 ≤ 9090521118391^3955*1250000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668184743 1250000000 9090521118391 20000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (853989733/5000000000 : ℝ)^4979 ≤ (675526855657/6250000000000 : ℝ)^3955 := by
    have hnat : (853989733 : ℕ)^4979*6250000000000^3955 ≤ 675526855657^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853989733 5000000000 675526855657 6250000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184762221/10000000000 : ℝ)^4979 ≤ (21869482351859/50000000000000 : ℝ)^3955 := by
    have hnat : (5184762221 : ℕ)^4979*50000000000000^3955 ≤ 21869482351859^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184762221 10000000000 21869482351859 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668184743/1250000000 : ℝ), (-853989733/5000000000 : ℝ), (5184762221/10000000000 : ℝ)] ![(9090521118391/20000000000000 : ℝ), (675526855657/6250000000000 : ℝ), (21869482351859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668184743/1250000000 : ℝ)|^4979 ≤ (9090521118391/20000000000000 : ℝ)^3955
        have hw : |(668184743/1250000000 : ℝ)|=(668184743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-853989733/5000000000 : ℝ)|^4979 ≤ (675526855657/6250000000000 : ℝ)^3955
        have hw : |(-853989733/5000000000 : ℝ)|=(853989733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184762221/10000000000 : ℝ)|^4979 ≤ (21869482351859/50000000000000 : ℝ)^3955
        have hw : |(5184762221/10000000000 : ℝ)|=(5184762221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s3_2 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345477987/10000000000 : ℝ)*x 0 + (1036952431/2000000000 : ℝ)*x 1 + (-1707979497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345477987/10000000000 : ℝ)^4979 ≤ (181810424209/400000000000 : ℝ)^3955 := by
    have hnat : (5345477987 : ℕ)^4979*400000000000^3955 ≤ 181810424209^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345477987 10000000000 181810424209 400000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036952431/2000000000 : ℝ)^4979 ≤ (2186948200139/5000000000000 : ℝ)^3955 := by
    have hnat : (1036952431 : ℕ)^4979*5000000000000^3955 ≤ 2186948200139^3955*2000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036952431 2000000000 2186948200139 5000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1707979497/10000000000 : ℝ)^4979 ≤ (5404214968739/50000000000000 : ℝ)^3955 := by
    have hnat : (1707979497 : ℕ)^4979*50000000000000^3955 ≤ 5404214968739^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1707979497 10000000000 5404214968739 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345477987/10000000000 : ℝ), (1036952431/2000000000 : ℝ), (-1707979497/10000000000 : ℝ)] ![(181810424209/400000000000 : ℝ), (2186948200139/5000000000000 : ℝ), (5404214968739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345477987/10000000000 : ℝ)|^4979 ≤ (181810424209/400000000000 : ℝ)^3955
        have hw : |(5345477987/10000000000 : ℝ)|=(5345477987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036952431/2000000000 : ℝ)|^4979 ≤ (2186948200139/5000000000000 : ℝ)^3955
        have hw : |(1036952431/2000000000 : ℝ)|=(1036952431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1707979497/10000000000 : ℝ)|^4979 ≤ (5404214968739/50000000000000 : ℝ)^3955
        have hw : |(-1707979497/10000000000 : ℝ)|=(1707979497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s3_3 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4169373741/10000000000 : ℝ)*x 0 + (191931363/500000000 : ℝ)*x 1 + (2259933681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4169373741/10000000000 : ℝ)^4979 ≤ (16621580492849/50000000000000 : ℝ)^3955 := by
    have hnat : (4169373741 : ℕ)^4979*50000000000000^3955 ≤ 16621580492849^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169373741 10000000000 16621580492849 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (191931363/500000000 : ℝ)^4979 ≤ (14979033415849/50000000000000 : ℝ)^3955 := by
    have hnat : (191931363 : ℕ)^4979*50000000000000^3955 ≤ 14979033415849^3955*500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191931363 500000000 14979033415849 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259933681/5000000000 : ℝ)^4979 ≤ (36798772155613/100000000000000 : ℝ)^3955 := by
    have hnat : (2259933681 : ℕ)^4979*100000000000000^3955 ≤ 36798772155613^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259933681 5000000000 36798772155613 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4169373741/10000000000 : ℝ), (191931363/500000000 : ℝ), (2259933681/5000000000 : ℝ)] ![(16621580492849/50000000000000 : ℝ), (14979033415849/50000000000000 : ℝ), (36798772155613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4169373741/10000000000 : ℝ)|^4979 ≤ (16621580492849/50000000000000 : ℝ)^3955
        have hw : |(4169373741/10000000000 : ℝ)|=(4169373741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(191931363/500000000 : ℝ)|^4979 ≤ (14979033415849/50000000000000 : ℝ)^3955
        have hw : |(191931363/500000000 : ℝ)|=(191931363/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2259933681/5000000000 : ℝ)|^4979 ≤ (36798772155613/100000000000000 : ℝ)^3955
        have hw : |(2259933681/5000000000 : ℝ)|=(2259933681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s3_4 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-787543967/5000000000 : ℝ)*x 0 + (2593365451/5000000000 : ℝ)*x 1 + (1360297439/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (787543967/5000000000 : ℝ)^4979 ≤ (9760605706127/100000000000000 : ℝ)^3955 := by
    have hnat : (787543967 : ℕ)^4979*100000000000000^3955 ≤ 9760605706127^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      787543967 5000000000 9760605706127 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593365451/5000000000 : ℝ)^4979 ≤ (43759873642391/100000000000000 : ℝ)^3955 := by
    have hnat : (2593365451 : ℕ)^4979*100000000000000^3955 ≤ 43759873642391^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593365451 5000000000 43759873642391 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360297439/2500000000 : ℝ)^4979 ≤ (9295904126847/20000000000000 : ℝ)^3955 := by
    have hnat : (1360297439 : ℕ)^4979*20000000000000^3955 ≤ 9295904126847^3955*2500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360297439 2500000000 9295904126847 20000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-787543967/5000000000 : ℝ), (2593365451/5000000000 : ℝ), (1360297439/2500000000 : ℝ)] ![(9760605706127/100000000000000 : ℝ), (43759873642391/100000000000000 : ℝ), (9295904126847/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-787543967/5000000000 : ℝ)|^4979 ≤ (9760605706127/100000000000000 : ℝ)^3955
        have hw : |(-787543967/5000000000 : ℝ)|=(787543967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593365451/5000000000 : ℝ)|^4979 ≤ (43759873642391/100000000000000 : ℝ)^3955
        have hw : |(2593365451/5000000000 : ℝ)|=(2593365451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360297439/2500000000 : ℝ)|^4979 ≤ (9295904126847/20000000000000 : ℝ)^3955
        have hw : |(1360297439/2500000000 : ℝ)|=(1360297439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s3_5 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638164189/5000000000 : ℝ)*x 0 + (-290310381/2000000000 : ℝ)*x 1 + (5441189747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638164189/5000000000 : ℝ)^4979 ≤ (22356817552773/50000000000000 : ℝ)^3955 := by
    have hnat : (2638164189 : ℕ)^4979*50000000000000^3955 ≤ 22356817552773^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638164189 5000000000 22356817552773 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (290310381/2000000000 : ℝ)^4979 ≤ (1761368867561/20000000000000 : ℝ)^3955 := by
    have hnat : (290310381 : ℕ)^4979*20000000000000^3955 ≤ 1761368867561^3955*2000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290310381 2000000000 1761368867561 20000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5441189747/10000000000 : ℝ)^4979 ≤ (929590410749/2000000000000 : ℝ)^3955 := by
    have hnat : (5441189747 : ℕ)^4979*2000000000000^3955 ≤ 929590410749^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441189747 10000000000 929590410749 2000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638164189/5000000000 : ℝ), (-290310381/2000000000 : ℝ), (5441189747/10000000000 : ℝ)] ![(22356817552773/50000000000000 : ℝ), (1761368867561/20000000000000 : ℝ), (929590410749/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638164189/5000000000 : ℝ)|^4979 ≤ (22356817552773/50000000000000 : ℝ)^3955
        have hw : |(2638164189/5000000000 : ℝ)|=(2638164189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-290310381/2000000000 : ℝ)|^4979 ≤ (1761368867561/20000000000000 : ℝ)^3955
        have hw : |(-290310381/2000000000 : ℝ)|=(290310381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5441189747/10000000000 : ℝ)|^4979 ≤ (929590410749/2000000000000 : ℝ)^3955
        have hw : |(5441189747/10000000000 : ℝ)|=(5441189747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s3_6 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638164163/5000000000 : ℝ)*x 0 + (1360297461/2500000000 : ℝ)*x 1 + (-1451551843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638164163/5000000000 : ℝ)^4979 ≤ (44713634550783/100000000000000 : ℝ)^3955 := by
    have hnat : (2638164163 : ℕ)^4979*100000000000000^3955 ≤ 44713634550783^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638164163 5000000000 44713634550783 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360297461/2500000000 : ℝ)^4979 ≤ (11619880395143/25000000000000 : ℝ)^3955 := by
    have hnat : (1360297461 : ℕ)^4979*25000000000000^3955 ≤ 11619880395143^3955*2500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360297461 2500000000 11619880395143 25000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1451551843/10000000000 : ℝ)^4979 ≤ (1761368772849/20000000000000 : ℝ)^3955 := by
    have hnat : (1451551843 : ℕ)^4979*20000000000000^3955 ≤ 1761368772849^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1451551843 10000000000 1761368772849 20000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638164163/5000000000 : ℝ), (1360297461/2500000000 : ℝ), (-1451551843/10000000000 : ℝ)] ![(44713634550783/100000000000000 : ℝ), (11619880395143/25000000000000 : ℝ), (1761368772849/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638164163/5000000000 : ℝ)|^4979 ≤ (44713634550783/100000000000000 : ℝ)^3955
        have hw : |(2638164163/5000000000 : ℝ)|=(2638164163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360297461/2500000000 : ℝ)|^4979 ≤ (11619880395143/25000000000000 : ℝ)^3955
        have hw : |(1360297461/2500000000 : ℝ)|=(1360297461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1451551843/10000000000 : ℝ)|^4979 ≤ (1761368772849/20000000000000 : ℝ)^3955
        have hw : |(-1451551843/10000000000 : ℝ)|=(1451551843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s3_7 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (833907593/2000000000 : ℝ)*x 0 + (4514677421/10000000000 : ℝ)*x 1 + (1921935963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (833907593/2000000000 : ℝ)^4979 ≤ (33244809398447/100000000000000 : ℝ)^3955 := by
    have hnat : (833907593 : ℕ)^4979*100000000000000^3955 ≤ 33244809398447^3955*2000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833907593 2000000000 33244809398447 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514677421/10000000000 : ℝ)^4979 ≤ (7349117138359/20000000000000 : ℝ)^3955 := by
    have hnat : (4514677421 : ℕ)^4979*20000000000000^3955 ≤ 7349117138359^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514677421 10000000000 7349117138359 20000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1921935963/5000000000 : ℝ)^4979 ≤ (30009604895577/100000000000000 : ℝ)^3955 := by
    have hnat : (1921935963 : ℕ)^4979*100000000000000^3955 ≤ 30009604895577^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921935963 5000000000 30009604895577 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(833907593/2000000000 : ℝ), (4514677421/10000000000 : ℝ), (1921935963/5000000000 : ℝ)] ![(33244809398447/100000000000000 : ℝ), (7349117138359/20000000000000 : ℝ), (30009604895577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(833907593/2000000000 : ℝ)|^4979 ≤ (33244809398447/100000000000000 : ℝ)^3955
        have hw : |(833907593/2000000000 : ℝ)|=(833907593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514677421/10000000000 : ℝ)|^4979 ≤ (7349117138359/20000000000000 : ℝ)^3955
        have hw : |(4514677421/10000000000 : ℝ)|=(4514677421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1921935963/5000000000 : ℝ)|^4979 ≤ (30009604895577/100000000000000 : ℝ)^3955
        have hw : |(1921935963/5000000000 : ℝ)|=(1921935963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1665_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181810191/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8149/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10691/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5371/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16241/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8149/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10691/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8149/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10691/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8149/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10691/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8149/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10691/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8149/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10691/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8149/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10691/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10691/100000 : ℝ) ^ (4975/1024 : ℝ) ≤ (1916832522814799/100000000000000000000 : ℝ) := by
    have hpowers : (10691/100000 : ℝ)^4975 ≤ (1916832522814799/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10691 : ℕ)^4975*100000000000000000000^1024 ≤ 1916832522814799^1024*100000^4975 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10691 100000 1916832522814799 100000000000000000000 4975 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10691/100000 : ℝ)) (X := (1916832522814799/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8149/50000 : ℝ) ^ (4975/1024 : ℝ) ≤ (297347694316813/2000000000000000000 : ℝ) := by
    have hpowers : (8149/50000 : ℝ)^4975 ≤ (297347694316813/2000000000000000000 : ℝ)^1024 := by
      have hnat : (8149 : ℕ)^4975*2000000000000000000^1024 ≤ 297347694316813^1024*50000^4975 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8149 50000 297347694316813 2000000000000000000 4975 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8149/50000 : ℝ)) (X := (297347694316813/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001916832522814799/50000000000000000000 : ℝ) ≤ (10000078906798953/10000000000000000 : ℝ) ^ (4975/1024 : ℝ) := by
    have hpowers : (50001916832522814799/50000000000000000000 : ℝ)^1024 ≤ (10000078906798953/10000000000000000 : ℝ)^4975 := by
      have hnat : (50001916832522814799 : ℕ)^1024*10000000000000000^4975 ≤ 10000078906798953^4975*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001916832522814799 50000000000000000000 10000078906798953 10000000000000000 1024 4975 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000078906798953/10000000000000000 : ℝ)) (X := (50001916832522814799/50000000000000000000 : ℝ)) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100016784217238655449/100000000000000000000 : ℝ) ≤ (10000345445087259/10000000000000000 : ℝ) ^ (4975/1024 : ℝ) := by
    have hpowers : (100016784217238655449/100000000000000000000 : ℝ)^1024 ≤ (10000345445087259/10000000000000000 : ℝ)^4975 := by
      have hnat : (100016784217238655449 : ℕ)^1024*10000000000000000^4975 ≤ 10000345445087259^4975*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100016784217238655449 100000000000000000000 10000345445087259 10000000000000000 1024 4975 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000345445087259/10000000000000000 : ℝ)) (X := (100016784217238655449/100000000000000000000 : ℝ)) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000297347694316813/1000000000000000000 : ℝ) ≤ (2000122396675113/2000000000000000 : ℝ) ^ (4975/1024 : ℝ) := by
    have hpowers : (1000297347694316813/1000000000000000000 : ℝ)^1024 ≤ (2000122396675113/2000000000000000 : ℝ)^4975 := by
      have hnat : (1000297347694316813 : ℕ)^1024*2000000000000000^4975 ≤ 2000122396675113^4975*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000297347694316813 1000000000000000000 2000122396675113 2000000000000000 1024 4975 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000122396675113/2000000000000000 : ℝ)) (X := (1000297347694316813/1000000000000000000 : ℝ)) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1916832522814799/100000000000000000000 : ℝ) ≤ ((18688247769580390193/18690000000000000000 : ℝ)+2*(44423048051/93450000000000 : ℝ)*(10691/100000 : ℝ))^(4975/1024 : ℝ) := by
    rw [show (18688247769580390193/18690000000000000000 : ℝ)+2*(44423048051/93450000000000 : ℝ)*(10691/100000 : ℝ)=(10000078906798953/10000000000000000 : ℝ) by norm_num, show 1+2*(1916832522814799/100000000000000000000 : ℝ)=(50001916832522814799/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(297347694316813/2000000000000000000 : ℝ)+(1916832522814799/100000000000000000000 : ℝ) ≤ ((18688247769580390193/18690000000000000000 : ℝ)+(44423048051/93450000000000 : ℝ)*((8149/50000 : ℝ)+(10691/100000 : ℝ)))^(4975/1024 : ℝ) := by
    rw [show (18688247769580390193/18690000000000000000 : ℝ)+(44423048051/93450000000000 : ℝ)*((8149/50000 : ℝ)+(10691/100000 : ℝ))=(10000345445087259/10000000000000000 : ℝ) by norm_num, show 1+(297347694316813/2000000000000000000 : ℝ)+(1916832522814799/100000000000000000000 : ℝ)=(100016784217238655449/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(297347694316813/2000000000000000000 : ℝ) ≤ ((18688247769580390193/18690000000000000000 : ℝ)+2*(44423048051/93450000000000 : ℝ)*(8149/50000 : ℝ))^(4975/1024 : ℝ) := by
    rw [show (18688247769580390193/18690000000000000000 : ℝ)+2*(44423048051/93450000000000 : ℝ)*(8149/50000 : ℝ)=(2000122396675113/2000000000000000 : ℝ) by norm_num, show 1+2*(297347694316813/2000000000000000000 : ℝ)=(1000297347694316813/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18688247769580390193/18690000000000000000 : ℝ)*(X 1 0+X 2 0)+(44423048051/93450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4975/1024 : ℝ)) (lo := (10691/100000 : ℝ)) (hi := (8149/50000 : ℝ)) (c := (18688247769580390193/18690000000000000000 : ℝ)) (alpha := (44423048051/93450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18688247769580390193/18690000000000000000 : ℝ)*(X 0 1+X 2 1)+(44423048051/93450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4975/1024 : ℝ)) (lo := (10691/100000 : ℝ)) (hi := (8149/50000 : ℝ)) (c := (18688247769580390193/18690000000000000000 : ℝ)) (alpha := (44423048051/93450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18688247769580390193/18690000000000000000 : ℝ)*(X 0 2+X 1 2)+(44423048051/93450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4975/1024 : ℝ)) (lo := (10691/100000 : ℝ)) (hi := (8149/50000 : ℝ)) (c := (18688247769580390193/18690000000000000000 : ℝ)) (alpha := (44423048051/93450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-787512787/5000000000 : ℝ)*X 0 0+(5443179287/10000000000 : ℝ)*X 0 1+(2592381079/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668184743/1250000000 : ℝ)*X 1 0+(-853989733/5000000000 : ℝ)*X 1 1+(5184762221/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345477987/10000000000 : ℝ)*X 2 0+(1036952431/2000000000 : ℝ)*X 2 1+(-1707979497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4169373741/10000000000 : ℝ)*X 0 0+(191931363/500000000 : ℝ)*X 0 1+(2259933681/5000000000 : ℝ)*X 0 2+(4169373741/10000000000 : ℝ)*X 1 0+(191931363/500000000 : ℝ)*X 1 1+(2259933681/5000000000 : ℝ)*X 1 2+(4169373741/10000000000 : ℝ)*X 2 0+(191931363/500000000 : ℝ)*X 2 1+(2259933681/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-787543967/5000000000 : ℝ)*X 0 0+(2593365451/5000000000 : ℝ)*X 0 1+(1360297439/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638164189/5000000000 : ℝ)*X 1 0+(-290310381/2000000000 : ℝ)*X 1 1+(5441189747/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638164163/5000000000 : ℝ)*X 2 0+(1360297461/2500000000 : ℝ)*X 2 1+(-1451551843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((833907593/2000000000 : ℝ)*X 0 0+(4514677421/10000000000 : ℝ)*X 0 1+(1921935963/5000000000 : ℝ)*X 0 2+(833907593/2000000000 : ℝ)*X 1 0+(4514677421/10000000000 : ℝ)*X 1 1+(1921935963/5000000000 : ℝ)*X 1 2+(833907593/2000000000 : ℝ)*X 2 0+(4514677421/10000000000 : ℝ)*X 2 1+(1921935963/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (449716838087991586063759901/38937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (112504649/6250000000000 : ℝ)*(base19) + (34396243/2000000000000 : ℝ)*(base23) + (59543961/100000000000000 : ℝ)*(lower2) + (5864759/2000000000000 : ℝ)*(upper3) + (38689259/20000000000000 : ℝ)*(upper5) + (333605610084119/12500000000000 : ℝ)*(major0) + (333605610084119/12500000000000 : ℝ)*(major1) + (333605610084119/12500000000000 : ℝ)*(major2) + (154789474396879/4000000000000 : ℝ)*(sp0) + (1934879188578357/50000000000000 : ℝ)*(sp1) + (3869758457418947/100000000000000 : ℝ)*(sp2) + (146791960018183/10000000000000 : ℝ)*(sp3) + (23317309123/100000000000000 : ℝ)*(sp4) + (9598942631/100000000000000 : ℝ)*(sp7) + (1467929199124461/100000000000000 : ℝ)*(f.failure) + (1934880088615549/50000000000000 : ℝ)*(f.sum) + (22845800171381/9345000000000000000000000000 : ℝ)*base66 + (1103538928584435011/77875000000000000000000000000000 : ℝ)*base68 + (519157497907685011/77875000000000000000000000000000 : ℝ)*base70 + (730576609634060011/77875000000000000000000000000000 : ℝ)*base72 + (12425044085711/9345000000000000000000000000 : ℝ)*base74 + (501879819906185011/77875000000000000000000000000000 : ℝ)*base76 + (723311158168935011/77875000000000000000000000000000 : ℝ)*base78 + (393225479674685011/77875000000000000000000000000000 : ℝ)*base80 + (6415462933189/9345000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (87182051/10000000000000000000000 : ℝ)*base89 + (87182051/10000000000000000000000 : ℝ)*base91 + (87182051/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1496566865173026572722943/278125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (873218889/100000000000000 : ℝ)*(base19) + (427153613/50000000000000 : ℝ)*(base23) + (130873367/100000000000000 : ℝ)*(upper3) + (917731/50000000000000 : ℝ)*(lower4) + (7207379/6250000000000 : ℝ)*(upper5) + (33879083023507/1250000000000 : ℝ)*(major0) + (33879083023507/1250000000000 : ℝ)*(major1) + (33879083023507/1250000000000 : ℝ)*(major2) + (10282579359/100000000000000 : ℝ)*(sp1) + (5764687061/50000000000000 : ℝ)*(sp2) + (1964953966929057/50000000000000 : ℝ)*(sp4) + (1964948389029933/50000000000000 : ℝ)*(sp5) + (785979110035353/20000000000000 : ℝ)*(sp6) + (1490745170539181/100000000000000 : ℝ)*(sp7) + (1490745170539181/100000000000000 : ℝ)*(f.failure) + (1964953966929057/50000000000000 : ℝ)*(f.sum) + (8517172183/1869000000000000000000000000 : ℝ)*base65 + (67622088980781883/7787500000000000000000000000000 : ℝ)*base68 + (98873651694569383/7787500000000000000000000000000 : ℝ)*base70 + (1412767791218117/7787500000000000000000000000000 : ℝ)*base71 + (4108207620389/1869000000000000000000000000 : ℝ)*base74 + (75158456263456883/7787500000000000000000000000000 : ℝ)*base76 + (20331198144781883/7787500000000000000000000000000 : ℝ)*base78 + (11065282559106883/7787500000000000000000000000000 : ℝ)*base80 + (9390530360489/1869000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (70593571/10000000000000000000000 : ℝ)*base89 + (70593571/10000000000000000000000 : ℝ)*base91 + (70593571/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1665_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181810191/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8149/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10691/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5371/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16241/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1665_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1665_s4_0 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-787528949/5000000000 : ℝ)*x 0 + (5443018327/10000000000 : ℝ)*x 1 + (5184901413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (787528949/5000000000 : ℝ)^4979 ≤ (4880185693261/50000000000000 : ℝ)^3955 := by
    have hnat : (787528949 : ℕ)^4979*50000000000000^3955 ≤ 4880185693261^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      787528949 5000000000 4880185693261 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443018327/10000000000 : ℝ)^4979 ≤ (46499185642213/100000000000000 : ℝ)^3955 := by
    have hnat : (5443018327 : ℕ)^4979*100000000000000^3955 ≤ 46499185642213^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443018327 10000000000 46499185642213 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184901413/10000000000 : ℝ)^4979 ≤ (43740442964577/100000000000000 : ℝ)^3955 := by
    have hnat : (5184901413 : ℕ)^4979*100000000000000^3955 ≤ 43740442964577^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184901413 10000000000 43740442964577 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-787528949/5000000000 : ℝ), (5443018327/10000000000 : ℝ), (5184901413/10000000000 : ℝ)] ![(4880185693261/50000000000000 : ℝ), (46499185642213/100000000000000 : ℝ), (43740442964577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-787528949/5000000000 : ℝ)|^4979 ≤ (4880185693261/50000000000000 : ℝ)^3955
        have hw : |(-787528949/5000000000 : ℝ)|=(787528949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443018327/10000000000 : ℝ)|^4979 ≤ (46499185642213/100000000000000 : ℝ)^3955
        have hw : |(5443018327/10000000000 : ℝ)|=(5443018327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184901413/10000000000 : ℝ)|^4979 ≤ (43740442964577/100000000000000 : ℝ)^3955
        have hw : |(5184901413/10000000000 : ℝ)|=(5184901413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s4_1 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345434003/10000000000 : ℝ)*x 0 + (-1707851809/10000000000 : ℝ)*x 1 + (518490227/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345434003/10000000000 : ℝ)^4979 ≤ (22726067612201/50000000000000 : ℝ)^3955 := by
    have hnat : (5345434003 : ℕ)^4979*50000000000000^3955 ≤ 22726067612201^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345434003 10000000000 22726067612201 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1707851809/10000000000 : ℝ)^4979 ≤ (337731646939/3125000000000 : ℝ)^3955 := by
    have hnat : (1707851809 : ℕ)^4979*3125000000000^3955 ≤ 337731646939^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1707851809 10000000000 337731646939 3125000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518490227/1000000000 : ℝ)^4979 ≤ (21870226033103/50000000000000 : ℝ)^3955 := by
    have hnat : (518490227 : ℕ)^4979*50000000000000^3955 ≤ 21870226033103^3955*1000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518490227 1000000000 21870226033103 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345434003/10000000000 : ℝ), (-1707851809/10000000000 : ℝ), (518490227/1000000000 : ℝ)] ![(22726067612201/50000000000000 : ℝ), (337731646939/3125000000000 : ℝ), (21870226033103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345434003/10000000000 : ℝ)|^4979 ≤ (22726067612201/50000000000000 : ℝ)^3955
        have hw : |(5345434003/10000000000 : ℝ)|=(5345434003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1707851809/10000000000 : ℝ)|^4979 ≤ (337731646939/3125000000000 : ℝ)^3955
        have hw : |(-1707851809/10000000000 : ℝ)|=(1707851809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518490227/1000000000 : ℝ)|^4979 ≤ (21870226033103/50000000000000 : ℝ)^3955
        have hw : |(518490227/1000000000 : ℝ)|=(518490227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s4_2 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345434023/10000000000 : ℝ)*x 0 + (5184902057/10000000000 : ℝ)*x 1 + (-853926033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345434023/10000000000 : ℝ)^4979 ≤ (11363033859623/25000000000000 : ℝ)^3955 := by
    have hnat : (5345434023 : ℕ)^4979*25000000000000^3955 ≤ 11363033859623^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345434023 10000000000 11363033859623 25000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184902057/10000000000 : ℝ)^4979 ≤ (21870224902037/50000000000000 : ℝ)^3955 := by
    have hnat : (5184902057 : ℕ)^4979*50000000000000^3955 ≤ 21870224902037^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184902057 10000000000 21870224902037 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (853926033/5000000000 : ℝ)^4979 ≤ (2701853687359/25000000000000 : ℝ)^3955 := by
    have hnat : (853926033 : ℕ)^4979*25000000000000^3955 ≤ 2701853687359^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853926033 5000000000 2701853687359 25000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345434023/10000000000 : ℝ), (5184902057/10000000000 : ℝ), (-853926033/5000000000 : ℝ)] ![(11363033859623/25000000000000 : ℝ), (21870224902037/50000000000000 : ℝ), (2701853687359/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345434023/10000000000 : ℝ)|^4979 ≤ (11363033859623/25000000000000 : ℝ)^3955
        have hw : |(5345434023/10000000000 : ℝ)|=(5345434023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184902057/10000000000 : ℝ)|^4979 ≤ (21870224902037/50000000000000 : ℝ)^3955
        have hw : |(5184902057/10000000000 : ℝ)|=(5184902057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-853926033/5000000000 : ℝ)|^4979 ≤ (2701853687359/25000000000000 : ℝ)^3955
        have hw : |(-853926033/5000000000 : ℝ)|=(853926033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s4_3 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4169394069/10000000000 : ℝ)*x 0 + (3839022331/10000000000 : ℝ)*x 1 + (2259734369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4169394069/10000000000 : ℝ)^4979 ≤ (16621682514431/50000000000000 : ℝ)^3955 := by
    have hnat : (4169394069 : ℕ)^4979*50000000000000^3955 ≤ 16621682514431^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169394069 10000000000 16621682514431 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3839022331/10000000000 : ℝ)^4979 ≤ (1198477938569/4000000000000 : ℝ)^3955 := by
    have hnat : (3839022331 : ℕ)^4979*4000000000000^3955 ≤ 1198477938569^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3839022331 10000000000 1198477938569 4000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259734369/5000000000 : ℝ)^4979 ≤ (9198671624991/25000000000000 : ℝ)^3955 := by
    have hnat : (2259734369 : ℕ)^4979*25000000000000^3955 ≤ 9198671624991^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259734369 5000000000 9198671624991 25000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4169394069/10000000000 : ℝ), (3839022331/10000000000 : ℝ), (2259734369/5000000000 : ℝ)] ![(16621682514431/50000000000000 : ℝ), (1198477938569/4000000000000 : ℝ), (9198671624991/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4169394069/10000000000 : ℝ)|^4979 ≤ (16621682514431/50000000000000 : ℝ)^3955
        have hw : |(4169394069/10000000000 : ℝ)|=(4169394069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3839022331/10000000000 : ℝ)|^4979 ≤ (1198477938569/4000000000000 : ℝ)^3955
        have hw : |(3839022331/10000000000 : ℝ)|=(3839022331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2259734369/5000000000 : ℝ)|^4979 ≤ (9198671624991/25000000000000 : ℝ)^3955
        have hw : |(2259734369/5000000000 : ℝ)|=(2259734369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s4_4 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1575119531/10000000000 : ℝ)*x 0 + (5186866199/10000000000 : ℝ)*x 1 + (1360258301/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1575119531/10000000000 : ℝ)^4979 ≤ (9760852204797/100000000000000 : ℝ)^3955 := by
    have hnat : (1575119531 : ℕ)^4979*100000000000000^3955 ≤ 9760852204797^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1575119531 10000000000 9760852204797 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5186866199/10000000000 : ℝ)^4979 ≤ (43761310678281/100000000000000 : ℝ)^3955 := by
    have hnat : (5186866199 : ℕ)^4979*100000000000000^3955 ≤ 43761310678281^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186866199 10000000000 43761310678281 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360258301/2500000000 : ℝ)^4979 ≤ (2323891855299/5000000000000 : ℝ)^3955 := by
    have hnat : (1360258301 : ℕ)^4979*5000000000000^3955 ≤ 2323891855299^3955*2500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360258301 2500000000 2323891855299 5000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1575119531/10000000000 : ℝ), (5186866199/10000000000 : ℝ), (1360258301/2500000000 : ℝ)] ![(9760852204797/100000000000000 : ℝ), (43761310678281/100000000000000 : ℝ), (2323891855299/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1575119531/10000000000 : ℝ)|^4979 ≤ (9760852204797/100000000000000 : ℝ)^3955
        have hw : |(-1575119531/10000000000 : ℝ)|=(1575119531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5186866199/10000000000 : ℝ)|^4979 ≤ (43761310678281/100000000000000 : ℝ)^3955
        have hw : |(5186866199/10000000000 : ℝ)|=(5186866199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360258301/2500000000 : ℝ)|^4979 ≤ (2323891855299/5000000000000 : ℝ)^3955
        have hw : |(1360258301/2500000000 : ℝ)|=(1360258301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s4_5 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276365223/10000000000 : ℝ)*x 0 + (-72586047/500000000 : ℝ)*x 1 + (5441033133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276365223/10000000000 : ℝ)^4979 ≤ (44714028187181/100000000000000 : ℝ)^3955 := by
    have hnat : (5276365223 : ℕ)^4979*100000000000000^3955 ≤ 44714028187181^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276365223 10000000000 44714028187181 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (72586047/500000000 : ℝ)^4979 ≤ (8808135457701/100000000000000 : ℝ)^3955 := by
    have hnat : (72586047 : ℕ)^4979*100000000000000^3955 ≤ 8808135457701^3955*500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72586047 500000000 8808135457701 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5441033133/10000000000 : ℝ)^4979 ≤ (46477836342463/100000000000000 : ℝ)^3955 := by
    have hnat : (5441033133 : ℕ)^4979*100000000000000^3955 ≤ 46477836342463^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441033133 10000000000 46477836342463 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276365223/10000000000 : ℝ), (-72586047/500000000 : ℝ), (5441033133/10000000000 : ℝ)] ![(44714028187181/100000000000000 : ℝ), (8808135457701/100000000000000 : ℝ), (46477836342463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276365223/10000000000 : ℝ)|^4979 ≤ (44714028187181/100000000000000 : ℝ)^3955
        have hw : |(5276365223/10000000000 : ℝ)|=(5276365223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-72586047/500000000 : ℝ)|^4979 ≤ (8808135457701/100000000000000 : ℝ)^3955
        have hw : |(-72586047/500000000 : ℝ)|=(72586047/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5441033133/10000000000 : ℝ)|^4979 ≤ (46477836342463/100000000000000 : ℝ)^3955
        have hw : |(5441033133/10000000000 : ℝ)|=(5441033133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s4_6 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319091317/2500000000 : ℝ)*x 0 + (5441033153/10000000000 : ℝ)*x 1 + (-90732553/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319091317/2500000000 : ℝ)^4979 ≤ (8942805733453/20000000000000 : ℝ)^3955 := by
    have hnat : (1319091317 : ℕ)^4979*20000000000000^3955 ≤ 8942805733453^3955*2500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319091317 2500000000 8942805733453 20000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441033153/10000000000 : ℝ)^4979 ≤ (23238918278769/50000000000000 : ℝ)^3955 := by
    have hnat : (5441033153 : ℕ)^4979*50000000000000^3955 ≤ 23238918278769^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441033153 10000000000 23238918278769 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90732553/625000000 : ℝ)^4979 ≤ (8808134754977/100000000000000 : ℝ)^3955 := by
    have hnat : (90732553 : ℕ)^4979*100000000000000^3955 ≤ 8808134754977^3955*625000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90732553 625000000 8808134754977 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319091317/2500000000 : ℝ), (5441033153/10000000000 : ℝ), (-90732553/625000000 : ℝ)] ![(8942805733453/20000000000000 : ℝ), (23238918278769/50000000000000 : ℝ), (8808134754977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319091317/2500000000 : ℝ)|^4979 ≤ (8942805733453/20000000000000 : ℝ)^3955
        have hw : |(1319091317/2500000000 : ℝ)|=(1319091317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441033153/10000000000 : ℝ)|^4979 ≤ (23238918278769/50000000000000 : ℝ)^3955
        have hw : |(5441033153/10000000000 : ℝ)|=(5441033153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90732553/625000000 : ℝ)|^4979 ≤ (8808134754977/100000000000000 : ℝ)^3955
        have hw : |(-90732553/625000000 : ℝ)|=(90732553/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s4_7 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4169558253/10000000000 : ℝ)*x 0 + (4514290623/10000000000 : ℝ)*x 1 + (961063611/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4169558253/10000000000 : ℝ)^4979 ≤ (16622506521093/50000000000000 : ℝ)^3955 := by
    have hnat : (4169558253 : ℕ)^4979*50000000000000^3955 ≤ 16622506521093^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169558253 10000000000 16622506521093 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514290623/10000000000 : ℝ)^4979 ≤ (18370811211671/50000000000000 : ℝ)^3955 := by
    have hnat : (4514290623 : ℕ)^4979*50000000000000^3955 ≤ 18370811211671^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514290623 10000000000 18370811211671 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (961063611/2500000000 : ℝ)^4979 ≤ (15006682260069/50000000000000 : ℝ)^3955 := by
    have hnat : (961063611 : ℕ)^4979*50000000000000^3955 ≤ 15006682260069^3955*2500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961063611 2500000000 15006682260069 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4169558253/10000000000 : ℝ), (4514290623/10000000000 : ℝ), (961063611/2500000000 : ℝ)] ![(16622506521093/50000000000000 : ℝ), (18370811211671/50000000000000 : ℝ), (15006682260069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4169558253/10000000000 : ℝ)|^4979 ≤ (16622506521093/50000000000000 : ℝ)^3955
        have hw : |(4169558253/10000000000 : ℝ)|=(4169558253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514290623/10000000000 : ℝ)|^4979 ≤ (18370811211671/50000000000000 : ℝ)^3955
        have hw : |(4514290623/10000000000 : ℝ)|=(4514290623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(961063611/2500000000 : ℝ)|^4979 ≤ (15006682260069/50000000000000 : ℝ)^3955
        have hw : |(961063611/2500000000 : ℝ)|=(961063611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1665_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181810191/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5371/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2149/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8119/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16241/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5371/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16241/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5371/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16241/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5371/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16241/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5371/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16241/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5371/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16241/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5371/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5371/50000 : ℝ) ^ (4975/1024 : ℝ) ≤ (392333680868341/20000000000000000000 : ℝ) := by
    have hpowers : (5371/50000 : ℝ)^4975 ≤ (392333680868341/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5371 : ℕ)^4975*20000000000000000000^1024 ≤ 392333680868341^1024*50000^4975 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5371 50000 392333680868341 20000000000000000000 4975 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5371/50000 : ℝ)) (X := (392333680868341/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16241/100000 : ℝ) ^ (4975/1024 : ℝ) ≤ (7308231599740379/50000000000000000000 : ℝ) := by
    have hpowers : (16241/100000 : ℝ)^4975 ≤ (7308231599740379/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16241 : ℕ)^4975*50000000000000000000^1024 ≤ 7308231599740379^1024*100000^4975 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16241 100000 7308231599740379 50000000000000000000 4975 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16241/100000 : ℝ)) (X := (7308231599740379/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000392333680868341/10000000000000000000 : ℝ) ≤ (5000040376224171/5000000000000000 : ℝ) ^ (4975/1024 : ℝ) := by
    have hpowers : (10000392333680868341/10000000000000000000 : ℝ)^1024 ≤ (5000040376224171/5000000000000000 : ℝ)^4975 := by
      have hnat : (10000392333680868341 : ℕ)^1024*5000000000000000^4975 ≤ 5000040376224171^4975*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000392333680868341 10000000000000000000 5000040376224171 5000000000000000 1024 4975 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000040376224171/5000000000000000 : ℝ)) (X := (10000392333680868341/10000000000000000000 : ℝ)) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100016578131603822463/100000000000000000000 : ℝ) ≤ (2000068240761221/2000000000000000 : ℝ) ^ (4975/1024 : ℝ) := by
    have hpowers : (100016578131603822463/100000000000000000000 : ℝ)^1024 ≤ (2000068240761221/2000000000000000 : ℝ)^4975 := by
      have hnat : (100016578131603822463 : ℕ)^1024*2000000000000000^4975 ≤ 2000068240761221^4975*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100016578131603822463 100000000000000000000 2000068240761221 2000000000000000 1024 4975 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000068240761221/2000000000000000 : ℝ)) (X := (100016578131603822463/100000000000000000000 : ℝ)) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25007308231599740379/25000000000000000000 : ℝ) ≤ (2500150413790967/2500000000000000 : ℝ) ^ (4975/1024 : ℝ) := by
    have hpowers : (25007308231599740379/25000000000000000000 : ℝ)^1024 ≤ (2500150413790967/2500000000000000 : ℝ)^4975 := by
      have hnat : (25007308231599740379 : ℕ)^1024*2500000000000000^4975 ≤ 2500150413790967^4975*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007308231599740379 25000000000000000000 2500150413790967 2500000000000000 1024 4975 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500150413790967/2500000000000000 : ℝ)) (X := (25007308231599740379/25000000000000000000 : ℝ)) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(392333680868341/20000000000000000000 : ℝ) ≤ ((27492424260371626183/27495000000000000000 : ℝ)+2*(260451357763/549900000000000 : ℝ)*(5371/50000 : ℝ))^(4975/1024 : ℝ) := by
    rw [show (27492424260371626183/27495000000000000000 : ℝ)+2*(260451357763/549900000000000 : ℝ)*(5371/50000 : ℝ)=(5000040376224171/5000000000000000 : ℝ) by norm_num, show 1+2*(392333680868341/20000000000000000000 : ℝ)=(10000392333680868341/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7308231599740379/50000000000000000000 : ℝ)+(392333680868341/20000000000000000000 : ℝ) ≤ ((27492424260371626183/27495000000000000000 : ℝ)+(260451357763/549900000000000 : ℝ)*((16241/100000 : ℝ)+(5371/50000 : ℝ)))^(4975/1024 : ℝ) := by
    rw [show (27492424260371626183/27495000000000000000 : ℝ)+(260451357763/549900000000000 : ℝ)*((16241/100000 : ℝ)+(5371/50000 : ℝ))=(2000068240761221/2000000000000000 : ℝ) by norm_num, show 1+(7308231599740379/50000000000000000000 : ℝ)+(392333680868341/20000000000000000000 : ℝ)=(100016578131603822463/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7308231599740379/50000000000000000000 : ℝ) ≤ ((27492424260371626183/27495000000000000000 : ℝ)+2*(260451357763/549900000000000 : ℝ)*(16241/100000 : ℝ))^(4975/1024 : ℝ) := by
    rw [show (27492424260371626183/27495000000000000000 : ℝ)+2*(260451357763/549900000000000 : ℝ)*(16241/100000 : ℝ)=(2500150413790967/2500000000000000 : ℝ) by norm_num, show 1+2*(7308231599740379/50000000000000000000 : ℝ)=(25007308231599740379/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27492424260371626183/27495000000000000000 : ℝ)*(X 1 0+X 2 0)+(260451357763/549900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4975/1024 : ℝ)) (lo := (5371/50000 : ℝ)) (hi := (16241/100000 : ℝ)) (c := (27492424260371626183/27495000000000000000 : ℝ)) (alpha := (260451357763/549900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27492424260371626183/27495000000000000000 : ℝ)*(X 0 1+X 2 1)+(260451357763/549900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4975/1024 : ℝ)) (lo := (5371/50000 : ℝ)) (hi := (16241/100000 : ℝ)) (c := (27492424260371626183/27495000000000000000 : ℝ)) (alpha := (260451357763/549900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27492424260371626183/27495000000000000000 : ℝ)*(X 0 2+X 1 2)+(260451357763/549900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4975/1024 : ℝ)) (lo := (5371/50000 : ℝ)) (hi := (16241/100000 : ℝ)) (c := (27492424260371626183/27495000000000000000 : ℝ)) (alpha := (260451357763/549900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-787528949/5000000000 : ℝ)*X 0 0+(5443018327/10000000000 : ℝ)*X 0 1+(5184901413/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345434003/10000000000 : ℝ)*X 1 0+(-1707851809/10000000000 : ℝ)*X 1 1+(518490227/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345434023/10000000000 : ℝ)*X 2 0+(5184902057/10000000000 : ℝ)*X 2 1+(-853926033/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4169394069/10000000000 : ℝ)*X 0 0+(3839022331/10000000000 : ℝ)*X 0 1+(2259734369/5000000000 : ℝ)*X 0 2+(4169394069/10000000000 : ℝ)*X 1 0+(3839022331/10000000000 : ℝ)*X 1 1+(2259734369/5000000000 : ℝ)*X 1 2+(4169394069/10000000000 : ℝ)*X 2 0+(3839022331/10000000000 : ℝ)*X 2 1+(2259734369/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1575119531/10000000000 : ℝ)*X 0 0+(5186866199/10000000000 : ℝ)*X 0 1+(1360258301/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276365223/10000000000 : ℝ)*X 1 0+(-72586047/500000000 : ℝ)*X 1 1+(5441033133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319091317/2500000000 : ℝ)*X 2 0+(5441033153/10000000000 : ℝ)*X 2 1+(-90732553/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4169558253/10000000000 : ℝ)*X 0 0+(4514290623/10000000000 : ℝ)*X 0 1+(961063611/2500000000 : ℝ)*X 0 2+(4169558253/10000000000 : ℝ)*X 1 0+(4514290623/10000000000 : ℝ)*X 1 1+(961063611/2500000000 : ℝ)*X 1 2+(4169558253/10000000000 : ℝ)*X 2 0+(4514290623/10000000000 : ℝ)*X 2 1+(961063611/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (418615964224039055226437569/38187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1085436267/50000000000000 : ℝ)*(base19) + (1776911169/100000000000000 : ℝ)*(base23) + (26478883/5000000000000 : ℝ)*(upper3) + (218338019/100000000000000 : ℝ)*(upper4) + (47706879/100000000000000 : ℝ)*(upper5) + (667991748354829/25000000000000 : ℝ)*(major0) + (667991748354829/25000000000000 : ℝ)*(major1) + (667991748354829/25000000000000 : ℝ)*(major2) + (1937127043412173/50000000000000 : ℝ)*(sp0) + (1937142506977697/50000000000000 : ℝ)*(sp1) + (1937142703958379/50000000000000 : ℝ)*(sp2) + (734816262442383/50000000000000 : ℝ)*(sp3) + (16549001791/50000000000000 : ℝ)*(sp4) + (13911721923/100000000000000 : ℝ)*(sp7) + (146964643660669/10000000000000 : ℝ)*(f.failure) + (484285898103491/12500000000000 : ℝ)*(f.sum) + (85811165560723/27495000000000000000000000000 : ℝ)*base65 + (139702813651487477/76375000000000000000000000000000 : ℝ)*base68 + (59288126891612477/76375000000000000000000000000000 : ℝ)*base70 + (976065888178987477/76375000000000000000000000000000 : ℝ)*base72 + (249748970101753/27495000000000000000000000000 : ℝ)*base73 + (551848832271637523/76375000000000000000000000000000 : ℝ)*base75 + (147564800550487477/76375000000000000000000000000000 : ℝ)*base78 + (1061335514185262523/76375000000000000000000000000000 : ℝ)*base79 + (1005737888473/1718437500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (10077779/1000000000000000000000 : ℝ)*base89 + (10077779/1000000000000000000000 : ℝ)*base91 + (10077779/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54740926276743131381465261/5728125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1510581379/100000000000000 : ℝ)*(base19) + (324822361/20000000000000 : ℝ)*(base23) + (5580281/1250000000000 : ℝ)*(lower1) + (42862461/20000000000000 : ℝ)*(upper3) + (1544841/6250000000000 : ℝ)*(lower4) + (38087271/20000000000000 : ℝ)*(upper5) + (33917832794471/1250000000000 : ℝ)*(major0) + (33917832794471/1250000000000 : ℝ)*(major1) + (33917832794471/1250000000000 : ℝ)*(major2) + (632722689/25000000000000 : ℝ)*(sp2) + (196720134658321/5000000000000 : ℝ)*(sp4) + (3934401182585041/100000000000000 : ℝ)*(sp5) + (3934398538163859/100000000000000 : ℝ)*(sp6) + (298490047079669/20000000000000 : ℝ)*(sp7) + (298490047079669/20000000000000 : ℝ)*(f.failure) + (196720134658321/5000000000000 : ℝ)*(f.sum) + (15370588738733/5499000000000000000000000000 : ℝ)*base65 + (5448342647224673/3818750000000000000000000000000 : ℝ)*base68 + (31955998514693423/3818750000000000000000000000000 : ℝ)*base70 + (320699012660006577/3818750000000000000000000000000 : ℝ)*base71 + (13221479841863/5499000000000000000000000000 : ℝ)*base73 + (91350368235337173/3818750000000000000000000000000 : ℝ)*base76 + (23624734841412173/3818750000000000000000000000000 : ℝ)*base78 + (32990179383030923/3818750000000000000000000000000 : ℝ)*base80 + (856210213559/274950000000000000000000000 : ℝ)*base82 + (13106779/2000000000000000000000 : ℝ)*base89 + (13106779/2000000000000000000000 : ℝ)*base91 + (13106779/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1665_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181810191/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5371/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2149/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8119/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1665_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1665_s5_0 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-19688237/125000000 : ℝ)*x 0 + (27215047/50000000 : ℝ)*x 1 + (648113709/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19688237/125000000 : ℝ)^4979 ≤ (4880189835737/50000000000000 : ℝ)^3955 := by
    have hnat : (19688237 : ℕ)^4979*50000000000000^3955 ≤ 4880189835737^3955*125000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19688237 125000000 4880189835737 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27215047/50000000 : ℝ)^4979 ≤ (11624772408597/25000000000000 : ℝ)^3955 := by
    have hnat : (27215047 : ℕ)^4979*25000000000000^3955 ≤ 11624772408597^3955*50000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27215047 50000000 11624772408597 25000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (648113709/1250000000 : ℝ)^4979 ≤ (43740530677961/100000000000000 : ℝ)^3955 := by
    have hnat : (648113709 : ℕ)^4979*100000000000000^3955 ≤ 43740530677961^3955*1250000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648113709 1250000000 43740530677961 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19688237/125000000 : ℝ), (27215047/50000000 : ℝ), (648113709/1250000000 : ℝ)] ![(4880189835737/50000000000000 : ℝ), (11624772408597/25000000000000 : ℝ), (43740530677961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19688237/125000000 : ℝ)|^4979 ≤ (4880189835737/50000000000000 : ℝ)^3955
        have hw : |(-19688237/125000000 : ℝ)|=(19688237/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27215047/50000000 : ℝ)|^4979 ≤ (11624772408597/25000000000000 : ℝ)^3955
        have hw : |(27215047/50000000 : ℝ)|=(27215047/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(648113709/1250000000 : ℝ)|^4979 ≤ (43740530677961/100000000000000 : ℝ)^3955
        have hw : |(648113709/1250000000 : ℝ)|=(648113709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s5_1 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213817281/400000000 : ℝ)*x 0 + (-1707844579/10000000000 : ℝ)*x 1 + (5184909687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213817281/400000000 : ℝ)^4979 ≤ (22726057025437/50000000000000 : ℝ)^3955 := by
    have hnat : (213817281 : ℕ)^4979*50000000000000^3955 ≤ 22726057025437^3955*400000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213817281 400000000 22726057025437 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1707844579/10000000000 : ℝ)^4979 ≤ (10807355104333/100000000000000 : ℝ)^3955 := by
    have hnat : (1707844579 : ℕ)^4979*100000000000000^3955 ≤ 10807355104333^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1707844579 10000000000 10807355104333 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184909687/10000000000 : ℝ)^4979 ≤ (21870265418633/50000000000000 : ℝ)^3955 := by
    have hnat : (5184909687 : ℕ)^4979*50000000000000^3955 ≤ 21870265418633^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184909687 10000000000 21870265418633 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213817281/400000000 : ℝ), (-1707844579/10000000000 : ℝ), (5184909687/10000000000 : ℝ)] ![(22726057025437/50000000000000 : ℝ), (10807355104333/100000000000000 : ℝ), (21870265418633/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213817281/400000000 : ℝ)|^4979 ≤ (22726057025437/50000000000000 : ℝ)^3955
        have hw : |(213817281/400000000 : ℝ)|=(213817281/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1707844579/10000000000 : ℝ)|^4979 ≤ (10807355104333/100000000000000 : ℝ)^3955
        have hw : |(-1707844579/10000000000 : ℝ)|=(1707844579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184909687/10000000000 : ℝ)|^4979 ≤ (21870265418633/50000000000000 : ℝ)^3955
        have hw : |(5184909687/10000000000 : ℝ)|=(5184909687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s5_2 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345431721/10000000000 : ℝ)*x 0 + (5184909847/10000000000 : ℝ)*x 1 + (-1707844773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345431721/10000000000 : ℝ)^4979 ≤ (22726055398351/50000000000000 : ℝ)^3955 := by
    have hnat : (5345431721 : ℕ)^4979*50000000000000^3955 ≤ 22726055398351^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345431721 10000000000 22726055398351 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184909847/10000000000 : ℝ)^4979 ≤ (43740532536521/100000000000000 : ℝ)^3955 := by
    have hnat : (5184909847 : ℕ)^4979*100000000000000^3955 ≤ 43740532536521^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184909847 10000000000 43740532536521 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1707844773/10000000000 : ℝ)^4979 ≤ (10807356649831/100000000000000 : ℝ)^3955 := by
    have hnat : (1707844773 : ℕ)^4979*100000000000000^3955 ≤ 10807356649831^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1707844773 10000000000 10807356649831 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345431721/10000000000 : ℝ), (5184909847/10000000000 : ℝ), (-1707844773/10000000000 : ℝ)] ![(22726055398351/50000000000000 : ℝ), (43740532536521/100000000000000 : ℝ), (10807356649831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345431721/10000000000 : ℝ)|^4979 ≤ (22726055398351/50000000000000 : ℝ)^3955
        have hw : |(5345431721/10000000000 : ℝ)|=(5345431721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184909847/10000000000 : ℝ)|^4979 ≤ (43740532536521/100000000000000 : ℝ)^3955
        have hw : |(5184909847/10000000000 : ℝ)|=(5184909847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1707844773/10000000000 : ℝ)|^4979 ≤ (10807356649831/100000000000000 : ℝ)^3955
        have hw : |(-1707844773/10000000000 : ℝ)|=(1707844773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s5_3 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2084697941/5000000000 : ℝ)*x 0 + (3839043267/10000000000 : ℝ)*x 1 + (1129861723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2084697941/5000000000 : ℝ)^4979 ≤ (33243383226939/100000000000000 : ℝ)^3955 := by
    have hnat : (2084697941 : ℕ)^4979*100000000000000^3955 ≤ 33243383226939^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084697941 5000000000 33243383226939 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3839043267/10000000000 : ℝ)^4979 ≤ (3745269270811/12500000000000 : ℝ)^3955 := by
    have hnat : (3839043267 : ℕ)^4979*12500000000000^3955 ≤ 3745269270811^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3839043267 10000000000 3745269270811 12500000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129861723/2500000000 : ℝ)^4979 ≤ (36794462594333/100000000000000 : ℝ)^3955 := by
    have hnat : (1129861723 : ℕ)^4979*100000000000000^3955 ≤ 36794462594333^3955*2500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129861723 2500000000 36794462594333 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2084697941/5000000000 : ℝ), (3839043267/10000000000 : ℝ), (1129861723/2500000000 : ℝ)] ![(33243383226939/100000000000000 : ℝ), (3745269270811/12500000000000 : ℝ), (36794462594333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2084697941/5000000000 : ℝ)|^4979 ≤ (33243383226939/100000000000000 : ℝ)^3955
        have hw : |(2084697941/5000000000 : ℝ)|=(2084697941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3839043267/10000000000 : ℝ)|^4979 ≤ (3745269270811/12500000000000 : ℝ)^3955
        have hw : |(3839043267/10000000000 : ℝ)|=(3839043267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1129861723/2500000000 : ℝ)|^4979 ≤ (36794462594333/100000000000000 : ℝ)^3955
        have hw : |(1129861723/2500000000 : ℝ)|=(1129861723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s5_4 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-315024187/2000000000 : ℝ)*x 0 + (5186873683/10000000000 : ℝ)*x 1 + (5441024793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (315024187/2000000000 : ℝ)^4979 ≤ (1220107894737/12500000000000 : ℝ)^3955 := by
    have hnat : (315024187 : ℕ)^4979*12500000000000^3955 ≤ 1220107894737^3955*2000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315024187 2000000000 1220107894737 12500000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5186873683/10000000000 : ℝ)^4979 ≤ (21880695084349/50000000000000 : ℝ)^3955 := by
    have hnat : (5186873683 : ℕ)^4979*50000000000000^3955 ≤ 21880695084349^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186873683 10000000000 21880695084349 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5441024793/10000000000 : ℝ)^4979 ≤ (46477746656157/100000000000000 : ℝ)^3955 := by
    have hnat : (5441024793 : ℕ)^4979*100000000000000^3955 ≤ 46477746656157^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441024793 10000000000 46477746656157 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-315024187/2000000000 : ℝ), (5186873683/10000000000 : ℝ), (5441024793/10000000000 : ℝ)] ![(1220107894737/12500000000000 : ℝ), (21880695084349/50000000000000 : ℝ), (46477746656157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-315024187/2000000000 : ℝ)|^4979 ≤ (1220107894737/12500000000000 : ℝ)^3955
        have hw : |(-315024187/2000000000 : ℝ)|=(315024187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5186873683/10000000000 : ℝ)|^4979 ≤ (21880695084349/50000000000000 : ℝ)^3955
        have hw : |(5186873683/10000000000 : ℝ)|=(5186873683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5441024793/10000000000 : ℝ)|^4979 ≤ (46477746656157/100000000000000 : ℝ)^3955
        have hw : |(5441024793/10000000000 : ℝ)|=(5441024793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s5_5 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276367281/10000000000 : ℝ)*x 0 + (2720512399/5000000000 : ℝ)*x 1 + (-7258649/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276367281/10000000000 : ℝ)^4979 ≤ (44714050143017/100000000000000 : ℝ)^3955 := by
    have hnat : (5276367281 : ℕ)^4979*100000000000000^3955 ≤ 44714050143017^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276367281 10000000000 44714050143017 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720512399/5000000000 : ℝ)^4979 ≤ (23238873354963/50000000000000 : ℝ)^3955 := by
    have hnat : (2720512399 : ℕ)^4979*50000000000000^3955 ≤ 23238873354963^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720512399 5000000000 23238873354963 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7258649/50000000 : ℝ)^4979 ≤ (68814086977/781250000000 : ℝ)^3955 := by
    have hnat : (7258649 : ℕ)^4979*781250000000^3955 ≤ 68814086977^3955*50000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7258649 50000000 68814086977 781250000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276367281/10000000000 : ℝ), (2720512399/5000000000 : ℝ), (-7258649/50000000 : ℝ)] ![(44714050143017/100000000000000 : ℝ), (23238873354963/50000000000000 : ℝ), (68814086977/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276367281/10000000000 : ℝ)|^4979 ≤ (44714050143017/100000000000000 : ℝ)^3955
        have hw : |(5276367281/10000000000 : ℝ)|=(5276367281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720512399/5000000000 : ℝ)|^4979 ≤ (23238873354963/50000000000000 : ℝ)^3955
        have hw : |(2720512399/5000000000 : ℝ)|=(2720512399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7258649/50000000 : ℝ)|^4979 ≤ (68814086977/781250000000 : ℝ)^3955
        have hw : |(-7258649/50000000 : ℝ)|=(7258649/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s5_6 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4169559411/10000000000 : ℝ)*x 0 + (180570783/400000000 : ℝ)*x 1 + (3844275203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4169559411/10000000000 : ℝ)^4979 ≤ (33245024665787/100000000000000 : ℝ)^3955 := by
    have hnat : (4169559411 : ℕ)^4979*100000000000000^3955 ≤ 33245024665787^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169559411 10000000000 33245024665787 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (180570783/400000000 : ℝ)^4979 ≤ (4592675845081/12500000000000 : ℝ)^3955 := by
    have hnat : (180570783 : ℕ)^4979*12500000000000^3955 ≤ 4592675845081^3955*400000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180570783 400000000 4592675845081 12500000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3844275203/10000000000 : ℝ)^4979 ≤ (15006784277629/50000000000000 : ℝ)^3955 := by
    have hnat : (3844275203 : ℕ)^4979*50000000000000^3955 ≤ 15006784277629^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3844275203 10000000000 15006784277629 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4169559411/10000000000 : ℝ), (180570783/400000000 : ℝ), (3844275203/10000000000 : ℝ)] ![(33245024665787/100000000000000 : ℝ), (4592675845081/12500000000000 : ℝ), (15006784277629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4169559411/10000000000 : ℝ)|^4979 ≤ (33245024665787/100000000000000 : ℝ)^3955
        have hw : |(4169559411/10000000000 : ℝ)|=(4169559411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(180570783/400000000 : ℝ)|^4979 ≤ (4592675845081/12500000000000 : ℝ)^3955
        have hw : |(180570783/400000000 : ℝ)|=(180570783/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3844275203/10000000000 : ℝ)|^4979 ≤ (15006784277629/50000000000000 : ℝ)^3955
        have hw : |(3844275203/10000000000 : ℝ)|=(3844275203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1665_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181810191/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2149/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5373/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8119/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2149/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2149/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2149/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2149/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2149/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2149/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2149/20000 : ℝ) ^ (4975/1024 : ℝ) ≤ (98216575630083/5000000000000000000 : ℝ) := by
    have hpowers : (2149/20000 : ℝ)^4975 ≤ (98216575630083/5000000000000000000 : ℝ)^1024 := by
      have hnat : (2149 : ℕ)^4975*5000000000000000000^1024 ≤ 98216575630083^1024*20000^4975 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2149 20000 98216575630083 5000000000000000000 4975 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2149/20000 : ℝ)) (X := (98216575630083/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8119/50000 : ℝ) ^ (4975/1024 : ℝ) ≤ (584134023572581/4000000000000000000 : ℝ) := by
    have hpowers : (8119/50000 : ℝ)^4975 ≤ (584134023572581/4000000000000000000 : ℝ)^1024 := by
      have hnat : (8119 : ℕ)^4975*4000000000000000000^1024 ≤ 584134023572581^1024*50000^4975 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8119 50000 584134023572581 4000000000000000000 4975 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8119/50000 : ℝ)) (X := (584134023572581/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500098216575630083/2500000000000000000 : ℝ) ≤ (10000080862073983/10000000000000000 : ℝ) ^ (4975/1024 : ℝ) := by
    have hpowers : (2500098216575630083/2500000000000000000 : ℝ)^1024 ≤ (10000080862073983/10000000000000000 : ℝ)^4975 := by
      have hnat : (2500098216575630083 : ℕ)^1024*10000000000000000^4975 ≤ 10000080862073983^4975*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500098216575630083 2500000000000000000 10000080862073983 10000000000000000 1024 4975 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000080862073983/10000000000000000 : ℝ)) (X := (2500098216575630083/2500000000000000000 : ℝ)) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20003313536420383237/20000000000000000000 : ℝ) ≤ (2500085247188301/2500000000000000 : ℝ) ^ (4975/1024 : ℝ) := by
    have hpowers : (20003313536420383237/20000000000000000000 : ℝ)^1024 ≤ (2500085247188301/2500000000000000 : ℝ)^4975 := by
      have hnat : (20003313536420383237 : ℕ)^1024*2500000000000000^4975 ≤ 2500085247188301^4975*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20003313536420383237 20000000000000000000 2500085247188301 2500000000000000 1024 4975 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500085247188301/2500000000000000 : ℝ)) (X := (20003313536420383237/20000000000000000000 : ℝ)) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2000584134023572581/2000000000000000000 : ℝ) ≤ (400024044617297/400000000000000 : ℝ) ^ (4975/1024 : ℝ) := by
    have hpowers : (2000584134023572581/2000000000000000000 : ℝ)^1024 ≤ (400024044617297/400000000000000 : ℝ)^4975 := by
      have hnat : (2000584134023572581 : ℕ)^1024*400000000000000^4975 ≤ 400024044617297^4975*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000584134023572581 2000000000000000000 400024044617297 400000000000000 1024 4975 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400024044617297/400000000000000 : ℝ)) (X := (2000584134023572581/2000000000000000000 : ℝ)) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(98216575630083/5000000000000000000 : ℝ) ≤ ((54924854053035929329/54930000000000000000 : ℝ)+2*(260126679221/549300000000000 : ℝ)*(2149/20000 : ℝ))^(4975/1024 : ℝ) := by
    rw [show (54924854053035929329/54930000000000000000 : ℝ)+2*(260126679221/549300000000000 : ℝ)*(2149/20000 : ℝ)=(10000080862073983/10000000000000000 : ℝ) by norm_num, show 1+2*(98216575630083/5000000000000000000 : ℝ)=(2500098216575630083/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(584134023572581/4000000000000000000 : ℝ)+(98216575630083/5000000000000000000 : ℝ) ≤ ((54924854053035929329/54930000000000000000 : ℝ)+(260126679221/549300000000000 : ℝ)*((8119/50000 : ℝ)+(2149/20000 : ℝ)))^(4975/1024 : ℝ) := by
    rw [show (54924854053035929329/54930000000000000000 : ℝ)+(260126679221/549300000000000 : ℝ)*((8119/50000 : ℝ)+(2149/20000 : ℝ))=(2500085247188301/2500000000000000 : ℝ) by norm_num, show 1+(584134023572581/4000000000000000000 : ℝ)+(98216575630083/5000000000000000000 : ℝ)=(20003313536420383237/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(584134023572581/4000000000000000000 : ℝ) ≤ ((54924854053035929329/54930000000000000000 : ℝ)+2*(260126679221/549300000000000 : ℝ)*(8119/50000 : ℝ))^(4975/1024 : ℝ) := by
    rw [show (54924854053035929329/54930000000000000000 : ℝ)+2*(260126679221/549300000000000 : ℝ)*(8119/50000 : ℝ)=(400024044617297/400000000000000 : ℝ) by norm_num, show 1+2*(584134023572581/4000000000000000000 : ℝ)=(2000584134023572581/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (54924854053035929329/54930000000000000000 : ℝ)*(X 1 0+X 2 0)+(260126679221/549300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4975/1024 : ℝ)) (lo := (2149/20000 : ℝ)) (hi := (8119/50000 : ℝ)) (c := (54924854053035929329/54930000000000000000 : ℝ)) (alpha := (260126679221/549300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (54924854053035929329/54930000000000000000 : ℝ)*(X 0 1+X 2 1)+(260126679221/549300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4975/1024 : ℝ)) (lo := (2149/20000 : ℝ)) (hi := (8119/50000 : ℝ)) (c := (54924854053035929329/54930000000000000000 : ℝ)) (alpha := (260126679221/549300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (54924854053035929329/54930000000000000000 : ℝ)*(X 0 2+X 1 2)+(260126679221/549300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4975/1024 : ℝ)) (lo := (2149/20000 : ℝ)) (hi := (8119/50000 : ℝ)) (c := (54924854053035929329/54930000000000000000 : ℝ)) (alpha := (260126679221/549300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-19688237/125000000 : ℝ)*X 0 0+(27215047/50000000 : ℝ)*X 0 1+(648113709/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213817281/400000000 : ℝ)*X 1 0+(-1707844579/10000000000 : ℝ)*X 1 1+(5184909687/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345431721/10000000000 : ℝ)*X 2 0+(5184909847/10000000000 : ℝ)*X 2 1+(-1707844773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2084697941/5000000000 : ℝ)*X 0 0+(3839043267/10000000000 : ℝ)*X 0 1+(1129861723/2500000000 : ℝ)*X 0 2+(2084697941/5000000000 : ℝ)*X 1 0+(3839043267/10000000000 : ℝ)*X 1 1+(1129861723/2500000000 : ℝ)*X 1 2+(2084697941/5000000000 : ℝ)*X 2 0+(3839043267/10000000000 : ℝ)*X 2 1+(1129861723/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-315024187/2000000000 : ℝ)*X 0 0+(5186873683/10000000000 : ℝ)*X 0 1+(5441024793/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276367281/10000000000 : ℝ)*X 2 0+(2720512399/5000000000 : ℝ)*X 2 1+(-7258649/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s5_5 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((4169559411/10000000000 : ℝ)*X 0 0+(180570783/400000000 : ℝ)*X 0 1+(3844275203/10000000000 : ℝ)*X 0 2+(4169559411/10000000000 : ℝ)*X 1 0+(180570783/400000000 : ℝ)*X 1 1+(3844275203/10000000000 : ℝ)*X 1 2+(4169559411/10000000000 : ℝ)*X 2 0+(180570783/400000000 : ℝ)*X 2 1+(3844275203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (787149459328857456728563227/457750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (351279301/50000000000000 : ℝ)*(base19) + (508258689/100000000000000 : ℝ)*(base23) + (17878173/100000000000000 : ℝ)*(upper2) + (67740411/50000000000000 : ℝ)*(upper3) + (1336054053706521/50000000000000 : ℝ)*(major0) + (1336054053706521/50000000000000 : ℝ)*(major1) + (1336054053706521/50000000000000 : ℝ)*(major2) + (1937241979632919/50000000000000 : ℝ)*(sp0) + (3874491402232863/100000000000000 : ℝ)*(sp1) + (1937245511915963/50000000000000 : ℝ)*(sp2) + (1469719616084147/100000000000000 : ℝ)*(sp3) + (8145525627/100000000000000 : ℝ)*(sp4) + (11454017/2000000000000 : ℝ)*(sp5) + (4436630281/100000000000000 : ℝ)*(sp6) + (367431013178607/25000000000000 : ℝ)*(f.failure) + (484311513098933/12500000000000 : ℝ)*(f.sum) + (403013859997/4577500000000000000000000000 : ℝ)*base65 + (3304150426515315197/915500000000000000000000000000000 : ℝ)*base68 + (5920702753474815197/915500000000000000000000000000000 : ℝ)*base70 + (1929073505067815197/915500000000000000000000000000000 : ℝ)*base72 + (9872299959309/9155000000000000000000000000 : ℝ)*base73 + (4830514856351815197/915500000000000000000000000000000 : ℝ)*base76 + (616407560743315197/915500000000000000000000000000000 : ℝ)*base78 + (2621921823220815197/915500000000000000000000000000000 : ℝ)*base80 + (16670802728101/9155000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (5783937/2500000000000000000000 : ℝ)*base89 + (5783937/2500000000000000000000 : ℝ)*base91 + (5783937/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1665_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181810191/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2149/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5373/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8119/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1665_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1665_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181810191/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8149/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10691/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5373/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8119/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1665_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1665_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1665_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181810191/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8149/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10691/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5373/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8119/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1665_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

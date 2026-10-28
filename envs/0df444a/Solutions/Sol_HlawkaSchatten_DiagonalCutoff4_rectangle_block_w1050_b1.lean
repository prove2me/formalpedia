-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1050_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:54:41.377528+00:00
-- url     : https://prove2.me/submissions/d17281e4-9a0f-4052-b96b-1b66a347ef27

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
theorem support_rectangle_w1050_s3_0 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-220670939/1000000000 : ℝ)*x 0 + (2719716807/5000000000 : ℝ)*x 1 + (2611299937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220670939/1000000000 : ℝ)^8243 ≤ (13390425723793/100000000000000 : ℝ)^6195 := by
    have hnat : (220670939 : ℕ)^8243*100000000000000^6195 ≤ 13390425723793^6195*1000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220670939 1000000000 13390425723793 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719716807/5000000000 : ℝ)^8243 ≤ (1389890572997/3125000000000 : ℝ)^6195 := by
    have hnat : (2719716807 : ℕ)^8243*3125000000000^6195 ≤ 1389890572997^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719716807 5000000000 1389890572997 3125000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2611299937/5000000000 : ℝ)^8243 ≤ (2106653795921/5000000000000 : ℝ)^6195 := by
    have hnat : (2611299937 : ℕ)^8243*5000000000000^6195 ≤ 2106653795921^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611299937 5000000000 2106653795921 5000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-220670939/1000000000 : ℝ), (2719716807/5000000000 : ℝ), (2611299937/5000000000 : ℝ)] ![(13390425723793/100000000000000 : ℝ), (1389890572997/3125000000000 : ℝ), (2106653795921/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-220670939/1000000000 : ℝ)|^8243 ≤ (13390425723793/100000000000000 : ℝ)^6195
        have hw : |(-220670939/1000000000 : ℝ)|=(220670939/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719716807/5000000000 : ℝ)|^8243 ≤ (1389890572997/3125000000000 : ℝ)^6195
        have hw : |(2719716807/5000000000 : ℝ)|=(2719716807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2611299937/5000000000 : ℝ)|^8243 ≤ (2106653795921/5000000000000 : ℝ)^6195
        have hw : |(2611299937/5000000000 : ℝ)|=(2611299937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s3_1 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5356108003/10000000000 : ℝ)*x 0 + (-1158895399/5000000000 : ℝ)*x 1 + (2611300007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356108003/10000000000 : ℝ)^8243 ≤ (43572235813191/100000000000000 : ℝ)^6195 := by
    have hnat : (5356108003 : ℕ)^8243*100000000000000^6195 ≤ 43572235813191^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356108003 10000000000 43572235813191 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1158895399/5000000000 : ℝ)^8243 ≤ (14294686757449/100000000000000 : ℝ)^6195 := by
    have hnat : (1158895399 : ℕ)^8243*100000000000000^6195 ≤ 14294686757449^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158895399 5000000000 14294686757449 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2611300007/5000000000 : ℝ)^8243 ≤ (8426615484249/20000000000000 : ℝ)^6195 := by
    have hnat : (2611300007 : ℕ)^8243*20000000000000^6195 ≤ 8426615484249^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611300007 5000000000 8426615484249 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356108003/10000000000 : ℝ), (-1158895399/5000000000 : ℝ), (2611300007/5000000000 : ℝ)] ![(43572235813191/100000000000000 : ℝ), (14294686757449/100000000000000 : ℝ), (8426615484249/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356108003/10000000000 : ℝ)|^8243 ≤ (43572235813191/100000000000000 : ℝ)^6195
        have hw : |(5356108003/10000000000 : ℝ)|=(5356108003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1158895399/5000000000 : ℝ)|^8243 ≤ (14294686757449/100000000000000 : ℝ)^6195
        have hw : |(-1158895399/5000000000 : ℝ)|=(1158895399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2611300007/5000000000 : ℝ)|^8243 ≤ (8426615484249/20000000000000 : ℝ)^6195
        have hw : |(2611300007/5000000000 : ℝ)|=(2611300007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s3_2 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5356108027/10000000000 : ℝ)*x 0 + (10200391/19531250 : ℝ)*x 1 + (-2317790533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356108027/10000000000 : ℝ)^8243 ≤ (43572236072977/100000000000000 : ℝ)^6195 := by
    have hnat : (5356108027 : ℕ)^8243*100000000000000^6195 ≤ 43572236072977^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356108027 10000000000 43572236072977 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10200391/19531250 : ℝ)^8243 ≤ (2106653966599/5000000000000 : ℝ)^6195 := by
    have hnat : (10200391 : ℕ)^8243*5000000000000^6195 ≤ 2106653966599^6195*19531250^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10200391 19531250 2106653966599 5000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2317790533/10000000000 : ℝ)^8243 ≤ (7147342291397/50000000000000 : ℝ)^6195 := by
    have hnat : (2317790533 : ℕ)^8243*50000000000000^6195 ≤ 7147342291397^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2317790533 10000000000 7147342291397 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356108027/10000000000 : ℝ), (10200391/19531250 : ℝ), (-2317790533/10000000000 : ℝ)] ![(43572236072977/100000000000000 : ℝ), (2106653966599/5000000000000 : ℝ), (7147342291397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356108027/10000000000 : ℝ)|^8243 ≤ (43572236072977/100000000000000 : ℝ)^6195
        have hw : |(5356108027/10000000000 : ℝ)|=(5356108027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10200391/19531250 : ℝ)|^8243 ≤ (2106653966599/5000000000000 : ℝ)^6195
        have hw : |(10200391/19531250 : ℝ)|=(10200391/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2317790533/10000000000 : ℝ)|^8243 ≤ (7147342291397/50000000000000 : ℝ)^6195
        have hw : |(-2317790533/10000000000 : ℝ)|=(2317790533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s3_3 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4374865439/10000000000 : ℝ)*x 0 + (4168264211/10000000000 : ℝ)*x 1 + (229593887/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374865439/10000000000 : ℝ)^8243 ≤ (4160844881667/12500000000000 : ℝ)^6195 := by
    have hnat : (4374865439 : ℕ)^8243*12500000000000^6195 ≤ 4160844881667^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374865439 10000000000 4160844881667 12500000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4168264211/10000000000 : ℝ)^8243 ≤ (31211637332149/100000000000000 : ℝ)^6195 := by
    have hnat : (4168264211 : ℕ)^8243*100000000000000^6195 ≤ 31211637332149^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4168264211 10000000000 31211637332149 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (229593887/500000000 : ℝ)^8243 ≤ (35501603604839/100000000000000 : ℝ)^6195 := by
    have hnat : (229593887 : ℕ)^8243*100000000000000^6195 ≤ 35501603604839^6195*500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229593887 500000000 35501603604839 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374865439/10000000000 : ℝ), (4168264211/10000000000 : ℝ), (229593887/500000000 : ℝ)] ![(4160844881667/12500000000000 : ℝ), (31211637332149/100000000000000 : ℝ), (35501603604839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374865439/10000000000 : ℝ)|^8243 ≤ (4160844881667/12500000000000 : ℝ)^6195
        have hw : |(4374865439/10000000000 : ℝ)|=(4374865439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4168264211/10000000000 : ℝ)|^8243 ≤ (31211637332149/100000000000000 : ℝ)^6195
        have hw : |(4168264211/10000000000 : ℝ)|=(4168264211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(229593887/500000000 : ℝ)|^8243 ≤ (35501603604839/100000000000000 : ℝ)^6195
        have hw : |(229593887/500000000 : ℝ)|=(229593887/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s3_4 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-88269317/400000000 : ℝ)*x 0 + (5223498987/10000000000 : ℝ)*x 1 + (1359632249/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88269317/400000000 : ℝ)^8243 ≤ (13390615747681/100000000000000 : ℝ)^6195 := by
    have hnat : (88269317 : ℕ)^8243*100000000000000^6195 ≤ 13390615747681^6195*400000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88269317 400000000 13390615747681 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5223498987/10000000000 : ℝ)^8243 ≤ (21071363845009/50000000000000 : ℝ)^6195 := by
    have hnat : (5223498987 : ℕ)^8243*50000000000000^6195 ≤ 21071363845009^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223498987 10000000000 21071363845009 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359632249/2500000000 : ℝ)^8243 ≤ (44466656543913/100000000000000 : ℝ)^6195 := by
    have hnat : (1359632249 : ℕ)^8243*100000000000000^6195 ≤ 44466656543913^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359632249 2500000000 44466656543913 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88269317/400000000 : ℝ), (5223498987/10000000000 : ℝ), (1359632249/2500000000 : ℝ)] ![(13390615747681/100000000000000 : ℝ), (21071363845009/50000000000000 : ℝ), (44466656543913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88269317/400000000 : ℝ)|^8243 ≤ (13390615747681/100000000000000 : ℝ)^6195
        have hw : |(-88269317/400000000 : ℝ)|=(88269317/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5223498987/10000000000 : ℝ)|^8243 ≤ (21071363845009/50000000000000 : ℝ)^6195
        have hw : |(5223498987/10000000000 : ℝ)|=(5223498987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359632249/2500000000 : ℝ)|^8243 ≤ (44466656543913/100000000000000 : ℝ)^6195
        have hw : |(1359632249/2500000000 : ℝ)|=(1359632249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s3_5 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5301556759/10000000000 : ℝ)*x 0 + (-168149/800000 : ℝ)*x 1 + (339908023/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301556759/10000000000 : ℝ)^8243 ≤ (10745686690321/25000000000000 : ℝ)^6195 := by
    have hnat : (5301556759 : ℕ)^8243*25000000000000^6195 ≤ 10745686690321^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301556759 10000000000 10745686690321 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168149/800000 : ℝ)^8243 ≤ (6275301760197/50000000000000 : ℝ)^6195 := by
    have hnat : (168149 : ℕ)^8243*50000000000000^6195 ≤ 6275301760197^6195*800000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168149 800000 6275301760197 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339908023/625000000 : ℝ)^8243 ≤ (1778665988471/4000000000000 : ℝ)^6195 := by
    have hnat : (339908023 : ℕ)^8243*4000000000000^6195 ≤ 1778665988471^6195*625000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339908023 625000000 1778665988471 4000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301556759/10000000000 : ℝ), (-168149/800000 : ℝ), (339908023/625000000 : ℝ)] ![(10745686690321/25000000000000 : ℝ), (6275301760197/50000000000000 : ℝ), (1778665988471/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301556759/10000000000 : ℝ)|^8243 ≤ (10745686690321/25000000000000 : ℝ)^6195
        have hw : |(5301556759/10000000000 : ℝ)|=(5301556759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-168149/800000 : ℝ)|^8243 ≤ (6275301760197/50000000000000 : ℝ)^6195
        have hw : |(-168149/800000 : ℝ)|=(168149/800000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339908023/625000000 : ℝ)|^8243 ≤ (1778665988471/4000000000000 : ℝ)^6195
        have hw : |(339908023/625000000 : ℝ)|=(339908023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s3_6 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5301556427/10000000000 : ℝ)*x 0 + (2719264423/5000000000 : ℝ)*x 1 + (-420372459/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301556427/10000000000 : ℝ)^8243 ≤ (42982743179719/100000000000000 : ℝ)^6195 := by
    have hnat : (5301556427 : ℕ)^8243*100000000000000^6195 ≤ 42982743179719^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301556427 10000000000 42982743179719 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719264423/5000000000 : ℝ)^8243 ≤ (44466654912033/100000000000000 : ℝ)^6195 := by
    have hnat : (2719264423 : ℕ)^8243*100000000000000^6195 ≤ 44466654912033^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719264423 5000000000 44466654912033 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (420372459/2000000000 : ℝ)^8243 ≤ (1255060189163/10000000000000 : ℝ)^6195 := by
    have hnat : (420372459 : ℕ)^8243*10000000000000^6195 ≤ 1255060189163^6195*2000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420372459 2000000000 1255060189163 10000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301556427/10000000000 : ℝ), (2719264423/5000000000 : ℝ), (-420372459/2000000000 : ℝ)] ![(42982743179719/100000000000000 : ℝ), (44466654912033/100000000000000 : ℝ), (1255060189163/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301556427/10000000000 : ℝ)|^8243 ≤ (42982743179719/100000000000000 : ℝ)^6195
        have hw : |(5301556427/10000000000 : ℝ)|=(5301556427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719264423/5000000000 : ℝ)|^8243 ≤ (44466654912033/100000000000000 : ℝ)^6195
        have hw : |(2719264423/5000000000 : ℝ)|=(2719264423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-420372459/2000000000 : ℝ)|^8243 ≤ (1255060189163/10000000000000 : ℝ)^6195
        have hw : |(-420372459/2000000000 : ℝ)|=(420372459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s3_7 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (218745543/500000000 : ℝ)*x 0 + (4590120783/10000000000 : ℝ)*x 1 + (4170031903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218745543/500000000 : ℝ)^8243 ≤ (8321804723729/25000000000000 : ℝ)^6195 := by
    have hnat : (218745543 : ℕ)^8243*25000000000000^6195 ≤ 8321804723729^6195*500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218745543 500000000 8321804723729 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4590120783/10000000000 : ℝ)^8243 ≤ (4435441299299/12500000000000 : ℝ)^6195 := by
    have hnat : (4590120783 : ℕ)^8243*12500000000000^6195 ≤ 4435441299299^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4590120783 10000000000 4435441299299 12500000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4170031903/10000000000 : ℝ)^8243 ≤ (31229250697251/100000000000000 : ℝ)^6195 := by
    have hnat : (4170031903 : ℕ)^8243*100000000000000^6195 ≤ 31229250697251^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170031903 10000000000 31229250697251 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218745543/500000000 : ℝ), (4590120783/10000000000 : ℝ), (4170031903/10000000000 : ℝ)] ![(8321804723729/25000000000000 : ℝ), (4435441299299/12500000000000 : ℝ), (31229250697251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218745543/500000000 : ℝ)|^8243 ≤ (8321804723729/25000000000000 : ℝ)^6195
        have hw : |(218745543/500000000 : ℝ)|=(218745543/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4590120783/10000000000 : ℝ)|^8243 ≤ (4435441299299/12500000000000 : ℝ)^6195
        have hw : |(4590120783/10000000000 : ℝ)|=(4590120783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4170031903/10000000000 : ℝ)|^8243 ≤ (31229250697251/100000000000000 : ℝ)^6195
        have hw : |(4170031903/10000000000 : ℝ)|=(4170031903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1050_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8397/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1079/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5171/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1493/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8397/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1079/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8397/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1079/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8397/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1079/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8397/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1079/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8397/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1079/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8397/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1079/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1079/12500 : ℝ) ^ (4121/1024 : ℝ) ≤ (5229641095025261/100000000000000000000 : ℝ) := by
    have hpowers : (1079/12500 : ℝ)^4121 ≤ (5229641095025261/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1079 : ℕ)^4121*100000000000000000000^1024 ≤ 5229641095025261^1024*12500^4121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1079 12500 5229641095025261 100000000000000000000 4121 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1079/12500 : ℝ)) (X := (5229641095025261/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8397/50000 : ℝ) ^ (4121/1024 : ℝ) ≤ (9519397749958653/12500000000000000000 : ℝ) := by
    have hpowers : (8397/50000 : ℝ)^4121 ≤ (9519397749958653/12500000000000000000 : ℝ)^1024 := by
      have hnat : (8397 : ℕ)^4121*12500000000000000000^1024 ≤ 9519397749958653^1024*50000^4121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8397 50000 9519397749958653 12500000000000000000 4121 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8397/50000 : ℝ)) (X := (9519397749958653/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005229641095025261/50000000000000000000 : ℝ) ≤ (2000051977112623/2000000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (50005229641095025261/50000000000000000000 : ℝ)^1024 ≤ (2000051977112623/2000000000000000 : ℝ)^4121 := by
      have hnat : (50005229641095025261 : ℕ)^1024*2000000000000000^4121 ≤ 2000051977112623^4121*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005229641095025261 50000000000000000000 2000051977112623 2000000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000051977112623/2000000000000000 : ℝ)) (X := (50005229641095025261/50000000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20016276964618938897/20000000000000000000 : ℝ) ≤ (10002021659435097/10000000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (20016276964618938897/20000000000000000000 : ℝ)^1024 ≤ (10002021659435097/10000000000000000 : ℝ)^4121 := by
      have hnat : (20016276964618938897 : ℕ)^1024*10000000000000000^4121 ≤ 10002021659435097^4121*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20016276964618938897 20000000000000000000 10002021659435097 10000000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002021659435097/10000000000000000 : ℝ)) (X := (20016276964618938897/20000000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6259519397749958653/6250000000000000000 : ℝ) ≤ (10003783433307079/10000000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (6259519397749958653/6250000000000000000 : ℝ)^1024 ≤ (10003783433307079/10000000000000000 : ℝ)^4121 := by
      have hnat : (6259519397749958653 : ℕ)^1024*10000000000000000^4121 ≤ 10003783433307079^4121*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6259519397749958653 6250000000000000000 10003783433307079 10000000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003783433307079/10000000000000000 : ℝ)) (X := (6259519397749958653/6250000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5229641095025261/100000000000000000000 : ℝ) ≤ ((40795852960920123691/40810000000000000000 : ℝ)+2*(880886935991/408100000000000 : ℝ)*(1079/12500 : ℝ))^(4121/1024 : ℝ) := by
    rw [show (40795852960920123691/40810000000000000000 : ℝ)+2*(880886935991/408100000000000 : ℝ)*(1079/12500 : ℝ)=(2000051977112623/2000000000000000 : ℝ) by norm_num, show 1+2*(5229641095025261/100000000000000000000 : ℝ)=(50005229641095025261/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9519397749958653/12500000000000000000 : ℝ)+(5229641095025261/100000000000000000000 : ℝ) ≤ ((40795852960920123691/40810000000000000000 : ℝ)+(880886935991/408100000000000 : ℝ)*((8397/50000 : ℝ)+(1079/12500 : ℝ)))^(4121/1024 : ℝ) := by
    rw [show (40795852960920123691/40810000000000000000 : ℝ)+(880886935991/408100000000000 : ℝ)*((8397/50000 : ℝ)+(1079/12500 : ℝ))=(10002021659435097/10000000000000000 : ℝ) by norm_num, show 1+(9519397749958653/12500000000000000000 : ℝ)+(5229641095025261/100000000000000000000 : ℝ)=(20016276964618938897/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9519397749958653/12500000000000000000 : ℝ) ≤ ((40795852960920123691/40810000000000000000 : ℝ)+2*(880886935991/408100000000000 : ℝ)*(8397/50000 : ℝ))^(4121/1024 : ℝ) := by
    rw [show (40795852960920123691/40810000000000000000 : ℝ)+2*(880886935991/408100000000000 : ℝ)*(8397/50000 : ℝ)=(10003783433307079/10000000000000000 : ℝ) by norm_num, show 1+2*(9519397749958653/12500000000000000000 : ℝ)=(6259519397749958653/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (40795852960920123691/40810000000000000000 : ℝ)*(X 1 0+X 2 0)+(880886935991/408100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (1079/12500 : ℝ)) (hi := (8397/50000 : ℝ)) (c := (40795852960920123691/40810000000000000000 : ℝ)) (alpha := (880886935991/408100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (40795852960920123691/40810000000000000000 : ℝ)*(X 0 1+X 2 1)+(880886935991/408100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (1079/12500 : ℝ)) (hi := (8397/50000 : ℝ)) (c := (40795852960920123691/40810000000000000000 : ℝ)) (alpha := (880886935991/408100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (40795852960920123691/40810000000000000000 : ℝ)*(X 0 2+X 1 2)+(880886935991/408100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (1079/12500 : ℝ)) (hi := (8397/50000 : ℝ)) (c := (40795852960920123691/40810000000000000000 : ℝ)) (alpha := (880886935991/408100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-220670939/1000000000 : ℝ)*X 0 0+(2719716807/5000000000 : ℝ)*X 0 1+(2611299937/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356108003/10000000000 : ℝ)*X 1 0+(-1158895399/5000000000 : ℝ)*X 1 1+(2611300007/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356108027/10000000000 : ℝ)*X 2 0+(10200391/19531250 : ℝ)*X 2 1+(-2317790533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4374865439/10000000000 : ℝ)*X 0 0+(4168264211/10000000000 : ℝ)*X 0 1+(229593887/500000000 : ℝ)*X 0 2+(4374865439/10000000000 : ℝ)*X 1 0+(4168264211/10000000000 : ℝ)*X 1 1+(229593887/500000000 : ℝ)*X 1 2+(4374865439/10000000000 : ℝ)*X 2 0+(4168264211/10000000000 : ℝ)*X 2 1+(229593887/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-88269317/400000000 : ℝ)*X 0 0+(5223498987/10000000000 : ℝ)*X 0 1+(1359632249/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301556759/10000000000 : ℝ)*X 1 0+(-168149/800000 : ℝ)*X 1 1+(339908023/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301556427/10000000000 : ℝ)*X 2 0+(2719264423/5000000000 : ℝ)*X 2 1+(-420372459/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((218745543/500000000 : ℝ)*X 0 0+(4590120783/10000000000 : ℝ)*X 0 1+(4170031903/10000000000 : ℝ)*X 0 2+(218745543/500000000 : ℝ)*X 1 0+(4590120783/10000000000 : ℝ)*X 1 1+(4170031903/10000000000 : ℝ)*X 1 2+(218745543/500000000 : ℝ)*X 2 0+(4590120783/10000000000 : ℝ)*X 2 1+(4170031903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2521437333042101913183/408100000000000000000000000 : ℝ) := by norm_num
    linear_combination (789115293/50000000000000 : ℝ)*(base19) + (26558631/2000000000000 : ℝ)*(base23) + (725657/500000000000 : ℝ)*(lower2) + (105387889/100000000000000 : ℝ)*(upper3) + (152550933/100000000000000 : ℝ)*(upper5) + (174313969989833/5000000000000 : ℝ)*(major0) + (174313969989833/5000000000000 : ℝ)*(major1) + (174313969989833/5000000000000 : ℝ)*(major2) + (2305928624014277/50000000000000 : ℝ)*(sp0) + (230594434870789/5000000000000 : ℝ)*(sp1) + (4611888947714817/100000000000000 : ℝ)*(sp2) + (236065503444567/10000000000000 : ℝ)*(sp3) + (8256904453/25000000000000 : ℝ)*(sp4) + (1328355197/10000000000000 : ℝ)*(sp7) + (59016707949941/2500000000000 : ℝ)*(f.failure) + (2305945137823183/50000000000000 : ℝ)*(f.sum) + (4050900366621/2040500000000000000000000000 : ℝ)*base65 + (1807716928428733603/204050000000000000000000000000000 : ℝ)*base67 + (870864598092166397/204050000000000000000000000000000 : ℝ)*base70 + (2581147805609233603/204050000000000000000000000000000 : ℝ)*base71 + (5288510381593/1020250000000000000000000000 : ℝ)*base73 + (3351080507478766397/204050000000000000000000000000000 : ℝ)*base76 + (547983664497283603/204050000000000000000000000000000 : ℝ)*base77 + (1326669465140466397/204050000000000000000000000000000 : ℝ)*base80 + (5785237084843/4081000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (665519/125000000000000000000 : ℝ)*base90 + (665519/125000000000000000000 : ℝ)*base92 + (665519/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2806349498811732327377605347/255062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2163255891/100000000000000 : ℝ)*(base19) + (963686047/50000000000000 : ℝ)*(base23) + (54001653/100000000000000 : ℝ)*(upper3) + (3042109/6250000000000 : ℝ)*(lower4) + (42572699/10000000000000 : ℝ)*(upper5) + (878870642885461/25000000000000 : ℝ)*(major0) + (878870642885461/25000000000000 : ℝ)*(major1) + (878870642885461/25000000000000 : ℝ)*(major2) + (14836138627/50000000000000 : ℝ)*(sp1) + (13064177289/50000000000000 : ℝ)*(sp2) + (4650522081578109/100000000000000 : ℝ)*(sp4) + (1162622561511241/25000000000000 : ℝ)*(sp5) + (2325247012925719/50000000000000 : ℝ)*(sp6) + (2380442694752389/100000000000000 : ℝ)*(sp7) + (2380442694752389/100000000000000 : ℝ)*(f.failure) + (4650522081578109/100000000000000 : ℝ)*(f.sum) + (18272098007171/20405000000000000000000000000 : ℝ)*base66 + (5412911713508156551/1020250000000000000000000000000000 : ℝ)*base67 + (3981359494622906551/1020250000000000000000000000000000 : ℝ)*base69 + (7982978793396156551/1020250000000000000000000000000000 : ℝ)*base71 + (121499690760071/20405000000000000000000000000 : ℝ)*base74 + (8639339697806906551/1020250000000000000000000000000000 : ℝ)*base75 + (4404233386967656551/1020250000000000000000000000000000 : ℝ)*base77 + (1991638302297093449/1020250000000000000000000000000000 : ℝ)*base80 + (93742444575711/20405000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (34241951/5000000000000000000000 : ℝ)*base90 + (34241951/5000000000000000000000 : ℝ)*base92 + (34241951/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1050_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8397/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1079/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5171/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1493/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1050_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1050_s4_0 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-442108753/2000000000 : ℝ)*x 0 + (5406722337/10000000000 : ℝ)*x 1 + (65660091/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (442108753/2000000000 : ℝ)^8243 ≤ (6710696837901/50000000000000 : ℝ)^6195 := by
    have hnat : (442108753 : ℕ)^8243*50000000000000^6195 ≤ 6710696837901^6195*2000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442108753 2000000000 6710696837901 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406722337/10000000000 : ℝ)^8243 ≤ (44120960443239/100000000000000 : ℝ)^6195 := by
    have hnat : (5406722337 : ℕ)^8243*100000000000000^6195 ≤ 44120960443239^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406722337 10000000000 44120960443239 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65660091/125000000 : ℝ)^8243 ≤ (42457645871783/100000000000000 : ℝ)^6195 := by
    have hnat : (65660091 : ℕ)^8243*100000000000000^6195 ≤ 42457645871783^6195*125000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65660091 125000000 42457645871783 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-442108753/2000000000 : ℝ), (5406722337/10000000000 : ℝ), (65660091/125000000 : ℝ)] ![(6710696837901/50000000000000 : ℝ), (44120960443239/100000000000000 : ℝ), (42457645871783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-442108753/2000000000 : ℝ)|^8243 ≤ (6710696837901/50000000000000 : ℝ)^6195
        have hw : |(-442108753/2000000000 : ℝ)|=(442108753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406722337/10000000000 : ℝ)|^8243 ≤ (44120960443239/100000000000000 : ℝ)^6195
        have hw : |(5406722337/10000000000 : ℝ)|=(5406722337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65660091/125000000 : ℝ)|^8243 ≤ (42457645871783/100000000000000 : ℝ)^6195
        have hw : |(65660091/125000000 : ℝ)|=(65660091/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s4_1 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2674010191/5000000000 : ℝ)*x 0 + (-2288844803/10000000000 : ℝ)*x 1 + (2626403623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674010191/5000000000 : ℝ)^8243 ≤ (10871178472427/25000000000000 : ℝ)^6195 := by
    have hnat : (2674010191 : ℕ)^8243*25000000000000^6195 ≤ 10871178472427^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674010191 5000000000 10871178472427 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2288844803/10000000000 : ℝ)^8243 ≤ (2811528119633/20000000000000 : ℝ)^6195 := by
    have hnat : (2288844803 : ℕ)^8243*20000000000000^6195 ≤ 2811528119633^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288844803 10000000000 2811528119633 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626403623/5000000000 : ℝ)^8243 ≤ (8491529101223/20000000000000 : ℝ)^6195 := by
    have hnat : (2626403623 : ℕ)^8243*20000000000000^6195 ≤ 8491529101223^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626403623 5000000000 8491529101223 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674010191/5000000000 : ℝ), (-2288844803/10000000000 : ℝ), (2626403623/5000000000 : ℝ)] ![(10871178472427/25000000000000 : ℝ), (2811528119633/20000000000000 : ℝ), (8491529101223/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674010191/5000000000 : ℝ)|^8243 ≤ (10871178472427/25000000000000 : ℝ)^6195
        have hw : |(2674010191/5000000000 : ℝ)|=(2674010191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2288844803/10000000000 : ℝ)|^8243 ≤ (2811528119633/20000000000000 : ℝ)^6195
        have hw : |(-2288844803/10000000000 : ℝ)|=(2288844803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626403623/5000000000 : ℝ)|^8243 ≤ (8491529101223/20000000000000 : ℝ)^6195
        have hw : |(2626403623/5000000000 : ℝ)|=(2626403623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s4_2 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5348020403/10000000000 : ℝ)*x 0 + (656600903/1250000000 : ℝ)*x 1 + (-2288844803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348020403/10000000000 : ℝ)^8243 ≤ (43484714116907/100000000000000 : ℝ)^6195 := by
    have hnat : (5348020403 : ℕ)^8243*100000000000000^6195 ≤ 43484714116907^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348020403 10000000000 43484714116907 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (656600903/1250000000 : ℝ)^8243 ≤ (21228822634753/50000000000000 : ℝ)^6195 := by
    have hnat : (656600903 : ℕ)^8243*50000000000000^6195 ≤ 21228822634753^6195*1250000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656600903 1250000000 21228822634753 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2288844803/10000000000 : ℝ)^8243 ≤ (2811528119633/20000000000000 : ℝ)^6195 := by
    have hnat : (2288844803 : ℕ)^8243*20000000000000^6195 ≤ 2811528119633^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288844803 10000000000 2811528119633 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348020403/10000000000 : ℝ), (656600903/1250000000 : ℝ), (-2288844803/10000000000 : ℝ)] ![(43484714116907/100000000000000 : ℝ), (21228822634753/50000000000000 : ℝ), (2811528119633/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348020403/10000000000 : ℝ)|^8243 ≤ (43484714116907/100000000000000 : ℝ)^6195
        have hw : |(5348020403/10000000000 : ℝ)|=(5348020403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(656600903/1250000000 : ℝ)|^8243 ≤ (21228822634753/50000000000000 : ℝ)^6195
        have hw : |(656600903/1250000000 : ℝ)|=(656600903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2288844803/10000000000 : ℝ)|^8243 ≤ (2811528119633/20000000000000 : ℝ)^6195
        have hw : |(-2288844803/10000000000 : ℝ)|=(2288844803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s4_3 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4377146431/10000000000 : ℝ)*x 0 + (422942387/1000000000 : ℝ)*x 1 + (4530118181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377146431/10000000000 : ℝ)^8243 ≤ (16654926867663/50000000000000 : ℝ)^6195 := by
    have hnat : (4377146431 : ℕ)^8243*50000000000000^6195 ≤ 16654926867663^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377146431 10000000000 16654926867663 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422942387/1000000000 : ℝ)^8243 ≤ (3977808171329/12500000000000 : ℝ)^6195 := by
    have hnat : (422942387 : ℕ)^8243*12500000000000^6195 ≤ 3977808171329^6195*1000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422942387 1000000000 3977808171329 12500000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4530118181/10000000000 : ℝ)^8243 ≤ (17433840437463/50000000000000 : ℝ)^6195 := by
    have hnat : (4530118181 : ℕ)^8243*50000000000000^6195 ≤ 17433840437463^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530118181 10000000000 17433840437463 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377146431/10000000000 : ℝ), (422942387/1000000000 : ℝ), (4530118181/10000000000 : ℝ)] ![(16654926867663/50000000000000 : ℝ), (3977808171329/12500000000000 : ℝ), (17433840437463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377146431/10000000000 : ℝ)|^8243 ≤ (16654926867663/50000000000000 : ℝ)^6195
        have hw : |(4377146431/10000000000 : ℝ)|=(4377146431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(422942387/1000000000 : ℝ)|^8243 ≤ (3977808171329/12500000000000 : ℝ)^6195
        have hw : |(422942387/1000000000 : ℝ)|=(422942387/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4530118181/10000000000 : ℝ)|^8243 ≤ (17433840437463/50000000000000 : ℝ)^6195
        have hw : |(4530118181/10000000000 : ℝ)|=(4530118181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s4_4 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-552638001/2500000000 : ℝ)*x 0 + (5253261343/10000000000 : ℝ)*x 1 + (1081253289/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (552638001/2500000000 : ℝ)^8243 ≤ (6710730118203/50000000000000 : ℝ)^6195 := by
    have hnat : (552638001 : ℕ)^8243*50000000000000^6195 ≤ 6710730118203^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552638001 2500000000 6710730118203 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253261343/10000000000 : ℝ)^8243 ≤ (42462529366831/100000000000000 : ℝ)^6195 := by
    have hnat : (5253261343 : ℕ)^8243*100000000000000^6195 ≤ 42462529366831^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253261343 10000000000 42462529366831 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081253289/2000000000 : ℝ)^8243 ≤ (44116010379421/100000000000000 : ℝ)^6195 := by
    have hnat : (1081253289 : ℕ)^8243*100000000000000^6195 ≤ 44116010379421^6195*2000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081253289 2000000000 44116010379421 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-552638001/2500000000 : ℝ), (5253261343/10000000000 : ℝ), (1081253289/2000000000 : ℝ)] ![(6710730118203/50000000000000 : ℝ), (42462529366831/100000000000000 : ℝ), (44116010379421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-552638001/2500000000 : ℝ)|^8243 ≤ (6710730118203/50000000000000 : ℝ)^6195
        have hw : |(-552638001/2500000000 : ℝ)|=(552638001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253261343/10000000000 : ℝ)|^8243 ≤ (42462529366831/100000000000000 : ℝ)^6195
        have hw : |(5253261343/10000000000 : ℝ)|=(5253261343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081253289/2000000000 : ℝ)|^8243 ≤ (44116010379421/100000000000000 : ℝ)^6195
        have hw : |(1081253289/2000000000 : ℝ)|=(1081253289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s4_5 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309303691/10000000000 : ℝ)*x 0 + (-2135385567/10000000000 : ℝ)*x 1 + (675783301/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309303691/10000000000 : ℝ)^8243 ≤ (43066339650201/100000000000000 : ℝ)^6195 := by
    have hnat : (5309303691 : ℕ)^8243*100000000000000^6195 ≤ 43066339650201^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309303691 10000000000 43066339650201 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2135385567/10000000000 : ℝ)^8243 ≤ (3204412589279/25000000000000 : ℝ)^6195 := by
    have hnat : (2135385567 : ℕ)^8243*25000000000000^6195 ≤ 3204412589279^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135385567 10000000000 3204412589279 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675783301/1250000000 : ℝ)^8243 ≤ (44116009977681/100000000000000 : ℝ)^6195 := by
    have hnat : (675783301 : ℕ)^8243*100000000000000^6195 ≤ 44116009977681^6195*1250000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675783301 1250000000 44116009977681 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309303691/10000000000 : ℝ), (-2135385567/10000000000 : ℝ), (675783301/1250000000 : ℝ)] ![(43066339650201/100000000000000 : ℝ), (3204412589279/25000000000000 : ℝ), (44116009977681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309303691/10000000000 : ℝ)|^8243 ≤ (43066339650201/100000000000000 : ℝ)^6195
        have hw : |(5309303691/10000000000 : ℝ)|=(5309303691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2135385567/10000000000 : ℝ)|^8243 ≤ (3204412589279/25000000000000 : ℝ)^6195
        have hw : |(-2135385567/10000000000 : ℝ)|=(2135385567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675783301/1250000000 : ℝ)|^8243 ≤ (44116009977681/100000000000000 : ℝ)^6195
        have hw : |(675783301/1250000000 : ℝ)|=(675783301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s4_6 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309303687/10000000000 : ℝ)*x 0 + (2703133189/5000000000 : ℝ)*x 1 + (-2135385613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309303687/10000000000 : ℝ)^8243 ≤ (43066339607029/100000000000000 : ℝ)^6195 := by
    have hnat : (5309303687 : ℕ)^8243*100000000000000^6195 ≤ 43066339607029^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309303687 10000000000 43066339607029 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703133189/5000000000 : ℝ)^8243 ≤ (22058004825973/50000000000000 : ℝ)^6195 := by
    have hnat : (2703133189 : ℕ)^8243*50000000000000^6195 ≤ 22058004825973^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703133189 5000000000 22058004825973 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2135385613/10000000000 : ℝ)^8243 ≤ (400551585141/3125000000000 : ℝ)^6195 := by
    have hnat : (2135385613 : ℕ)^8243*3125000000000^6195 ≤ 400551585141^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135385613 10000000000 400551585141 3125000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309303687/10000000000 : ℝ), (2703133189/5000000000 : ℝ), (-2135385613/10000000000 : ℝ)] ![(43066339607029/100000000000000 : ℝ), (22058004825973/50000000000000 : ℝ), (400551585141/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309303687/10000000000 : ℝ)|^8243 ≤ (43066339607029/100000000000000 : ℝ)^6195
        have hw : |(5309303687/10000000000 : ℝ)|=(5309303687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703133189/5000000000 : ℝ)|^8243 ≤ (22058004825973/50000000000000 : ℝ)^6195
        have hw : |(2703133189/5000000000 : ℝ)|=(2703133189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2135385613/10000000000 : ℝ)|^8243 ≤ (400551585141/3125000000000 : ℝ)^6195
        have hw : |(-2135385613/10000000000 : ℝ)|=(2135385613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s4_7 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (175086519/400000000 : ℝ)*x 0 + (4529230717/10000000000 : ℝ)*x 1 + (4230314921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (175086519/400000000 : ℝ)^8243 ≤ (33310021255237/100000000000000 : ℝ)^6195 := by
    have hnat : (175086519 : ℕ)^8243*100000000000000^6195 ≤ 33310021255237^6195*400000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175086519 400000000 33310021255237 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4529230717/10000000000 : ℝ)^8243 ≤ (34858592333303/100000000000000 : ℝ)^6195 := by
    have hnat : (4529230717 : ℕ)^8243*100000000000000^6195 ≤ 34858592333303^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529230717 10000000000 34858592333303 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230314921/10000000000 : ℝ)^8243 ≤ (15915693192969/50000000000000 : ℝ)^6195 := by
    have hnat : (4230314921 : ℕ)^8243*50000000000000^6195 ≤ 15915693192969^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230314921 10000000000 15915693192969 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(175086519/400000000 : ℝ), (4529230717/10000000000 : ℝ), (4230314921/10000000000 : ℝ)] ![(33310021255237/100000000000000 : ℝ), (34858592333303/100000000000000 : ℝ), (15915693192969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(175086519/400000000 : ℝ)|^8243 ≤ (33310021255237/100000000000000 : ℝ)^6195
        have hw : |(175086519/400000000 : ℝ)|=(175086519/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4529230717/10000000000 : ℝ)|^8243 ≤ (34858592333303/100000000000000 : ℝ)^6195
        have hw : |(4529230717/10000000000 : ℝ)|=(4529230717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230314921/10000000000 : ℝ)|^8243 ≤ (15915693192969/50000000000000 : ℝ)^6195
        have hw : |(4230314921/10000000000 : ℝ)|=(4230314921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1050_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1493/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5171/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10987/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7123/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1493/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5171/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1493/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5171/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1493/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5171/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1493/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5171/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1493/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5171/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1493/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5171/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5171/50000 : ℝ) ^ (4121/1024 : ℝ) ≤ (2164664639690241/20000000000000000000 : ℝ) := by
    have hpowers : (5171/50000 : ℝ)^4121 ≤ (2164664639690241/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5171 : ℕ)^4121*20000000000000000000^1024 ≤ 2164664639690241^1024*50000^4121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5171 50000 2164664639690241 20000000000000000000 4121 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5171/50000 : ℝ)) (X := (2164664639690241/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1493/10000 : ℝ) ^ (4121/1024 : ℝ) ≤ (47432353653007897/100000000000000000000 : ℝ) := by
    have hpowers : (1493/10000 : ℝ)^4121 ≤ (47432353653007897/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1493 : ℕ)^4121*100000000000000000000^1024 ≤ 47432353653007897^1024*10000^4121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1493 10000 47432353653007897 100000000000000000000 4121 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1493/10000 : ℝ)) (X := (47432353653007897/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002164664639690241/10000000000000000000 : ℝ) ≤ (10000537839436129/10000000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (10002164664639690241/10000000000000000000 : ℝ)^1024 ≤ (10000537839436129/10000000000000000 : ℝ)^4121 := by
      have hnat : (10002164664639690241 : ℕ)^1024*10000000000000000^4121 ≤ 10000537839436129^4121*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002164664639690241 10000000000000000000 10000537839436129 10000000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000537839436129/10000000000000000 : ℝ)) (X := (10002164664639690241/10000000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50029127838425729551/50000000000000000000 : ℝ) ≤ (10001447239972899/10000000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (50029127838425729551/50000000000000000000 : ℝ)^1024 ≤ (10001447239972899/10000000000000000 : ℝ)^4121 := by
      have hnat : (50029127838425729551 : ℕ)^1024*10000000000000000^4121 ≤ 10001447239972899^4121*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029127838425729551 50000000000000000000 10001447239972899 10000000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001447239972899/10000000000000000 : ℝ)) (X := (50029127838425729551/50000000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50047432353653007897/50000000000000000000 : ℝ) ≤ (10002356640509669/10000000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (50047432353653007897/50000000000000000000 : ℝ)^1024 ≤ (10002356640509669/10000000000000000 : ℝ)^4121 := by
      have hnat : (50047432353653007897 : ℕ)^1024*10000000000000000^4121 ≤ 10002356640509669^4121*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50047432353653007897 50000000000000000000 10002356640509669 10000000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002356640509669/10000000000000000 : ℝ)) (X := (50047432353653007897/50000000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2164664639690241/20000000000000000000 : ℝ) ≤ ((11465914391657602293/11470000000000000000 : ℝ)+2*(90940053677/45880000000000 : ℝ)*(5171/50000 : ℝ))^(4121/1024 : ℝ) := by
    rw [show (11465914391657602293/11470000000000000000 : ℝ)+2*(90940053677/45880000000000 : ℝ)*(5171/50000 : ℝ)=(10000537839436129/10000000000000000 : ℝ) by norm_num, show 1+2*(2164664639690241/20000000000000000000 : ℝ)=(10002164664639690241/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(47432353653007897/100000000000000000000 : ℝ)+(2164664639690241/20000000000000000000 : ℝ) ≤ ((11465914391657602293/11470000000000000000 : ℝ)+(90940053677/45880000000000 : ℝ)*((1493/10000 : ℝ)+(5171/50000 : ℝ)))^(4121/1024 : ℝ) := by
    rw [show (11465914391657602293/11470000000000000000 : ℝ)+(90940053677/45880000000000 : ℝ)*((1493/10000 : ℝ)+(5171/50000 : ℝ))=(10001447239972899/10000000000000000 : ℝ) by norm_num, show 1+(47432353653007897/100000000000000000000 : ℝ)+(2164664639690241/20000000000000000000 : ℝ)=(50029127838425729551/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(47432353653007897/100000000000000000000 : ℝ) ≤ ((11465914391657602293/11470000000000000000 : ℝ)+2*(90940053677/45880000000000 : ℝ)*(1493/10000 : ℝ))^(4121/1024 : ℝ) := by
    rw [show (11465914391657602293/11470000000000000000 : ℝ)+2*(90940053677/45880000000000 : ℝ)*(1493/10000 : ℝ)=(10002356640509669/10000000000000000 : ℝ) by norm_num, show 1+2*(47432353653007897/100000000000000000000 : ℝ)=(50047432353653007897/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11465914391657602293/11470000000000000000 : ℝ)*(X 1 0+X 2 0)+(90940053677/45880000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (5171/50000 : ℝ)) (hi := (1493/10000 : ℝ)) (c := (11465914391657602293/11470000000000000000 : ℝ)) (alpha := (90940053677/45880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11465914391657602293/11470000000000000000 : ℝ)*(X 0 1+X 2 1)+(90940053677/45880000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (5171/50000 : ℝ)) (hi := (1493/10000 : ℝ)) (c := (11465914391657602293/11470000000000000000 : ℝ)) (alpha := (90940053677/45880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11465914391657602293/11470000000000000000 : ℝ)*(X 0 2+X 1 2)+(90940053677/45880000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (5171/50000 : ℝ)) (hi := (1493/10000 : ℝ)) (c := (11465914391657602293/11470000000000000000 : ℝ)) (alpha := (90940053677/45880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-442108753/2000000000 : ℝ)*X 0 0+(5406722337/10000000000 : ℝ)*X 0 1+(65660091/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674010191/5000000000 : ℝ)*X 1 0+(-2288844803/10000000000 : ℝ)*X 1 1+(2626403623/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348020403/10000000000 : ℝ)*X 2 0+(656600903/1250000000 : ℝ)*X 2 1+(-2288844803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4377146431/10000000000 : ℝ)*X 0 0+(422942387/1000000000 : ℝ)*X 0 1+(4530118181/10000000000 : ℝ)*X 0 2+(4377146431/10000000000 : ℝ)*X 1 0+(422942387/1000000000 : ℝ)*X 1 1+(4530118181/10000000000 : ℝ)*X 1 2+(4377146431/10000000000 : ℝ)*X 2 0+(422942387/1000000000 : ℝ)*X 2 1+(4530118181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-552638001/2500000000 : ℝ)*X 0 0+(5253261343/10000000000 : ℝ)*X 0 1+(1081253289/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309303691/10000000000 : ℝ)*X 1 0+(-2135385567/10000000000 : ℝ)*X 1 1+(675783301/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309303687/10000000000 : ℝ)*X 2 0+(2703133189/5000000000 : ℝ)*X 2 1+(-2135385613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((175086519/400000000 : ℝ)*X 0 0+(4529230717/10000000000 : ℝ)*X 0 1+(4230314921/10000000000 : ℝ)*X 0 2+(175086519/400000000 : ℝ)*X 1 0+(4529230717/10000000000 : ℝ)*X 1 1+(4230314921/10000000000 : ℝ)*X 1 2+(175086519/400000000 : ℝ)*X 2 0+(4529230717/10000000000 : ℝ)*X 2 1+(4230314921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2274945158808604763071863/289062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (876923999/50000000000000 : ℝ)*(base19) + (1649399607/100000000000000 : ℝ)*(base23) + (69503263/100000000000000 : ℝ)*(lower2) + (4595927/2000000000000 : ℝ)*(upper3) + (135055527/100000000000000 : ℝ)*(upper5) + (19185243991117/390625000000 : ℝ)*(major0) + (19185243991117/390625000000 : ℝ)*(major1) + (19185243991117/390625000000 : ℝ)*(major2) + (259885190683907/4000000000000 : ℝ)*(sp0) + (6497165853852519/100000000000000 : ℝ)*(sp1) + (649716595830091/10000000000000 : ℝ)*(sp2) + (332565557524619/10000000000000 : ℝ)*(sp3) + (18920301421/50000000000000 : ℝ)*(sp4) + (21478169171/100000000000000 : ℝ)*(sp7) + (1662838526707681/50000000000000 : ℝ)*(f.failure) + (6497167607700517/100000000000000 : ℝ)*(f.sum) + (753555422473/71687500000000000000000000 : ℝ)*base65 + (5901158358874211/1120117187500000000000000000000 : ℝ)*base68 + (17786608940809499/17921875000000000000000000000000 : ℝ)*base69 + (188973444502846751/17921875000000000000000000000000 : ℝ)*base72 + (486986853351/573500000000000000000000000 : ℝ)*base73 + (128342319008809499/17921875000000000000000000000000 : ℝ)*base75 + (186320932538028249/17921875000000000000000000000000 : ℝ)*base77 + (84155556395934499/17921875000000000000000000000000 : ℝ)*base79 + (88527943911/229400000000000000000000000 : ℝ)*base81 + (3032179/2500000000000000000000 : ℝ)*base90 + (3032179/2500000000000000000000 : ℝ)*base92 + (3032179/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9793329301557255465579/2294000000000000000000000000 : ℝ) := by norm_num
    linear_combination (875207891/100000000000000 : ℝ)*(base19) + (1235388049/100000000000000 : ℝ)*(base23) + (24112821/12500000000000 : ℝ)*(lower4) + (24285683/12500000000000 : ℝ)*(upper5) + (4940577270336043/100000000000000 : ℝ)*(major0) + (4940577270336043/100000000000000 : ℝ)*(major1) + (4940577270336043/100000000000000 : ℝ)*(major2) + (632457929/50000000000000 : ℝ)*(sp0) + (25888077021/100000000000000 : ℝ)*(sp1) + (26131446313/100000000000000 : ℝ)*(sp2) + (653573445146701/10000000000000 : ℝ)*(sp4) + (1633927238274489/25000000000000 : ℝ)*(sp5) + (3267854174774253/50000000000000 : ℝ)*(sp6) + (1672709340992839/50000000000000 : ℝ)*(sp7) + (1672709340992839/50000000000000 : ℝ)*(f.failure) + (1633933929095717/25000000000000 : ℝ)*(f.sum) + (7413907340049/2294000000000000000000000000 : ℝ)*base66 + (4894095620591096599/1147000000000000000000000000000000 : ℝ)*base67 + (1763139895030903401/1147000000000000000000000000000000 : ℝ)*base70 + (3699783488410903401/1147000000000000000000000000000000 : ℝ)*base72 + (345456884077/2294000000000000000000000000 : ℝ)*base73 + (5928836493941096599/1147000000000000000000000000000000 : ℝ)*base75 + (11436376648431903401/1147000000000000000000000000000000 : ℝ)*base78 + (6252623291403096599/1147000000000000000000000000000000 : ℝ)*base79 + (2906512262663/2294000000000000000000000000 : ℝ)*base82 + (31021499/2500000000000000000000 : ℝ)*base89 + (31021499/2500000000000000000000 : ℝ)*base91 + (31021499/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1050_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1493/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5171/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7123/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1050_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1050_s5_0 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1105711641/5000000000 : ℝ)*x 0 + (2698732007/5000000000 : ℝ)*x 1 + (5261488699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1105711641/5000000000 : ℝ)^8243 ≤ (13428499513497/100000000000000 : ℝ)^6195 := by
    have hnat : (1105711641 : ℕ)^8243*100000000000000^6195 ≤ 13428499513497^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105711641 5000000000 13428499513497 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698732007/5000000000 : ℝ)^8243 ≤ (4402046086979/10000000000000 : ℝ)^6195 := by
    have hnat : (2698732007 : ℕ)^8243*10000000000000^6195 ≤ 4402046086979^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698732007 5000000000 4402046086979 10000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261488699/10000000000 : ℝ)^8243 ≤ (42551039604377/100000000000000 : ℝ)^6195 := by
    have hnat : (5261488699 : ℕ)^8243*100000000000000^6195 ≤ 42551039604377^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261488699 10000000000 42551039604377 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1105711641/5000000000 : ℝ), (2698732007/5000000000 : ℝ), (5261488699/10000000000 : ℝ)] ![(13428499513497/100000000000000 : ℝ), (4402046086979/10000000000000 : ℝ), (42551039604377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1105711641/5000000000 : ℝ)|^8243 ≤ (13428499513497/100000000000000 : ℝ)^6195
        have hw : |(-1105711641/5000000000 : ℝ)|=(1105711641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698732007/5000000000 : ℝ)|^8243 ≤ (4402046086979/10000000000000 : ℝ)^6195
        have hw : |(2698732007/5000000000 : ℝ)|=(2698732007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261488699/10000000000 : ℝ)|^8243 ≤ (42551039604377/100000000000000 : ℝ)^6195
        have hw : |(5261488699/10000000000 : ℝ)|=(5261488699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s5_1 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345717489/10000000000 : ℝ)*x 0 + (-456091937/2000000000 : ℝ)*x 1 + (1052297789/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345717489/10000000000 : ℝ)^8243 ≤ (43459800639129/100000000000000 : ℝ)^6195 := by
    have hnat : (5345717489 : ℕ)^8243*100000000000000^6195 ≤ 43459800639129^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345717489 10000000000 43459800639129 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (456091937/2000000000 : ℝ)^8243 ≤ (2797831418789/20000000000000 : ℝ)^6195 := by
    have hnat : (456091937 : ℕ)^8243*20000000000000^6195 ≤ 2797831418789^6195*2000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456091937 2000000000 2797831418789 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052297789/2000000000 : ℝ)^8243 ≤ (2127552112577/5000000000000 : ℝ)^6195 := by
    have hnat : (1052297789 : ℕ)^8243*5000000000000^6195 ≤ 2127552112577^6195*2000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052297789 2000000000 2127552112577 5000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345717489/10000000000 : ℝ), (-456091937/2000000000 : ℝ), (1052297789/2000000000 : ℝ)] ![(43459800639129/100000000000000 : ℝ), (2797831418789/20000000000000 : ℝ), (2127552112577/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345717489/10000000000 : ℝ)|^8243 ≤ (43459800639129/100000000000000 : ℝ)^6195
        have hw : |(5345717489/10000000000 : ℝ)|=(5345717489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-456091937/2000000000 : ℝ)|^8243 ≤ (2797831418789/20000000000000 : ℝ)^6195
        have hw : |(-456091937/2000000000 : ℝ)|=(456091937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052297789/2000000000 : ℝ)|^8243 ≤ (2127552112577/5000000000000 : ℝ)^6195
        have hw : |(1052297789/2000000000 : ℝ)|=(1052297789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s5_2 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345717437/10000000000 : ℝ)*x 0 + (2630744473/5000000000 : ℝ)*x 1 + (-2280459753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345717437/10000000000 : ℝ)^8243 ≤ (43459800076621/100000000000000 : ℝ)^6195 := by
    have hnat : (5345717437 : ℕ)^8243*100000000000000^6195 ≤ 43459800076621^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345717437 10000000000 43459800076621 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630744473/5000000000 : ℝ)^8243 ≤ (42551042262301/100000000000000 : ℝ)^6195 := by
    have hnat : (2630744473 : ℕ)^8243*100000000000000^6195 ≤ 42551042262301^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630744473 5000000000 42551042262301 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2280459753/10000000000 : ℝ)^8243 ≤ (6994578824491/50000000000000 : ℝ)^6195 := by
    have hnat : (2280459753 : ℕ)^8243*50000000000000^6195 ≤ 6994578824491^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280459753 10000000000 6994578824491 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345717437/10000000000 : ℝ), (2630744473/5000000000 : ℝ), (-2280459753/10000000000 : ℝ)] ![(43459800076621/100000000000000 : ℝ), (42551042262301/100000000000000 : ℝ), (6994578824491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345717437/10000000000 : ℝ)|^8243 ≤ (43459800076621/100000000000000 : ℝ)^6195
        have hw : |(5345717437/10000000000 : ℝ)|=(5345717437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630744473/5000000000 : ℝ)|^8243 ≤ (42551042262301/100000000000000 : ℝ)^6195
        have hw : |(2630744473/5000000000 : ℝ)|=(2630744473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2280459753/10000000000 : ℝ)|^8243 ≤ (6994578824491/50000000000000 : ℝ)^6195
        have hw : |(-2280459753/10000000000 : ℝ)|=(2280459753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s5_3 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2188827597/5000000000 : ℝ)*x 0 + (2123440377/5000000000 : ℝ)*x 1 + (112813181/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188827597/5000000000 : ℝ)^8243 ≤ (1332600216909/4000000000000 : ℝ)^6195 := by
    have hnat : (2188827597 : ℕ)^8243*4000000000000^6195 ≤ 1332600216909^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188827597 5000000000 1332600216909 4000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123440377/5000000000 : ℝ)^8243 ≤ (31997353064203/100000000000000 : ℝ)^6195 := by
    have hnat : (2123440377 : ℕ)^8243*100000000000000^6195 ≤ 31997353064203^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123440377 5000000000 31997353064203 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112813181/250000000 : ℝ)^8243 ≤ (6937528299279/20000000000000 : ℝ)^6195 := by
    have hnat : (112813181 : ℕ)^8243*20000000000000^6195 ≤ 6937528299279^6195*250000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112813181 250000000 6937528299279 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188827597/5000000000 : ℝ), (2123440377/5000000000 : ℝ), (112813181/250000000 : ℝ)] ![(1332600216909/4000000000000 : ℝ), (31997353064203/100000000000000 : ℝ), (6937528299279/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188827597/5000000000 : ℝ)|^8243 ≤ (1332600216909/4000000000000 : ℝ)^6195
        have hw : |(2188827597/5000000000 : ℝ)|=(2188827597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2123440377/5000000000 : ℝ)|^8243 ≤ (31997353064203/100000000000000 : ℝ)^6195
        have hw : |(2123440377/5000000000 : ℝ)|=(2123440377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(112813181/250000000 : ℝ)|^8243 ≤ (6937528299279/20000000000000 : ℝ)^6195
        have hw : |(112813181/250000000 : ℝ)|=(112813181/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s5_4 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2211429/10000000 : ℝ)*x 0 + (1052368681/2000000000 : ℝ)*x 1 + (2698554011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2211429/10000000 : ℝ)^8243 ≤ (2685709142741/20000000000000 : ℝ)^6195 := by
    have hnat : (2211429 : ℕ)^8243*20000000000000^6195 ≤ 2685709142741^6195*10000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211429 10000000 2685709142741 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052368681/2000000000 : ℝ)^8243 ≤ (2659678535981/6250000000000 : ℝ)^6195 := by
    have hnat : (1052368681 : ℕ)^8243*6250000000000^6195 ≤ 2659678535981^6195*2000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052368681 2000000000 2659678535981 6250000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698554011/5000000000 : ℝ)^8243 ≤ (1100414942383/2500000000000 : ℝ)^6195 := by
    have hnat : (2698554011 : ℕ)^8243*2500000000000^6195 ≤ 1100414942383^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698554011 5000000000 1100414942383 2500000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2211429/10000000 : ℝ), (1052368681/2000000000 : ℝ), (2698554011/5000000000 : ℝ)] ![(2685709142741/20000000000000 : ℝ), (2659678535981/6250000000000 : ℝ), (1100414942383/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2211429/10000000 : ℝ)|^8243 ≤ (2685709142741/20000000000000 : ℝ)^6195
        have hw : |(-2211429/10000000 : ℝ)|=(2211429/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052368681/2000000000 : ℝ)|^8243 ≤ (2659678535981/6250000000000 : ℝ)^6195
        have hw : |(1052368681/2000000000 : ℝ)|=(1052368681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698554011/5000000000 : ℝ)|^8243 ≤ (1100414942383/2500000000000 : ℝ)^6195
        have hw : |(2698554011/5000000000 : ℝ)|=(2698554011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s5_5 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311512629/10000000000 : ℝ)*x 0 + (-17158723/80000000 : ℝ)*x 1 + (2698554011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311512629/10000000000 : ℝ)^8243 ≤ (21545091239273/50000000000000 : ℝ)^6195 := by
    have hnat : (5311512629 : ℕ)^8243*50000000000000^6195 ≤ 21545091239273^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311512629 10000000000 21545091239273 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17158723/80000000 : ℝ)^8243 ≤ (12893219803249/100000000000000 : ℝ)^6195 := by
    have hnat : (17158723 : ℕ)^8243*100000000000000^6195 ≤ 12893219803249^6195*80000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17158723 80000000 12893219803249 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698554011/5000000000 : ℝ)^8243 ≤ (1100414942383/2500000000000 : ℝ)^6195 := by
    have hnat : (2698554011 : ℕ)^8243*2500000000000^6195 ≤ 1100414942383^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698554011 5000000000 1100414942383 2500000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311512629/10000000000 : ℝ), (-17158723/80000000 : ℝ), (2698554011/5000000000 : ℝ)] ![(21545091239273/50000000000000 : ℝ), (12893219803249/100000000000000 : ℝ), (1100414942383/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311512629/10000000000 : ℝ)|^8243 ≤ (21545091239273/50000000000000 : ℝ)^6195
        have hw : |(5311512629/10000000000 : ℝ)|=(5311512629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17158723/80000000 : ℝ)|^8243 ≤ (12893219803249/100000000000000 : ℝ)^6195
        have hw : |(-17158723/80000000 : ℝ)|=(17158723/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698554011/5000000000 : ℝ)|^8243 ≤ (1100414942383/2500000000000 : ℝ)^6195
        have hw : |(2698554011/5000000000 : ℝ)|=(2698554011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s5_6 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531151263/1000000000 : ℝ)*x 0 + (2698554011/5000000000 : ℝ)*x 1 + (-17158723/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531151263/1000000000 : ℝ)^8243 ≤ (43090182489341/100000000000000 : ℝ)^6195 := by
    have hnat : (531151263 : ℕ)^8243*100000000000000^6195 ≤ 43090182489341^6195*1000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531151263 1000000000 43090182489341 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698554011/5000000000 : ℝ)^8243 ≤ (1100414942383/2500000000000 : ℝ)^6195 := by
    have hnat : (2698554011 : ℕ)^8243*2500000000000^6195 ≤ 1100414942383^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698554011 5000000000 1100414942383 2500000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17158723/80000000 : ℝ)^8243 ≤ (12893219803249/100000000000000 : ℝ)^6195 := by
    have hnat : (17158723 : ℕ)^8243*100000000000000^6195 ≤ 12893219803249^6195*80000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17158723 80000000 12893219803249 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531151263/1000000000 : ℝ), (2698554011/5000000000 : ℝ), (-17158723/80000000 : ℝ)] ![(43090182489341/100000000000000 : ℝ), (1100414942383/2500000000000 : ℝ), (12893219803249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531151263/1000000000 : ℝ)|^8243 ≤ (43090182489341/100000000000000 : ℝ)^6195
        have hw : |(531151263/1000000000 : ℝ)|=(531151263/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698554011/5000000000 : ℝ)|^8243 ≤ (1100414942383/2500000000000 : ℝ)^6195
        have hw : |(2698554011/5000000000 : ℝ)|=(2698554011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17158723/80000000 : ℝ)|^8243 ≤ (12893219803249/100000000000000 : ℝ)^6195
        have hw : |(-17158723/80000000 : ℝ)|=(17158723/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s5_7 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4377666369/10000000000 : ℝ)*x 0 + (2255917189/5000000000 : ℝ)*x 1 + (4247576329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377666369/10000000000 : ℝ)^8243 ≤ (3331511858197/10000000000000 : ℝ)^6195 := by
    have hnat : (4377666369 : ℕ)^8243*10000000000000^6195 ≤ 3331511858197^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377666369 10000000000 3331511858197 10000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255917189/5000000000 : ℝ)^8243 ≤ (34680554949833/100000000000000 : ℝ)^6195 := by
    have hnat : (2255917189 : ℕ)^8243*100000000000000^6195 ≤ 34680554949833^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255917189 5000000000 34680554949833 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4247576329/10000000000 : ℝ)^8243 ≤ (8001081612517/25000000000000 : ℝ)^6195 := by
    have hnat : (4247576329 : ℕ)^8243*25000000000000^6195 ≤ 8001081612517^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247576329 10000000000 8001081612517 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377666369/10000000000 : ℝ), (2255917189/5000000000 : ℝ), (4247576329/10000000000 : ℝ)] ![(3331511858197/10000000000000 : ℝ), (34680554949833/100000000000000 : ℝ), (8001081612517/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377666369/10000000000 : ℝ)|^8243 ≤ (3331511858197/10000000000000 : ℝ)^6195
        have hw : |(4377666369/10000000000 : ℝ)|=(4377666369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2255917189/5000000000 : ℝ)|^8243 ≤ (34680554949833/100000000000000 : ℝ)^6195
        have hw : |(2255917189/5000000000 : ℝ)|=(2255917189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4247576329/10000000000 : ℝ)|^8243 ≤ (8001081612517/25000000000000 : ℝ)^6195
        have hw : |(4247576329/10000000000 : ℝ)|=(4247576329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1050_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7123/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2793/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3513/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7123/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10987/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7123/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10987/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7123/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10987/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7123/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10987/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7123/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10987/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7123/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10987/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10987/100000 : ℝ) ^ (4121/1024 : ℝ) ≤ (13807036122302251/100000000000000000000 : ℝ) := by
    have hpowers : (10987/100000 : ℝ)^4121 ≤ (13807036122302251/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10987 : ℕ)^4121*100000000000000000000^1024 ≤ 13807036122302251^1024*100000^4121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10987 100000 13807036122302251 100000000000000000000 4121 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10987/100000 : ℝ)) (X := (13807036122302251/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7123/50000 : ℝ) ^ (4121/1024 : ℝ) ≤ (7854887371832031/20000000000000000000 : ℝ) := by
    have hpowers : (7123/50000 : ℝ)^4121 ≤ (7854887371832031/20000000000000000000 : ℝ)^1024 := by
      have hnat : (7123 : ℕ)^4121*20000000000000000000^1024 ≤ 7854887371832031^1024*50000^4121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7123 50000 7854887371832031 20000000000000000000 4121 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7123/50000 : ℝ)) (X := (7854887371832031/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013807036122302251/50000000000000000000 : ℝ) ≤ (2000137218521661/2000000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (50013807036122302251/50000000000000000000 : ℝ)^1024 ≤ (2000137218521661/2000000000000000 : ℝ)^4121 := by
      have hnat : (50013807036122302251 : ℕ)^1024*2000000000000000^4121 ≤ 2000137218521661^4121*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013807036122302251 50000000000000000000 2000137218521661 2000000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000137218521661/2000000000000000 : ℝ)) (X := (50013807036122302251/50000000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026540736490731203/50000000000000000000 : ℝ) ≤ (1250164840421209/1250000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (50026540736490731203/50000000000000000000 : ℝ)^1024 ≤ (1250164840421209/1250000000000000 : ℝ)^4121 := by
      have hnat : (50026540736490731203 : ℕ)^1024*1250000000000000^4121 ≤ 1250164840421209^4121*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026540736490731203 50000000000000000000 1250164840421209 1250000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250164840421209/1250000000000000 : ℝ)) (X := (50026540736490731203/50000000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007854887371832031/10000000000000000000 : ℝ) ≤ (10001951354131039/10000000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (10007854887371832031/10000000000000000000 : ℝ)^1024 ≤ (10001951354131039/10000000000000000 : ℝ)^4121 := by
      have hnat : (10007854887371832031 : ℕ)^1024*10000000000000000^4121 ≤ 10001951354131039^4121*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007854887371832031 10000000000000000000 10001951354131039 10000000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001951354131039/10000000000000000 : ℝ)) (X := (10007854887371832031/10000000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13807036122302251/100000000000000000000 : ℝ) ≤ ((32578334547460187537/32590000000000000000 : ℝ)+2*(632630761367/325900000000000 : ℝ)*(10987/100000 : ℝ))^(4121/1024 : ℝ) := by
    rw [show (32578334547460187537/32590000000000000000 : ℝ)+2*(632630761367/325900000000000 : ℝ)*(10987/100000 : ℝ)=(2000137218521661/2000000000000000 : ℝ) by norm_num, show 1+2*(13807036122302251/100000000000000000000 : ℝ)=(50013807036122302251/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7854887371832031/20000000000000000000 : ℝ)+(13807036122302251/100000000000000000000 : ℝ) ≤ ((32578334547460187537/32590000000000000000 : ℝ)+(632630761367/325900000000000 : ℝ)*((7123/50000 : ℝ)+(10987/100000 : ℝ)))^(4121/1024 : ℝ) := by
    rw [show (32578334547460187537/32590000000000000000 : ℝ)+(632630761367/325900000000000 : ℝ)*((7123/50000 : ℝ)+(10987/100000 : ℝ))=(1250164840421209/1250000000000000 : ℝ) by norm_num, show 1+(7854887371832031/20000000000000000000 : ℝ)+(13807036122302251/100000000000000000000 : ℝ)=(50026540736490731203/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7854887371832031/20000000000000000000 : ℝ) ≤ ((32578334547460187537/32590000000000000000 : ℝ)+2*(632630761367/325900000000000 : ℝ)*(7123/50000 : ℝ))^(4121/1024 : ℝ) := by
    rw [show (32578334547460187537/32590000000000000000 : ℝ)+2*(632630761367/325900000000000 : ℝ)*(7123/50000 : ℝ)=(10001951354131039/10000000000000000 : ℝ) by norm_num, show 1+2*(7854887371832031/20000000000000000000 : ℝ)=(10007854887371832031/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32578334547460187537/32590000000000000000 : ℝ)*(X 1 0+X 2 0)+(632630761367/325900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (10987/100000 : ℝ)) (hi := (7123/50000 : ℝ)) (c := (32578334547460187537/32590000000000000000 : ℝ)) (alpha := (632630761367/325900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32578334547460187537/32590000000000000000 : ℝ)*(X 0 1+X 2 1)+(632630761367/325900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (10987/100000 : ℝ)) (hi := (7123/50000 : ℝ)) (c := (32578334547460187537/32590000000000000000 : ℝ)) (alpha := (632630761367/325900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32578334547460187537/32590000000000000000 : ℝ)*(X 0 2+X 1 2)+(632630761367/325900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (10987/100000 : ℝ)) (hi := (7123/50000 : ℝ)) (c := (32578334547460187537/32590000000000000000 : ℝ)) (alpha := (632630761367/325900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1105711641/5000000000 : ℝ)*X 0 0+(2698732007/5000000000 : ℝ)*X 0 1+(5261488699/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345717489/10000000000 : ℝ)*X 1 0+(-456091937/2000000000 : ℝ)*X 1 1+(1052297789/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345717437/10000000000 : ℝ)*X 2 0+(2630744473/5000000000 : ℝ)*X 2 1+(-2280459753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2188827597/5000000000 : ℝ)*X 0 0+(2123440377/5000000000 : ℝ)*X 0 1+(112813181/250000000 : ℝ)*X 0 2+(2188827597/5000000000 : ℝ)*X 1 0+(2123440377/5000000000 : ℝ)*X 1 1+(112813181/250000000 : ℝ)*X 1 2+(2188827597/5000000000 : ℝ)*X 2 0+(2123440377/5000000000 : ℝ)*X 2 1+(112813181/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2211429/10000000 : ℝ)*X 0 0+(1052368681/2000000000 : ℝ)*X 0 1+(2698554011/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311512629/10000000000 : ℝ)*X 1 0+(-17158723/80000000 : ℝ)*X 1 1+(2698554011/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531151263/1000000000 : ℝ)*X 2 0+(2698554011/5000000000 : ℝ)*X 2 1+(-17158723/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4377666369/10000000000 : ℝ)*X 0 0+(2255917189/5000000000 : ℝ)*X 0 1+(4247576329/10000000000 : ℝ)*X 0 2+(4377666369/10000000000 : ℝ)*X 1 0+(2255917189/5000000000 : ℝ)*X 1 1+(4247576329/10000000000 : ℝ)*X 1 2+(4377666369/10000000000 : ℝ)*X 2 0+(2255917189/5000000000 : ℝ)*X 2 1+(4247576329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1716168255909746350574224689/162950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1567199729/100000000000000 : ℝ)*(base19) + (339171991/25000000000000 : ℝ)*(base23) + (74290943/100000000000000 : ℝ)*(lower2) + (73629181/20000000000000 : ℝ)*(upper3) + (9243763/6250000000000 : ℝ)*(upper5) + (1111881482585701/20000000000000 : ℝ)*(major0) + (1111881482585701/20000000000000 : ℝ)*(major1) + (1111881482585701/20000000000000 : ℝ)*(major2) + (7354325685374539/100000000000000 : ℝ)*(sp0) + (7354365070365647/100000000000000 : ℝ)*(sp1) + (7354365280877411/100000000000000 : ℝ)*(sp2) + (470552780495627/12500000000000 : ℝ)*(sp3) + (10238047709/25000000000000 : ℝ)*(sp4) + (25593264269/100000000000000 : ℝ)*(sp7) + (752889567445857/20000000000000 : ℝ)*(f.failure) + (114911978711959/1562500000000 : ℝ)*(f.sum) + (4074537470893/1629500000000000000000000000 : ℝ)*base66 + (2669520041491708437/651800000000000000000000000000000 : ℝ)*base67 + (244154237472108437/651800000000000000000000000000000 : ℝ)*base69 + (3664398311314908437/651800000000000000000000000000000 : ℝ)*base71 + (907823058779/1629500000000000000000000000 : ℝ)*base73 + (4926065404900508437/651800000000000000000000000000000 : ℝ)*base75 + (7673349468311708437/651800000000000000000000000000000 : ℝ)*base77 + (5207628101332291563/651800000000000000000000000000000 : ℝ)*base80 + (1783998272209/651800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (2568563/1000000000000000000000 : ℝ)*base90 + (2568563/1000000000000000000000 : ℝ)*base92 + (2568563/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3427008167042782964535083427/814750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (792102807/100000000000000 : ℝ)*(base19) + (858166649/100000000000000 : ℝ)*(base23) + (85573967/100000000000000 : ℝ)*(upper3) + (1824421/6250000000000 : ℝ)*(lower4) + (8610227/10000000000000 : ℝ)*(upper5) + (2794273863943781/50000000000000 : ℝ)*(major0) + (2794273863943781/50000000000000 : ℝ)*(major1) + (2794273863943781/50000000000000 : ℝ)*(major2) + (4114795747/20000000000000 : ℝ)*(sp1) + (22082531221/100000000000000 : ℝ)*(sp2) + (7392915663870909/100000000000000 : ℝ)*(sp4) + (7392894297789367/100000000000000 : ℝ)*(sp5) + (3696446361586519/50000000000000 : ℝ)*(sp6) + (1892089825848631/50000000000000 : ℝ)*(sp7) + (1892089825848631/50000000000000 : ℝ)*(f.failure) + (7392915663870909/100000000000000 : ℝ)*(f.sum) + (9821297867311/4073750000000000000000000000 : ℝ)*base65 + (3617756443608057397/1629500000000000000000000000000000 : ℝ)*base67 + (15940092451665557397/1629500000000000000000000000000000 : ℝ)*base69 + (18954747720835557397/1629500000000000000000000000000000 : ℝ)*base71 + (2601393114933/8147500000000000000000000000 : ℝ)*base74 + (48801803997861057397/1629500000000000000000000000000000 : ℝ)*base75 + (27749064287795057397/1629500000000000000000000000000000 : ℝ)*base77 + (6253816914076557397/1629500000000000000000000000000000 : ℝ)*base79 + (20472367935571/16295000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (13398229/2500000000000000000000 : ℝ)*base90 + (13398229/2500000000000000000000 : ℝ)*base92 + (13398229/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1050_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7123/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2793/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1050_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1050_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8397/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1079/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2793/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1050_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1050_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1050_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8397/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1079/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2793/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1050_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

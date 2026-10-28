-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1265_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:57:25.345917+00:00
-- url     : https://prove2.me/submissions/f9532af3-a292-4b52-8e29-cd91acb2d336

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
theorem support_rectangle_w1265_s9_0 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2109422411/10000000000 : ℝ)*x 0 + (5390721667/10000000000 : ℝ)*x 1 + (263377899/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109422411/10000000000 : ℝ)^4229 ≤ (64150979073/500000000000 : ℝ)^3205 := by
    have hnat : (2109422411 : ℕ)^4229*500000000000^3205 ≤ 64150979073^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109422411 10000000000 64150979073 500000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390721667/10000000000 : ℝ)^4229 ≤ (2212472551343/5000000000000 : ℝ)^3205 := by
    have hnat : (5390721667 : ℕ)^4229*5000000000000^3205 ≤ 2212472551343^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390721667 10000000000 2212472551343 5000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263377899/500000000 : ℝ)^4229 ≤ (5365044143/12500000000 : ℝ)^3205 := by
    have hnat : (263377899 : ℕ)^4229*12500000000^3205 ≤ 5365044143^3205*500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263377899 500000000 5365044143 12500000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2109422411/10000000000 : ℝ), (5390721667/10000000000 : ℝ), (263377899/500000000 : ℝ)] ![(64150979073/500000000000 : ℝ), (2212472551343/5000000000000 : ℝ), (5365044143/12500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2109422411/10000000000 : ℝ)|^4229 ≤ (64150979073/500000000000 : ℝ)^3205
        have hw : |(-2109422411/10000000000 : ℝ)|=(2109422411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390721667/10000000000 : ℝ)|^4229 ≤ (2212472551343/5000000000000 : ℝ)^3205
        have hw : |(5390721667/10000000000 : ℝ)|=(5390721667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263377899/500000000 : ℝ)|^4229 ≤ (5365044143/12500000000 : ℝ)^3205
        have hw : |(263377899/500000000 : ℝ)|=(263377899/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s9_1 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672086013/5000000000 : ℝ)*x 0 + (-1085931861/5000000000 : ℝ)*x 1 + (329222371/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672086013/5000000000 : ℝ)^4229 ≤ (43745966327133/100000000000000 : ℝ)^3205 := by
    have hnat : (2672086013 : ℕ)^4229*100000000000000^3205 ≤ 43745966327133^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672086013 5000000000 43745966327133 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085931861/5000000000 : ℝ)^4229 ≤ (833355061661/6250000000000 : ℝ)^3205 := by
    have hnat : (1085931861 : ℕ)^4229*6250000000000^3205 ≤ 833355061661^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085931861 5000000000 833355061661 6250000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329222371/625000000 : ℝ)^4229 ≤ (2146017633547/5000000000000 : ℝ)^3205 := by
    have hnat : (329222371 : ℕ)^4229*5000000000000^3205 ≤ 2146017633547^3205*625000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329222371 625000000 2146017633547 5000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672086013/5000000000 : ℝ), (-1085931861/5000000000 : ℝ), (329222371/625000000 : ℝ)] ![(43745966327133/100000000000000 : ℝ), (833355061661/6250000000000 : ℝ), (2146017633547/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672086013/5000000000 : ℝ)|^4229 ≤ (43745966327133/100000000000000 : ℝ)^3205
        have hw : |(2672086013/5000000000 : ℝ)|=(2672086013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1085931861/5000000000 : ℝ)|^4229 ≤ (833355061661/6250000000000 : ℝ)^3205
        have hw : |(-1085931861/5000000000 : ℝ)|=(1085931861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329222371/625000000 : ℝ)|^4229 ≤ (2146017633547/5000000000000 : ℝ)^3205
        have hw : |(329222371/625000000 : ℝ)|=(329222371/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s9_2 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344171953/10000000000 : ℝ)*x 0 + (210702321/400000000 : ℝ)*x 1 + (-2171863701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344171953/10000000000 : ℝ)^4229 ≤ (21872982769327/50000000000000 : ℝ)^3205 := by
    have hnat : (5344171953 : ℕ)^4229*50000000000000^3205 ≤ 21872982769327^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344171953 10000000000 21872982769327 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210702321/400000000 : ℝ)^4229 ≤ (10730088406953/25000000000000 : ℝ)^3205 := by
    have hnat : (210702321 : ℕ)^4229*25000000000000^3205 ≤ 10730088406953^3205*400000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210702321 400000000 10730088406953 25000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2171863701/10000000000 : ℝ)^4229 ≤ (13333680816459/100000000000000 : ℝ)^3205 := by
    have hnat : (2171863701 : ℕ)^4229*100000000000000^3205 ≤ 13333680816459^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171863701 10000000000 13333680816459 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344171953/10000000000 : ℝ), (210702321/400000000 : ℝ), (-2171863701/10000000000 : ℝ)] ![(21872982769327/50000000000000 : ℝ), (10730088406953/25000000000000 : ℝ), (13333680816459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344171953/10000000000 : ℝ)|^4229 ≤ (21872982769327/50000000000000 : ℝ)^3205
        have hw : |(5344171953/10000000000 : ℝ)|=(5344171953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210702321/400000000 : ℝ)|^4229 ≤ (10730088406953/25000000000000 : ℝ)^3205
        have hw : |(210702321/400000000 : ℝ)|=(210702321/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2171863701/10000000000 : ℝ)|^4229 ≤ (13333680816459/100000000000000 : ℝ)^3205
        have hw : |(-2171863701/10000000000 : ℝ)|=(2171863701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s9_3 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4347630643/10000000000 : ℝ)*x 0 + (1055975919/2500000000 : ℝ)*x 1 + (4474859963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347630643/10000000000 : ℝ)^4229 ≤ (16658814110173/50000000000000 : ℝ)^3205 := by
    have hnat : (4347630643 : ℕ)^4229*50000000000000^3205 ≤ 16658814110173^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347630643 10000000000 16658814110173 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055975919/2500000000 : ℝ)^4229 ≤ (6414448672527/20000000000000 : ℝ)^3205 := by
    have hnat : (1055975919 : ℕ)^4229*20000000000000^3205 ≤ 6414448672527^3205*2500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055975919 2500000000 6414448672527 20000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4474859963/10000000000 : ℝ)^4229 ≤ (34610128403511/100000000000000 : ℝ)^3205 := by
    have hnat : (4474859963 : ℕ)^4229*100000000000000^3205 ≤ 34610128403511^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474859963 10000000000 34610128403511 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347630643/10000000000 : ℝ), (1055975919/2500000000 : ℝ), (4474859963/10000000000 : ℝ)] ![(16658814110173/50000000000000 : ℝ), (6414448672527/20000000000000 : ℝ), (34610128403511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347630643/10000000000 : ℝ)|^4229 ≤ (16658814110173/50000000000000 : ℝ)^3205
        have hw : |(4347630643/10000000000 : ℝ)|=(4347630643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055975919/2500000000 : ℝ)|^4229 ≤ (6414448672527/20000000000000 : ℝ)^3205
        have hw : |(1055975919/2500000000 : ℝ)|=(1055975919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4474859963/10000000000 : ℝ)|^4229 ≤ (34610128403511/100000000000000 : ℝ)^3205
        have hw : |(4474859963/10000000000 : ℝ)|=(4474859963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s9_4 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-263678387/1250000000 : ℝ)*x 0 + (210714747/400000000 : ℝ)*x 1 + (269520489/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263678387/1250000000 : ℝ)^4229 ≤ (12830233414711/100000000000000 : ℝ)^3205 := by
    have hnat : (263678387 : ℕ)^4229*100000000000000^3205 ≤ 12830233414711^3205*1250000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263678387 1250000000 12830233414711 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210714747/400000000 : ℝ)^4229 ≤ (134136542409/312500000000 : ℝ)^3205 := by
    have hnat : (210714747 : ℕ)^4229*312500000000^3205 ≤ 134136542409^3205*400000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210714747 400000000 134136542409 312500000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269520489/500000000 : ℝ)^4229 ≤ (691344890529/1562500000000 : ℝ)^3205 := by
    have hnat : (269520489 : ℕ)^4229*1562500000000^3205 ≤ 691344890529^3205*500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269520489 500000000 691344890529 1562500000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-263678387/1250000000 : ℝ), (210714747/400000000 : ℝ), (269520489/500000000 : ℝ)] ![(12830233414711/100000000000000 : ℝ), (134136542409/312500000000 : ℝ), (691344890529/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-263678387/1250000000 : ℝ)|^4229 ≤ (12830233414711/100000000000000 : ℝ)^3205
        have hw : |(-263678387/1250000000 : ℝ)|=(263678387/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210714747/400000000 : ℝ)|^4229 ≤ (134136542409/312500000000 : ℝ)^3205
        have hw : |(210714747/400000000 : ℝ)|=(210714747/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269520489/500000000 : ℝ)|^4229 ≤ (691344890529/1562500000000 : ℝ)^3205
        have hw : |(269520489/500000000 : ℝ)|=(269520489/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s9_5 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2173819981/5000000000 : ℝ)*x 0 + (4474227/10000000 : ℝ)*x 1 + (528067373/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173819981/5000000000 : ℝ)^4229 ≤ (3331772245281/10000000000000 : ℝ)^3205 := by
    have hnat : (2173819981 : ℕ)^4229*10000000000000^3205 ≤ 3331772245281^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173819981 5000000000 3331772245281 10000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4474227/10000000 : ℝ)^4229 ≤ (8650917214647/25000000000000 : ℝ)^3205 := by
    have hnat : (4474227 : ℕ)^4229*25000000000000^3205 ≤ 8650917214647^3205*10000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474227 10000000 8650917214647 25000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528067373/1250000000 : ℝ)^4229 ≤ (16039304337663/50000000000000 : ℝ)^3205 := by
    have hnat : (528067373 : ℕ)^4229*50000000000000^3205 ≤ 16039304337663^3205*1250000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528067373 1250000000 16039304337663 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173819981/5000000000 : ℝ), (4474227/10000000 : ℝ), (528067373/1250000000 : ℝ)] ![(3331772245281/10000000000000 : ℝ), (8650917214647/25000000000000 : ℝ), (16039304337663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173819981/5000000000 : ℝ)|^4229 ≤ (3331772245281/10000000000000 : ℝ)^3205
        have hw : |(2173819981/5000000000 : ℝ)|=(2173819981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4474227/10000000 : ℝ)|^4229 ≤ (8650917214647/25000000000000 : ℝ)^3205
        have hw : |(4474227/10000000 : ℝ)|=(4474227/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528067373/1250000000 : ℝ)|^4229 ≤ (16039304337663/50000000000000 : ℝ)^3205
        have hw : |(528067373/1250000000 : ℝ)|=(528067373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1265_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5753/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11507/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3529/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3529/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5753/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3529/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5753/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3529/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5753/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3529/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5753/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3529/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5753/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3529/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5753/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5753/50000 : ℝ) ^ (8457/2048 : ℝ) ≤ (13249095416068211/100000000000000000000 : ℝ) := by
    have hpowers : (5753/50000 : ℝ)^8457 ≤ (13249095416068211/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5753 : ℕ)^8457*100000000000000000000^2048 ≤ 13249095416068211^2048*50000^8457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5753 50000 13249095416068211 100000000000000000000 8457 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5753/50000 : ℝ)) (X := (13249095416068211/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3529/25000 : ℝ) ^ (8457/2048 : ℝ) ≤ (1540969136817749/5000000000000000000 : ℝ) := by
    have hpowers : (3529/25000 : ℝ)^8457 ≤ (1540969136817749/5000000000000000000 : ℝ)^2048 := by
      have hnat : (3529 : ℕ)^8457*5000000000000000000^2048 ≤ 1540969136817749^2048*25000^8457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3529 25000 1540969136817749 5000000000000000000 8457 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3529/25000 : ℝ)) (X := (1540969136817749/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013249095416068211/50000000000000000000 : ℝ) ≤ (400025665293509/400000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (50013249095416068211/50000000000000000000 : ℝ)^2048 ≤ (400025665293509/400000000000000 : ℝ)^8457 := by
      have hnat : (50013249095416068211 : ℕ)^2048*400000000000000^8457 ≤ 400025665293509^8457*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013249095416068211 50000000000000000000 400025665293509 400000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400025665293509/400000000000000 : ℝ)) (X := (50013249095416068211/50000000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044068478152423191/100000000000000000000 : ℝ) ≤ (39066668014319/39062500000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (100044068478152423191/100000000000000000000 : ℝ)^2048 ≤ (39066668014319/39062500000000 : ℝ)^8457 := by
      have hnat : (100044068478152423191 : ℕ)^2048*39062500000000^8457 ≤ 39066668014319^8457*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044068478152423191 100000000000000000000 39066668014319 39062500000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39066668014319/39062500000000 : ℝ)) (X := (100044068478152423191/100000000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501540969136817749/2500000000000000000 : ℝ) ≤ (10001492390993603/10000000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (2501540969136817749/2500000000000000000 : ℝ)^2048 ≤ (10001492390993603/10000000000000000 : ℝ)^8457 := by
      have hnat : (2501540969136817749 : ℕ)^2048*10000000000000000^8457 ≤ 10001492390993603^8457*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501540969136817749 2500000000000000000 10001492390993603 10000000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001492390993603/10000000000000000 : ℝ)) (X := (2501540969136817749/2500000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13249095416068211/100000000000000000000 : ℝ) ≤ ((1449549212850384999/1450000000000000000 : ℝ)+2*(47264369771/29000000000000 : ℝ)*(5753/50000 : ℝ))^(8457/2048 : ℝ) := by
    rw [show (1449549212850384999/1450000000000000000 : ℝ)+2*(47264369771/29000000000000 : ℝ)*(5753/50000 : ℝ)=(400025665293509/400000000000000 : ℝ) by norm_num, show 1+2*(13249095416068211/100000000000000000000 : ℝ)=(50013249095416068211/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1540969136817749/5000000000000000000 : ℝ)+(13249095416068211/100000000000000000000 : ℝ) ≤ ((1449549212850384999/1450000000000000000 : ℝ)+(47264369771/29000000000000 : ℝ)*((3529/25000 : ℝ)+(5753/50000 : ℝ)))^(8457/2048 : ℝ) := by
    rw [show (1449549212850384999/1450000000000000000 : ℝ)+(47264369771/29000000000000 : ℝ)*((3529/25000 : ℝ)+(5753/50000 : ℝ))=(39066668014319/39062500000000 : ℝ) by norm_num, show 1+(1540969136817749/5000000000000000000 : ℝ)+(13249095416068211/100000000000000000000 : ℝ)=(100044068478152423191/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1540969136817749/5000000000000000000 : ℝ) ≤ ((1449549212850384999/1450000000000000000 : ℝ)+2*(47264369771/29000000000000 : ℝ)*(3529/25000 : ℝ))^(8457/2048 : ℝ) := by
    rw [show (1449549212850384999/1450000000000000000 : ℝ)+2*(47264369771/29000000000000 : ℝ)*(3529/25000 : ℝ)=(10001492390993603/10000000000000000 : ℝ) by norm_num, show 1+2*(1540969136817749/5000000000000000000 : ℝ)=(2501540969136817749/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1449549212850384999/1450000000000000000 : ℝ)*(X 1 0+X 2 0)+(47264369771/29000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (5753/50000 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (1449549212850384999/1450000000000000000 : ℝ)) (alpha := (47264369771/29000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1449549212850384999/1450000000000000000 : ℝ)*(X 0 1+X 2 1)+(47264369771/29000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (5753/50000 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (1449549212850384999/1450000000000000000 : ℝ)) (alpha := (47264369771/29000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1449549212850384999/1450000000000000000 : ℝ)*(X 0 2+X 1 2)+(47264369771/29000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (5753/50000 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (1449549212850384999/1450000000000000000 : ℝ)) (alpha := (47264369771/29000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2109422411/10000000000 : ℝ)*X 0 0+(5390721667/10000000000 : ℝ)*X 0 1+(263377899/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672086013/5000000000 : ℝ)*X 1 0+(-1085931861/5000000000 : ℝ)*X 1 1+(329222371/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344171953/10000000000 : ℝ)*X 2 0+(210702321/400000000 : ℝ)*X 2 1+(-2171863701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4347630643/10000000000 : ℝ)*X 0 0+(1055975919/2500000000 : ℝ)*X 0 1+(4474859963/10000000000 : ℝ)*X 0 2+(4347630643/10000000000 : ℝ)*X 1 0+(1055975919/2500000000 : ℝ)*X 1 1+(4474859963/10000000000 : ℝ)*X 1 2+(4347630643/10000000000 : ℝ)*X 2 0+(1055975919/2500000000 : ℝ)*X 2 1+(4474859963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-263678387/1250000000 : ℝ)*X 0 0+(210714747/400000000 : ℝ)*X 0 1+(269520489/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2173819981/5000000000 : ℝ)*X 0 0+(4474227/10000000 : ℝ)*X 0 1+(528067373/1250000000 : ℝ)*X 0 2+(2173819981/5000000000 : ℝ)*X 1 0+(4474227/10000000 : ℝ)*X 1 1+(528067373/1250000000 : ℝ)*X 1 2+(2173819981/5000000000 : ℝ)*X 2 0+(4474227/10000000 : ℝ)*X 2 1+(528067373/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (319252301132035262313/181250000000000000000000000 : ℝ) := by norm_num
    linear_combination (493288717/100000000000000 : ℝ)*(base19) + (17894177/6250000000000 : ℝ)*(base23) + (6417973/12500000000000 : ℝ)*(lower2) + (748873/1250000000000 : ℝ)*(upper3) + (2192649/50000000000000 : ℝ)*(upper5) + (756504457066267/12500000000000 : ℝ)*(major0) + (756504457066267/12500000000000 : ℝ)*(major1) + (756504457066267/12500000000000 : ℝ)*(major2) + (4059644921805343/50000000000000 : ℝ)*(sp0) + (1623860113601089/20000000000000 : ℝ)*(sp1) + (811930077498733/10000000000000 : ℝ)*(sp2) + (3984763385003633/100000000000000 : ℝ)*(sp3) + (2804420869/25000000000000 : ℝ)*(sp4) + (3404024701/50000000000000 : ℝ)*(sp5) + (796954038610607/20000000000000 : ℝ)*(f.failure) + (4059650530647081/50000000000000 : ℝ)*(f.sum) + (800388797/725000000000000000000000000 : ℝ)*base66 + (25298361292328733/18125000000000000000000000000000 : ℝ)*base67 + (47737158815796267/18125000000000000000000000000000 : ℝ)*base70 + (194258640825453733/18125000000000000000000000000000 : ℝ)*base71 + (182071969311/362500000000000000000000000 : ℝ)*base74 + (418821013090796267/18125000000000000000000000000000 : ℝ)*base76 + (137497051025453733/18125000000000000000000000000000 : ℝ)*base77 + (221135942615171267/18125000000000000000000000000000 : ℝ)*base80 + (3507658532897/725000000000000000000000000 : ℝ)*base82 + (1826863/500000000000000000000 : ℝ)*base90 + (1826863/500000000000000000000 : ℝ)*base92 + (1826863/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1265_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5753/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11507/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1265_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1265_box_0 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1986437801/10000000000 : ℝ)*x 0 + (167952903/312500000 : ℝ)*x 1 + (107489847/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1986437801/10000000000 : ℝ)^4229 ≤ (11852483974123/100000000000000 : ℝ)^3205 := by
    have hnat : (1986437801 : ℕ)^4229*100000000000000^3205 ≤ 11852483974123^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986437801 10000000000 11852483974123 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (167952903/312500000 : ℝ)^4229 ≤ (44073760961789/100000000000000 : ℝ)^3205 := by
    have hnat : (167952903 : ℕ)^4229*100000000000000^3205 ≤ 44073760961789^3205*312500000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167952903 312500000 44073760961789 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107489847/200000000 : ℝ)^4229 ≤ (44073755053729/100000000000000 : ℝ)^3205 := by
    have hnat : (107489847 : ℕ)^4229*100000000000000^3205 ≤ 44073755053729^3205*200000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107489847 200000000 44073755053729 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1986437801/10000000000 : ℝ), (167952903/312500000 : ℝ), (107489847/200000000 : ℝ)] ![(11852483974123/100000000000000 : ℝ), (44073760961789/100000000000000 : ℝ), (44073755053729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1986437801/10000000000 : ℝ)|^4229 ≤ (11852483974123/100000000000000 : ℝ)^3205
        have hw : |(-1986437801/10000000000 : ℝ)|=(1986437801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(167952903/312500000 : ℝ)|^4229 ≤ (44073760961789/100000000000000 : ℝ)^3205
        have hw : |(167952903/312500000 : ℝ)|=(167952903/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107489847/200000000 : ℝ)|^4229 ≤ (44073755053729/100000000000000 : ℝ)^3205
        have hw : |(107489847/200000000 : ℝ)|=(107489847/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_box_1 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (662118803/1250000000 : ℝ)*x 0 + (-2091880189/10000000000 : ℝ)*x 1 + (671811611/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662118803/1250000000 : ℝ)^4229 ≤ (43236643374819/100000000000000 : ℝ)^3205 := by
    have hnat : (662118803 : ℕ)^4229*100000000000000^3205 ≤ 43236643374819^3205*1250000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662118803 1250000000 43236643374819 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2091880189/10000000000 : ℝ)^4229 ≤ (12689595742421/100000000000000 : ℝ)^3205 := by
    have hnat : (2091880189 : ℕ)^4229*100000000000000^3205 ≤ 12689595742421^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091880189 10000000000 12689595742421 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (671811611/1250000000 : ℝ)^4229 ≤ (5509220109403/12500000000000 : ℝ)^3205 := by
    have hnat : (671811611 : ℕ)^4229*12500000000000^3205 ≤ 5509220109403^3205*1250000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671811611 1250000000 5509220109403 12500000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662118803/1250000000 : ℝ), (-2091880189/10000000000 : ℝ), (671811611/1250000000 : ℝ)] ![(43236643374819/100000000000000 : ℝ), (12689595742421/100000000000000 : ℝ), (5509220109403/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662118803/1250000000 : ℝ)|^4229 ≤ (43236643374819/100000000000000 : ℝ)^3205
        have hw : |(662118803/1250000000 : ℝ)|=(662118803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2091880189/10000000000 : ℝ)|^4229 ≤ (12689595742421/100000000000000 : ℝ)^3205
        have hw : |(-2091880189/10000000000 : ℝ)|=(2091880189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(671811611/1250000000 : ℝ)|^4229 ≤ (5509220109403/12500000000000 : ℝ)^3205
        have hw : |(671811611/1250000000 : ℝ)|=(671811611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_box_2 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2648475129/5000000000 : ℝ)*x 0 + (5374492587/10000000000 : ℝ)*x 1 + (-1045940409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648475129/5000000000 : ℝ)^4229 ≤ (10809160396729/25000000000000 : ℝ)^3205 := by
    have hnat : (2648475129 : ℕ)^4229*25000000000000^3205 ≤ 10809160396729^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648475129 5000000000 10809160396729 25000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5374492587/10000000000 : ℝ)^4229 ≤ (44073757618217/100000000000000 : ℝ)^3205 := by
    have hnat : (5374492587 : ℕ)^4229*100000000000000^3205 ≤ 44073757618217^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374492587 10000000000 44073757618217 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045940409/5000000000 : ℝ)^4229 ≤ (6344800388547/50000000000000 : ℝ)^3205 := by
    have hnat : (1045940409 : ℕ)^4229*50000000000000^3205 ≤ 6344800388547^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045940409 5000000000 6344800388547 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648475129/5000000000 : ℝ), (5374492587/10000000000 : ℝ), (-1045940409/5000000000 : ℝ)] ![(10809160396729/25000000000000 : ℝ), (44073757618217/100000000000000 : ℝ), (6344800388547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648475129/5000000000 : ℝ)|^4229 ≤ (10809160396729/25000000000000 : ℝ)^3205
        have hw : |(2648475129/5000000000 : ℝ)|=(2648475129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5374492587/10000000000 : ℝ)|^4229 ≤ (44073757618217/100000000000000 : ℝ)^3205
        have hw : |(5374492587/10000000000 : ℝ)|=(5374492587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1045940409/5000000000 : ℝ)|^4229 ≤ (6344800388547/50000000000000 : ℝ)^3205
        have hw : |(-1045940409/5000000000 : ℝ)|=(1045940409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_box_3 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4453933477/10000000000 : ℝ)*x 0 + (4296506313/10000000000 : ℝ)*x 1 + (4296506017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4453933477/10000000000 : ℝ)^4229 ≤ (34396723297057/100000000000000 : ℝ)^3205 := by
    have hnat : (4453933477 : ℕ)^4229*100000000000000^3205 ≤ 34396723297057^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4453933477 10000000000 34396723297057 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4296506313/10000000000 : ℝ)^4229 ≤ (8200409958679/25000000000000 : ℝ)^3205 := by
    have hnat : (4296506313 : ℕ)^4229*25000000000000^3205 ≤ 8200409958679^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296506313 10000000000 8200409958679 25000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4296506017/10000000000 : ℝ)^4229 ≤ (1025051151653/3125000000000 : ℝ)^3205 := by
    have hnat : (4296506017 : ℕ)^4229*3125000000000^3205 ≤ 1025051151653^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296506017 10000000000 1025051151653 3125000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4453933477/10000000000 : ℝ), (4296506313/10000000000 : ℝ), (4296506017/10000000000 : ℝ)] ![(34396723297057/100000000000000 : ℝ), (8200409958679/25000000000000 : ℝ), (1025051151653/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4453933477/10000000000 : ℝ)|^4229 ≤ (34396723297057/100000000000000 : ℝ)^3205
        have hw : |(4453933477/10000000000 : ℝ)|=(4453933477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4296506313/10000000000 : ℝ)|^4229 ≤ (8200409958679/25000000000000 : ℝ)^3205
        have hw : |(4296506313/10000000000 : ℝ)|=(4296506313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4296506017/10000000000 : ℝ)|^4229 ≤ (1025051151653/3125000000000 : ℝ)^3205
        have hw : |(4296506017/10000000000 : ℝ)|=(4296506017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_box_4 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2233780647/10000000000 : ℝ)*x 0 + (5282515221/10000000000 : ℝ)*x 1 + (1056503043/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2233780647/10000000000 : ℝ)^4229 ≤ (13837526437239/100000000000000 : ℝ)^3205 := by
    have hnat : (2233780647 : ℕ)^4229*100000000000000^3205 ≤ 13837526437239^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2233780647 10000000000 13837526437239 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282515221/10000000000 : ℝ)^4229 ≤ (43081236802773/100000000000000 : ℝ)^3205 := by
    have hnat : (5282515221 : ℕ)^4229*100000000000000^3205 ≤ 43081236802773^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282515221 10000000000 43081236802773 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056503043/2000000000 : ℝ)^4229 ≤ (43081236738207/100000000000000 : ℝ)^3205 := by
    have hnat : (1056503043 : ℕ)^4229*100000000000000^3205 ≤ 43081236738207^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056503043 2000000000 43081236738207 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2233780647/10000000000 : ℝ), (5282515221/10000000000 : ℝ), (1056503043/2000000000 : ℝ)] ![(13837526437239/100000000000000 : ℝ), (43081236802773/100000000000000 : ℝ), (43081236738207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2233780647/10000000000 : ℝ)|^4229 ≤ (13837526437239/100000000000000 : ℝ)^3205
        have hw : |(-2233780647/10000000000 : ℝ)|=(2233780647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282515221/10000000000 : ℝ)|^4229 ≤ (43081236802773/100000000000000 : ℝ)^3205
        have hw : |(5282515221/10000000000 : ℝ)|=(5282515221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056503043/2000000000 : ℝ)|^4229 ≤ (43081236738207/100000000000000 : ℝ)^3205
        have hw : |(1056503043/2000000000 : ℝ)|=(1056503043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_box_5 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2680877779/5000000000 : ℝ)*x 0 + (-532101703/2500000000 : ℝ)*x 1 + (5282515189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680877779/5000000000 : ℝ)^4229 ≤ (5491998404663/12500000000000 : ℝ)^3205 := by
    have hnat : (2680877779 : ℕ)^4229*12500000000000^3205 ≤ 5491998404663^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680877779 5000000000 5491998404663 12500000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (532101703/2500000000 : ℝ)^4229 ≤ (324569407197/2500000000000 : ℝ)^3205 := by
    have hnat : (532101703 : ℕ)^4229*2500000000000^3205 ≤ 324569407197^3205*2500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532101703 2500000000 324569407197 2500000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282515189/10000000000 : ℝ)^4229 ≤ (21540618229209/50000000000000 : ℝ)^3205 := by
    have hnat : (5282515189 : ℕ)^4229*50000000000000^3205 ≤ 21540618229209^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282515189 10000000000 21540618229209 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680877779/5000000000 : ℝ), (-532101703/2500000000 : ℝ), (5282515189/10000000000 : ℝ)] ![(5491998404663/12500000000000 : ℝ), (324569407197/2500000000000 : ℝ), (21540618229209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680877779/5000000000 : ℝ)|^4229 ≤ (5491998404663/12500000000000 : ℝ)^3205
        have hw : |(2680877779/5000000000 : ℝ)|=(2680877779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-532101703/2500000000 : ℝ)|^4229 ≤ (324569407197/2500000000000 : ℝ)^3205
        have hw : |(-532101703/2500000000 : ℝ)|=(532101703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282515189/10000000000 : ℝ)|^4229 ≤ (21540618229209/50000000000000 : ℝ)^3205
        have hw : |(5282515189/10000000000 : ℝ)|=(5282515189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_box_6 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361755531/10000000000 : ℝ)*x 0 + (5282515231/10000000000 : ℝ)*x 1 + (-266050849/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361755531/10000000000 : ℝ)^4229 ≤ (5491998368171/12500000000000 : ℝ)^3205 := by
    have hnat : (5361755531 : ℕ)^4229*12500000000000^3205 ≤ 5491998368171^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361755531 10000000000 5491998368171 12500000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282515231/10000000000 : ℝ)^4229 ≤ (8616247382077/20000000000000 : ℝ)^3205 := by
    have hnat : (5282515231 : ℕ)^4229*20000000000000^3205 ≤ 8616247382077^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282515231 10000000000 8616247382077 20000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266050849/1250000000 : ℝ)^4229 ≤ (12982776126907/100000000000000 : ℝ)^3205 := by
    have hnat : (266050849 : ℕ)^4229*100000000000000^3205 ≤ 12982776126907^3205*1250000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266050849 1250000000 12982776126907 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361755531/10000000000 : ℝ), (5282515231/10000000000 : ℝ), (-266050849/1250000000 : ℝ)] ![(5491998368171/12500000000000 : ℝ), (8616247382077/20000000000000 : ℝ), (12982776126907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361755531/10000000000 : ℝ)|^4229 ≤ (5491998368171/12500000000000 : ℝ)^3205
        have hw : |(5361755531/10000000000 : ℝ)|=(5361755531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282515231/10000000000 : ℝ)|^4229 ≤ (8616247382077/20000000000000 : ℝ)^3205
        have hw : |(5282515231/10000000000 : ℝ)|=(5282515231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-266050849/1250000000 : ℝ)|^4229 ≤ (12982776126907/100000000000000 : ℝ)^3205
        have hw : |(-266050849/1250000000 : ℝ)|=(266050849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_box_7 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4240915673/10000000000 : ℝ)*x 0 + (4402995147/10000000000 : ℝ)*x 1 + (4402995109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4240915673/10000000000 : ℝ)^4229 ≤ (16121398181431/50000000000000 : ℝ)^3205 := by
    have hnat : (4240915673 : ℕ)^4229*50000000000000^3205 ≤ 16121398181431^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240915673 10000000000 16121398181431 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4402995147/10000000000 : ℝ)^4229 ≤ (8469650501631/25000000000000 : ℝ)^3205 := by
    have hnat : (4402995147 : ℕ)^4229*25000000000000^3205 ≤ 8469650501631^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4402995147 10000000000 8469650501631 25000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4402995109/10000000000 : ℝ)^4229 ≤ (8469650405179/25000000000000 : ℝ)^3205 := by
    have hnat : (4402995109 : ℕ)^4229*25000000000000^3205 ≤ 8469650405179^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4402995109 10000000000 8469650405179 25000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4240915673/10000000000 : ℝ), (4402995147/10000000000 : ℝ), (4402995109/10000000000 : ℝ)] ![(16121398181431/50000000000000 : ℝ), (8469650501631/25000000000000 : ℝ), (8469650405179/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4240915673/10000000000 : ℝ)|^4229 ≤ (16121398181431/50000000000000 : ℝ)^3205
        have hw : |(4240915673/10000000000 : ℝ)|=(4240915673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4402995147/10000000000 : ℝ)|^4229 ≤ (8469650501631/25000000000000 : ℝ)^3205
        have hw : |(4402995147/10000000000 : ℝ)|=(4402995147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4402995109/10000000000 : ℝ)|^4229 ≤ (8469650405179/25000000000000 : ℝ)^3205
        have hw : |(4402995109/10000000000 : ℝ)|=(4402995109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_box_8 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-218192699/1000000000 : ℝ)*x 0 + (1043946917/2000000000 : ℝ)*x 1 + (5384105471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218192699/1000000000 : ℝ)^4229 ≤ (536610465661/4000000000000 : ℝ)^3205 := by
    have hnat : (218192699 : ℕ)^4229*4000000000000^3205 ≤ 536610465661^3205*1000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218192699 1000000000 536610465661 4000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043946917/2000000000 : ℝ)^4229 ≤ (5300866702989/12500000000000 : ℝ)^3205 := by
    have hnat : (1043946917 : ℕ)^4229*12500000000000^3205 ≤ 5300866702989^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043946917 2000000000 5300866702989 12500000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384105471/10000000000 : ℝ)^4229 ≤ (44177804719949/100000000000000 : ℝ)^3205 := by
    have hnat : (5384105471 : ℕ)^4229*100000000000000^3205 ≤ 44177804719949^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384105471 10000000000 44177804719949 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-218192699/1000000000 : ℝ), (1043946917/2000000000 : ℝ), (5384105471/10000000000 : ℝ)] ![(536610465661/4000000000000 : ℝ), (5300866702989/12500000000000 : ℝ), (44177804719949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-218192699/1000000000 : ℝ)|^4229 ≤ (536610465661/4000000000000 : ℝ)^3205
        have hw : |(-218192699/1000000000 : ℝ)|=(218192699/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043946917/2000000000 : ℝ)|^4229 ≤ (5300866702989/12500000000000 : ℝ)^3205
        have hw : |(1043946917/2000000000 : ℝ)|=(1043946917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384105471/10000000000 : ℝ)|^4229 ≤ (44177804719949/100000000000000 : ℝ)^3205
        have hw : |(5384105471/10000000000 : ℝ)|=(5384105471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_box_9 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2645087209/5000000000 : ℝ)*x 0 + (-260999521/1250000000 : ℝ)*x 1 + (5384105621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645087209/5000000000 : ℝ)^4229 ≤ (43163677346137/100000000000000 : ℝ)^3205 := by
    have hnat : (2645087209 : ℕ)^4229*100000000000000^3205 ≤ 43163677346137^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645087209 5000000000 43163677346137 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260999521/1250000000 : ℝ)^4229 ≤ (12658516293419/100000000000000 : ℝ)^3205 := by
    have hnat : (260999521 : ℕ)^4229*100000000000000^3205 ≤ 12658516293419^3205*1250000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260999521 1250000000 12658516293419 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384105621/10000000000 : ℝ)^4229 ≤ (4417780634397/10000000000000 : ℝ)^3205 := by
    have hnat : (5384105621 : ℕ)^4229*10000000000000^3205 ≤ 4417780634397^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384105621 10000000000 4417780634397 10000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645087209/5000000000 : ℝ), (-260999521/1250000000 : ℝ), (5384105621/10000000000 : ℝ)] ![(43163677346137/100000000000000 : ℝ), (12658516293419/100000000000000 : ℝ), (4417780634397/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645087209/5000000000 : ℝ)|^4229 ≤ (43163677346137/100000000000000 : ℝ)^3205
        have hw : |(2645087209/5000000000 : ℝ)|=(2645087209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-260999521/1250000000 : ℝ)|^4229 ≤ (12658516293419/100000000000000 : ℝ)^3205
        have hw : |(-260999521/1250000000 : ℝ)|=(260999521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384105621/10000000000 : ℝ)|^4229 ≤ (4417780634397/10000000000000 : ℝ)^3205
        have hw : |(5384105621/10000000000 : ℝ)|=(5384105621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_box_10 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290174589/10000000000 : ℝ)*x 0 + (5384105467/10000000000 : ℝ)*x 1 + (-1043998073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290174589/10000000000 : ℝ)^4229 ≤ (43163679187139/100000000000000 : ℝ)^3205 := by
    have hnat : (5290174589 : ℕ)^4229*100000000000000^3205 ≤ 43163679187139^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290174589 10000000000 43163679187139 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5384105467/10000000000 : ℝ)^4229 ≤ (22088902338321/50000000000000 : ℝ)^3205 := by
    have hnat : (5384105467 : ℕ)^4229*50000000000000^3205 ≤ 22088902338321^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384105467 10000000000 22088902338321 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043998073/5000000000 : ℝ)^4229 ≤ (1265851611743/10000000000000 : ℝ)^3205 := by
    have hnat : (1043998073 : ℕ)^4229*10000000000000^3205 ≤ 1265851611743^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043998073 5000000000 1265851611743 10000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290174589/10000000000 : ℝ), (5384105467/10000000000 : ℝ), (-1043998073/5000000000 : ℝ)] ![(43163679187139/100000000000000 : ℝ), (22088902338321/50000000000000 : ℝ), (1265851611743/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290174589/10000000000 : ℝ)|^4229 ≤ (43163679187139/100000000000000 : ℝ)^3205
        have hw : |(5290174589/10000000000 : ℝ)|=(5290174589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5384105467/10000000000 : ℝ)|^4229 ≤ (22088902338321/50000000000000 : ℝ)^3205
        have hw : |(5384105467/10000000000 : ℝ)|=(5384105467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1043998073/5000000000 : ℝ)|^4229 ≤ (1265851611743/10000000000000 : ℝ)^3205
        have hw : |(-1043998073/5000000000 : ℝ)|=(1043998073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_box_11 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2237962441/5000000000 : ℝ)*x 0 + (4285369971/10000000000 : ℝ)*x 1 + (535671237/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2237962441/5000000000 : ℝ)^4229 ≤ (34620996825637/100000000000000 : ℝ)^3205 := by
    have hnat : (2237962441 : ℕ)^4229*100000000000000^3205 ≤ 34620996825637^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237962441 5000000000 34620996825637 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4285369971/10000000000 : ℝ)^4229 ≤ (2043093872143/6250000000000 : ℝ)^3205 := by
    have hnat : (4285369971 : ℕ)^4229*6250000000000^3205 ≤ 2043093872143^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4285369971 10000000000 2043093872143 6250000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (535671237/1250000000 : ℝ)^4229 ≤ (16344750599693/50000000000000 : ℝ)^3205 := by
    have hnat : (535671237 : ℕ)^4229*50000000000000^3205 ≤ 16344750599693^3205*1250000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535671237 1250000000 16344750599693 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2237962441/5000000000 : ℝ), (4285369971/10000000000 : ℝ), (535671237/1250000000 : ℝ)] ![(34620996825637/100000000000000 : ℝ), (2043093872143/6250000000000 : ℝ), (16344750599693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2237962441/5000000000 : ℝ)|^4229 ≤ (34620996825637/100000000000000 : ℝ)^3205
        have hw : |(2237962441/5000000000 : ℝ)|=(2237962441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4285369971/10000000000 : ℝ)|^4229 ≤ (2043093872143/6250000000000 : ℝ)^3205
        have hw : |(4285369971/10000000000 : ℝ)|=(4285369971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(535671237/1250000000 : ℝ)|^4229 ≤ (16344750599693/50000000000000 : ℝ)^3205
        have hw : |(535671237/1250000000 : ℝ)|=(535671237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_box_12 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-63704321/312500000 : ℝ)*x 0 + (5436079687/10000000000 : ℝ)*x 1 + (5274428097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63704321/312500000 : ℝ)^4229 ≤ (2452876627971/20000000000000 : ℝ)^3205 := by
    have hnat : (63704321 : ℕ)^4229*20000000000000^3205 ≤ 2452876627971^3205*312500000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63704321 312500000 2452876627971 20000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436079687/10000000000 : ℝ)^4229 ≤ (5592673147579/12500000000000 : ℝ)^3205 := by
    have hnat : (5436079687 : ℕ)^4229*12500000000000^3205 ≤ 5592673147579^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436079687 10000000000 5592673147579 12500000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274428097/10000000000 : ℝ)^4229 ≤ (42994231665649/100000000000000 : ℝ)^3205 := by
    have hnat : (5274428097 : ℕ)^4229*100000000000000^3205 ≤ 42994231665649^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274428097 10000000000 42994231665649 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-63704321/312500000 : ℝ), (5436079687/10000000000 : ℝ), (5274428097/10000000000 : ℝ)] ![(2452876627971/20000000000000 : ℝ), (5592673147579/12500000000000 : ℝ), (42994231665649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-63704321/312500000 : ℝ)|^4229 ≤ (2452876627971/20000000000000 : ℝ)^3205
        have hw : |(-63704321/312500000 : ℝ)|=(63704321/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436079687/10000000000 : ℝ)|^4229 ≤ (5592673147579/12500000000000 : ℝ)^3205
        have hw : |(5436079687/10000000000 : ℝ)|=(5436079687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274428097/10000000000 : ℝ)|^4229 ≤ (42994231665649/100000000000000 : ℝ)^3205
        have hw : |(5274428097/10000000000 : ℝ)|=(5274428097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_box_13 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2683725979/5000000000 : ℝ)*x 0 + (-1065781393/5000000000 : ℝ)*x 1 + (1318606911/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683725979/5000000000 : ℝ)^4229 ≤ (4399758957493/10000000000000 : ℝ)^3205 := by
    have hnat : (2683725979 : ℕ)^4229*10000000000000^3205 ≤ 4399758957493^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683725979 5000000000 4399758957493 10000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1065781393/5000000000 : ℝ)^4229 ≤ (1626022950773/12500000000000 : ℝ)^3205 := by
    have hnat : (1065781393 : ℕ)^4229*12500000000000^3205 ≤ 1626022950773^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065781393 5000000000 1626022950773 12500000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318606911/2500000000 : ℝ)^4229 ≤ (10748556698313/25000000000000 : ℝ)^3205 := by
    have hnat : (1318606911 : ℕ)^4229*25000000000000^3205 ≤ 10748556698313^3205*2500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318606911 2500000000 10748556698313 25000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683725979/5000000000 : ℝ), (-1065781393/5000000000 : ℝ), (1318606911/2500000000 : ℝ)] ![(4399758957493/10000000000000 : ℝ), (1626022950773/12500000000000 : ℝ), (10748556698313/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683725979/5000000000 : ℝ)|^4229 ≤ (4399758957493/10000000000000 : ℝ)^3205
        have hw : |(2683725979/5000000000 : ℝ)|=(2683725979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1065781393/5000000000 : ℝ)|^4229 ≤ (1626022950773/12500000000000 : ℝ)^3205
        have hw : |(-1065781393/5000000000 : ℝ)|=(1065781393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318606911/2500000000 : ℝ)|^4229 ≤ (10748556698313/25000000000000 : ℝ)^3205
        have hw : |(1318606911/2500000000 : ℝ)|=(1318606911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_box_14 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2683725909/5000000000 : ℝ)*x 0 + (1054885559/2000000000 : ℝ)*x 1 + (-1065781387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683725909/5000000000 : ℝ)^4229 ≤ (43997588060677/100000000000000 : ℝ)^3205 := by
    have hnat : (2683725909 : ℕ)^4229*100000000000000^3205 ≤ 43997588060677^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683725909 5000000000 43997588060677 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054885559/2000000000 : ℝ)^4229 ≤ (5374278552173/12500000000000 : ℝ)^3205 := by
    have hnat : (1054885559 : ℕ)^4229*12500000000000^3205 ≤ 5374278552173^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054885559 2000000000 5374278552173 12500000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1065781387/5000000000 : ℝ)^4229 ≤ (2601636701911/20000000000000 : ℝ)^3205 := by
    have hnat : (1065781387 : ℕ)^4229*20000000000000^3205 ≤ 2601636701911^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065781387 5000000000 2601636701911 20000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683725909/5000000000 : ℝ), (1054885559/2000000000 : ℝ), (-1065781387/5000000000 : ℝ)] ![(43997588060677/100000000000000 : ℝ), (5374278552173/12500000000000 : ℝ), (2601636701911/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683725909/5000000000 : ℝ)|^4229 ≤ (43997588060677/100000000000000 : ℝ)^3205
        have hw : |(2683725909/5000000000 : ℝ)|=(2683725909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054885559/2000000000 : ℝ)|^4229 ≤ (5374278552173/12500000000000 : ℝ)^3205
        have hw : |(1054885559/2000000000 : ℝ)|=(1054885559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1065781387/5000000000 : ℝ)|^4229 ≤ (2601636701911/20000000000000 : ℝ)^3205
        have hw : |(-1065781387/5000000000 : ℝ)|=(1065781387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_box_15 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105548833/250000000 : ℝ)*x 0 + (4412353383/10000000000 : ℝ)*x 1 + (1103088401/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105548833/250000000 : ℝ)^4229 ≤ (4006588020009/12500000000000 : ℝ)^3205 := by
    have hnat : (105548833 : ℕ)^4229*12500000000000^3205 ≤ 4006588020009^3205*250000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105548833 250000000 4006588020009 12500000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4412353383/10000000000 : ℝ)^4229 ≤ (16986823394591/50000000000000 : ℝ)^3205 := by
    have hnat : (4412353383 : ℕ)^4229*50000000000000^3205 ≤ 16986823394591^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4412353383 10000000000 16986823394591 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103088401/2500000000 : ℝ)^4229 ≤ (33973649034479/100000000000000 : ℝ)^3205 := by
    have hnat : (1103088401 : ℕ)^4229*100000000000000^3205 ≤ 33973649034479^3205*2500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103088401 2500000000 33973649034479 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105548833/250000000 : ℝ), (4412353383/10000000000 : ℝ), (1103088401/2500000000 : ℝ)] ![(4006588020009/12500000000000 : ℝ), (16986823394591/50000000000000 : ℝ), (33973649034479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105548833/250000000 : ℝ)|^4229 ≤ (4006588020009/12500000000000 : ℝ)^3205
        have hw : |(105548833/250000000 : ℝ)|=(105548833/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4412353383/10000000000 : ℝ)|^4229 ≤ (16986823394591/50000000000000 : ℝ)^3205
        have hw : |(4412353383/10000000000 : ℝ)|=(4412353383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1103088401/2500000000 : ℝ)|^4229 ≤ (33973649034479/100000000000000 : ℝ)^3205
        have hw : |(1103088401/2500000000 : ℝ)|=(1103088401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1265_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11507/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62251/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14849/25000 : ℝ) ∧ (80177/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (20849/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3529/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11507/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3529/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11507/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3529/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11507/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3529/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11507/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3529/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11507/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3529/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11507/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11507/100000 : ℝ) ^ (8457/2048 : ℝ) ≤ (6626925518859347/50000000000000000000 : ℝ) := by
    have hpowers : (11507/100000 : ℝ)^8457 ≤ (6626925518859347/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11507 : ℕ)^8457*50000000000000000000^2048 ≤ 6626925518859347^2048*100000^8457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11507 100000 6626925518859347 50000000000000000000 8457 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11507/100000 : ℝ)) (X := (6626925518859347/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3529/25000 : ℝ) ^ (8457/2048 : ℝ) ≤ (1540969136817749/5000000000000000000 : ℝ) := by
    have hpowers : (3529/25000 : ℝ)^8457 ≤ (1540969136817749/5000000000000000000 : ℝ)^2048 := by
      have hnat : (3529 : ℕ)^8457*5000000000000000000^2048 ≤ 1540969136817749^2048*25000^8457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3529 25000 1540969136817749 5000000000000000000 8457 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3529/25000 : ℝ)) (X := (1540969136817749/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006626925518859347/25000000000000000000 : ℝ) ≤ (10000641862621689/10000000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (25006626925518859347/25000000000000000000 : ℝ)^2048 ≤ (10000641862621689/10000000000000000 : ℝ)^8457 := by
      have hnat : (25006626925518859347 : ℕ)^2048*10000000000000000^8457 ≤ 10000641862621689^8457*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006626925518859347 25000000000000000000 10000641862621689 10000000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000641862621689/10000000000000000 : ℝ)) (X := (25006626925518859347/25000000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022036616887036837/50000000000000000000 : ℝ) ≤ (10001067126792323/10000000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (50022036616887036837/50000000000000000000 : ℝ)^2048 ≤ (10001067126792323/10000000000000000 : ℝ)^8457 := by
      have hnat : (50022036616887036837 : ℕ)^2048*10000000000000000^8457 ≤ 10001067126792323^8457*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022036616887036837 50000000000000000000 10001067126792323 10000000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001067126792323/10000000000000000 : ℝ)) (X := (50022036616887036837/50000000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501540969136817749/2500000000000000000 : ℝ) ≤ (10001492390962957/10000000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (2501540969136817749/2500000000000000000 : ℝ)^2048 ≤ (10001492390962957/10000000000000000 : ℝ)^8457 := by
      have hnat : (2501540969136817749 : ℕ)^2048*10000000000000000^8457 ≤ 10001492390962957^8457*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501540969136817749 2500000000000000000 10001492390962957 10000000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001492390962957/10000000000000000 : ℝ)) (X := (2501540969136817749/2500000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6626925518859347/50000000000000000000 : ℝ) ≤ ((1043275503598280629/1043600000000000000 : ℝ)+2*(212632085317/130450000000000 : ℝ)*(11507/100000 : ℝ))^(8457/2048 : ℝ) := by
    rw [show (1043275503598280629/1043600000000000000 : ℝ)+2*(212632085317/130450000000000 : ℝ)*(11507/100000 : ℝ)=(10000641862621689/10000000000000000 : ℝ) by norm_num, show 1+2*(6626925518859347/50000000000000000000 : ℝ)=(25006626925518859347/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1540969136817749/5000000000000000000 : ℝ)+(6626925518859347/50000000000000000000 : ℝ) ≤ ((1043275503598280629/1043600000000000000 : ℝ)+(212632085317/130450000000000 : ℝ)*((3529/25000 : ℝ)+(11507/100000 : ℝ)))^(8457/2048 : ℝ) := by
    rw [show (1043275503598280629/1043600000000000000 : ℝ)+(212632085317/130450000000000 : ℝ)*((3529/25000 : ℝ)+(11507/100000 : ℝ))=(10001067126792323/10000000000000000 : ℝ) by norm_num, show 1+(1540969136817749/5000000000000000000 : ℝ)+(6626925518859347/50000000000000000000 : ℝ)=(50022036616887036837/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1540969136817749/5000000000000000000 : ℝ) ≤ ((1043275503598280629/1043600000000000000 : ℝ)+2*(212632085317/130450000000000 : ℝ)*(3529/25000 : ℝ))^(8457/2048 : ℝ) := by
    rw [show (1043275503598280629/1043600000000000000 : ℝ)+2*(212632085317/130450000000000 : ℝ)*(3529/25000 : ℝ)=(10001492390962957/10000000000000000 : ℝ) by norm_num, show 1+2*(1540969136817749/5000000000000000000 : ℝ)=(2501540969136817749/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1043275503598280629/1043600000000000000 : ℝ)*(X 1 0+X 2 0)+(212632085317/130450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (11507/100000 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (1043275503598280629/1043600000000000000 : ℝ)) (alpha := (212632085317/130450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1043275503598280629/1043600000000000000 : ℝ)*(X 0 1+X 2 1)+(212632085317/130450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (11507/100000 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (1043275503598280629/1043600000000000000 : ℝ)) (alpha := (212632085317/130450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1043275503598280629/1043600000000000000 : ℝ)*(X 0 2+X 1 2)+(212632085317/130450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (11507/100000 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (1043275503598280629/1043600000000000000 : ℝ)) (alpha := (212632085317/130450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1986437801/10000000000 : ℝ)*X 0 0+(167952903/312500000 : ℝ)*X 0 1+(107489847/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((662118803/1250000000 : ℝ)*X 1 0+(-2091880189/10000000000 : ℝ)*X 1 1+(671811611/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2648475129/5000000000 : ℝ)*X 2 0+(5374492587/10000000000 : ℝ)*X 2 1+(-1045940409/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4453933477/10000000000 : ℝ)*X 0 0+(4296506313/10000000000 : ℝ)*X 0 1+(4296506017/10000000000 : ℝ)*X 0 2+(4453933477/10000000000 : ℝ)*X 1 0+(4296506313/10000000000 : ℝ)*X 1 1+(4296506017/10000000000 : ℝ)*X 1 2+(4453933477/10000000000 : ℝ)*X 2 0+(4296506313/10000000000 : ℝ)*X 2 1+(4296506017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2233780647/10000000000 : ℝ)*X 0 0+(5282515221/10000000000 : ℝ)*X 0 1+(1056503043/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2680877779/5000000000 : ℝ)*X 1 0+(-532101703/2500000000 : ℝ)*X 1 1+(5282515189/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5361755531/10000000000 : ℝ)*X 2 0+(5282515231/10000000000 : ℝ)*X 2 1+(-266050849/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4240915673/10000000000 : ℝ)*X 0 0+(4402995147/10000000000 : ℝ)*X 0 1+(4402995109/10000000000 : ℝ)*X 0 2+(4240915673/10000000000 : ℝ)*X 1 0+(4402995147/10000000000 : ℝ)*X 1 1+(4402995109/10000000000 : ℝ)*X 1 2+(4240915673/10000000000 : ℝ)*X 2 0+(4402995147/10000000000 : ℝ)*X 2 1+(4402995109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-218192699/1000000000 : ℝ)*X 0 0+(1043946917/2000000000 : ℝ)*X 0 1+(5384105471/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2645087209/5000000000 : ℝ)*X 1 0+(-260999521/1250000000 : ℝ)*X 1 1+(5384105621/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5290174589/10000000000 : ℝ)*X 2 0+(5384105467/10000000000 : ℝ)*X 2 1+(-1043998073/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2237962441/5000000000 : ℝ)*X 0 0+(4285369971/10000000000 : ℝ)*X 0 1+(535671237/1250000000 : ℝ)*X 0 2+(2237962441/5000000000 : ℝ)*X 1 0+(4285369971/10000000000 : ℝ)*X 1 1+(535671237/1250000000 : ℝ)*X 1 2+(2237962441/5000000000 : ℝ)*X 2 0+(4285369971/10000000000 : ℝ)*X 2 1+(535671237/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-63704321/312500000 : ℝ)*X 0 0+(5436079687/10000000000 : ℝ)*X 0 1+(5274428097/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2683725979/5000000000 : ℝ)*X 1 0+(-1065781393/5000000000 : ℝ)*X 1 1+(1318606911/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2683725909/5000000000 : ℝ)*X 2 0+(1054885559/2000000000 : ℝ)*X 2 1+(-1065781387/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((105548833/250000000 : ℝ)*X 0 0+(4412353383/10000000000 : ℝ)*X 0 1+(1103088401/2500000000 : ℝ)*X 0 2+(105548833/250000000 : ℝ)*X 1 0+(4412353383/10000000000 : ℝ)*X 1 1+(1103088401/2500000000 : ℝ)*X 1 2+(105548833/250000000 : ℝ)*X 2 0+(4412353383/10000000000 : ℝ)*X 2 1+(1103088401/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62251/100000 : ℝ) ≤ (-406017341065221165367217949/652250000000000000000000000 : ℝ) := by norm_num
    linear_combination (4423727/50000000000000 : ℝ)*(lower0) + (16927921/50000000000000 : ℝ)*(lower2) + (6279241/20000000000000 : ℝ)*(lower4) + (80441634531317/2000000000000 : ℝ)*(major0) + (80441634531317/2000000000000 : ℝ)*(major1) + (80441634531317/2000000000000 : ℝ)*(major2) + (2444792137/100000000000000 : ℝ)*(sp1) + (5416700544978327/100000000000000 : ℝ)*(sp4) + (1083339785470663/20000000000000 : ℝ)*(sp5) + (5416699193143041/100000000000000 : ℝ)*(sp6) + (2648210231008043/100000000000000 : ℝ)*(sp7) + (6617337/800000000000 : ℝ)*(sp8) + (2179002411/100000000000000 : ℝ)*(sp14) + (1426626477/100000000000000 : ℝ)*(sp15) + (66205291440863/2500000000000 : ℝ)*(f.failure) + (1354175343036363/25000000000000 : ℝ)*(f.sum) + (149232552241/16306250000000000000000000 : ℝ)*base66 + (10255653113241593/2087200000000000000000000000000 : ℝ)*base67 + (15096936144149607/2087200000000000000000000000000 : ℝ)*base70 + (33411509028363993/2087200000000000000000000000000 : ℝ)*base71 + (2933886331671/2609000000000000000000000000 : ℝ)*base74 + (14335602833508807/2087200000000000000000000000000 : ℝ)*base76 + (37378750022284793/2087200000000000000000000000000 : ℝ)*base77 + (9289801513011207/2087200000000000000000000000000 : ℝ)*base80 + (5178719163501/2609000000000000000000000000 : ℝ)*base82 + (719633/62500000000000000000 : ℝ)*base89 + (719633/62500000000000000000 : ℝ)*base91 + (719633/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (14849/25000 : ℝ) ≤ (7748529333158334965017894107/13045000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19720021/50000000000000 : ℝ)*(upper1) + (114784433/50000000000000 : ℝ)*(upper2) + (201316573/100000000000000 : ℝ)*(upper3) + (103957481/100000000000000 : ℝ)*(lower5) + (2044126204700827/50000000000000 : ℝ)*(major0) + (2044126204700827/50000000000000 : ℝ)*(major1) + (2044126204700827/50000000000000 : ℝ)*(major2) + (1366231423639053/25000000000000 : ℝ)*(sp0) + (341556958025859/6250000000000 : ℝ)*(sp1) + (5464858171894879/100000000000000 : ℝ)*(sp2) + (336464567931989/12500000000000 : ℝ)*(sp3) + (14366142467/100000000000000 : ℝ)*(sp5) + (16880665333/25000000000000 : ℝ)*(sp10) + (63093546603/100000000000000 : ℝ)*(sp11) + (1345889818501257/50000000000000 : ℝ)*(f.failure) + (1366231423639053/25000000000000 : ℝ)*(f.sum) + (26310310083987/6522500000000000000000000000 : ℝ)*base66 + (849938476133872183/52180000000000000000000000000000 : ℝ)*base67 + (1288004646910907817/52180000000000000000000000000000 : ℝ)*base70 + (134130627603492183/52180000000000000000000000000000 : ℝ)*base71 + (51116401624931/13045000000000000000000000000 : ℝ)*base73 + (279673408163207817/52180000000000000000000000000000 : ℝ)*base76 + (68427555584347817/52180000000000000000000000000000 : ℝ)*base78 + (553932081822172183/52180000000000000000000000000000 : ℝ)*base79 + (475979221090613/6522500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (13472713/1250000000000000000000 : ℝ)*base90 + (13472713/1250000000000000000000 : ℝ)*base92 + (13472713/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (80177/100000 : ℝ) ≤ (1307419174542183466869622599/1630625000000000000000000000 : ℝ) := by norm_num
    linear_combination (17074521/25000000000000 : ℝ)*(upper0) + (14271529/25000000000000 : ℝ)*(upper1) + (34283367/50000000000000 : ℝ)*(upper4) + (142335042830577/3125000000000 : ℝ)*(major0) + (142335042830577/3125000000000 : ℝ)*(major1) + (142335042830577/3125000000000 : ℝ)*(major2) + (40466102941/25000000000000 : ℝ)*(sp1) + (54764399809/50000000000000 : ℝ)*(sp2) + (3165216511/10000000000000 : ℝ)*(sp3) + (713921307/100000000000000 : ℝ)*(sp4) + (1520951103399997/25000000000000 : ℝ)*(sp8) + (6083643263109531/100000000000000 : ℝ)*(sp9) + (6083695598721677/100000000000000 : ℝ)*(sp10) + (1499439810432031/50000000000000 : ℝ)*(sp11) + (749727818257293/25000000000000 : ℝ)*(f.failure) + (1216761025504259/20000000000000 : ℝ)*(f.sum) + (9294882677049/13045000000000000000000000000 : ℝ)*base66 + (13323639595648817/3261250000000000000000000000000 : ℝ)*base68 + (6656264003796183/3261250000000000000000000000000 : ℝ)*base69 + (14722381224724933/3261250000000000000000000000000 : ℝ)*base71 + (19228430553979/3261250000000000000000000000 : ℝ)*base73 + (9587330306791317/3261250000000000000000000000000 : ℝ)*base76 + (2702387850316183/3261250000000000000000000000000 : ℝ)*base77 + (2736451626501317/3261250000000000000000000000000 : ℝ)*base80 + (524852211957/1630625000000000000000000000 : ℝ)*base81 + (564237/625000000000000000000 : ℝ)*base90 + (564237/625000000000000000000 : ℝ)*base92 + (564237/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-20849/25000 : ℝ) ≤ (-43514633492916370537194300420897/52180000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30379351/50000000000000 : ℝ)*(upper3) + (8373087/12500000000000 : ℝ)*(lower4) + (62051447/50000000000000 : ℝ)*(upper5) + (4590382370661077/100000000000000 : ℝ)*(major0) + (4590382370661077/100000000000000 : ℝ)*(major1) + (4590382370661077/100000000000000 : ℝ)*(major2) + (27338103349/100000000000000 : ℝ)*(sp4) + (71834093/16000000000 : ℝ)*(sp5) + (207262754083/50000000000000 : ℝ)*(sp6) + (230872504581/100000000000000 : ℝ)*(sp7) + (3093072026415499/50000000000000 : ℝ)*(sp12) + (6185722427853097/100000000000000 : ℝ)*(sp13) + (6185756865426181/100000000000000 : ℝ)*(sp14) + (3022160250652429/100000000000000 : ℝ)*(sp15) + (302239112315701/10000000000000 : ℝ)*(f.failure) + (6186171390934347/100000000000000 : ℝ)*(f.sum) + (4406356860089/1630625000000000000000000000 : ℝ)*base66 + (1333287299919809433/104360000000000000000000000000000 : ℝ)*base67 + (118285828857689433/104360000000000000000000000000000 : ℝ)*base69 + (7266676429809433/104360000000000000000000000000000 : ℝ)*base71 + (64380057632789/6522500000000000000000000000 : ℝ)*base73 + (621800508653969433/104360000000000000000000000000000 : ℝ)*base75 + (219398019277729433/104360000000000000000000000000000 : ℝ)*base77 + (178891994160849433/104360000000000000000000000000000 : ℝ)*base79 + (161378086263/13045000000000000000000000000 : ℝ)*base81 + (488491/250000000000000000000 : ℝ)*base89 + (488491/250000000000000000000 : ℝ)*base91 + (488491/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1265_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11507/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62251/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14849/25000 : ℝ) else (80177/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20849/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1265_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1265_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5753/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62251/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14849/25000 : ℝ) else (80177/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20849/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1265_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1265_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5753/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62251/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14849/25000 : ℝ) else (80177/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20849/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1265_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1332_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:02:32.48359+00:00
-- url     : https://prove2.me/submissions/d0f9bb14-111c-49f7-96bf-e40ba5e062f9

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
theorem support_rectangle_w1332_s3_0 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1025389051/5000000000 : ℝ)*x 0 + (5428469137/10000000000 : ℝ)*x 1 + (1046054623/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1025389051/5000000000 : ℝ)^1073 ≤ (6241432022021/50000000000000 : ℝ)^817 := by
    have hnat : (1025389051 : ℕ)^1073*50000000000000^817 ≤ 6241432022021^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025389051 5000000000 6241432022021 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428469137/10000000000 : ℝ)^1073 ≤ (2801694659261/6250000000000 : ℝ)^817 := by
    have hnat : (5428469137 : ℕ)^1073*6250000000000^817 ≤ 2801694659261^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428469137 10000000000 2801694659261 6250000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046054623/2000000000 : ℝ)^1073 ≤ (21345010699069/50000000000000 : ℝ)^817 := by
    have hnat : (1046054623 : ℕ)^1073*50000000000000^817 ≤ 21345010699069^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046054623 2000000000 21345010699069 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1025389051/5000000000 : ℝ), (5428469137/10000000000 : ℝ), (1046054623/2000000000 : ℝ)] ![(6241432022021/50000000000000 : ℝ), (2801694659261/6250000000000 : ℝ), (21345010699069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1025389051/5000000000 : ℝ)|^1073 ≤ (6241432022021/50000000000000 : ℝ)^817
        have hw : |(-1025389051/5000000000 : ℝ)|=(1025389051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428469137/10000000000 : ℝ)|^1073 ≤ (2801694659261/6250000000000 : ℝ)^817
        have hw : |(5428469137/10000000000 : ℝ)|=(5428469137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1046054623/2000000000 : ℝ)|^1073 ≤ (21345010699069/50000000000000 : ℝ)^817
        have hw : |(1046054623/2000000000 : ℝ)|=(1046054623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s3_1 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2676524797/5000000000 : ℝ)*x 0 + (-2152097473/10000000000 : ℝ)*x 1 + (2615136397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676524797/5000000000 : ℝ)^1073 ≤ (44010954008743/100000000000000 : ℝ)^817 := by
    have hnat : (2676524797 : ℕ)^1073*100000000000000^817 ≤ 44010954008743^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676524797 5000000000 44010954008743 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2152097473/10000000000 : ℝ)^1073 ≤ (13299028013777/100000000000000 : ℝ)^817 := by
    have hnat : (2152097473 : ℕ)^1073*100000000000000^817 ≤ 13299028013777^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152097473 10000000000 13299028013777 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615136397/5000000000 : ℝ)^1073 ≤ (21345008978569/50000000000000 : ℝ)^817 := by
    have hnat : (2615136397 : ℕ)^1073*50000000000000^817 ≤ 21345008978569^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615136397 5000000000 21345008978569 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676524797/5000000000 : ℝ), (-2152097473/10000000000 : ℝ), (2615136397/5000000000 : ℝ)] ![(44010954008743/100000000000000 : ℝ), (13299028013777/100000000000000 : ℝ), (21345008978569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676524797/5000000000 : ℝ)|^1073 ≤ (44010954008743/100000000000000 : ℝ)^817
        have hw : |(2676524797/5000000000 : ℝ)|=(2676524797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2152097473/10000000000 : ℝ)|^1073 ≤ (13299028013777/100000000000000 : ℝ)^817
        have hw : |(-2152097473/10000000000 : ℝ)|=(2152097473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615136397/5000000000 : ℝ)|^1073 ≤ (21345008978569/50000000000000 : ℝ)^817
        have hw : |(2615136397/5000000000 : ℝ)|=(2615136397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s3_2 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5353049911/10000000000 : ℝ)*x 0 + (104605439/200000000 : ℝ)*x 1 + (-2152098167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353049911/10000000000 : ℝ)^1073 ≤ (2200547871583/5000000000000 : ℝ)^817 := by
    have hnat : (5353049911 : ℕ)^1073*5000000000000^817 ≤ 2200547871583^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353049911 10000000000 2200547871583 5000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104605439/200000000 : ℝ)^1073 ≤ (42690008909773/100000000000000 : ℝ)^817 := by
    have hnat : (104605439 : ℕ)^1073*100000000000000^817 ≤ 42690008909773^817*200000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104605439 200000000 42690008909773 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2152098167/10000000000 : ℝ)^1073 ≤ (6649516823099/50000000000000 : ℝ)^817 := by
    have hnat : (2152098167 : ℕ)^1073*50000000000000^817 ≤ 6649516823099^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152098167 10000000000 6649516823099 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353049911/10000000000 : ℝ), (104605439/200000000 : ℝ), (-2152098167/10000000000 : ℝ)] ![(2200547871583/5000000000000 : ℝ), (42690008909773/100000000000000 : ℝ), (6649516823099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353049911/10000000000 : ℝ)|^1073 ≤ (2200547871583/5000000000000 : ℝ)^817
        have hw : |(5353049911/10000000000 : ℝ)|=(5353049911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104605439/200000000 : ℝ)|^1073 ≤ (42690008909773/100000000000000 : ℝ)^817
        have hw : |(104605439/200000000 : ℝ)|=(104605439/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2152098167/10000000000 : ℝ)|^1073 ≤ (6649516823099/50000000000000 : ℝ)^817
        have hw : |(-2152098167/10000000000 : ℝ)|=(2152098167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s3_3 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (865622793/2000000000 : ℝ)*x 0 + (2062980123/5000000000 : ℝ)*x 1 + (1134883889/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865622793/2000000000 : ℝ)^1073 ≤ (6658340047411/20000000000000 : ℝ)^817 := by
    have hnat : (865622793 : ℕ)^1073*20000000000000^817 ≤ 6658340047411^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865622793 2000000000 6658340047411 20000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2062980123/5000000000 : ℝ)^1073 ≤ (31264614697917/100000000000000 : ℝ)^817 := by
    have hnat : (2062980123 : ℕ)^1073*100000000000000^817 ≤ 31264614697917^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062980123 5000000000 31264614697917 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1134883889/2500000000 : ℝ)^1073 ≤ (35443685057463/100000000000000 : ℝ)^817 := by
    have hnat : (1134883889 : ℕ)^1073*100000000000000^817 ≤ 35443685057463^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134883889 2500000000 35443685057463 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865622793/2000000000 : ℝ), (2062980123/5000000000 : ℝ), (1134883889/2500000000 : ℝ)] ![(6658340047411/20000000000000 : ℝ), (31264614697917/100000000000000 : ℝ), (35443685057463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865622793/2000000000 : ℝ)|^1073 ≤ (6658340047411/20000000000000 : ℝ)^817
        have hw : |(865622793/2000000000 : ℝ)|=(865622793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2062980123/5000000000 : ℝ)|^1073 ≤ (31264614697917/100000000000000 : ℝ)^817
        have hw : |(2062980123/5000000000 : ℝ)|=(2062980123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1134883889/2500000000 : ℝ)|^1073 ≤ (35443685057463/100000000000000 : ℝ)^817
        have hw : |(1134883889/2500000000 : ℝ)|=(1134883889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s3_4 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-102539903/500000000 : ℝ)*x 0 + (5231103657/10000000000 : ℝ)*x 1 + (2713816733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (102539903/500000000 : ℝ)^1073 ≤ (12483023591877/100000000000000 : ℝ)^817 := by
    have hnat : (102539903 : ℕ)^1073*100000000000000^817 ≤ 12483023591877^817*500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102539903 500000000 12483023591877 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231103657/10000000000 : ℝ)^1073 ≤ (21349462360001/50000000000000 : ℝ)^817 := by
    have hnat : (5231103657 : ℕ)^1073*50000000000000^817 ≤ 21349462360001^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231103657 10000000000 21349462360001 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713816733/5000000000 : ℝ)^1073 ≤ (2801128229647/6250000000000 : ℝ)^817 := by
    have hnat : (2713816733 : ℕ)^1073*6250000000000^817 ≤ 2801128229647^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713816733 5000000000 2801128229647 6250000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-102539903/500000000 : ℝ), (5231103657/10000000000 : ℝ), (2713816733/5000000000 : ℝ)] ![(12483023591877/100000000000000 : ℝ), (21349462360001/50000000000000 : ℝ), (2801128229647/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-102539903/500000000 : ℝ)|^1073 ≤ (12483023591877/100000000000000 : ℝ)^817
        have hw : |(-102539903/500000000 : ℝ)|=(102539903/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231103657/10000000000 : ℝ)|^1073 ≤ (21349462360001/50000000000000 : ℝ)^817
        have hw : |(5231103657/10000000000 : ℝ)|=(5231103657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713816733/5000000000 : ℝ)|^1073 ≤ (2801128229647/6250000000000 : ℝ)^817
        have hw : |(2713816733/5000000000 : ℝ)|=(2713816733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s3_5 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5302055837/10000000000 : ℝ)*x 0 + (-244342143/1250000000 : ℝ)*x 1 + (1085526733/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302055837/10000000000 : ℝ)^1073 ≤ (21730577395609/50000000000000 : ℝ)^817 := by
    have hnat : (5302055837 : ℕ)^1073*50000000000000^817 ≤ 21730577395609^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302055837 10000000000 21730577395609 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (244342143/1250000000 : ℝ)^1073 ≤ (1465098920603/12500000000000 : ℝ)^817 := by
    have hnat : (244342143 : ℕ)^1073*12500000000000^817 ≤ 1465098920603^817*1250000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244342143 1250000000 1465098920603 12500000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085526733/2000000000 : ℝ)^1073 ≤ (2240902691623/5000000000000 : ℝ)^817 := by
    have hnat : (1085526733 : ℕ)^1073*5000000000000^817 ≤ 2240902691623^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085526733 2000000000 2240902691623 5000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302055837/10000000000 : ℝ), (-244342143/1250000000 : ℝ), (1085526733/2000000000 : ℝ)] ![(21730577395609/50000000000000 : ℝ), (1465098920603/12500000000000 : ℝ), (2240902691623/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302055837/10000000000 : ℝ)|^1073 ≤ (21730577395609/50000000000000 : ℝ)^817
        have hw : |(5302055837/10000000000 : ℝ)|=(5302055837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-244342143/1250000000 : ℝ)|^1073 ≤ (1465098920603/12500000000000 : ℝ)^817
        have hw : |(-244342143/1250000000 : ℝ)|=(244342143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085526733/2000000000 : ℝ)|^1073 ≤ (2240902691623/5000000000000 : ℝ)^817
        have hw : |(1085526733/2000000000 : ℝ)|=(1085526733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s3_6 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2651028749/5000000000 : ℝ)*x 0 + (2713816253/5000000000 : ℝ)*x 1 + (-1954736469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651028749/5000000000 : ℝ)^1073 ≤ (10865293168183/25000000000000 : ℝ)^817 := by
    have hnat : (2651028749 : ℕ)^1073*25000000000000^817 ≤ 10865293168183^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651028749 5000000000 10865293168183 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713816253/5000000000 : ℝ)^1073 ≤ (22409020631689/50000000000000 : ℝ)^817 := by
    have hnat : (2713816253 : ℕ)^1073*50000000000000^817 ≤ 22409020631689^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713816253 5000000000 22409020631689 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1954736469/10000000000 : ℝ)^1073 ≤ (11720786049253/100000000000000 : ℝ)^817 := by
    have hnat : (1954736469 : ℕ)^1073*100000000000000^817 ≤ 11720786049253^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954736469 10000000000 11720786049253 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651028749/5000000000 : ℝ), (2713816253/5000000000 : ℝ), (-1954736469/10000000000 : ℝ)] ![(10865293168183/25000000000000 : ℝ), (22409020631689/50000000000000 : ℝ), (11720786049253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651028749/5000000000 : ℝ)|^1073 ≤ (10865293168183/25000000000000 : ℝ)^817
        have hw : |(2651028749/5000000000 : ℝ)|=(2651028749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713816253/5000000000 : ℝ)|^1073 ≤ (22409020631689/50000000000000 : ℝ)^817
        have hw : |(2713816253/5000000000 : ℝ)|=(2713816253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1954736469/10000000000 : ℝ)|^1073 ≤ (11720786049253/100000000000000 : ℝ)^817
        have hw : |(-1954736469/10000000000 : ℝ)|=(1954736469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s3_7 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4328155347/10000000000 : ℝ)*x 0 + (4537802317/10000000000 : ℝ)*x 1 + (4127703919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328155347/10000000000 : ℝ)^1073 ≤ (665842365719/2000000000000 : ℝ)^817 := by
    have hnat : (4328155347 : ℕ)^1073*2000000000000^817 ≤ 665842365719^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328155347 10000000000 665842365719 2000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4537802317/10000000000 : ℝ)^1073 ≤ (35425913005147/100000000000000 : ℝ)^817 := by
    have hnat : (4537802317 : ℕ)^1073*100000000000000^817 ≤ 35425913005147^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4537802317 10000000000 35425913005147 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4127703919/10000000000 : ℝ)^1073 ≤ (31281968694237/100000000000000 : ℝ)^817 := by
    have hnat : (4127703919 : ℕ)^1073*100000000000000^817 ≤ 31281968694237^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127703919 10000000000 31281968694237 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328155347/10000000000 : ℝ), (4537802317/10000000000 : ℝ), (4127703919/10000000000 : ℝ)] ![(665842365719/2000000000000 : ℝ), (35425913005147/100000000000000 : ℝ), (31281968694237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328155347/10000000000 : ℝ)|^1073 ≤ (665842365719/2000000000000 : ℝ)^817
        have hw : |(4328155347/10000000000 : ℝ)|=(4328155347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4537802317/10000000000 : ℝ)|^1073 ≤ (35425913005147/100000000000000 : ℝ)^817
        have hw : |(4537802317/10000000000 : ℝ)|=(4537802317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4127703919/10000000000 : ℝ)|^1073 ≤ (31281968694237/100000000000000 : ℝ)^817
        have hw : |(4127703919/10000000000 : ℝ)|=(4127703919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s3_8 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-84725643/10000000000 : ℝ)*x 0 + (2861307311/5000000000 : ℝ)*x 1 + (6057159533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84725643/10000000000 : ℝ)^1073 ≤ (47502445523/25000000000000 : ℝ)^817 := by
    have hnat : (84725643 : ℕ)^1073*25000000000000^817 ≤ 47502445523^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84725643 10000000000 47502445523 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2861307311/5000000000 : ℝ)^1073 ≤ (24021980121819/50000000000000 : ℝ)^817 := by
    have hnat : (2861307311 : ℕ)^1073*50000000000000^817 ≤ 24021980121819^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2861307311 5000000000 24021980121819 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6057159533/10000000000 : ℝ)^1073 ≤ (808844218199/1562500000000 : ℝ)^817 := by
    have hnat : (6057159533 : ℕ)^1073*1562500000000^817 ≤ 808844218199^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6057159533 10000000000 808844218199 1562500000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-84725643/10000000000 : ℝ), (2861307311/5000000000 : ℝ), (6057159533/10000000000 : ℝ)] ![(47502445523/25000000000000 : ℝ), (24021980121819/50000000000000 : ℝ), (808844218199/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-84725643/10000000000 : ℝ)|^1073 ≤ (47502445523/25000000000000 : ℝ)^817
        have hw : |(-84725643/10000000000 : ℝ)|=(84725643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2861307311/5000000000 : ℝ)|^1073 ≤ (24021980121819/50000000000000 : ℝ)^817
        have hw : |(2861307311/5000000000 : ℝ)|=(2861307311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6057159533/10000000000 : ℝ)|^1073 ≤ (808844218199/1562500000000 : ℝ)^817
        have hw : |(6057159533/10000000000 : ℝ)|=(6057159533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s3_9 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (503959257/5000000000 : ℝ)*x 0 + (-2144346169/5000000000 : ℝ)*x 1 + (1741416401/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (503959257/5000000000 : ℝ)^1073 ≤ (1227714160619/25000000000000 : ℝ)^817 := by
    have hnat : (503959257 : ℕ)^1073*25000000000000^817 ≤ 1227714160619^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503959257 5000000000 1227714160619 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2144346169/5000000000 : ℝ)^1073 ≤ (3289402548571/10000000000000 : ℝ)^817 := by
    have hnat : (2144346169 : ℕ)^1073*10000000000000^817 ≤ 3289402548571^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144346169 5000000000 3289402548571 10000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1741416401/2500000000 : ℝ)^1073 ≤ (62195117858897/100000000000000 : ℝ)^817 := by
    have hnat : (1741416401 : ℕ)^1073*100000000000000^817 ≤ 62195117858897^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1741416401 2500000000 62195117858897 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(503959257/5000000000 : ℝ), (-2144346169/5000000000 : ℝ), (1741416401/2500000000 : ℝ)] ![(1227714160619/25000000000000 : ℝ), (3289402548571/10000000000000 : ℝ), (62195117858897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(503959257/5000000000 : ℝ)|^1073 ≤ (1227714160619/25000000000000 : ℝ)^817
        have hw : |(503959257/5000000000 : ℝ)|=(503959257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2144346169/5000000000 : ℝ)|^1073 ≤ (3289402548571/10000000000000 : ℝ)^817
        have hw : |(-2144346169/5000000000 : ℝ)|=(2144346169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1741416401/2500000000 : ℝ)|^1073 ≤ (62195117858897/100000000000000 : ℝ)^817
        have hw : |(1741416401/2500000000 : ℝ)|=(1741416401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s3_10 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (31497923/312500000 : ℝ)*x 0 + (3482849313/5000000000 : ℝ)*x 1 + (-4288644353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31497923/312500000 : ℝ)^1073 ≤ (49109527679/1000000000000 : ℝ)^817 := by
    have hnat : (31497923 : ℕ)^1073*1000000000000^817 ≤ 49109527679^817*312500000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31497923 312500000 49109527679 1000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3482849313/5000000000 : ℝ)^1073 ≤ (62195505094281/100000000000000 : ℝ)^817 := by
    have hnat : (3482849313 : ℕ)^1073*100000000000000^817 ≤ 62195505094281^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3482849313 5000000000 62195505094281 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4288644353/10000000000 : ℝ)^1073 ≤ (657870842429/2000000000000 : ℝ)^817 := by
    have hnat : (4288644353 : ℕ)^1073*2000000000000^817 ≤ 657870842429^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4288644353 10000000000 657870842429 2000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(31497923/312500000 : ℝ), (3482849313/5000000000 : ℝ), (-4288644353/10000000000 : ℝ)] ![(49109527679/1000000000000 : ℝ), (62195505094281/100000000000000 : ℝ), (657870842429/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(31497923/312500000 : ℝ)|^1073 ≤ (49109527679/1000000000000 : ℝ)^817
        have hw : |(31497923/312500000 : ℝ)|=(31497923/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3482849313/5000000000 : ℝ)|^1073 ≤ (62195505094281/100000000000000 : ℝ)^817
        have hw : |(3482849313/5000000000 : ℝ)|=(3482849313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4288644353/10000000000 : ℝ)|^1073 ≤ (657870842429/2000000000000 : ℝ)^817
        have hw : |(-4288644353/10000000000 : ℝ)|=(4288644353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s3_11 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (928854961/10000000000 : ℝ)*x 0 + (2930562679/5000000000 : ℝ)*x 1 + (2768680911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (928854961/10000000000 : ℝ)^1073 ≤ (4411265124767/100000000000000 : ℝ)^817 := by
    have hnat : (928854961 : ℕ)^1073*100000000000000^817 ≤ 4411265124767^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928854961 10000000000 4411265124767 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2930562679/5000000000 : ℝ)^1073 ≤ (3098559576393/6250000000000 : ℝ)^817 := by
    have hnat : (2930562679 : ℕ)^1073*6250000000000^817 ≤ 3098559576393^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2930562679 5000000000 3098559576393 6250000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2768680911/5000000000 : ℝ)^1073 ≤ (46011781643483/100000000000000 : ℝ)^817 := by
    have hnat : (2768680911 : ℕ)^1073*100000000000000^817 ≤ 46011781643483^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2768680911 5000000000 46011781643483 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(928854961/10000000000 : ℝ), (2930562679/5000000000 : ℝ), (2768680911/5000000000 : ℝ)] ![(4411265124767/100000000000000 : ℝ), (3098559576393/6250000000000 : ℝ), (46011781643483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(928854961/10000000000 : ℝ)|^1073 ≤ (4411265124767/100000000000000 : ℝ)^817
        have hw : |(928854961/10000000000 : ℝ)|=(928854961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2930562679/5000000000 : ℝ)|^1073 ≤ (3098559576393/6250000000000 : ℝ)^817
        have hw : |(2930562679/5000000000 : ℝ)|=(2930562679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2768680911/5000000000 : ℝ)|^1073 ≤ (46011781643483/100000000000000 : ℝ)^817
        have hw : |(2768680911/5000000000 : ℝ)|=(2768680911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1332_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1009/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1957/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5413/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15019/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1009/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1957/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1009/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1957/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1009/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1957/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1009/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1957/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1009/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1957/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1009/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1957/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1957/20000 : ℝ) ^ (4291/1024 : ℝ) ≤ (736081914539111/12500000000000000000 : ℝ) := by
    have hpowers : (1957/20000 : ℝ)^4291 ≤ (736081914539111/12500000000000000000 : ℝ)^1024 := by
      have hnat : (1957 : ℕ)^4291*12500000000000000000^1024 ≤ 736081914539111^1024*20000^4291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1957 20000 736081914539111 12500000000000000000 4291 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1957/20000 : ℝ)) (X := (736081914539111/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1009/6250 : ℝ) ^ (4291/1024 : ℝ) ≤ (191993443282111/400000000000000000 : ℝ) := by
    have hpowers : (1009/6250 : ℝ)^4291 ≤ (191993443282111/400000000000000000 : ℝ)^1024 := by
      have hnat : (1009 : ℕ)^4291*400000000000000000^1024 ≤ 191993443282111^1024*6250^4291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1009 6250 191993443282111 400000000000000000 4291 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1009/6250 : ℝ)) (X := (191993443282111/400000000000000000 : ℝ)) (by norm_num) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250736081914539111/6250000000000000000 : ℝ) ≤ (2000056207995477/2000000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (6250736081914539111/6250000000000000000 : ℝ)^1024 ≤ (2000056207995477/2000000000000000 : ℝ)^4291 := by
      have hnat : (6250736081914539111 : ℕ)^1024*2000000000000000^4291 ≤ 2000056207995477^4291*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250736081914539111 6250000000000000000 2000056207995477 2000000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000056207995477/2000000000000000 : ℝ)) (X := (6250736081914539111/6250000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026943508068420319/50000000000000000000 : ℝ) ≤ (10001285690714569/10000000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (50026943508068420319/50000000000000000000 : ℝ)^1024 ≤ (10001285690714569/10000000000000000 : ℝ)^4291 := by
      have hnat : (50026943508068420319 : ℕ)^1024*10000000000000000^4291 ≤ 10001285690714569^4291*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026943508068420319 50000000000000000000 10001285690714569 10000000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001285690714569/10000000000000000 : ℝ)) (X := (50026943508068420319/50000000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (200191993443282111/200000000000000000 : ℝ) ≤ (10002290341451753/10000000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (200191993443282111/200000000000000000 : ℝ)^1024 ≤ (10002290341451753/10000000000000000 : ℝ)^4291 := by
      have hnat : (200191993443282111 : ℕ)^1024*10000000000000000^4291 ≤ 10002290341451753^4291*200000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        200191993443282111 200000000000000000 10002290341451753 10000000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002290341451753/10000000000000000 : ℝ)) (X := (200191993443282111/200000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(736081914539111/12500000000000000000 : ℝ) ≤ ((12714425223657900067/12718000000000000000 : ℝ)+2*(31395335537/19871875000000 : ℝ)*(1957/20000 : ℝ))^(4291/1024 : ℝ) := by
    rw [show (12714425223657900067/12718000000000000000 : ℝ)+2*(31395335537/19871875000000 : ℝ)*(1957/20000 : ℝ)=(2000056207995477/2000000000000000 : ℝ) by norm_num, show 1+2*(736081914539111/12500000000000000000 : ℝ)=(6250736081914539111/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(191993443282111/400000000000000000 : ℝ)+(736081914539111/12500000000000000000 : ℝ) ≤ ((12714425223657900067/12718000000000000000 : ℝ)+(31395335537/19871875000000 : ℝ)*((1009/6250 : ℝ)+(1957/20000 : ℝ)))^(4291/1024 : ℝ) := by
    rw [show (12714425223657900067/12718000000000000000 : ℝ)+(31395335537/19871875000000 : ℝ)*((1009/6250 : ℝ)+(1957/20000 : ℝ))=(10001285690714569/10000000000000000 : ℝ) by norm_num, show 1+(191993443282111/400000000000000000 : ℝ)+(736081914539111/12500000000000000000 : ℝ)=(50026943508068420319/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(191993443282111/400000000000000000 : ℝ) ≤ ((12714425223657900067/12718000000000000000 : ℝ)+2*(31395335537/19871875000000 : ℝ)*(1009/6250 : ℝ))^(4291/1024 : ℝ) := by
    rw [show (12714425223657900067/12718000000000000000 : ℝ)+2*(31395335537/19871875000000 : ℝ)*(1009/6250 : ℝ)=(10002290341451753/10000000000000000 : ℝ) by norm_num, show 1+2*(191993443282111/400000000000000000 : ℝ)=(200191993443282111/200000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12714425223657900067/12718000000000000000 : ℝ)*(X 1 0+X 2 0)+(31395335537/19871875000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (1957/20000 : ℝ)) (hi := (1009/6250 : ℝ)) (c := (12714425223657900067/12718000000000000000 : ℝ)) (alpha := (31395335537/19871875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12714425223657900067/12718000000000000000 : ℝ)*(X 0 1+X 2 1)+(31395335537/19871875000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (1957/20000 : ℝ)) (hi := (1009/6250 : ℝ)) (c := (12714425223657900067/12718000000000000000 : ℝ)) (alpha := (31395335537/19871875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12714425223657900067/12718000000000000000 : ℝ)*(X 0 2+X 1 2)+(31395335537/19871875000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (1957/20000 : ℝ)) (hi := (1009/6250 : ℝ)) (c := (12714425223657900067/12718000000000000000 : ℝ)) (alpha := (31395335537/19871875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1025389051/5000000000 : ℝ)*X 0 0+(5428469137/10000000000 : ℝ)*X 0 1+(1046054623/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676524797/5000000000 : ℝ)*X 1 0+(-2152097473/10000000000 : ℝ)*X 1 1+(2615136397/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353049911/10000000000 : ℝ)*X 2 0+(104605439/200000000 : ℝ)*X 2 1+(-2152098167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((865622793/2000000000 : ℝ)*X 0 0+(2062980123/5000000000 : ℝ)*X 0 1+(1134883889/2500000000 : ℝ)*X 0 2+(865622793/2000000000 : ℝ)*X 1 0+(2062980123/5000000000 : ℝ)*X 1 1+(1134883889/2500000000 : ℝ)*X 1 2+(865622793/2000000000 : ℝ)*X 2 0+(2062980123/5000000000 : ℝ)*X 2 1+(1134883889/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-102539903/500000000 : ℝ)*X 0 0+(5231103657/10000000000 : ℝ)*X 0 1+(2713816733/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302055837/10000000000 : ℝ)*X 1 0+(-244342143/1250000000 : ℝ)*X 1 1+(1085526733/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651028749/5000000000 : ℝ)*X 2 0+(2713816253/5000000000 : ℝ)*X 2 1+(-1954736469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4328155347/10000000000 : ℝ)*X 0 0+(4537802317/10000000000 : ℝ)*X 0 1+(4127703919/10000000000 : ℝ)*X 0 2+(4328155347/10000000000 : ℝ)*X 1 0+(4537802317/10000000000 : ℝ)*X 1 1+(4127703919/10000000000 : ℝ)*X 1 2+(4328155347/10000000000 : ℝ)*X 2 0+(4537802317/10000000000 : ℝ)*X 2 1+(4127703919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-84725643/10000000000 : ℝ)*X 0 0+(2861307311/5000000000 : ℝ)*X 0 1+(6057159533/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((503959257/5000000000 : ℝ)*X 1 0+(-2144346169/5000000000 : ℝ)*X 1 1+(1741416401/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((31497923/312500000 : ℝ)*X 2 0+(3482849313/5000000000 : ℝ)*X 2 1+(-4288644353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s3_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((928854961/10000000000 : ℝ)*X 0 0+(2930562679/5000000000 : ℝ)*X 0 1+(2768680911/5000000000 : ℝ)*X 0 2+(928854961/10000000000 : ℝ)*X 1 0+(2930562679/5000000000 : ℝ)*X 1 1+(2768680911/5000000000 : ℝ)*X 1 2+(928854961/10000000000 : ℝ)*X 2 0+(2930562679/5000000000 : ℝ)*X 2 1+(2768680911/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s3_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (90908518659116820732147/31795000000000000000000000000 : ℝ) := by norm_num
    linear_combination (165907027/50000000000000 : ℝ)*(lower2) + (1865861707407653/50000000000000 : ℝ)*(major0) + (1865861707407653/50000000000000 : ℝ)*(major1) + (1865861707407653/50000000000000 : ℝ)*(major2) + (5045503687714881/100000000000000 : ℝ)*(sp0) + (1009099130036847/20000000000000 : ℝ)*(sp1) + (630684755260089/12500000000000 : ℝ)*(sp2) + (151121170965427/6250000000000 : ℝ)*(sp3) + (8863985817/100000000000000 : ℝ)*(sp5) + (27081427647/100000000000000 : ℝ)*(sp6) + (1314068807/50000000000000 : ℝ)*(sp7) + (1435793479/100000000000000 : ℝ)*(sp8) + (609338307/100000000000000 : ℝ)*(sp9) + (247230869/100000000000000 : ℝ)*(sp11) + (483588322163063/20000000000000 : ℝ)*(f.failure) + (5045505123508359/100000000000000 : ℝ)*(f.sum) + (2783189970211/7948750000000000000000000000 : ℝ)*base65 + (705233597599247249/635900000000000000000000000000000 : ℝ)*base68 + (1790537342239852751/635900000000000000000000000000000 : ℝ)*base69 + (7077019140989547249/635900000000000000000000000000000 : ℝ)*base72 + (205259166309881/31795000000000000000000000000 : ℝ)*base74 + (845834953873952751/635900000000000000000000000000000 : ℝ)*base75 + (4362065470583447249/635900000000000000000000000000000 : ℝ)*base78 + (126431939323452751/635900000000000000000000000000000 : ℝ)*base79 + (65456105734751/31795000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (239/195312500000000000 : ℝ)*base89 + (239/195312500000000000 : ℝ)*base91 + (239/195312500000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13733911771840582747958667/5087200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (193502503/100000000000000 : ℝ)*(lower2) + (30107074126867/800000000000 : ℝ)*(major0) + (30107074126867/800000000000 : ℝ)*(major1) + (30107074126867/800000000000 : ℝ)*(major2) + (515293991/6250000000000 : ℝ)*(sp0) + (4306522623/50000000000000 : ℝ)*(sp1) + (6109021197/100000000000000 : ℝ)*(sp3) + (5088302687232247/100000000000000 : ℝ)*(sp4) + (2544151905938507/50000000000000 : ℝ)*(sp5) + (2544155504813841/50000000000000 : ℝ)*(sp6) + (1219224705280101/50000000000000 : ℝ)*(sp7) + (1492986157/100000000000000 : ℝ)*(sp8) + (707647289/50000000000000 : ℝ)*(sp10) + (4972231/1000000000000 : ℝ)*(sp11) + (1219228008402249/50000000000000 : ℝ)*(f.failure) + (254415621246113/5000000000000 : ℝ)*(f.sum) + (472132026917/198718750000000000000000000 : ℝ)*base66 + (19812269893385689/10174400000000000000000000000000 : ℝ)*base67 + (35757639509340889/10174400000000000000000000000000 : ℝ)*base69 + (3359688432630311/10174400000000000000000000000000 : ℝ)*base72 + (22831392789899/3179500000000000000000000000 : ℝ)*base74 + (7545821825937511/10174400000000000000000000000000 : ℝ)*base76 + (113374118388019111/10174400000000000000000000000000 : ℝ)*base78 + (83536982992510311/10174400000000000000000000000000 : ℝ)*base80 + (21796549974701/3179500000000000000000000000 : ℝ)*base82 + (5023/7812500000000000000 : ℝ)*base90 + (5023/7812500000000000000 : ℝ)*base92 + (5023/7812500000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1332_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1009/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1957/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5413/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15019/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1332_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1332_s4_0 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2052319637/10000000000 : ℝ)*x 0 + (270798359/500000000 : ℝ)*x 1 + (5241763371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2052319637/10000000000 : ℝ)^1073 ≤ (12495188783801/100000000000000 : ℝ)^817 := by
    have hnat : (2052319637 : ℕ)^1073*100000000000000^817 ≤ 12495188783801^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052319637 10000000000 12495188783801 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270798359/500000000 : ℝ)^1073 ≤ (446915761759/1000000000000 : ℝ)^817 := by
    have hnat : (270798359 : ℕ)^1073*1000000000000^817 ≤ 446915761759^817*500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270798359 500000000 446915761759 1000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241763371/10000000000 : ℝ)^1073 ≤ (42813235028133/100000000000000 : ℝ)^817 := by
    have hnat : (5241763371 : ℕ)^1073*100000000000000^817 ≤ 42813235028133^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241763371 10000000000 42813235028133 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2052319637/10000000000 : ℝ), (270798359/500000000 : ℝ), (5241763371/10000000000 : ℝ)] ![(12495188783801/100000000000000 : ℝ), (446915761759/1000000000000 : ℝ), (42813235028133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2052319637/10000000000 : ℝ)|^1073 ≤ (12495188783801/100000000000000 : ℝ)^817
        have hw : |(-2052319637/10000000000 : ℝ)|=(2052319637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270798359/500000000 : ℝ)|^1073 ≤ (446915761759/1000000000000 : ℝ)^817
        have hw : |(270798359/500000000 : ℝ)|=(270798359/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241763371/10000000000 : ℝ)|^1073 ≤ (42813235028133/100000000000000 : ℝ)^817
        have hw : |(5241763371/10000000000 : ℝ)|=(5241763371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s4_1 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1337467233/2500000000 : ℝ)*x 0 + (-2141138057/10000000000 : ℝ)*x 1 + (5241763213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337467233/2500000000 : ℝ)^1073 ≤ (5497076612967/12500000000000 : ℝ)^817 := by
    have hnat : (1337467233 : ℕ)^1073*12500000000000^817 ≤ 5497076612967^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337467233 2500000000 5497076612967 12500000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2141138057/10000000000 : ℝ)^1073 ≤ (1651269219109/12500000000000 : ℝ)^817 := by
    have hnat : (2141138057 : ℕ)^1073*12500000000000^817 ≤ 1651269219109^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141138057 10000000000 1651269219109 12500000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241763213/10000000000 : ℝ)^1073 ≤ (42813233333267/100000000000000 : ℝ)^817 := by
    have hnat : (5241763213 : ℕ)^1073*100000000000000^817 ≤ 42813233333267^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241763213 10000000000 42813233333267 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337467233/2500000000 : ℝ), (-2141138057/10000000000 : ℝ), (5241763213/10000000000 : ℝ)] ![(5497076612967/12500000000000 : ℝ), (1651269219109/12500000000000 : ℝ), (42813233333267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337467233/2500000000 : ℝ)|^1073 ≤ (5497076612967/12500000000000 : ℝ)^817
        have hw : |(1337467233/2500000000 : ℝ)|=(1337467233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2141138057/10000000000 : ℝ)|^1073 ≤ (1651269219109/12500000000000 : ℝ)^817
        have hw : |(-2141138057/10000000000 : ℝ)|=(2141138057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241763213/10000000000 : ℝ)|^1073 ≤ (42813233333267/100000000000000 : ℝ)^817
        have hw : |(5241763213/10000000000 : ℝ)|=(5241763213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s4_2 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (267493453/500000000 : ℝ)*x 0 + (2620881477/5000000000 : ℝ)*x 1 + (-2141138229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267493453/500000000 : ℝ)^1073 ≤ (43976614285603/100000000000000 : ℝ)^817 := by
    have hnat : (267493453 : ℕ)^1073*100000000000000^817 ≤ 43976614285603^817*500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267493453 500000000 43976614285603 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620881477/5000000000 : ℝ)^1073 ≤ (21406615277487/50000000000000 : ℝ)^817 := by
    have hnat : (2620881477 : ℕ)^1073*50000000000000^817 ≤ 21406615277487^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620881477 5000000000 21406615277487 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2141138229/10000000000 : ℝ)^1073 ≤ (3302538786643/25000000000000 : ℝ)^817 := by
    have hnat : (2141138229 : ℕ)^1073*25000000000000^817 ≤ 3302538786643^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141138229 10000000000 3302538786643 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267493453/500000000 : ℝ), (2620881477/5000000000 : ℝ), (-2141138229/10000000000 : ℝ)] ![(43976614285603/100000000000000 : ℝ), (21406615277487/50000000000000 : ℝ), (3302538786643/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267493453/500000000 : ℝ)|^1073 ≤ (43976614285603/100000000000000 : ℝ)^817
        have hw : |(267493453/500000000 : ℝ)|=(267493453/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620881477/5000000000 : ℝ)|^1073 ≤ (21406615277487/50000000000000 : ℝ)^817
        have hw : |(2620881477/5000000000 : ℝ)|=(2620881477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2141138229/10000000000 : ℝ)|^1073 ≤ (3302538786643/25000000000000 : ℝ)^817
        have hw : |(-2141138229/10000000000 : ℝ)|=(2141138229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s4_3 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4329050319/10000000000 : ℝ)*x 0 + (2075438119/5000000000 : ℝ)*x 1 + (2257193553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4329050319/10000000000 : ℝ)^1073 ≤ (16650579885527/50000000000000 : ℝ)^817 := by
    have hnat : (4329050319 : ℕ)^1073*50000000000000^817 ≤ 16650579885527^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4329050319 10000000000 16650579885527 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2075438119/5000000000 : ℝ)^1073 ≤ (31512810264409/100000000000000 : ℝ)^817 := by
    have hnat : (2075438119 : ℕ)^1073*100000000000000^817 ≤ 31512810264409^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075438119 5000000000 31512810264409 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257193553/5000000000 : ℝ)^1073 ≤ (35186029952187/100000000000000 : ℝ)^817 := by
    have hnat : (2257193553 : ℕ)^1073*100000000000000^817 ≤ 35186029952187^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257193553 5000000000 35186029952187 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4329050319/10000000000 : ℝ), (2075438119/5000000000 : ℝ), (2257193553/5000000000 : ℝ)] ![(16650579885527/50000000000000 : ℝ), (31512810264409/100000000000000 : ℝ), (35186029952187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4329050319/10000000000 : ℝ)|^1073 ≤ (16650579885527/50000000000000 : ℝ)^817
        have hw : |(4329050319/10000000000 : ℝ)|=(4329050319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2075438119/5000000000 : ℝ)|^1073 ≤ (31512810264409/100000000000000 : ℝ)^817
        have hw : |(2075438119/5000000000 : ℝ)|=(2075438119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2257193553/5000000000 : ℝ)|^1073 ≤ (35186029952187/100000000000000 : ℝ)^817
        have hw : |(2257193553/5000000000 : ℝ)|=(2257193553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s4_4 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-410466653/2000000000 : ℝ)*x 0 + (5242405691/10000000000 : ℝ)*x 1 + (5415321327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410466653/2000000000 : ℝ)^1073 ≤ (78095610963/625000000000 : ℝ)^817 := by
    have hnat : (410466653 : ℕ)^1073*625000000000^817 ≤ 78095610963^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410466653 2000000000 78095610963 625000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242405691/10000000000 : ℝ)^1073 ≤ (5352515665917/12500000000000 : ℝ)^817 := by
    have hnat : (5242405691 : ℕ)^1073*12500000000000^817 ≤ 5352515665917^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242405691 10000000000 5352515665917 12500000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415321327/10000000000 : ℝ)^1073 ≤ (22342288451877/50000000000000 : ℝ)^817 := by
    have hnat : (5415321327 : ℕ)^1073*50000000000000^817 ≤ 22342288451877^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415321327 10000000000 22342288451877 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-410466653/2000000000 : ℝ), (5242405691/10000000000 : ℝ), (5415321327/10000000000 : ℝ)] ![(78095610963/625000000000 : ℝ), (5352515665917/12500000000000 : ℝ), (22342288451877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-410466653/2000000000 : ℝ)|^1073 ≤ (78095610963/625000000000 : ℝ)^817
        have hw : |(-410466653/2000000000 : ℝ)|=(410466653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242405691/10000000000 : ℝ)|^1073 ≤ (5352515665917/12500000000000 : ℝ)^817
        have hw : |(5242405691/10000000000 : ℝ)|=(5242405691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415321327/10000000000 : ℝ)|^1073 ≤ (22342288451877/50000000000000 : ℝ)^817
        have hw : |(5415321327/10000000000 : ℝ)|=(5415321327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s4_5 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305049949/10000000000 : ℝ)*x 0 + (-1967580063/10000000000 : ℝ)*x 1 + (5415321327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305049949/10000000000 : ℝ)^1073 ≤ (10873347696719/25000000000000 : ℝ)^817 := by
    have hnat : (5305049949 : ℕ)^1073*25000000000000^817 ≤ 10873347696719^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305049949 10000000000 10873347696719 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1967580063/10000000000 : ℝ)^1073 ≤ (1477754036691/12500000000000 : ℝ)^817 := by
    have hnat : (1967580063 : ℕ)^1073*12500000000000^817 ≤ 1477754036691^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967580063 10000000000 1477754036691 12500000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415321327/10000000000 : ℝ)^1073 ≤ (22342288451877/50000000000000 : ℝ)^817 := by
    have hnat : (5415321327 : ℕ)^1073*50000000000000^817 ≤ 22342288451877^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415321327 10000000000 22342288451877 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305049949/10000000000 : ℝ), (-1967580063/10000000000 : ℝ), (5415321327/10000000000 : ℝ)] ![(10873347696719/25000000000000 : ℝ), (1477754036691/12500000000000 : ℝ), (22342288451877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305049949/10000000000 : ℝ)|^1073 ≤ (10873347696719/25000000000000 : ℝ)^817
        have hw : |(5305049949/10000000000 : ℝ)|=(5305049949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1967580063/10000000000 : ℝ)|^1073 ≤ (1477754036691/12500000000000 : ℝ)^817
        have hw : |(-1967580063/10000000000 : ℝ)|=(1967580063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415321327/10000000000 : ℝ)|^1073 ≤ (22342288451877/50000000000000 : ℝ)^817
        have hw : |(5415321327/10000000000 : ℝ)|=(5415321327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s4_6 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1326262489/2500000000 : ℝ)*x 0 + (2707660659/5000000000 : ℝ)*x 1 + (-1967580067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326262489/2500000000 : ℝ)^1073 ≤ (5436673857781/12500000000000 : ℝ)^817 := by
    have hnat : (1326262489 : ℕ)^1073*12500000000000^817 ≤ 5436673857781^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326262489 2500000000 5436673857781 12500000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707660659/5000000000 : ℝ)^1073 ≤ (44684576806221/100000000000000 : ℝ)^817 := by
    have hnat : (2707660659 : ℕ)^1073*100000000000000^817 ≤ 44684576806221^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707660659 5000000000 44684576806221 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1967580067/10000000000 : ℝ)^1073 ≤ (2955508081273/25000000000000 : ℝ)^817 := by
    have hnat : (1967580067 : ℕ)^1073*25000000000000^817 ≤ 2955508081273^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967580067 10000000000 2955508081273 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326262489/2500000000 : ℝ), (2707660659/5000000000 : ℝ), (-1967580067/10000000000 : ℝ)] ![(5436673857781/12500000000000 : ℝ), (44684576806221/100000000000000 : ℝ), (2955508081273/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326262489/2500000000 : ℝ)|^1073 ≤ (5436673857781/12500000000000 : ℝ)^817
        have hw : |(1326262489/2500000000 : ℝ)|=(1326262489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707660659/5000000000 : ℝ)|^1073 ≤ (44684576806221/100000000000000 : ℝ)^817
        have hw : |(2707660659/5000000000 : ℝ)|=(2707660659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1967580067/10000000000 : ℝ)|^1073 ≤ (2955508081273/25000000000000 : ℝ)^817
        have hw : |(-1967580067/10000000000 : ℝ)|=(1967580067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s4_7 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4329078289/10000000000 : ℝ)*x 0 + (225652317/500000000 : ℝ)*x 1 + (4152224267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4329078289/10000000000 : ℝ)^1073 ≤ (3330144234837/10000000000000 : ℝ)^817 := by
    have hnat : (4329078289 : ℕ)^1073*10000000000000^817 ≤ 3330144234837^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4329078289 10000000000 3330144234837 10000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225652317/500000000 : ℝ)^1073 ≤ (3517230591409/10000000000000 : ℝ)^817 := by
    have hnat : (225652317 : ℕ)^1073*10000000000000^817 ≤ 3517230591409^817*500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225652317 500000000 3517230591409 10000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4152224267/10000000000 : ℝ)^1073 ≤ (6305250344271/20000000000000 : ℝ)^817 := by
    have hnat : (4152224267 : ℕ)^1073*20000000000000^817 ≤ 6305250344271^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152224267 10000000000 6305250344271 20000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4329078289/10000000000 : ℝ), (225652317/500000000 : ℝ), (4152224267/10000000000 : ℝ)] ![(3330144234837/10000000000000 : ℝ), (3517230591409/10000000000000 : ℝ), (6305250344271/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4329078289/10000000000 : ℝ)|^1073 ≤ (3330144234837/10000000000000 : ℝ)^817
        have hw : |(4329078289/10000000000 : ℝ)|=(4329078289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225652317/500000000 : ℝ)|^1073 ≤ (3517230591409/10000000000000 : ℝ)^817
        have hw : |(225652317/500000000 : ℝ)|=(225652317/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4152224267/10000000000 : ℝ)|^1073 ≤ (6305250344271/20000000000000 : ℝ)^817
        have hw : |(4152224267/10000000000 : ℝ)|=(4152224267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1332_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15019/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5413/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11071/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7379/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15019/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5413/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15019/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5413/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15019/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5413/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15019/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5413/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15019/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5413/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15019/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5413/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5413/50000 : ℝ) ^ (4291/1024 : ℝ) ≤ (4497551475634387/50000000000000000000 : ℝ) := by
    have hpowers : (5413/50000 : ℝ)^4291 ≤ (4497551475634387/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5413 : ℕ)^4291*50000000000000000000^1024 ≤ 4497551475634387^1024*50000^4291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5413 50000 4497551475634387 50000000000000000000 4291 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5413/50000 : ℝ)) (X := (4497551475634387/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15019/100000 : ℝ) ^ (4291/1024 : ℝ) ≤ (35462722641518833/100000000000000000000 : ℝ) := by
    have hpowers : (15019/100000 : ℝ)^4291 ≤ (35462722641518833/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15019 : ℕ)^4291*100000000000000000000^1024 ≤ 35462722641518833^1024*100000^4291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15019 100000 35462722641518833 100000000000000000000 4291 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15019/100000 : ℝ)) (X := (35462722641518833/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004497551475634387/25000000000000000000 : ℝ) ≤ (10000429287097297/10000000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (25004497551475634387/25000000000000000000 : ℝ)^1024 ≤ (10000429287097297/10000000000000000 : ℝ)^4291 := by
      have hnat : (25004497551475634387 : ℕ)^1024*10000000000000000^4291 ≤ 10000429287097297^4291*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004497551475634387 25000000000000000000 10000429287097297 10000000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000429287097297/10000000000000000 : ℝ)) (X := (25004497551475634387/25000000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044457825592787607/100000000000000000000 : ℝ) ≤ (2500265189412111/2500000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (100044457825592787607/100000000000000000000 : ℝ)^1024 ≤ (2500265189412111/2500000000000000 : ℝ)^4291 := by
      have hnat : (100044457825592787607 : ℕ)^1024*2500000000000000^4291 ≤ 2500265189412111^4291*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044457825592787607 100000000000000000000 2500265189412111 2500000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500265189412111/2500000000000000 : ℝ)) (X := (100044457825592787607/100000000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035462722641518833/50000000000000000000 : ℝ) ≤ (10001692228199591/10000000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (50035462722641518833/50000000000000000000 : ℝ)^1024 ≤ (10001692228199591/10000000000000000 : ℝ)^4291 := by
      have hnat : (50035462722641518833 : ℕ)^1024*10000000000000000^4291 ≤ 10001692228199591^4291*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035462722641518833 50000000000000000000 10001692228199591 10000000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001692228199591/10000000000000000 : ℝ)) (X := (50035462722641518833/50000000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4497551475634387/50000000000000000000 : ℝ) ≤ ((41918127400425531477/41930000000000000000 : ℝ)+2*(631470551147/419300000000000 : ℝ)*(5413/50000 : ℝ))^(4291/1024 : ℝ) := by
    rw [show (41918127400425531477/41930000000000000000 : ℝ)+2*(631470551147/419300000000000 : ℝ)*(5413/50000 : ℝ)=(10000429287097297/10000000000000000 : ℝ) by norm_num, show 1+2*(4497551475634387/50000000000000000000 : ℝ)=(25004497551475634387/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35462722641518833/100000000000000000000 : ℝ)+(4497551475634387/50000000000000000000 : ℝ) ≤ ((41918127400425531477/41930000000000000000 : ℝ)+(631470551147/419300000000000 : ℝ)*((15019/100000 : ℝ)+(5413/50000 : ℝ)))^(4291/1024 : ℝ) := by
    rw [show (41918127400425531477/41930000000000000000 : ℝ)+(631470551147/419300000000000 : ℝ)*((15019/100000 : ℝ)+(5413/50000 : ℝ))=(2500265189412111/2500000000000000 : ℝ) by norm_num, show 1+(35462722641518833/100000000000000000000 : ℝ)+(4497551475634387/50000000000000000000 : ℝ)=(100044457825592787607/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35462722641518833/100000000000000000000 : ℝ) ≤ ((41918127400425531477/41930000000000000000 : ℝ)+2*(631470551147/419300000000000 : ℝ)*(15019/100000 : ℝ))^(4291/1024 : ℝ) := by
    rw [show (41918127400425531477/41930000000000000000 : ℝ)+2*(631470551147/419300000000000 : ℝ)*(15019/100000 : ℝ)=(10001692228199591/10000000000000000 : ℝ) by norm_num, show 1+2*(35462722641518833/100000000000000000000 : ℝ)=(50035462722641518833/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (41918127400425531477/41930000000000000000 : ℝ)*(X 1 0+X 2 0)+(631470551147/419300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (5413/50000 : ℝ)) (hi := (15019/100000 : ℝ)) (c := (41918127400425531477/41930000000000000000 : ℝ)) (alpha := (631470551147/419300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (41918127400425531477/41930000000000000000 : ℝ)*(X 0 1+X 2 1)+(631470551147/419300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (5413/50000 : ℝ)) (hi := (15019/100000 : ℝ)) (c := (41918127400425531477/41930000000000000000 : ℝ)) (alpha := (631470551147/419300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (41918127400425531477/41930000000000000000 : ℝ)*(X 0 2+X 1 2)+(631470551147/419300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (5413/50000 : ℝ)) (hi := (15019/100000 : ℝ)) (c := (41918127400425531477/41930000000000000000 : ℝ)) (alpha := (631470551147/419300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2052319637/10000000000 : ℝ)*X 0 0+(270798359/500000000 : ℝ)*X 0 1+(5241763371/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337467233/2500000000 : ℝ)*X 1 0+(-2141138057/10000000000 : ℝ)*X 1 1+(5241763213/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267493453/500000000 : ℝ)*X 2 0+(2620881477/5000000000 : ℝ)*X 2 1+(-2141138229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4329050319/10000000000 : ℝ)*X 0 0+(2075438119/5000000000 : ℝ)*X 0 1+(2257193553/5000000000 : ℝ)*X 0 2+(4329050319/10000000000 : ℝ)*X 1 0+(2075438119/5000000000 : ℝ)*X 1 1+(2257193553/5000000000 : ℝ)*X 1 2+(4329050319/10000000000 : ℝ)*X 2 0+(2075438119/5000000000 : ℝ)*X 2 1+(2257193553/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-410466653/2000000000 : ℝ)*X 0 0+(5242405691/10000000000 : ℝ)*X 0 1+(5415321327/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305049949/10000000000 : ℝ)*X 1 0+(-1967580063/10000000000 : ℝ)*X 1 1+(5415321327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326262489/2500000000 : ℝ)*X 2 0+(2707660659/5000000000 : ℝ)*X 2 1+(-1967580067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4329078289/10000000000 : ℝ)*X 0 0+(225652317/500000000 : ℝ)*X 0 1+(4152224267/10000000000 : ℝ)*X 0 2+(4329078289/10000000000 : ℝ)*X 1 0+(225652317/500000000 : ℝ)*X 1 1+(4152224267/10000000000 : ℝ)*X 1 2+(4329078289/10000000000 : ℝ)*X 2 0+(225652317/500000000 : ℝ)*X 2 1+(4152224267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (592969772066679019072049439/104825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9542983/800000000000 : ℝ)*(base19) + (662254327/50000000000000 : ℝ)*(base23) + (20971767/25000000000000 : ℝ)*(lower2) + (91939303/50000000000000 : ℝ)*(upper3) + (16166569/20000000000000 : ℝ)*(lower4) + (212285401622769/5000000000000 : ℝ)*(major0) + (212285401622769/5000000000000 : ℝ)*(major1) + (212285401622769/5000000000000 : ℝ)*(major2) + (574042498529721/10000000000000 : ℝ)*(sp0) + (2870220337760417/50000000000000 : ℝ)*(sp1) + (1148088108777011/20000000000000 : ℝ)*(sp2) + (171935005493559/6250000000000 : ℝ)*(sp3) + (16883096499/100000000000000 : ℝ)*(sp4) + (13920061461/100000000000000 : ℝ)*(sp7) + (687743501989601/25000000000000 : ℝ)*(f.failure) + (574044186839371/10000000000000 : ℝ)*(f.sum) + (3754944226423/1048250000000000000000000000 : ℝ)*base65 + (1627480140658950187/209650000000000000000000000000000 : ℝ)*base68 + (2484748259914400187/209650000000000000000000000000000 : ℝ)*base70 + (103366855692249813/209650000000000000000000000000000 : ℝ)*base71 + (617058222751/419300000000000000000000000 : ℝ)*base74 + (2802588259608750187/209650000000000000000000000000000 : ℝ)*base76 + (1108519312326449813/209650000000000000000000000000000 : ℝ)*base77 + (69342233367600187/209650000000000000000000000000000 : ℝ)*base80 + (1510976287321/262062500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (10349/1953125000000000000 : ℝ)*base89 + (10349/1953125000000000000 : ℝ)*base91 + (10349/1953125000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2098806862680315020923580691/524125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (71401571/10000000000000 : ℝ)*(base19) + (774667783/100000000000000 : ℝ)*(base23) + (81892877/100000000000000 : ℝ)*(upper3) + (6195209/25000000000000 : ℝ)*(lower4) + (86149509/100000000000000 : ℝ)*(upper5) + (1069326960733461/25000000000000 : ℝ)*(major0) + (1069326960733461/25000000000000 : ℝ)*(major1) + (1069326960733461/25000000000000 : ℝ)*(major2) + (2828567049/20000000000000 : ℝ)*(sp1) + (7444808103/50000000000000 : ℝ)*(sp2) + (5783166689206463/100000000000000 : ℝ)*(sp4) + (5783151832355507/100000000000000 : ℝ)*(sp5) + (5783151024922473/100000000000000 : ℝ)*(sp6) + (692862215795293/25000000000000 : ℝ)*(sp7) + (692862215795293/25000000000000 : ℝ)*(f.failure) + (5783166689206463/100000000000000 : ℝ)*(f.sum) + (85746476951523/20965000000000000000000000000 : ℝ)*base65 + (3658746085037898103/1048250000000000000000000000000000 : ℝ)*base68 + (7308905537291898103/1048250000000000000000000000000000 : ℝ)*base70 + (3921452841923601897/1048250000000000000000000000000000 : ℝ)*base71 + (14662599762421/10482500000000000000000000000 : ℝ)*base74 + (18497615307689148103/1048250000000000000000000000000000 : ℝ)*base76 + (6000988216212648103/1048250000000000000000000000000000 : ℝ)*base78 + (1249337563970851897/1048250000000000000000000000000000 : ℝ)*base79 + (73474969642133/20965000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (17557/1953125000000000000 : ℝ)*base89 + (17557/1953125000000000000 : ℝ)*base91 + (17557/1953125000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1332_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15019/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5413/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11071/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1332_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1332_s5_0 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-513147607/2500000000 : ℝ)*x 0 + (1353411091/2500000000 : ℝ)*x 1 + (2621953977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (513147607/2500000000 : ℝ)^1073 ≤ (781084630429/6250000000000 : ℝ)^817 := by
    have hnat : (513147607 : ℕ)^1073*6250000000000^817 ≤ 781084630429^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513147607 2500000000 781084630429 6250000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353411091/2500000000 : ℝ)^1073 ≤ (44666404453339/100000000000000 : ℝ)^817 := by
    have hnat : (1353411091 : ℕ)^1073*100000000000000^817 ≤ 44666404453339^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353411091 2500000000 44666404453339 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621953977/5000000000 : ℝ)^1073 ≤ (8567248289079/20000000000000 : ℝ)^817 := by
    have hnat : (2621953977 : ℕ)^1073*20000000000000^817 ≤ 8567248289079^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621953977 5000000000 8567248289079 20000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-513147607/2500000000 : ℝ), (1353411091/2500000000 : ℝ), (2621953977/5000000000 : ℝ)] ![(781084630429/6250000000000 : ℝ), (44666404453339/100000000000000 : ℝ), (8567248289079/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-513147607/2500000000 : ℝ)|^1073 ≤ (781084630429/6250000000000 : ℝ)^817
        have hw : |(-513147607/2500000000 : ℝ)|=(513147607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353411091/2500000000 : ℝ)|^1073 ≤ (44666404453339/100000000000000 : ℝ)^817
        have hw : |(1353411091/2500000000 : ℝ)|=(1353411091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621953977/5000000000 : ℝ)|^1073 ≤ (8567248289079/20000000000000 : ℝ)^817
        have hw : |(2621953977/5000000000 : ℝ)|=(2621953977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s5_1 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349276027/10000000000 : ℝ)*x 0 + (-2139088197/10000000000 : ℝ)*x 1 + (1048781591/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349276027/10000000000 : ℝ)^1073 ≤ (2198510605471/5000000000000 : ℝ)^817 := by
    have hnat : (5349276027 : ℕ)^1073*5000000000000^817 ≤ 2198510605471^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349276027 10000000000 2198510605471 5000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2139088197/10000000000 : ℝ)^1073 ≤ (13193546419327/100000000000000 : ℝ)^817 := by
    have hnat : (2139088197 : ℕ)^1073*100000000000000^817 ≤ 13193546419327^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139088197 10000000000 13193546419327 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048781591/2000000000 : ℝ)^1073 ≤ (10709060364031/25000000000000 : ℝ)^817 := by
    have hnat : (1048781591 : ℕ)^1073*25000000000000^817 ≤ 10709060364031^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048781591 2000000000 10709060364031 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349276027/10000000000 : ℝ), (-2139088197/10000000000 : ℝ), (1048781591/2000000000 : ℝ)] ![(2198510605471/5000000000000 : ℝ), (13193546419327/100000000000000 : ℝ), (10709060364031/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349276027/10000000000 : ℝ)|^1073 ≤ (2198510605471/5000000000000 : ℝ)^817
        have hw : |(5349276027/10000000000 : ℝ)|=(5349276027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2139088197/10000000000 : ℝ)|^1073 ≤ (13193546419327/100000000000000 : ℝ)^817
        have hw : |(-2139088197/10000000000 : ℝ)|=(2139088197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048781591/2000000000 : ℝ)|^1073 ≤ (10709060364031/25000000000000 : ℝ)^817
        have hw : |(1048781591/2000000000 : ℝ)|=(1048781591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s5_2 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1337319011/2500000000 : ℝ)*x 0 + (5243907953/10000000000 : ℝ)*x 1 + (-2139088177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337319011/2500000000 : ℝ)^1073 ≤ (43970212292943/100000000000000 : ℝ)^817 := by
    have hnat : (1337319011 : ℕ)^1073*100000000000000^817 ≤ 43970212292943^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337319011 2500000000 43970212292943 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243907953/10000000000 : ℝ)^1073 ≤ (42836241434667/100000000000000 : ℝ)^817 := by
    have hnat : (5243907953 : ℕ)^1073*100000000000000^817 ≤ 42836241434667^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243907953 10000000000 42836241434667 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2139088177/10000000000 : ℝ)^1073 ≤ (6596773128659/50000000000000 : ℝ)^817 := by
    have hnat : (2139088177 : ℕ)^1073*50000000000000^817 ≤ 6596773128659^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139088177 10000000000 6596773128659 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337319011/2500000000 : ℝ), (5243907953/10000000000 : ℝ), (-2139088177/10000000000 : ℝ)] ![(43970212292943/100000000000000 : ℝ), (42836241434667/100000000000000 : ℝ), (6596773128659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337319011/2500000000 : ℝ)|^1073 ≤ (43970212292943/100000000000000 : ℝ)^817
        have hw : |(1337319011/2500000000 : ℝ)|=(1337319011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243907953/10000000000 : ℝ)|^1073 ≤ (42836241434667/100000000000000 : ℝ)^817
        have hw : |(5243907953/10000000000 : ℝ)|=(5243907953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2139088177/10000000000 : ℝ)|^1073 ≤ (6596773128659/50000000000000 : ℝ)^817
        have hw : |(-2139088177/10000000000 : ℝ)|=(2139088177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s5_3 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4329211337/10000000000 : ℝ)*x 0 + (4155517687/10000000000 : ℝ)*x 1 + (563713211/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4329211337/10000000000 : ℝ)^1073 ≤ (33302786523053/100000000000000 : ℝ)^817 := by
    have hnat : (4329211337 : ℕ)^1073*100000000000000^817 ≤ 33302786523053^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4329211337 10000000000 33302786523053 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4155517687/10000000000 : ℝ)^1073 ≤ (31559096797699/100000000000000 : ℝ)^817 := by
    have hnat : (4155517687 : ℕ)^1073*100000000000000^817 ≤ 31559096797699^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155517687 10000000000 31559096797699 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563713211/1250000000 : ℝ)^1073 ≤ (4392264583007/12500000000000 : ℝ)^817 := by
    have hnat : (563713211 : ℕ)^1073*12500000000000^817 ≤ 4392264583007^817*1250000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563713211 1250000000 4392264583007 12500000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4329211337/10000000000 : ℝ), (4155517687/10000000000 : ℝ), (563713211/1250000000 : ℝ)] ![(33302786523053/100000000000000 : ℝ), (31559096797699/100000000000000 : ℝ), (4392264583007/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4329211337/10000000000 : ℝ)|^1073 ≤ (33302786523053/100000000000000 : ℝ)^817
        have hw : |(4329211337/10000000000 : ℝ)|=(4329211337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4155517687/10000000000 : ℝ)|^1073 ≤ (31559096797699/100000000000000 : ℝ)^817
        have hw : |(4155517687/10000000000 : ℝ)|=(4155517687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563713211/1250000000 : ℝ)|^1073 ≤ (4392264583007/12500000000000 : ℝ)^817
        have hw : |(563713211/1250000000 : ℝ)|=(563713211/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s5_4 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-513150737/2500000000 : ℝ)*x 0 + (5244518053/10000000000 : ℝ)*x 1 + (5413031063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (513150737/2500000000 : ℝ)^1073 ≤ (12497454201641/100000000000000 : ℝ)^817 := by
    have hnat : (513150737 : ℕ)^1073*100000000000000^817 ≤ 12497454201641^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513150737 2500000000 12497454201641 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244518053/10000000000 : ℝ)^1073 ≤ (10710696733957/25000000000000 : ℝ)^817 := by
    have hnat : (5244518053 : ℕ)^1073*25000000000000^817 ≤ 10710696733957^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244518053 10000000000 10710696733957 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413031063/10000000000 : ℝ)^1073 ≤ (44659758842567/100000000000000 : ℝ)^817 := by
    have hnat : (5413031063 : ℕ)^1073*100000000000000^817 ≤ 44659758842567^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413031063 10000000000 44659758842567 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-513150737/2500000000 : ℝ), (5244518053/10000000000 : ℝ), (5413031063/10000000000 : ℝ)] ![(12497454201641/100000000000000 : ℝ), (10710696733957/25000000000000 : ℝ), (44659758842567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-513150737/2500000000 : ℝ)|^1073 ≤ (12497454201641/100000000000000 : ℝ)^817
        have hw : |(-513150737/2500000000 : ℝ)|=(513150737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244518053/10000000000 : ℝ)|^1073 ≤ (10710696733957/25000000000000 : ℝ)^817
        have hw : |(5244518053/10000000000 : ℝ)|=(5244518053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413031063/10000000000 : ℝ)|^1073 ≤ (44659758842567/100000000000000 : ℝ)^817
        have hw : |(5413031063/10000000000 : ℝ)|=(5413031063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s5_5 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (10362513/19531250 : ℝ)*x 0 + (-78798601/400000000 : ℝ)*x 1 + (216521243/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10362513/19531250 : ℝ)^1073 ≤ (4349938518077/10000000000000 : ℝ)^817 := by
    have hnat : (10362513 : ℕ)^1073*10000000000000^817 ≤ 4349938518077^817*19531250^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10362513 19531250 4349938518077 10000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (78798601/400000000 : ℝ)^1073 ≤ (2960213958383/25000000000000 : ℝ)^817 := by
    have hnat : (78798601 : ℕ)^1073*25000000000000^817 ≤ 2960213958383^817*400000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78798601 400000000 2960213958383 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216521243/400000000 : ℝ)^1073 ≤ (22329879486297/50000000000000 : ℝ)^817 := by
    have hnat : (216521243 : ℕ)^1073*50000000000000^817 ≤ 22329879486297^817*400000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216521243 400000000 22329879486297 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10362513/19531250 : ℝ), (-78798601/400000000 : ℝ), (216521243/400000000 : ℝ)] ![(4349938518077/10000000000000 : ℝ), (2960213958383/25000000000000 : ℝ), (22329879486297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10362513/19531250 : ℝ)|^1073 ≤ (4349938518077/10000000000000 : ℝ)^817
        have hw : |(10362513/19531250 : ℝ)|=(10362513/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-78798601/400000000 : ℝ)|^1073 ≤ (2960213958383/25000000000000 : ℝ)^817
        have hw : |(-78798601/400000000 : ℝ)|=(78798601/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216521243/400000000 : ℝ)|^1073 ≤ (22329879486297/50000000000000 : ℝ)^817
        have hw : |(216521243/400000000 : ℝ)|=(216521243/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s5_6 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (33160041/62500000 : ℝ)*x 0 + (2706515583/5000000000 : ℝ)*x 1 + (-246245629/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33160041/62500000 : ℝ)^1073 ≤ (8699876829413/20000000000000 : ℝ)^817 := by
    have hnat : (33160041 : ℕ)^1073*20000000000000^817 ≤ 8699876829413^817*62500000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33160041 62500000 8699876829413 20000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706515583/5000000000 : ℝ)^1073 ≤ (8931951991727/20000000000000 : ℝ)^817 := by
    have hnat : (2706515583 : ℕ)^1073*20000000000000^817 ≤ 8931951991727^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706515583 5000000000 8931951991727 20000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (246245629/1250000000 : ℝ)^1073 ≤ (1184085588879/10000000000000 : ℝ)^817 := by
    have hnat : (246245629 : ℕ)^1073*10000000000000^817 ≤ 1184085588879^817*1250000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246245629 1250000000 1184085588879 10000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33160041/62500000 : ℝ), (2706515583/5000000000 : ℝ), (-246245629/1250000000 : ℝ)] ![(8699876829413/20000000000000 : ℝ), (8931951991727/20000000000000 : ℝ), (1184085588879/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33160041/62500000 : ℝ)|^1073 ≤ (8699876829413/20000000000000 : ℝ)^817
        have hw : |(33160041/62500000 : ℝ)|=(33160041/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706515583/5000000000 : ℝ)|^1073 ≤ (8931951991727/20000000000000 : ℝ)^817
        have hw : |(2706515583/5000000000 : ℝ)|=(2706515583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-246245629/1250000000 : ℝ)|^1073 ≤ (1184085588879/10000000000000 : ℝ)^817
        have hw : |(-246245629/1250000000 : ℝ)|=(246245629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s5_7 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2164618639/5000000000 : ℝ)*x 0 + (450843269/1000000000 : ℝ)*x 1 + (2078398669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164618639/5000000000 : ℝ)^1073 ≤ (16651524302339/50000000000000 : ℝ)^817 := by
    have hnat : (2164618639 : ℕ)^1073*50000000000000^817 ≤ 16651524302339^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164618639 5000000000 16651524302339 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450843269/1000000000 : ℝ)^1073 ≤ (35125090502537/100000000000000 : ℝ)^817 := by
    have hnat : (450843269 : ℕ)^1073*100000000000000^817 ≤ 35125090502537^817*1000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450843269 1000000000 35125090502537 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078398669/5000000000 : ℝ)^1073 ≤ (3946482609967/12500000000000 : ℝ)^817 := by
    have hnat : (2078398669 : ℕ)^1073*12500000000000^817 ≤ 3946482609967^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078398669 5000000000 3946482609967 12500000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2164618639/5000000000 : ℝ), (450843269/1000000000 : ℝ), (2078398669/5000000000 : ℝ)] ![(16651524302339/50000000000000 : ℝ), (35125090502537/100000000000000 : ℝ), (3946482609967/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2164618639/5000000000 : ℝ)|^1073 ≤ (16651524302339/50000000000000 : ℝ)^817
        have hw : |(2164618639/5000000000 : ℝ)|=(2164618639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(450843269/1000000000 : ℝ)|^1073 ≤ (35125090502537/100000000000000 : ℝ)^817
        have hw : |(450843269/1000000000 : ℝ)|=(450843269/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2078398669/5000000000 : ℝ)|^1073 ≤ (3946482609967/12500000000000 : ℝ)^817
        have hw : |(2078398669/5000000000 : ℝ)|=(2078398669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1332_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11071/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11117/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1471/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11071/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11071/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11071/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11071/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11071/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11071/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11071/100000 : ℝ) ^ (4291/1024 : ℝ) ≤ (4939718586699947/50000000000000000000 : ℝ) := by
    have hpowers : (11071/100000 : ℝ)^4291 ≤ (4939718586699947/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11071 : ℕ)^4291*50000000000000000000^1024 ≤ 4939718586699947^1024*100000^4291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11071 100000 4939718586699947 50000000000000000000 4291 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11071/100000 : ℝ)) (X := (4939718586699947/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7379/50000 : ℝ) ^ (4291/1024 : ℝ) ≤ (8237742271342951/25000000000000000000 : ℝ) := by
    have hpowers : (7379/50000 : ℝ)^4291 ≤ (8237742271342951/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7379 : ℕ)^4291*25000000000000000000^1024 ≤ 8237742271342951^1024*50000^4291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7379 50000 8237742271342951 25000000000000000000 4291 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7379/50000 : ℝ)) (X := (8237742271342951/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004939718586699947/25000000000000000000 : ℝ) ≤ (10000471488361959/10000000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (25004939718586699947/25000000000000000000 : ℝ)^1024 ≤ (10000471488361959/10000000000000000 : ℝ)^4291 := by
      have hnat : (25004939718586699947 : ℕ)^1024*10000000000000000^4291 ≤ 10000471488361959^4291*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004939718586699947 25000000000000000000 10000471488361959 10000000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000471488361959/10000000000000000 : ℝ)) (X := (25004939718586699947/25000000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021415203129385849/50000000000000000000 : ℝ) ≤ (10001021933974283/10000000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (50021415203129385849/50000000000000000000 : ℝ)^1024 ≤ (10001021933974283/10000000000000000 : ℝ)^4291 := by
      have hnat : (50021415203129385849 : ℕ)^1024*10000000000000000^4291 ≤ 10001021933974283^4291*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021415203129385849 50000000000000000000 10001021933974283 10000000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001021933974283/10000000000000000 : ℝ)) (X := (50021415203129385849/50000000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508237742271342951/12500000000000000000 : ℝ) ≤ (10001572379586607/10000000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (12508237742271342951/12500000000000000000 : ℝ)^1024 ≤ (10001572379586607/10000000000000000 : ℝ)^4291 := by
      have hnat : (12508237742271342951 : ℕ)^1024*10000000000000000^4291 ≤ 10001572379586607^4291*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508237742271342951 12500000000000000000 10001572379586607 10000000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001572379586607/10000000000000000 : ℝ)) (X := (12508237742271342951/12500000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4939718586699947/50000000000000000000 : ℝ) ≤ ((1474382016433698593/1474800000000000000 : ℝ)+2*(137611403081/92175000000000 : ℝ)*(11071/100000 : ℝ))^(4291/1024 : ℝ) := by
    rw [show (1474382016433698593/1474800000000000000 : ℝ)+2*(137611403081/92175000000000 : ℝ)*(11071/100000 : ℝ)=(10000471488361959/10000000000000000 : ℝ) by norm_num, show 1+2*(4939718586699947/50000000000000000000 : ℝ)=(25004939718586699947/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8237742271342951/25000000000000000000 : ℝ)+(4939718586699947/50000000000000000000 : ℝ) ≤ ((1474382016433698593/1474800000000000000 : ℝ)+(137611403081/92175000000000 : ℝ)*((7379/50000 : ℝ)+(11071/100000 : ℝ)))^(4291/1024 : ℝ) := by
    rw [show (1474382016433698593/1474800000000000000 : ℝ)+(137611403081/92175000000000 : ℝ)*((7379/50000 : ℝ)+(11071/100000 : ℝ))=(10001021933974283/10000000000000000 : ℝ) by norm_num, show 1+(8237742271342951/25000000000000000000 : ℝ)+(4939718586699947/50000000000000000000 : ℝ)=(50021415203129385849/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8237742271342951/25000000000000000000 : ℝ) ≤ ((1474382016433698593/1474800000000000000 : ℝ)+2*(137611403081/92175000000000 : ℝ)*(7379/50000 : ℝ))^(4291/1024 : ℝ) := by
    rw [show (1474382016433698593/1474800000000000000 : ℝ)+2*(137611403081/92175000000000 : ℝ)*(7379/50000 : ℝ)=(10001572379586607/10000000000000000 : ℝ) by norm_num, show 1+2*(8237742271342951/25000000000000000000 : ℝ)=(12508237742271342951/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1474382016433698593/1474800000000000000 : ℝ)*(X 1 0+X 2 0)+(137611403081/92175000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (11071/100000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (1474382016433698593/1474800000000000000 : ℝ)) (alpha := (137611403081/92175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1474382016433698593/1474800000000000000 : ℝ)*(X 0 1+X 2 1)+(137611403081/92175000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (11071/100000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (1474382016433698593/1474800000000000000 : ℝ)) (alpha := (137611403081/92175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1474382016433698593/1474800000000000000 : ℝ)*(X 0 2+X 1 2)+(137611403081/92175000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (11071/100000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (1474382016433698593/1474800000000000000 : ℝ)) (alpha := (137611403081/92175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-513147607/2500000000 : ℝ)*X 0 0+(1353411091/2500000000 : ℝ)*X 0 1+(2621953977/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349276027/10000000000 : ℝ)*X 1 0+(-2139088197/10000000000 : ℝ)*X 1 1+(1048781591/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337319011/2500000000 : ℝ)*X 2 0+(5243907953/10000000000 : ℝ)*X 2 1+(-2139088177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4329211337/10000000000 : ℝ)*X 0 0+(4155517687/10000000000 : ℝ)*X 0 1+(563713211/1250000000 : ℝ)*X 0 2+(4329211337/10000000000 : ℝ)*X 1 0+(4155517687/10000000000 : ℝ)*X 1 1+(563713211/1250000000 : ℝ)*X 1 2+(4329211337/10000000000 : ℝ)*X 2 0+(4155517687/10000000000 : ℝ)*X 2 1+(563713211/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-513150737/2500000000 : ℝ)*X 0 0+(5244518053/10000000000 : ℝ)*X 0 1+(5413031063/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((10362513/19531250 : ℝ)*X 1 0+(-78798601/400000000 : ℝ)*X 1 1+(216521243/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((33160041/62500000 : ℝ)*X 2 0+(2706515583/5000000000 : ℝ)*X 2 1+(-246245629/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2164618639/5000000000 : ℝ)*X 0 0+(450843269/1000000000 : ℝ)*X 0 1+(2078398669/5000000000 : ℝ)*X 0 2+(2164618639/5000000000 : ℝ)*X 1 0+(450843269/1000000000 : ℝ)*X 1 1+(2078398669/5000000000 : ℝ)*X 1 2+(2164618639/5000000000 : ℝ)*X 2 0+(450843269/1000000000 : ℝ)*X 2 1+(2078398669/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49111414266072723434354259/12290000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (386966547/50000000000000 : ℝ)*(base19) + (73924589/10000000000000 : ℝ)*(base23) + (1142829/4000000000000 : ℝ)*(lower2) + (4749597/5000000000000 : ℝ)*(upper3) + (20771267/25000000000000 : ℝ)*(upper5) + (4357447240238637/100000000000000 : ℝ)*(major0) + (4357447240238637/100000000000000 : ℝ)*(major1) + (4357447240238637/100000000000000 : ℝ)*(major2) + (5891503592577669/100000000000000 : ℝ)*(sp0) + (92054984396067/1562500000000 : ℝ)*(sp1) + (5891519036035493/100000000000000 : ℝ)*(sp2) + (1411683348447501/50000000000000 : ℝ)*(sp3) + (16182703713/100000000000000 : ℝ)*(sp4) + (7875099321/100000000000000 : ℝ)*(sp7) + (705843642998581/25000000000000 : ℝ)*(f.failure) + (2945759887640691/50000000000000 : ℝ)*(f.sum) + (3223621306331/1536250000000000000000000000 : ℝ)*base66 + (601722943805523247/49160000000000000000000000000000 : ℝ)*base67 + (583329589699523247/49160000000000000000000000000000 : ℝ)*base69 + (450099959291483247/49160000000000000000000000000000 : ℝ)*base71 + (5983555904809/1536250000000000000000000000 : ℝ)*base73 + (1195739557461323247/49160000000000000000000000000000 : ℝ)*base75 + (68483763340923247/49160000000000000000000000000000 : ℝ)*base77 + (191731132874316753/49160000000000000000000000000000 : ℝ)*base80 + (12819359713911/6145000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (106351/7812500000000000000 : ℝ)*base89 + (106351/7812500000000000000 : ℝ)*base91 + (106351/7812500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2309080312933980814169507/245800000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1803921917/100000000000000 : ℝ)*(base19) + (173240111/10000000000000 : ℝ)*(base23) + (116760449/50000000000000 : ℝ)*(upper3) + (13068827/100000000000000 : ℝ)*(lower4) + (181189363/100000000000000 : ℝ)*(upper5) + (43890563377033/1000000000000 : ℝ)*(major0) + (43890563377033/1000000000000 : ℝ)*(major1) + (43890563377033/1000000000000 : ℝ)*(major2) + (35539409933/100000000000000 : ℝ)*(sp1) + (18451358787/50000000000000 : ℝ)*(sp2) + (593425691761981/10000000000000 : ℝ)*(sp4) + (5934219574287961/100000000000000 : ℝ)*(sp5) + (5934218282501127/100000000000000 : ℝ)*(sp6) + (710963861162171/25000000000000 : ℝ)*(sp7) + (710963861162171/25000000000000 : ℝ)*(f.failure) + (593425691761981/10000000000000 : ℝ)*(f.sum) + (1836027822689/230437500000000000000000000 : ℝ)*base66 + (6530018506389431/1474800000000000000000000000000 : ℝ)*base68 + (17485940970823031/1474800000000000000000000000000 : ℝ)*base70 + (21975859752790631/1474800000000000000000000000000 : ℝ)*base72 + (2271216307391/1843500000000000000000000000 : ℝ)*base73 + (8640012494911031/1474800000000000000000000000000 : ℝ)*base76 + (20574424812911831/1474800000000000000000000000000 : ℝ)*base78 + (20034998331004631/1474800000000000000000000000000 : ℝ)*base80 + (487650440327/368700000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (28029/1953125000000000000 : ℝ)*base89 + (28029/1953125000000000000 : ℝ)*base91 + (28029/1953125000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1332_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11071/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11117/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1332_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1332_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1009/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1957/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11117/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1332_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1332_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1332_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1009/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1957/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11117/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1332_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

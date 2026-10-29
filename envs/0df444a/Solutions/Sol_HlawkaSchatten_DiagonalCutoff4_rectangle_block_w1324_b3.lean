-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1324_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:44:50.708978+00:00
-- url     : https://prove2.me/submissions/1d6de6a4-70b4-4af0-a0c4-5ec6a54bc87a

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
theorem support_rectangle_w1324_box_0 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1890931321/10000000000 : ℝ)*x 0 + (2695344387/5000000000 : ℝ)*x 1 + (2695344349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1890931321/10000000000 : ℝ)^1071 ≤ (11206553438129/100000000000000 : ℝ)^815 := by
    have hnat : (1890931321 : ℕ)^1071*100000000000000^815 ≤ 11206553438129^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1890931321 10000000000 11206553438129 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695344387/5000000000 : ℝ)^1071 ≤ (8879344736687/20000000000000 : ℝ)^815 := by
    have hnat : (2695344387 : ℕ)^1071*20000000000000^815 ≤ 8879344736687^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695344387 5000000000 8879344736687 20000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695344349/5000000000 : ℝ)^1071 ≤ (5549590357613/12500000000000 : ℝ)^815 := by
    have hnat : (2695344349 : ℕ)^1071*12500000000000^815 ≤ 5549590357613^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695344349 5000000000 5549590357613 12500000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1890931321/10000000000 : ℝ), (2695344387/5000000000 : ℝ), (2695344349/5000000000 : ℝ)] ![(11206553438129/100000000000000 : ℝ), (8879344736687/20000000000000 : ℝ), (5549590357613/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1890931321/10000000000 : ℝ)|^1071 ≤ (11206553438129/100000000000000 : ℝ)^815
        have hw : |(-1890931321/10000000000 : ℝ)|=(1890931321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695344387/5000000000 : ℝ)|^1071 ≤ (8879344736687/20000000000000 : ℝ)^815
        have hw : |(2695344387/5000000000 : ℝ)|=(2695344387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695344349/5000000000 : ℝ)|^1071 ≤ (5549590357613/12500000000000 : ℝ)^815
        have hw : |(2695344349/5000000000 : ℝ)|=(2695344349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_box_1 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1321225817/2500000000 : ℝ)*x 0 + (-508942293/2500000000 : ℝ)*x 1 + (5390689211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321225817/2500000000 : ℝ)^1071 ≤ (4325537576521/10000000000000 : ℝ)^815 := by
    have hnat : (1321225817 : ℕ)^1071*10000000000000^815 ≤ 4325537576521^815*2500000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321225817 2500000000 4325537576521 10000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508942293/2500000000 : ℝ)^1071 ≤ (6173947904537/50000000000000 : ℝ)^815 := by
    have hnat : (508942293 : ℕ)^1071*50000000000000^815 ≤ 6173947904537^815*2500000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508942293 2500000000 6173947904537 50000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390689211/10000000000 : ℝ)^1071 ≤ (22198364206493/50000000000000 : ℝ)^815 := by
    have hnat : (5390689211 : ℕ)^1071*50000000000000^815 ≤ 22198364206493^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390689211 10000000000 22198364206493 50000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321225817/2500000000 : ℝ), (-508942293/2500000000 : ℝ), (5390689211/10000000000 : ℝ)] ![(4325537576521/10000000000000 : ℝ), (6173947904537/50000000000000 : ℝ), (22198364206493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321225817/2500000000 : ℝ)|^1071 ≤ (4325537576521/10000000000000 : ℝ)^815
        have hw : |(1321225817/2500000000 : ℝ)|=(1321225817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-508942293/2500000000 : ℝ)|^1071 ≤ (6173947904537/50000000000000 : ℝ)^815
        have hw : |(-508942293/2500000000 : ℝ)|=(508942293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390689211/10000000000 : ℝ)|^1071 ≤ (22198364206493/50000000000000 : ℝ)^815
        have hw : |(5390689211/10000000000 : ℝ)|=(5390689211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_box_2 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4128831/7812500 : ℝ)*x 0 + (5390688953/10000000000 : ℝ)*x 1 + (-1017884483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4128831/7812500 : ℝ)^1071 ≤ (1081384504913/2500000000000 : ℝ)^815 := by
    have hnat : (4128831 : ℕ)^1071*2500000000000^815 ≤ 1081384504913^815*7812500^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128831 7812500 1081384504913 2500000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390688953/10000000000 : ℝ)^1071 ≤ (44396725620711/100000000000000 : ℝ)^815 := by
    have hnat : (5390688953 : ℕ)^1071*100000000000000^815 ≤ 44396725620711^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390688953 10000000000 44396725620711 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1017884483/5000000000 : ℝ)^1071 ≤ (12347894167111/100000000000000 : ℝ)^815 := by
    have hnat : (1017884483 : ℕ)^1071*100000000000000^815 ≤ 12347894167111^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017884483 5000000000 12347894167111 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4128831/7812500 : ℝ), (5390688953/10000000000 : ℝ), (-1017884483/5000000000 : ℝ)] ![(1081384504913/2500000000000 : ℝ), (44396725620711/100000000000000 : ℝ), (12347894167111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4128831/7812500 : ℝ)|^1071 ≤ (1081384504913/2500000000000 : ℝ)^815
        have hw : |(4128831/7812500 : ℝ)|=(4128831/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390688953/10000000000 : ℝ)|^1071 ≤ (44396725620711/100000000000000 : ℝ)^815
        have hw : |(5390688953/10000000000 : ℝ)|=(5390688953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1017884483/5000000000 : ℝ)|^1071 ≤ (12347894167111/100000000000000 : ℝ)^815
        have hw : |(-1017884483/5000000000 : ℝ)|=(1017884483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_box_3 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4479968797/10000000000 : ℝ)*x 0 + (4260971763/10000000000 : ℝ)*x 1 + (4260971871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4479968797/10000000000 : ℝ)^1071 ≤ (34812629353171/100000000000000 : ℝ)^815 := by
    have hnat : (4479968797 : ℕ)^1071*100000000000000^815 ≤ 34812629353171^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479968797 10000000000 34812629353171 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4260971763/10000000000 : ℝ)^1071 ≤ (32593684779391/100000000000000 : ℝ)^815 := by
    have hnat : (4260971763 : ℕ)^1071*100000000000000^815 ≤ 32593684779391^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4260971763 10000000000 32593684779391 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4260971871/10000000000 : ℝ)^1071 ≤ (32593685865017/100000000000000 : ℝ)^815 := by
    have hnat : (4260971871 : ℕ)^1071*100000000000000^815 ≤ 32593685865017^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4260971871 10000000000 32593685865017 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4479968797/10000000000 : ℝ), (4260971763/10000000000 : ℝ), (4260971871/10000000000 : ℝ)] ![(34812629353171/100000000000000 : ℝ), (32593684779391/100000000000000 : ℝ), (32593685865017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4479968797/10000000000 : ℝ)|^1071 ≤ (34812629353171/100000000000000 : ℝ)^815
        have hw : |(4479968797/10000000000 : ℝ)|=(4479968797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4260971763/10000000000 : ℝ)|^1071 ≤ (32593684779391/100000000000000 : ℝ)^815
        have hw : |(4260971763/10000000000 : ℝ)|=(4260971763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4260971871/10000000000 : ℝ)|^1071 ≤ (32593685865017/100000000000000 : ℝ)^815
        have hw : |(4260971871/10000000000 : ℝ)|=(4260971871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_box_4 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-44621611/200000000 : ℝ)*x 0 + (5264512091/10000000000 : ℝ)*x 1 + (2632255831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44621611/200000000 : ℝ)^1071 ≤ (3481906495909/25000000000000 : ℝ)^815 := by
    have hnat : (44621611 : ℕ)^1071*25000000000000^815 ≤ 3481906495909^815*200000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44621611 200000000 3481906495909 25000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264512091/10000000000 : ℝ)^1071 ≤ (10759047326977/25000000000000 : ℝ)^815 := by
    have hnat : (5264512091 : ℕ)^1071*25000000000000^815 ≤ 10759047326977^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264512091 10000000000 10759047326977 25000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632255831/5000000000 : ℝ)^1071 ≤ (43036184699353/100000000000000 : ℝ)^815 := by
    have hnat : (2632255831 : ℕ)^1071*100000000000000^815 ≤ 43036184699353^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632255831 5000000000 43036184699353 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-44621611/200000000 : ℝ), (5264512091/10000000000 : ℝ), (2632255831/5000000000 : ℝ)] ![(3481906495909/25000000000000 : ℝ), (10759047326977/25000000000000 : ℝ), (43036184699353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-44621611/200000000 : ℝ)|^1071 ≤ (3481906495909/25000000000000 : ℝ)^815
        have hw : |(-44621611/200000000 : ℝ)|=(44621611/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264512091/10000000000 : ℝ)|^1071 ≤ (10759047326977/25000000000000 : ℝ)^815
        have hw : |(5264512091/10000000000 : ℝ)|=(5264512091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632255831/5000000000 : ℝ)|^1071 ≤ (43036184699353/100000000000000 : ℝ)^815
        have hw : |(2632255831/5000000000 : ℝ)|=(2632255831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_box_5 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2686797661/5000000000 : ℝ)*x 0 + (-260783867/1250000000 : ℝ)*x 1 + (5264512441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686797661/5000000000 : ℝ)^1071 ≤ (44211817341047/100000000000000 : ℝ)^815 := by
    have hnat : (2686797661 : ℕ)^1071*100000000000000^815 ≤ 44211817341047^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686797661 5000000000 44211817341047 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260783867/1250000000 : ℝ)^1071 ≤ (6375994782653/50000000000000 : ℝ)^815 := by
    have hnat : (260783867 : ℕ)^1071*50000000000000^815 ≤ 6375994782653^815*1250000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260783867 1250000000 6375994782653 50000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264512441/10000000000 : ℝ)^1071 ≤ (21518096533901/50000000000000 : ℝ)^815 := by
    have hnat : (5264512441 : ℕ)^1071*50000000000000^815 ≤ 21518096533901^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264512441 10000000000 21518096533901 50000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686797661/5000000000 : ℝ), (-260783867/1250000000 : ℝ), (5264512441/10000000000 : ℝ)] ![(44211817341047/100000000000000 : ℝ), (6375994782653/50000000000000 : ℝ), (21518096533901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686797661/5000000000 : ℝ)|^1071 ≤ (44211817341047/100000000000000 : ℝ)^815
        have hw : |(2686797661/5000000000 : ℝ)|=(2686797661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-260783867/1250000000 : ℝ)|^1071 ≤ (6375994782653/50000000000000 : ℝ)^815
        have hw : |(-260783867/1250000000 : ℝ)|=(260783867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264512441/10000000000 : ℝ)|^1071 ≤ (21518096533901/50000000000000 : ℝ)^815
        have hw : |(5264512441/10000000000 : ℝ)|=(5264512441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_box_6 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2686797991/5000000000 : ℝ)*x 0 + (5264511687/10000000000 : ℝ)*x 1 + (-1043135529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686797991/5000000000 : ℝ)^1071 ≤ (22105912238477/50000000000000 : ℝ)^815 := by
    have hnat : (2686797991 : ℕ)^1071*50000000000000^815 ≤ 22105912238477^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686797991 5000000000 22105912238477 50000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264511687/10000000000 : ℝ)^1071 ≤ (10759046241979/25000000000000 : ℝ)^815 := by
    have hnat : (5264511687 : ℕ)^1071*25000000000000^815 ≤ 10759046241979^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264511687 10000000000 10759046241979 25000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043135529/5000000000 : ℝ)^1071 ≤ (3187997636311/25000000000000 : ℝ)^815 := by
    have hnat : (1043135529 : ℕ)^1071*25000000000000^815 ≤ 3187997636311^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043135529 5000000000 3187997636311 25000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686797991/5000000000 : ℝ), (5264511687/10000000000 : ℝ), (-1043135529/5000000000 : ℝ)] ![(22105912238477/50000000000000 : ℝ), (10759046241979/25000000000000 : ℝ), (3187997636311/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686797991/5000000000 : ℝ)|^1071 ≤ (22105912238477/50000000000000 : ℝ)^815
        have hw : |(2686797991/5000000000 : ℝ)|=(2686797991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264511687/10000000000 : ℝ)|^1071 ≤ (10759046241979/25000000000000 : ℝ)^815
        have hw : |(5264511687/10000000000 : ℝ)|=(5264511687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1043135529/5000000000 : ℝ)|^1071 ≤ (3187997636311/25000000000000 : ℝ)^815
        have hw : |(-1043135529/5000000000 : ℝ)|=(1043135529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_box_7 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4181834677/10000000000 : ℝ)*x 0 + (4409985297/10000000000 : ℝ)*x 1 + (2204992023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4181834677/10000000000 : ℝ)^1071 ≤ (99376629499/312500000000 : ℝ)^815 := by
    have hnat : (4181834677 : ℕ)^1071*312500000000^815 ≤ 99376629499^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4181834677 10000000000 99376629499 312500000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4409985297/10000000000 : ℝ)^1071 ≤ (34099745630161/100000000000000 : ℝ)^815 := by
    have hnat : (4409985297 : ℕ)^1071*100000000000000^815 ≤ 34099745630161^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4409985297 10000000000 34099745630161 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2204992023/5000000000 : ℝ)^1071 ≤ (1363989316739/4000000000000 : ℝ)^815 := by
    have hnat : (2204992023 : ℕ)^1071*4000000000000^815 ≤ 1363989316739^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204992023 5000000000 1363989316739 4000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4181834677/10000000000 : ℝ), (4409985297/10000000000 : ℝ), (2204992023/5000000000 : ℝ)] ![(99376629499/312500000000 : ℝ), (34099745630161/100000000000000 : ℝ), (1363989316739/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4181834677/10000000000 : ℝ)|^1071 ≤ (99376629499/312500000000 : ℝ)^815
        have hw : |(4181834677/10000000000 : ℝ)|=(4181834677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4409985297/10000000000 : ℝ)|^1071 ≤ (34099745630161/100000000000000 : ℝ)^815
        have hw : |(4409985297/10000000000 : ℝ)|=(4409985297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2204992023/5000000000 : ℝ)|^1071 ≤ (1363989316739/4000000000000 : ℝ)^815
        have hw : |(2204992023/5000000000 : ℝ)|=(2204992023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_box_8 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2159698429/10000000000 : ℝ)*x 0 + (517773413/1000000000 : ℝ)*x 1 + (5404715217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159698429/10000000000 : ℝ)^1071 ≤ (13345014409311/100000000000000 : ℝ)^815 := by
    have hnat : (2159698429 : ℕ)^1071*100000000000000^815 ≤ 13345014409311^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159698429 10000000000 13345014409311 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517773413/1000000000 : ℝ)^1071 ≤ (5263299361253/12500000000000 : ℝ)^815 := by
    have hnat : (517773413 : ℕ)^1071*12500000000000^815 ≤ 5263299361253^815*1000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517773413 1000000000 5263299361253 12500000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404715217/10000000000 : ℝ)^1071 ≤ (8909718136461/20000000000000 : ℝ)^815 := by
    have hnat : (5404715217 : ℕ)^1071*20000000000000^815 ≤ 8909718136461^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404715217 10000000000 8909718136461 20000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2159698429/10000000000 : ℝ), (517773413/1000000000 : ℝ), (5404715217/10000000000 : ℝ)] ![(13345014409311/100000000000000 : ℝ), (5263299361253/12500000000000 : ℝ), (8909718136461/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2159698429/10000000000 : ℝ)|^1071 ≤ (13345014409311/100000000000000 : ℝ)^815
        have hw : |(-2159698429/10000000000 : ℝ)|=(2159698429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517773413/1000000000 : ℝ)|^1071 ≤ (5263299361253/12500000000000 : ℝ)^815
        have hw : |(517773413/1000000000 : ℝ)|=(517773413/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404715217/10000000000 : ℝ)|^1071 ≤ (8909718136461/20000000000000 : ℝ)^815
        have hw : |(5404715217/10000000000 : ℝ)|=(5404715217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_box_9 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (659379803/1250000000 : ℝ)*x 0 + (-507505207/2500000000 : ℝ)*x 1 + (270235793/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659379803/1250000000 : ℝ)^1071 ≤ (21574652251191/50000000000000 : ℝ)^815 := by
    have hnat : (659379803 : ℕ)^1071*50000000000000^815 ≤ 21574652251191^815*1250000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659379803 1250000000 21574652251191 50000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (507505207/2500000000 : ℝ)^1071 ≤ (12302097834687/100000000000000 : ℝ)^815 := by
    have hnat : (507505207 : ℕ)^1071*100000000000000^815 ≤ 12302097834687^815*2500000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507505207 2500000000 12302097834687 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270235793/500000000 : ℝ)^1071 ≤ (44548597647031/100000000000000 : ℝ)^815 := by
    have hnat : (270235793 : ℕ)^1071*100000000000000^815 ≤ 44548597647031^815*500000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270235793 500000000 44548597647031 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659379803/1250000000 : ℝ), (-507505207/2500000000 : ℝ), (270235793/500000000 : ℝ)] ![(21574652251191/50000000000000 : ℝ), (12302097834687/100000000000000 : ℝ), (44548597647031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659379803/1250000000 : ℝ)|^1071 ≤ (21574652251191/50000000000000 : ℝ)^815
        have hw : |(659379803/1250000000 : ℝ)|=(659379803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-507505207/2500000000 : ℝ)|^1071 ≤ (12302097834687/100000000000000 : ℝ)^815
        have hw : |(-507505207/2500000000 : ℝ)|=(507505207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270235793/500000000 : ℝ)|^1071 ≤ (44548597647031/100000000000000 : ℝ)^815
        have hw : |(270235793/500000000 : ℝ)|=(270235793/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_box_10 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5275038581/10000000000 : ℝ)*x 0 + (5404715651/10000000000 : ℝ)*x 1 + (-2030020901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275038581/10000000000 : ℝ)^1071 ≤ (43149306190021/100000000000000 : ℝ)^815 := by
    have hnat : (5275038581 : ℕ)^1071*100000000000000^815 ≤ 43149306190021^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275038581 10000000000 43149306190021 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404715651/10000000000 : ℝ)^1071 ≤ (5568574422903/12500000000000 : ℝ)^815 := by
    have hnat : (5404715651 : ℕ)^1071*12500000000000^815 ≤ 5568574422903^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404715651 10000000000 5568574422903 12500000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2030020901/10000000000 : ℝ)^1071 ≤ (384440575501/3125000000000 : ℝ)^815 := by
    have hnat : (2030020901 : ℕ)^1071*3125000000000^815 ≤ 384440575501^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030020901 10000000000 384440575501 3125000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275038581/10000000000 : ℝ), (5404715651/10000000000 : ℝ), (-2030020901/10000000000 : ℝ)] ![(43149306190021/100000000000000 : ℝ), (5568574422903/12500000000000 : ℝ), (384440575501/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275038581/10000000000 : ℝ)|^1071 ≤ (43149306190021/100000000000000 : ℝ)^815
        have hw : |(5275038581/10000000000 : ℝ)|=(5275038581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404715651/10000000000 : ℝ)|^1071 ≤ (5568574422903/12500000000000 : ℝ)^815
        have hw : |(5404715651/10000000000 : ℝ)|=(5404715651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2030020901/10000000000 : ℝ)|^1071 ≤ (384440575501/3125000000000 : ℝ)^815
        have hw : |(-2030020901/10000000000 : ℝ)|=(2030020901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_box_11 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1128137949/2500000000 : ℝ)*x 0 + (530549081/1250000000 : ℝ)*x 1 + (4244392951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1128137949/2500000000 : ℝ)^1071 ≤ (35145733263449/100000000000000 : ℝ)^815 := by
    have hnat : (1128137949 : ℕ)^1071*100000000000000^815 ≤ 35145733263449^815*2500000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128137949 2500000000 35145733263449 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530549081/1250000000 : ℝ)^1071 ≤ (2026695740033/6250000000000 : ℝ)^815 := by
    have hnat : (530549081 : ℕ)^1071*6250000000000^815 ≤ 2026695740033^815*1250000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530549081 1250000000 2026695740033 6250000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4244392951/10000000000 : ℝ)^1071 ≤ (16213567441293/50000000000000 : ℝ)^815 := by
    have hnat : (4244392951 : ℕ)^1071*50000000000000^815 ≤ 16213567441293^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244392951 10000000000 16213567441293 50000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1128137949/2500000000 : ℝ), (530549081/1250000000 : ℝ), (4244392951/10000000000 : ℝ)] ![(35145733263449/100000000000000 : ℝ), (2026695740033/6250000000000 : ℝ), (16213567441293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1128137949/2500000000 : ℝ)|^1071 ≤ (35145733263449/100000000000000 : ℝ)^815
        have hw : |(1128137949/2500000000 : ℝ)|=(1128137949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(530549081/1250000000 : ℝ)|^1071 ≤ (2026695740033/6250000000000 : ℝ)^815
        have hw : |(530549081/1250000000 : ℝ)|=(530549081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4244392951/10000000000 : ℝ)|^1071 ≤ (16213567441293/50000000000000 : ℝ)^815
        have hw : |(4244392951/10000000000 : ℝ)|=(4244392951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_box_12 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-981343421/5000000000 : ℝ)*x 0 + (2737610057/5000000000 : ℝ)*x 1 + (5253457817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (981343421/5000000000 : ℝ)^1071 ≤ (235373808177/2000000000000 : ℝ)^815 := by
    have hnat : (981343421 : ℕ)^1071*2000000000000^815 ≤ 235373808177^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981343421 5000000000 235373808177 2000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2737610057/5000000000 : ℝ)^1071 ≤ (45313832219937/100000000000000 : ℝ)^815 := by
    have hnat : (2737610057 : ℕ)^1071*100000000000000^815 ≤ 45313832219937^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737610057 5000000000 45313832219937 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253457817/10000000000 : ℝ)^1071 ≤ (42917477353549/100000000000000 : ℝ)^815 := by
    have hnat : (5253457817 : ℕ)^1071*100000000000000^815 ≤ 42917477353549^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253457817 10000000000 42917477353549 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-981343421/5000000000 : ℝ), (2737610057/5000000000 : ℝ), (5253457817/10000000000 : ℝ)] ![(235373808177/2000000000000 : ℝ), (45313832219937/100000000000000 : ℝ), (42917477353549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-981343421/5000000000 : ℝ)|^1071 ≤ (235373808177/2000000000000 : ℝ)^815
        have hw : |(-981343421/5000000000 : ℝ)|=(981343421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2737610057/5000000000 : ℝ)|^1071 ≤ (45313832219937/100000000000000 : ℝ)^815
        have hw : |(2737610057/5000000000 : ℝ)|=(2737610057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253457817/10000000000 : ℝ)|^1071 ≤ (42917477353549/100000000000000 : ℝ)^815
        have hw : |(5253457817/10000000000 : ℝ)|=(5253457817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_box_13 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5381363073/10000000000 : ℝ)*x 0 + (-2090590909/10000000000 : ℝ)*x 1 + (5253457943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381363073/10000000000 : ℝ)^1071 ≤ (44295821177651/100000000000000 : ℝ)^815 := by
    have hnat : (5381363073 : ℕ)^1071*100000000000000^815 ≤ 44295821177651^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381363073 10000000000 44295821177651 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2090590909/10000000000 : ℝ)^1071 ≤ (3196675024567/25000000000000 : ℝ)^815 := by
    have hnat : (2090590909 : ℕ)^1071*25000000000000^815 ≤ 3196675024567^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090590909 10000000000 3196675024567 25000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253457943/10000000000 : ℝ)^1071 ≤ (42917478706217/100000000000000 : ℝ)^815 := by
    have hnat : (5253457943 : ℕ)^1071*100000000000000^815 ≤ 42917478706217^815*10000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253457943 10000000000 42917478706217 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381363073/10000000000 : ℝ), (-2090590909/10000000000 : ℝ), (5253457943/10000000000 : ℝ)] ![(44295821177651/100000000000000 : ℝ), (3196675024567/25000000000000 : ℝ), (42917478706217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381363073/10000000000 : ℝ)|^1071 ≤ (44295821177651/100000000000000 : ℝ)^815
        have hw : |(5381363073/10000000000 : ℝ)|=(5381363073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2090590909/10000000000 : ℝ)|^1071 ≤ (3196675024567/25000000000000 : ℝ)^815
        have hw : |(-2090590909/10000000000 : ℝ)|=(2090590909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253457943/10000000000 : ℝ)|^1071 ≤ (42917478706217/100000000000000 : ℝ)^815
        have hw : |(5253457943/10000000000 : ℝ)|=(5253457943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_box_14 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (672670483/1250000000 : ℝ)*x 0 + (1313364289/2500000000 : ℝ)*x 1 + (-130661931/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672670483/1250000000 : ℝ)^1071 ≤ (4429582973381/10000000000000 : ℝ)^815 := by
    have hnat : (672670483 : ℕ)^1071*10000000000000^815 ≤ 4429582973381^815*1250000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672670483 1250000000 4429582973381 10000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313364289/2500000000 : ℝ)^1071 ≤ (42917470257407/100000000000000 : ℝ)^815 := by
    have hnat : (1313364289 : ℕ)^1071*100000000000000^815 ≤ 42917470257407^815*2500000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313364289 2500000000 42917470257407 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130661931/625000000 : ℝ)^1071 ≤ (12786699993781/100000000000000 : ℝ)^815 := by
    have hnat : (130661931 : ℕ)^1071*100000000000000^815 ≤ 12786699993781^815*625000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130661931 625000000 12786699993781 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672670483/1250000000 : ℝ), (1313364289/2500000000 : ℝ), (-130661931/625000000 : ℝ)] ![(4429582973381/10000000000000 : ℝ), (42917470257407/100000000000000 : ℝ), (12786699993781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672670483/1250000000 : ℝ)|^1071 ≤ (4429582973381/10000000000000 : ℝ)^815
        have hw : |(672670483/1250000000 : ℝ)|=(672670483/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313364289/2500000000 : ℝ)|^1071 ≤ (42917470257407/100000000000000 : ℝ)^815
        have hw : |(1313364289/2500000000 : ℝ)|=(1313364289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-130661931/625000000 : ℝ)|^1071 ≤ (12786699993781/100000000000000 : ℝ)^815
        have hw : |(-130661931/625000000 : ℝ)|=(130661931/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1324_box_15 (p : ℝ) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2077634411/5000000000 : ℝ)*x 0 + (2211514327/5000000000 : ℝ)*x 1 + (442302873/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2077634411/5000000000 : ℝ)^1071 ≤ (7883828013621/25000000000000 : ℝ)^815 := by
    have hnat : (2077634411 : ℕ)^1071*25000000000000^815 ≤ 7883828013621^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077634411 5000000000 7883828013621 25000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2211514327/5000000000 : ℝ)^1071 ≤ (1711617178807/5000000000000 : ℝ)^815 := by
    have hnat : (2211514327 : ℕ)^1071*5000000000000^815 ≤ 1711617178807^815*5000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211514327 5000000000 1711617178807 5000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442302873/1000000000 : ℝ)^1071 ≤ (34232344349109/100000000000000 : ℝ)^815 := by
    have hnat : (442302873 : ℕ)^1071*100000000000000^815 ≤ 34232344349109^815*1000000000^1071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442302873 1000000000 34232344349109 100000000000000 1071 815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1071/256 : ℝ)) 1071 815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2077634411/5000000000 : ℝ), (2211514327/5000000000 : ℝ), (442302873/1000000000 : ℝ)] ![(7883828013621/25000000000000 : ℝ), (1711617178807/5000000000000 : ℝ), (34232344349109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2077634411/5000000000 : ℝ)|^1071 ≤ (7883828013621/25000000000000 : ℝ)^815
        have hw : |(2077634411/5000000000 : ℝ)|=(2077634411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2211514327/5000000000 : ℝ)|^1071 ≤ (1711617178807/5000000000000 : ℝ)^815
        have hw : |(2211514327/5000000000 : ℝ)|=(2211514327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(442302873/1000000000 : ℝ)|^1071 ≤ (34232344349109/100000000000000 : ℝ)^815
        have hw : |(442302873/1000000000 : ℝ)|=(442302873/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1324_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38504949/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62849/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29453/50000 : ℝ) ∧ (9981/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42141/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7347/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11107/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7347/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11107/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7347/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11107/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7347/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11107/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7347/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11107/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7347/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11107/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11107/100000 : ℝ) ^ (4283/1024 : ℝ) ≤ (10188181054176271/100000000000000000000 : ℝ) := by
    have hpowers : (11107/100000 : ℝ)^4283 ≤ (10188181054176271/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11107 : ℕ)^4283*100000000000000000000^1024 ≤ 10188181054176271^1024*100000^4283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11107 100000 10188181054176271 100000000000000000000 4283 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11107/100000 : ℝ)) (X := (10188181054176271/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4283 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7347/50000 : ℝ) ^ (4283/1024 : ℝ) ≤ (32844722560842949/100000000000000000000 : ℝ) := by
    have hpowers : (7347/50000 : ℝ)^4283 ≤ (32844722560842949/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7347 : ℕ)^4283*100000000000000000000^1024 ≤ 32844722560842949^1024*50000^4283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7347 50000 32844722560842949 100000000000000000000 4283 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7347/50000 : ℝ)) (X := (32844722560842949/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4283 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010188181054176271/50000000000000000000 : ℝ) ≤ (10000487129989157/10000000000000000 : ℝ) ^ (4283/1024 : ℝ) := by
    have hpowers : (50010188181054176271/50000000000000000000 : ℝ)^1024 ≤ (10000487129989157/10000000000000000 : ℝ)^4283 := by
      have hnat : (50010188181054176271 : ℕ)^1024*10000000000000000^4283 ≤ 10000487129989157^4283*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010188181054176271 50000000000000000000 10000487129989157 10000000000000000 1024 4283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000487129989157/10000000000000000 : ℝ)) (X := (50010188181054176271/50000000000000000000 : ℝ)) (by norm_num) 4283 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002151645180750961/5000000000000000000 : ℝ) ≤ (5000514341356547/5000000000000000 : ℝ) ^ (4283/1024 : ℝ) := by
    have hpowers : (5002151645180750961/5000000000000000000 : ℝ)^1024 ≤ (5000514341356547/5000000000000000 : ℝ)^4283 := by
      have hnat : (5002151645180750961 : ℕ)^1024*5000000000000000^4283 ≤ 5000514341356547^4283*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002151645180750961 5000000000000000000 5000514341356547 5000000000000000 1024 4283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000514341356547/5000000000000000 : ℝ)) (X := (5002151645180750961/5000000000000000000 : ℝ)) (by norm_num) 4283 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032844722560842949/50000000000000000000 : ℝ) ≤ (10001570235437031/10000000000000000 : ℝ) ^ (4283/1024 : ℝ) := by
    have hpowers : (50032844722560842949/50000000000000000000 : ℝ)^1024 ≤ (10001570235437031/10000000000000000 : ℝ)^4283 := by
      have hnat : (50032844722560842949 : ℕ)^1024*10000000000000000^4283 ≤ 10001570235437031^4283*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032844722560842949 50000000000000000000 10001570235437031 10000000000000000 1024 4283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001570235437031/10000000000000000 : ℝ)) (X := (50032844722560842949/50000000000000000000 : ℝ)) (by norm_num) 4283 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10188181054176271/100000000000000000000 : ℝ) ≤ ((35859717283061569641/35870000000000000000 : ℝ)+2*(541552723937/358700000000000 : ℝ)*(11107/100000 : ℝ))^(4283/1024 : ℝ) := by
    rw [show (35859717283061569641/35870000000000000000 : ℝ)+2*(541552723937/358700000000000 : ℝ)*(11107/100000 : ℝ)=(10000487129989157/10000000000000000 : ℝ) by norm_num, show 1+2*(10188181054176271/100000000000000000000 : ℝ)=(50010188181054176271/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32844722560842949/100000000000000000000 : ℝ)+(10188181054176271/100000000000000000000 : ℝ) ≤ ((35859717283061569641/35870000000000000000 : ℝ)+(541552723937/358700000000000 : ℝ)*((7347/50000 : ℝ)+(11107/100000 : ℝ)))^(4283/1024 : ℝ) := by
    rw [show (35859717283061569641/35870000000000000000 : ℝ)+(541552723937/358700000000000 : ℝ)*((7347/50000 : ℝ)+(11107/100000 : ℝ))=(5000514341356547/5000000000000000 : ℝ) by norm_num, show 1+(32844722560842949/100000000000000000000 : ℝ)+(10188181054176271/100000000000000000000 : ℝ)=(5002151645180750961/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32844722560842949/100000000000000000000 : ℝ) ≤ ((35859717283061569641/35870000000000000000 : ℝ)+2*(541552723937/358700000000000 : ℝ)*(7347/50000 : ℝ))^(4283/1024 : ℝ) := by
    rw [show (35859717283061569641/35870000000000000000 : ℝ)+2*(541552723937/358700000000000 : ℝ)*(7347/50000 : ℝ)=(10001570235437031/10000000000000000 : ℝ) by norm_num, show 1+2*(32844722560842949/100000000000000000000 : ℝ)=(50032844722560842949/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35859717283061569641/35870000000000000000 : ℝ)*(X 1 0+X 2 0)+(541552723937/358700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4283/1024 : ℝ)) (lo := (11107/100000 : ℝ)) (hi := (7347/50000 : ℝ)) (c := (35859717283061569641/35870000000000000000 : ℝ)) (alpha := (541552723937/358700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35859717283061569641/35870000000000000000 : ℝ)*(X 0 1+X 2 1)+(541552723937/358700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4283/1024 : ℝ)) (lo := (11107/100000 : ℝ)) (hi := (7347/50000 : ℝ)) (c := (35859717283061569641/35870000000000000000 : ℝ)) (alpha := (541552723937/358700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35859717283061569641/35870000000000000000 : ℝ)*(X 0 2+X 1 2)+(541552723937/358700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4283/1024 : ℝ)) (lo := (11107/100000 : ℝ)) (hi := (7347/50000 : ℝ)) (c := (35859717283061569641/35870000000000000000 : ℝ)) (alpha := (541552723937/358700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1890931321/10000000000 : ℝ)*X 0 0+(2695344387/5000000000 : ℝ)*X 0 1+(2695344349/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1321225817/2500000000 : ℝ)*X 1 0+(-508942293/2500000000 : ℝ)*X 1 1+(5390689211/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((4128831/7812500 : ℝ)*X 2 0+(5390688953/10000000000 : ℝ)*X 2 1+(-1017884483/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4479968797/10000000000 : ℝ)*X 0 0+(4260971763/10000000000 : ℝ)*X 0 1+(4260971871/10000000000 : ℝ)*X 0 2+(4479968797/10000000000 : ℝ)*X 1 0+(4260971763/10000000000 : ℝ)*X 1 1+(4260971871/10000000000 : ℝ)*X 1 2+(4479968797/10000000000 : ℝ)*X 2 0+(4260971763/10000000000 : ℝ)*X 2 1+(4260971871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-44621611/200000000 : ℝ)*X 0 0+(5264512091/10000000000 : ℝ)*X 0 1+(2632255831/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2686797661/5000000000 : ℝ)*X 1 0+(-260783867/1250000000 : ℝ)*X 1 1+(5264512441/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2686797991/5000000000 : ℝ)*X 2 0+(5264511687/10000000000 : ℝ)*X 2 1+(-1043135529/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4181834677/10000000000 : ℝ)*X 0 0+(4409985297/10000000000 : ℝ)*X 0 1+(2204992023/5000000000 : ℝ)*X 0 2+(4181834677/10000000000 : ℝ)*X 1 0+(4409985297/10000000000 : ℝ)*X 1 1+(2204992023/5000000000 : ℝ)*X 1 2+(4181834677/10000000000 : ℝ)*X 2 0+(4409985297/10000000000 : ℝ)*X 2 1+(2204992023/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2159698429/10000000000 : ℝ)*X 0 0+(517773413/1000000000 : ℝ)*X 0 1+(5404715217/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((659379803/1250000000 : ℝ)*X 1 0+(-507505207/2500000000 : ℝ)*X 1 1+(270235793/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275038581/10000000000 : ℝ)*X 2 0+(5404715651/10000000000 : ℝ)*X 2 1+(-2030020901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1128137949/2500000000 : ℝ)*X 0 0+(530549081/1250000000 : ℝ)*X 0 1+(4244392951/10000000000 : ℝ)*X 0 2+(1128137949/2500000000 : ℝ)*X 1 0+(530549081/1250000000 : ℝ)*X 1 1+(4244392951/10000000000 : ℝ)*X 1 2+(1128137949/2500000000 : ℝ)*X 2 0+(530549081/1250000000 : ℝ)*X 2 1+(4244392951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-981343421/5000000000 : ℝ)*X 0 0+(2737610057/5000000000 : ℝ)*X 0 1+(5253457817/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5381363073/10000000000 : ℝ)*X 1 0+(-2090590909/10000000000 : ℝ)*X 1 1+(5253457943/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((672670483/1250000000 : ℝ)*X 2 0+(1313364289/2500000000 : ℝ)*X 2 1+(-130661931/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2077634411/5000000000 : ℝ)*X 0 0+(2211514327/5000000000 : ℝ)*X 0 1+(442302873/1000000000 : ℝ)*X 0 2+(2077634411/5000000000 : ℝ)*X 1 0+(2211514327/5000000000 : ℝ)*X 1 1+(442302873/1000000000 : ℝ)*X 1 2+(2077634411/5000000000 : ℝ)*X 2 0+(2211514327/5000000000 : ℝ)*X 2 1+(442302873/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1324_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62849/100000 : ℝ) ≤ (-281786443081719394399188916792503/448375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (145668349/100000000000000 : ℝ)*(lower0) + (42876389/100000000000000 : ℝ)*(upper1) + (45712891/50000000000000 : ℝ)*(lower2) + (2900440872706157/100000000000000 : ℝ)*(major0) + (2900440872706157/100000000000000 : ℝ)*(major1) + (1450220436353079/50000000000000 : ℝ)*(major2) + (5795163659/50000000000000 : ℝ)*(sp2) + (492331387587289/12500000000000 : ℝ)*(sp4) + (3938584753173619/100000000000000 : ℝ)*(sp5) + (3938657780794931/100000000000000 : ℝ)*(sp6) + (188314467991677/10000000000000 : ℝ)*(sp7) + (18270423937/100000000000000 : ℝ)*(sp8) + (8461794863/10000000000000 : ℝ)*(sp13) + (3282475909/20000000000000 : ℝ)*(sp15) + (470790273074079/25000000000000 : ℝ)*(f.failure) + (492333671390281/12500000000000 : ℝ)*(f.sum) + (36875956296813/7174000000000000000000000000 : ℝ)*base65 + (21998288839824420363/3587000000000000000000000000000000 : ℝ)*base68 + (7497159861458224639/1793500000000000000000000000000000 : ℝ)*base69 + (3421058965966420363/3587000000000000000000000000000000 : ℝ)*base72 + (20026968189347/7174000000000000000000000000 : ℝ)*base73 + (9496377546932224639/1793500000000000000000000000000000 : ℝ)*base75 + (193637151498120363/3587000000000000000000000000000000 : ℝ)*base78 + (140263522914781120363/3587000000000000000000000000000000 : ℝ)*base80 + (60400031008569/17935000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3866971/625000000000000000000 : ℝ)*base89 + (3866971/625000000000000000000 : ℝ)*base91 + (2383029/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (29453/50000 : ℝ) ≤ (31074430843158709707036060792327/52750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29664079/50000000000000 : ℝ)*(upper0) + (42630673/100000000000000 : ℝ)*(lower1) + (166236793/100000000000000 : ℝ)*(upper4) + (2968532612317511/100000000000000 : ℝ)*(major0) + (2968532612317511/100000000000000 : ℝ)*(major1) + (371066576539689/12500000000000 : ℝ)*(major2) + (997514153412611/25000000000000 : ℝ)*(sp0) + (199502271556401/5000000000000 : ℝ)*(sp1) + (798009044596633/20000000000000 : ℝ)*(sp2) + (1927368044039469/100000000000000 : ℝ)*(sp3) + (2535525331/20000000000000 : ℝ)*(sp5) + (12885771511/100000000000000 : ℝ)*(sp6) + (2780628751/100000000000000 : ℝ)*(sp7) + (186888029/12500000000000 : ℝ)*(sp8) + (96368541233411/5000000000000 : ℝ)*(f.failure) + (997514527188669/25000000000000 : ℝ)*(f.sum) + (239715893689391/35870000000000000000000000000 : ℝ)*base65 + (4572239949034683551/3587000000000000000000000000000000 : ℝ)*base67 + (1605623576598194149/448375000000000000000000000000000 : ℝ)*base69 + (39274733217174683551/3587000000000000000000000000000000 : ℝ)*base71 + (953509157800171/35870000000000000000000000000 : ℝ)*base73 + (8829156989129069149/448375000000000000000000000000000 : ℝ)*base75 + (15649185913096983551/3587000000000000000000000000000000 : ℝ)*base77 + (178929246656358983551/3587000000000000000000000000000000 : ℝ)*base79 + (7777571091307/1120937500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1098961/125000000000000000000 : ℝ)*base90 + (1098961/125000000000000000000 : ℝ)*base92 + (2348961/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (9981/12500 : ℝ) ≤ (358031528272038115791169329304083/448375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56472837/100000000000000 : ℝ)*(lower1) + (4708413/5000000000000 : ℝ)*(lower3) + (1948417/2500000000000 : ℝ)*(lower5) + (1640696159382921/50000000000000 : ℝ)*(major0) + (1640696159382921/50000000000000 : ℝ)*(major1) + (3281392318765843/100000000000000 : ℝ)*(major2) + (1992390327/12500000000000 : ℝ)*(sp0) + (9790987809/4000000000000 : ℝ)*(sp1) + (2728961493/1562500000000 : ℝ)*(sp2) + (13291747543/20000000000000 : ℝ)*(sp3) + (275353210049829/6250000000000 : ℝ)*(sp8) + (275338907826541/6250000000000 : ℝ)*(sp9) + (550686580798041/12500000000000 : ℝ)*(sp10) + (426086781617811/20000000000000 : ℝ)*(sp11) + (213050036682677/10000000000000 : ℝ)*(f.failure) + (110141682497997/2500000000000 : ℝ)*(f.sum) + (3169233117887/7174000000000000000000000000 : ℝ)*base65 + (13724271962899448639/1793500000000000000000000000000000 : ℝ)*base68 + (51132243555850027637/3587000000000000000000000000000000 : ℝ)*base70 + (21928291190764448639/1793500000000000000000000000000000 : ℝ)*base72 + (4195255765389/7174000000000000000000000000 : ℝ)*base74 + (15346339897676972363/3587000000000000000000000000000000 : ℝ)*base75 + (15123411667015298639/1793500000000000000000000000000000 : ℝ)*base78 + (9012458943476298639/1793500000000000000000000000000000 : ℝ)*base80 + (26479996676403/560468750000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2068473/250000000000000000000 : ℝ)*base89 + (2068473/250000000000000000000 : ℝ)*base91 + (431527/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-42141/50000 : ℝ) ≤ (-1511544634373620790220116340733197/1793500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (511357/6250000000000 : ℝ)*(lower0) + (61252851/50000000000000 : ℝ)*(lower1) + (7642431/4000000000000 : ℝ)*(lower2) + (165882815687689/5000000000000 : ℝ)*(major0) + (165882815687689/5000000000000 : ℝ)*(major1) + (3317656313753781/100000000000000 : ℝ)*(major2) + (27670550671/100000000000000 : ℝ)*(sp0) + (201462413121/50000000000000 : ℝ)*(sp5) + (154035422131/25000000000000 : ℝ)*(sp6) + (18300309363/25000000000000 : ℝ)*(sp7) + (2254666291170753/50000000000000 : ℝ)*(sp12) + (281809833004121/6250000000000 : ℝ)*(sp13) + (2254372055601827/50000000000000 : ℝ)*(sp14) + (1076986093838609/50000000000000 : ℝ)*(sp15) + (215404538891467/10000000000000 : ℝ)*(f.failure) + (2254680126446089/50000000000000 : ℝ)*(f.sum) + (259326498395933/35870000000000000000000000000 : ℝ)*base66 + (230913216693934649/179350000000000000000000000000000 : ℝ)*base67 + (1730833816359437379/3587000000000000000000000000000000 : ℝ)*base70 + (2079450992457365351/179350000000000000000000000000000 : ℝ)*base72 + (58532685059943/35870000000000000000000000000 : ℝ)*base74 + (61360898023429437379/3587000000000000000000000000000000 : ℝ)*base76 + (2130340841595250351/179350000000000000000000000000000 : ℝ)*base78 + (1738422711412650351/179350000000000000000000000000000 : ℝ)*base80 + (3963577793/717400000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (3370183/250000000000000000000 : ℝ)*base89 + (3370183/250000000000000000000 : ℝ)*base91 + (870183/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1324_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38504949/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62849/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29453/50000 : ℝ) else (9981/12500 : ℝ) ≤ X j i ∧ X j i ≤ (42141/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1324_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1324_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38504949/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62849/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29453/50000 : ℝ) else (9981/12500 : ℝ) ≤ X j i ∧ X j i ≤ (42141/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1324_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4283/1024 : ℝ) ≤ p) (hpb : p ≤ (1071/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38504949/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62849/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29453/50000 : ℝ) else (9981/12500 : ℝ) ≤ X j i ∧ X j i ≤ (42141/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1324_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

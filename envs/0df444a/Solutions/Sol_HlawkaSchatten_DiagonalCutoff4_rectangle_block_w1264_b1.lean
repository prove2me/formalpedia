-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1264_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:56:14.4185+00:00
-- url     : https://prove2.me/submissions/e5266d74-b3aa-4b14-9fa7-b20c8ae4534e

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
theorem support_rectangle_w1264_s3_0 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-131700421/625000000 : ℝ)*x 0 + (2708878951/5000000000 : ℝ)*x 1 + (2621140319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131700421/625000000 : ℝ)^8457 ≤ (12811422006137/100000000000000 : ℝ)^6409 := by
    have hnat : (131700421 : ℕ)^8457*100000000000000^6409 ≤ 12811422006137^6409*625000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131700421 625000000 12811422006137 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708878951/5000000000 : ℝ)^8457 ≤ (22270577644077/50000000000000 : ℝ)^6409 := by
    have hnat : (2708878951 : ℕ)^8457*50000000000000^6409 ≤ 22270577644077^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708878951 5000000000 22270577644077 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621140319/5000000000 : ℝ)^8457 ≤ (42647422681307/100000000000000 : ℝ)^6409 := by
    have hnat : (2621140319 : ℕ)^8457*100000000000000^6409 ≤ 42647422681307^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621140319 5000000000 42647422681307 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-131700421/625000000 : ℝ), (2708878951/5000000000 : ℝ), (2621140319/5000000000 : ℝ)] ![(12811422006137/100000000000000 : ℝ), (22270577644077/50000000000000 : ℝ), (42647422681307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-131700421/625000000 : ℝ)|^8457 ≤ (12811422006137/100000000000000 : ℝ)^6409
        have hw : |(-131700421/625000000 : ℝ)|=(131700421/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708878951/5000000000 : ℝ)|^8457 ≤ (22270577644077/50000000000000 : ℝ)^6409
        have hw : |(2708878951/5000000000 : ℝ)|=(2708878951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621140319/5000000000 : ℝ)|^8457 ≤ (42647422681307/100000000000000 : ℝ)^6409
        have hw : |(2621140319/5000000000 : ℝ)|=(2621140319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s3_1 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2675503779/5000000000 : ℝ)*x 0 + (-1098344539/5000000000 : ℝ)*x 1 + (5242280749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675503779/5000000000 : ℝ)^8457 ≤ (21909223299191/50000000000000 : ℝ)^6409 := by
    have hnat : (2675503779 : ℕ)^8457*50000000000000^6409 ≤ 21909223299191^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675503779 5000000000 21909223299191 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098344539/5000000000 : ℝ)^8457 ≤ (3383532376927/25000000000000 : ℝ)^6409 := by
    have hnat : (1098344539 : ℕ)^8457*25000000000000^6409 ≤ 3383532376927^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098344539 5000000000 3383532376927 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242280749/10000000000 : ℝ)^8457 ≤ (21323711936441/50000000000000 : ℝ)^6409 := by
    have hnat : (5242280749 : ℕ)^8457*50000000000000^6409 ≤ 21323711936441^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242280749 10000000000 21323711936441 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675503779/5000000000 : ℝ), (-1098344539/5000000000 : ℝ), (5242280749/10000000000 : ℝ)] ![(21909223299191/50000000000000 : ℝ), (3383532376927/25000000000000 : ℝ), (21323711936441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675503779/5000000000 : ℝ)|^8457 ≤ (21909223299191/50000000000000 : ℝ)^6409
        have hw : |(2675503779/5000000000 : ℝ)|=(2675503779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1098344539/5000000000 : ℝ)|^8457 ≤ (3383532376927/25000000000000 : ℝ)^6409
        have hw : |(-1098344539/5000000000 : ℝ)|=(1098344539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242280749/10000000000 : ℝ)|^8457 ≤ (21323711936441/50000000000000 : ℝ)^6409
        have hw : |(5242280749/10000000000 : ℝ)|=(5242280749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s3_2 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2675503771/5000000000 : ℝ)*x 0 + (655285153/1250000000 : ℝ)*x 1 + (-2196688473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675503771/5000000000 : ℝ)^8457 ≤ (43818446425493/100000000000000 : ℝ)^6409 := by
    have hnat : (2675503771 : ℕ)^8457*100000000000000^6409 ≤ 43818446425493^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675503771 5000000000 43818446425493 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655285153/1250000000 : ℝ)^8457 ≤ (42647428971967/100000000000000 : ℝ)^6409 := by
    have hnat : (655285153 : ℕ)^8457*100000000000000^6409 ≤ 42647428971967^6409*1250000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655285153 1250000000 42647428971967 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2196688473/10000000000 : ℝ)^8457 ≤ (13534124589089/100000000000000 : ℝ)^6409 := by
    have hnat : (2196688473 : ℕ)^8457*100000000000000^6409 ≤ 13534124589089^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196688473 10000000000 13534124589089 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675503771/5000000000 : ℝ), (655285153/1250000000 : ℝ), (-2196688473/10000000000 : ℝ)] ![(43818446425493/100000000000000 : ℝ), (42647428971967/100000000000000 : ℝ), (13534124589089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675503771/5000000000 : ℝ)|^8457 ≤ (43818446425493/100000000000000 : ℝ)^6409
        have hw : |(2675503771/5000000000 : ℝ)|=(2675503771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655285153/1250000000 : ℝ)|^8457 ≤ (42647428971967/100000000000000 : ℝ)^6409
        have hw : |(655285153/1250000000 : ℝ)|=(655285153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2196688473/10000000000 : ℝ)|^8457 ≤ (13534124589089/100000000000000 : ℝ)^6409
        have hw : |(-2196688473/10000000000 : ℝ)|=(2196688473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s3_3 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1086542473/2500000000 : ℝ)*x 0 + (834196481/2000000000 : ℝ)*x 1 + (4528461339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086542473/2500000000 : ℝ)^8457 ≤ (33301474693983/100000000000000 : ℝ)^6409 := by
    have hnat : (1086542473 : ℕ)^8457*100000000000000^6409 ≤ 33301474693983^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086542473 2500000000 33301474693983 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (834196481/2000000000 : ℝ)^8457 ≤ (6308342735351/20000000000000 : ℝ)^6409 := by
    have hnat : (834196481 : ℕ)^8457*20000000000000^6409 ≤ 6308342735351^6409*2000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834196481 2000000000 6308342735351 20000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4528461339/10000000000 : ℝ)^8457 ≤ (3515681160801/10000000000000 : ℝ)^6409 := by
    have hnat : (4528461339 : ℕ)^8457*10000000000000^6409 ≤ 3515681160801^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4528461339 10000000000 3515681160801 10000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086542473/2500000000 : ℝ), (834196481/2000000000 : ℝ), (4528461339/10000000000 : ℝ)] ![(33301474693983/100000000000000 : ℝ), (6308342735351/20000000000000 : ℝ), (3515681160801/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086542473/2500000000 : ℝ)|^8457 ≤ (33301474693983/100000000000000 : ℝ)^6409
        have hw : |(1086542473/2500000000 : ℝ)|=(1086542473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(834196481/2000000000 : ℝ)|^8457 ≤ (6308342735351/20000000000000 : ℝ)^6409
        have hw : |(834196481/2000000000 : ℝ)|=(834196481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4528461339/10000000000 : ℝ)|^8457 ≤ (3515681160801/10000000000000 : ℝ)^6409
        have hw : |(4528461339/10000000000 : ℝ)|=(4528461339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s3_4 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2107220669/10000000000 : ℝ)*x 0 + (1310727447/2500000000 : ℝ)*x 1 + (5417125011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2107220669/10000000000 : ℝ)^8457 ≤ (12811533785427/100000000000000 : ℝ)^6409 := by
    have hnat : (2107220669 : ℕ)^8457*100000000000000^6409 ≤ 12811533785427^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107220669 10000000000 12811533785427 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310727447/2500000000 : ℝ)^8457 ≤ (42654176682163/100000000000000 : ℝ)^6409 := by
    have hnat : (1310727447 : ℕ)^8457*100000000000000^6409 ≤ 42654176682163^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310727447 2500000000 42654176682163 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417125011/10000000000 : ℝ)^8457 ≤ (22267144762989/50000000000000 : ℝ)^6409 := by
    have hnat : (5417125011 : ℕ)^8457*50000000000000^6409 ≤ 22267144762989^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417125011 10000000000 22267144762989 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2107220669/10000000000 : ℝ), (1310727447/2500000000 : ℝ), (5417125011/10000000000 : ℝ)] ![(12811533785427/100000000000000 : ℝ), (42654176682163/100000000000000 : ℝ), (22267144762989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2107220669/10000000000 : ℝ)|^8457 ≤ (12811533785427/100000000000000 : ℝ)^6409
        have hw : |(-2107220669/10000000000 : ℝ)|=(2107220669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310727447/2500000000 : ℝ)|^8457 ≤ (42654176682163/100000000000000 : ℝ)^6409
        have hw : |(1310727447/2500000000 : ℝ)|=(1310727447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417125011/10000000000 : ℝ)|^8457 ≤ (22267144762989/50000000000000 : ℝ)^6409
        have hw : |(5417125011/10000000000 : ℝ)|=(5417125011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s3_5 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2653087169/5000000000 : ℝ)*x 0 + (-50546103/250000000 : ℝ)*x 1 + (5417124849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2653087169/5000000000 : ℝ)^8457 ≤ (43334648088519/100000000000000 : ℝ)^6409 := by
    have hnat : (2653087169 : ℕ)^8457*100000000000000^6409 ≤ 43334648088519^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2653087169 5000000000 43334648088519 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50546103/250000000 : ℝ)^8457 ≤ (12131064123331/100000000000000 : ℝ)^6409 := by
    have hnat : (50546103 : ℕ)^8457*100000000000000^6409 ≤ 12131064123331^6409*250000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50546103 250000000 12131064123331 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417124849/10000000000 : ℝ)^8457 ≤ (44534287768593/100000000000000 : ℝ)^6409 := by
    have hnat : (5417124849 : ℕ)^8457*100000000000000^6409 ≤ 44534287768593^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417124849 10000000000 44534287768593 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2653087169/5000000000 : ℝ), (-50546103/250000000 : ℝ), (5417124849/10000000000 : ℝ)] ![(43334648088519/100000000000000 : ℝ), (12131064123331/100000000000000 : ℝ), (44534287768593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2653087169/5000000000 : ℝ)|^8457 ≤ (43334648088519/100000000000000 : ℝ)^6409
        have hw : |(2653087169/5000000000 : ℝ)|=(2653087169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-50546103/250000000 : ℝ)|^8457 ≤ (12131064123331/100000000000000 : ℝ)^6409
        have hw : |(-50546103/250000000 : ℝ)|=(50546103/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417124849/10000000000 : ℝ)|^8457 ≤ (44534287768593/100000000000000 : ℝ)^6409
        have hw : |(5417124849/10000000000 : ℝ)|=(5417124849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s3_6 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1326543417/2500000000 : ℝ)*x 0 + (5417125293/10000000000 : ℝ)*x 1 + (-80873777/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326543417/2500000000 : ℝ)^8457 ≤ (4333464086823/10000000000000 : ℝ)^6409 := by
    have hnat : (1326543417 : ℕ)^8457*10000000000000^6409 ≤ 4333464086823^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326543417 2500000000 4333464086823 10000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417125293/10000000000 : ℝ)^8457 ≤ (5566786573141/12500000000000 : ℝ)^6409 := by
    have hnat : (5417125293 : ℕ)^8457*12500000000000^6409 ≤ 5566786573141^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417125293 10000000000 5566786573141 12500000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80873777/400000000 : ℝ)^8457 ≤ (12131066538109/100000000000000 : ℝ)^6409 := by
    have hnat : (80873777 : ℕ)^8457*100000000000000^6409 ≤ 12131066538109^6409*400000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80873777 400000000 12131066538109 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326543417/2500000000 : ℝ), (5417125293/10000000000 : ℝ), (-80873777/400000000 : ℝ)] ![(4333464086823/10000000000000 : ℝ), (5566786573141/12500000000000 : ℝ), (12131066538109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326543417/2500000000 : ℝ)|^8457 ≤ (4333464086823/10000000000000 : ℝ)^6409
        have hw : |(1326543417/2500000000 : ℝ)|=(1326543417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417125293/10000000000 : ℝ)|^8457 ≤ (5566786573141/12500000000000 : ℝ)^6409
        have hw : |(5417125293/10000000000 : ℝ)|=(5417125293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-80873777/400000000 : ℝ)|^8457 ≤ (12131066538109/100000000000000 : ℝ)^6409
        have hw : |(-80873777/400000000 : ℝ)|=(80873777/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s3_7 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2173098813/5000000000 : ℝ)*x 0 + (905435773/2000000000 : ℝ)*x 1 + (2086135401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173098813/5000000000 : ℝ)^8457 ≤ (2081359694091/6250000000000 : ℝ)^6409 := by
    have hnat : (2173098813 : ℕ)^8457*6250000000000^6409 ≤ 2081359694091^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173098813 5000000000 2081359694091 6250000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (905435773/2000000000 : ℝ)^8457 ≤ (7028734815167/20000000000000 : ℝ)^6409 := by
    have hnat : (905435773 : ℕ)^8457*20000000000000^6409 ≤ 7028734815167^6409*2000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905435773 2000000000 7028734815167 20000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086135401/5000000000 : ℝ)^8457 ≤ (7888642702341/25000000000000 : ℝ)^6409 := by
    have hnat : (2086135401 : ℕ)^8457*25000000000000^6409 ≤ 7888642702341^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086135401 5000000000 7888642702341 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173098813/5000000000 : ℝ), (905435773/2000000000 : ℝ), (2086135401/5000000000 : ℝ)] ![(2081359694091/6250000000000 : ℝ), (7028734815167/20000000000000 : ℝ), (7888642702341/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173098813/5000000000 : ℝ)|^8457 ≤ (2081359694091/6250000000000 : ℝ)^6409
        have hw : |(2173098813/5000000000 : ℝ)|=(2173098813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(905435773/2000000000 : ℝ)|^8457 ≤ (7028734815167/20000000000000 : ℝ)^6409
        have hw : |(905435773/2000000000 : ℝ)|=(905435773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086135401/5000000000 : ℝ)|^8457 ≤ (7888642702341/25000000000000 : ℝ)^6409
        have hw : |(2086135401/5000000000 : ℝ)|=(2086135401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1264_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8083/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2397/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10967/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14681/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8083/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2397/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8083/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2397/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8083/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2397/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8083/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2397/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8083/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2397/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8083/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2397/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2397/25000 : ℝ) ^ (1057/256 : ℝ) ≤ (6246697560787747/100000000000000000000 : ℝ) := by
    have hpowers : (2397/25000 : ℝ)^1057 ≤ (6246697560787747/100000000000000000000 : ℝ)^256 := by
      have hnat : (2397 : ℕ)^1057*100000000000000000000^256 ≤ 6246697560787747^256*25000^1057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2397 25000 6246697560787747 100000000000000000000 1057 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2397/25000 : ℝ)) (X := (6246697560787747/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hpowhi : (8083/50000 : ℝ) ^ (1057/256 : ℝ) ≤ (54000057649023499/100000000000000000000 : ℝ) := by
    have hpowers : (8083/50000 : ℝ)^1057 ≤ (54000057649023499/100000000000000000000 : ℝ)^256 := by
      have hnat : (8083 : ℕ)^1057*100000000000000000000^256 ≤ 54000057649023499^256*50000^1057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8083 50000 54000057649023499 100000000000000000000 1057 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8083/50000 : ℝ)) (X := (54000057649023499/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006246697560787747/50000000000000000000 : ℝ) ≤ (2500075642331157/2500000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (50006246697560787747/50000000000000000000 : ℝ)^256 ≤ (2500075642331157/2500000000000000 : ℝ)^1057 := by
      have hnat : (50006246697560787747 : ℕ)^256*2500000000000000^1057 ≤ 2500075642331157^1057*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006246697560787747 50000000000000000000 2500075642331157 2500000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500075642331157/2500000000000000 : ℝ)) (X := (50006246697560787747/50000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50030123377604905623/50000000000000000000 : ℝ) ≤ (10001458812661213/10000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (50030123377604905623/50000000000000000000 : ℝ)^256 ≤ (10001458812661213/10000000000000000 : ℝ)^1057 := by
      have hnat : (50030123377604905623 : ℕ)^256*10000000000000000^1057 ≤ 10001458812661213^1057*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030123377604905623 50000000000000000000 10001458812661213 10000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001458812661213/10000000000000000 : ℝ)) (X := (50030123377604905623/50000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50054000057649023499/50000000000000000000 : ℝ) ≤ (5001307527998899/5000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (50054000057649023499/50000000000000000000 : ℝ)^256 ≤ (5001307527998899/5000000000000000 : ℝ)^1057 := by
      have hnat : (50054000057649023499 : ℕ)^256*5000000000000000^1057 ≤ 5001307527998899^1057*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50054000057649023499 50000000000000000000 5001307527998899 5000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001307527998899/5000000000000000 : ℝ)) (X := (50054000057649023499/50000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6246697560787747/100000000000000000000 : ℝ) ≤ ((1027497159043672641/1027812500000000000 : ℝ)+2*(231248667317/131560000000000 : ℝ)*(2397/25000 : ℝ))^(1057/256 : ℝ) := by
    rw [show (1027497159043672641/1027812500000000000 : ℝ)+2*(231248667317/131560000000000 : ℝ)*(2397/25000 : ℝ)=(2500075642331157/2500000000000000 : ℝ) by norm_num, show 1+2*(6246697560787747/100000000000000000000 : ℝ)=(50006246697560787747/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(54000057649023499/100000000000000000000 : ℝ)+(6246697560787747/100000000000000000000 : ℝ) ≤ ((1027497159043672641/1027812500000000000 : ℝ)+(231248667317/131560000000000 : ℝ)*((8083/50000 : ℝ)+(2397/25000 : ℝ)))^(1057/256 : ℝ) := by
    rw [show (1027497159043672641/1027812500000000000 : ℝ)+(231248667317/131560000000000 : ℝ)*((8083/50000 : ℝ)+(2397/25000 : ℝ))=(10001458812661213/10000000000000000 : ℝ) by norm_num, show 1+(54000057649023499/100000000000000000000 : ℝ)+(6246697560787747/100000000000000000000 : ℝ)=(50030123377604905623/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(54000057649023499/100000000000000000000 : ℝ) ≤ ((1027497159043672641/1027812500000000000 : ℝ)+2*(231248667317/131560000000000 : ℝ)*(8083/50000 : ℝ))^(1057/256 : ℝ) := by
    rw [show (1027497159043672641/1027812500000000000 : ℝ)+2*(231248667317/131560000000000 : ℝ)*(8083/50000 : ℝ)=(5001307527998899/5000000000000000 : ℝ) by norm_num, show 1+2*(54000057649023499/100000000000000000000 : ℝ)=(50054000057649023499/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1027497159043672641/1027812500000000000 : ℝ)*(X 1 0+X 2 0)+(231248667317/131560000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (2397/25000 : ℝ)) (hi := (8083/50000 : ℝ)) (c := (1027497159043672641/1027812500000000000 : ℝ)) (alpha := (231248667317/131560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1027497159043672641/1027812500000000000 : ℝ)*(X 0 1+X 2 1)+(231248667317/131560000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (2397/25000 : ℝ)) (hi := (8083/50000 : ℝ)) (c := (1027497159043672641/1027812500000000000 : ℝ)) (alpha := (231248667317/131560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1027497159043672641/1027812500000000000 : ℝ)*(X 0 2+X 1 2)+(231248667317/131560000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (2397/25000 : ℝ)) (hi := (8083/50000 : ℝ)) (c := (1027497159043672641/1027812500000000000 : ℝ)) (alpha := (231248667317/131560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-131700421/625000000 : ℝ)*X 0 0+(2708878951/5000000000 : ℝ)*X 0 1+(2621140319/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675503779/5000000000 : ℝ)*X 1 0+(-1098344539/5000000000 : ℝ)*X 1 1+(5242280749/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675503771/5000000000 : ℝ)*X 2 0+(655285153/1250000000 : ℝ)*X 2 1+(-2196688473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1086542473/2500000000 : ℝ)*X 0 0+(834196481/2000000000 : ℝ)*X 0 1+(4528461339/10000000000 : ℝ)*X 0 2+(1086542473/2500000000 : ℝ)*X 1 0+(834196481/2000000000 : ℝ)*X 1 1+(4528461339/10000000000 : ℝ)*X 1 2+(1086542473/2500000000 : ℝ)*X 2 0+(834196481/2000000000 : ℝ)*X 2 1+(4528461339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2107220669/10000000000 : ℝ)*X 0 0+(1310727447/2500000000 : ℝ)*X 0 1+(5417125011/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2653087169/5000000000 : ℝ)*X 1 0+(-50546103/250000000 : ℝ)*X 1 1+(5417124849/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326543417/2500000000 : ℝ)*X 2 0+(5417125293/10000000000 : ℝ)*X 2 1+(-80873777/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2173098813/5000000000 : ℝ)*X 0 0+(905435773/2000000000 : ℝ)*X 0 1+(2086135401/5000000000 : ℝ)*X 0 2+(2173098813/5000000000 : ℝ)*X 1 0+(905435773/2000000000 : ℝ)*X 1 1+(2086135401/5000000000 : ℝ)*X 1 2+(2173098813/5000000000 : ℝ)*X 2 0+(905435773/2000000000 : ℝ)*X 2 1+(2086135401/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (112687787773186383281662029/25695312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (11240657/6250000000000 : ℝ)*(base19) + (93649941/50000000000000 : ℝ)*(lower2) + (104463117/100000000000000 : ℝ)*(lower3) + (23849947/50000000000000 : ℝ)*(lower4) + (265505153258531/6250000000000 : ℝ)*(major0) + (265505153258531/6250000000000 : ℝ)*(major1) + (265505153258531/6250000000000 : ℝ)*(major2) + (1424690726617019/25000000000000 : ℝ)*(sp0) + (5698777213053489/100000000000000 : ℝ)*(sp1) + (113975781969773/2000000000000 : ℝ)*(sp2) + (1398685843387/50000000000 : ℝ)*(sp3) + (13096010287/50000000000000 : ℝ)*(sp4) + (11705584649/100000000000000 : ℝ)*(sp5) + (993206429/25000000000000 : ℝ)*(sp7) + (699343914899929/25000000000000 : ℝ)*(f.failure) + (113975781969773/2000000000000 : ℝ)*(f.sum) + (804652864343/328900000000000000000000000 : ℝ)*base65 + (6344071255233501/1605957031250000000000000000000 : ℝ)*base68 + (855106324907891/25695312500000000000000000000000 : ℝ)*base70 + (7459026801085117/12847656250000000000000000000000 : ℝ)*base71 + (3013552895143/1644500000000000000000000000 : ℝ)*base74 + (32741382152564141/25695312500000000000000000000000 : ℝ)*base76 + (17141933410267373/3211914062500000000000000000000 : ℝ)*base77 + (32704990093313/802978515625000000000000000000 : ℝ)*base80 + (5538762328309/1644500000000000000000000000 : ℝ)*base81 + (6671027/2500000000000000000000 : ℝ)*base89 + (6671027/2500000000000000000000 : ℝ)*base91 + (6671027/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3446476984453549544035947/1868750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2309295163/100000000000000 : ℝ)*(base19) + (1458893837/100000000000000 : ℝ)*(base23) + (35457309/100000000000000 : ℝ)*(lower4) + (371207463/100000000000000 : ℝ)*(upper5) + (855765720301801/20000000000000 : ℝ)*(major0) + (855765720301801/20000000000000 : ℝ)*(major1) + (855765720301801/20000000000000 : ℝ)*(major2) + (72764029/6250000000000 : ℝ)*(sp0) + (56375272757/100000000000000 : ℝ)*(sp1) + (6719725947/20000000000000 : ℝ)*(sp2) + (5740033881626119/100000000000000 : ℝ)*(sp4) + (5739976361282663/100000000000000 : ℝ)*(sp5) + (5739999988327011/100000000000000 : ℝ)*(sp6) + (1408811047845899/50000000000000 : ℝ)*(sp7) + (1408811047845899/50000000000000 : ℝ)*(f.failure) + (5740035045850583/100000000000000 : ℝ)*(f.sum) + (5938471542689/6578000000000000000000000000 : ℝ)*base66 + (335219620895718993/41112500000000000000000000000000 : ℝ)*base68 + (450739816116506493/41112500000000000000000000000000 : ℝ)*base70 + (82896375627506007/41112500000000000000000000000000 : ℝ)*base71 + (44029572680207/6578000000000000000000000000 : ℝ)*base74 + (878168287938643993/41112500000000000000000000000000 : ℝ)*base76 + (155490682235018993/41112500000000000000000000000000 : ℝ)*base78 + (572131124204556493/41112500000000000000000000000000 : ℝ)*base80 + (17766013085363/6578000000000000000000000000 : ℝ)*base82 + (63482137/5000000000000000000000 : ℝ)*base89 + (63482137/5000000000000000000000 : ℝ)*base91 + (63482137/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1264_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8083/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2397/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10967/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14681/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1264_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1264_s4_0 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1054682583/5000000000 : ℝ)*x 0 + (674577233/1250000000 : ℝ)*x 1 + (5262005751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054682583/5000000000 : ℝ)^8457 ≤ (12828741104259/100000000000000 : ℝ)^6409 := by
    have hnat : (1054682583 : ℕ)^8457*100000000000000^6409 ≤ 12828741104259^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054682583 5000000000 12828741104259 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674577233/1250000000 : ℝ)^8457 ≤ (8862392323103/20000000000000 : ℝ)^6409 := by
    have hnat : (674577233 : ℕ)^8457*20000000000000^6409 ≤ 8862392323103^6409*1250000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674577233 1250000000 8862392323103 20000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262005751/10000000000 : ℝ)^8457 ≤ (42859297270653/100000000000000 : ℝ)^6409 := by
    have hnat : (5262005751 : ℕ)^8457*100000000000000^6409 ≤ 42859297270653^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262005751 10000000000 42859297270653 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1054682583/5000000000 : ℝ), (674577233/1250000000 : ℝ), (5262005751/10000000000 : ℝ)] ![(12828741104259/100000000000000 : ℝ), (8862392323103/20000000000000 : ℝ), (42859297270653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1054682583/5000000000 : ℝ)|^8457 ≤ (12828741104259/100000000000000 : ℝ)^6409
        have hw : |(-1054682583/5000000000 : ℝ)|=(1054682583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674577233/1250000000 : ℝ)|^8457 ≤ (8862392323103/20000000000000 : ℝ)^6409
        have hw : |(674577233/1250000000 : ℝ)|=(674577233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262005751/10000000000 : ℝ)|^8457 ≤ (42859297270653/100000000000000 : ℝ)^6409
        have hw : |(5262005751/10000000000 : ℝ)|=(5262005751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s4_1 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069133583/2000000000 : ℝ)*x 0 + (-2177697867/10000000000 : ℝ)*x 1 + (5262005671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069133583/2000000000 : ℝ)^8457 ≤ (43760757941149/100000000000000 : ℝ)^6409 := by
    have hnat : (1069133583 : ℕ)^8457*100000000000000^6409 ≤ 43760757941149^6409*2000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069133583 2000000000 43760757941149 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2177697867/10000000000 : ℝ)^8457 ≤ (13379945631637/100000000000000 : ℝ)^6409 := by
    have hnat : (2177697867 : ℕ)^8457*100000000000000^6409 ≤ 13379945631637^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177697867 10000000000 13379945631637 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262005671/10000000000 : ℝ)^8457 ≤ (10714824102707/25000000000000 : ℝ)^6409 := by
    have hnat : (5262005671 : ℕ)^8457*25000000000000^6409 ≤ 10714824102707^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262005671 10000000000 10714824102707 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069133583/2000000000 : ℝ), (-2177697867/10000000000 : ℝ), (5262005671/10000000000 : ℝ)] ![(43760757941149/100000000000000 : ℝ), (13379945631637/100000000000000 : ℝ), (10714824102707/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069133583/2000000000 : ℝ)|^8457 ≤ (43760757941149/100000000000000 : ℝ)^6409
        have hw : |(1069133583/2000000000 : ℝ)|=(1069133583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2177697867/10000000000 : ℝ)|^8457 ≤ (13379945631637/100000000000000 : ℝ)^6409
        have hw : |(-2177697867/10000000000 : ℝ)|=(2177697867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262005671/10000000000 : ℝ)|^8457 ≤ (10714824102707/25000000000000 : ℝ)^6409
        have hw : |(5262005671/10000000000 : ℝ)|=(5262005671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s4_2 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534566801/1000000000 : ℝ)*x 0 + (5262005539/10000000000 : ℝ)*x 1 + (-544424479/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534566801/1000000000 : ℝ)^8457 ≤ (875215179347/2000000000000 : ℝ)^6409 := by
    have hnat : (534566801 : ℕ)^8457*2000000000000^6409 ≤ 875215179347^6409*1000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534566801 1000000000 875215179347 2000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262005539/10000000000 : ℝ)^8457 ≤ (21429647496059/50000000000000 : ℝ)^6409 := by
    have hnat : (5262005539 : ℕ)^8457*50000000000000^6409 ≤ 21429647496059^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262005539 10000000000 21429647496059 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544424479/2500000000 : ℝ)^8457 ≤ (133799460289/1000000000000 : ℝ)^6409 := by
    have hnat : (544424479 : ℕ)^8457*1000000000000^6409 ≤ 133799460289^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544424479 2500000000 133799460289 1000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534566801/1000000000 : ℝ), (5262005539/10000000000 : ℝ), (-544424479/2500000000 : ℝ)] ![(875215179347/2000000000000 : ℝ), (21429647496059/50000000000000 : ℝ), (133799460289/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534566801/1000000000 : ℝ)|^8457 ≤ (875215179347/2000000000000 : ℝ)^6409
        have hw : |(534566801/1000000000 : ℝ)|=(534566801/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262005539/10000000000 : ℝ)|^8457 ≤ (21429647496059/50000000000000 : ℝ)^6409
        have hw : |(5262005539/10000000000 : ℝ)|=(5262005539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-544424479/2500000000 : ℝ)|^8457 ≤ (133799460289/1000000000000 : ℝ)^6409
        have hw : |(-544424479/2500000000 : ℝ)|=(544424479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s4_3 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1086866389/2500000000 : ℝ)*x 0 + (842488347/2000000000 : ℝ)*x 1 + (4486672681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086866389/2500000000 : ℝ)^8457 ≤ (6662915087247/20000000000000 : ℝ)^6409 := by
    have hnat : (1086866389 : ℕ)^8457*20000000000000^6409 ≤ 6662915087247^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086866389 2500000000 6662915087247 20000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (842488347/2000000000 : ℝ)^8457 ≤ (15978039259977/50000000000000 : ℝ)^6409 := by
    have hnat : (842488347 : ℕ)^8457*50000000000000^6409 ≤ 15978039259977^6409*2000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842488347 2000000000 15978039259977 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486672681/10000000000 : ℝ)^8457 ≤ (34729346024709/100000000000000 : ℝ)^6409 := by
    have hnat : (4486672681 : ℕ)^8457*100000000000000^6409 ≤ 34729346024709^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486672681 10000000000 34729346024709 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086866389/2500000000 : ℝ), (842488347/2000000000 : ℝ), (4486672681/10000000000 : ℝ)] ![(6662915087247/20000000000000 : ℝ), (15978039259977/50000000000000 : ℝ), (34729346024709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086866389/2500000000 : ℝ)|^8457 ≤ (6662915087247/20000000000000 : ℝ)^6409
        have hw : |(1086866389/2500000000 : ℝ)|=(1086866389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(842488347/2000000000 : ℝ)|^8457 ≤ (15978039259977/50000000000000 : ℝ)^6409
        have hw : |(842488347/2000000000 : ℝ)|=(842488347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486672681/10000000000 : ℝ)|^8457 ≤ (34729346024709/100000000000000 : ℝ)^6409
        have hw : |(4486672681/10000000000 : ℝ)|=(4486672681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s4_4 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1054685683/5000000000 : ℝ)*x 0 + (5262376183/10000000000 : ℝ)*x 1 + (5396245809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054685683/5000000000 : ℝ)^8457 ≤ (3207197715201/25000000000000 : ℝ)^6409 := by
    have hnat : (1054685683 : ℕ)^8457*25000000000000^6409 ≤ 3207197715201^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054685683 5000000000 3207197715201 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262376183/10000000000 : ℝ)^8457 ≤ (42863278646411/100000000000000 : ℝ)^6409 := by
    have hnat : (5262376183 : ℕ)^8457*100000000000000^6409 ≤ 42863278646411^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262376183 10000000000 42863278646411 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396245809/10000000000 : ℝ)^8457 ≤ (44307930476923/100000000000000 : ℝ)^6409 := by
    have hnat : (5396245809 : ℕ)^8457*100000000000000^6409 ≤ 44307930476923^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396245809 10000000000 44307930476923 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1054685683/5000000000 : ℝ), (5262376183/10000000000 : ℝ), (5396245809/10000000000 : ℝ)] ![(3207197715201/25000000000000 : ℝ), (42863278646411/100000000000000 : ℝ), (44307930476923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1054685683/5000000000 : ℝ)|^8457 ≤ (3207197715201/25000000000000 : ℝ)^6409
        have hw : |(-1054685683/5000000000 : ℝ)|=(1054685683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262376183/10000000000 : ℝ)|^8457 ≤ (42863278646411/100000000000000 : ℝ)^6409
        have hw : |(5262376183/10000000000 : ℝ)|=(5262376183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396245809/10000000000 : ℝ)|^8457 ≤ (44307930476923/100000000000000 : ℝ)^6409
        have hw : |(5396245809/10000000000 : ℝ)|=(5396245809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s4_5 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311272553/10000000000 : ℝ)*x 0 + (-1021728667/5000000000 : ℝ)*x 1 + (2698122801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311272553/10000000000 : ℝ)^8457 ≤ (21694798849297/50000000000000 : ℝ)^6409 := by
    have hnat : (5311272553 : ℕ)^8457*50000000000000^6409 ≤ 21694798849297^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311272553 10000000000 21694798849297 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1021728667/5000000000 : ℝ)^8457 ≤ (12302474056399/100000000000000 : ℝ)^6409 := by
    have hnat : (1021728667 : ℕ)^8457*100000000000000^6409 ≤ 12302474056399^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021728667 5000000000 12302474056399 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698122801/5000000000 : ℝ)^8457 ≤ (22153964117073/50000000000000 : ℝ)^6409 := by
    have hnat : (2698122801 : ℕ)^8457*50000000000000^6409 ≤ 22153964117073^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698122801 5000000000 22153964117073 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311272553/10000000000 : ℝ), (-1021728667/5000000000 : ℝ), (2698122801/5000000000 : ℝ)] ![(21694798849297/50000000000000 : ℝ), (12302474056399/100000000000000 : ℝ), (22153964117073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311272553/10000000000 : ℝ)|^8457 ≤ (21694798849297/50000000000000 : ℝ)^6409
        have hw : |(5311272553/10000000000 : ℝ)|=(5311272553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1021728667/5000000000 : ℝ)|^8457 ≤ (12302474056399/100000000000000 : ℝ)^6409
        have hw : |(-1021728667/5000000000 : ℝ)|=(1021728667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698122801/5000000000 : ℝ)|^8457 ≤ (22153964117073/50000000000000 : ℝ)^6409
        have hw : |(2698122801/5000000000 : ℝ)|=(2698122801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s4_6 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062254419/2000000000 : ℝ)*x 0 + (5396245547/10000000000 : ℝ)*x 1 + (-2043458031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062254419/2000000000 : ℝ)^8457 ≤ (43389592761419/100000000000000 : ℝ)^6409 := by
    have hnat : (1062254419 : ℕ)^8457*100000000000000^6409 ≤ 43389592761419^6409*2000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062254419 2000000000 43389592761419 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396245547/10000000000 : ℝ)^8457 ≤ (44307927638239/100000000000000 : ℝ)^6409 := by
    have hnat : (5396245547 : ℕ)^8457*100000000000000^6409 ≤ 44307927638239^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396245547 10000000000 44307927638239 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2043458031/10000000000 : ℝ)^8457 ≤ (6151239796771/50000000000000 : ℝ)^6409 := by
    have hnat : (2043458031 : ℕ)^8457*50000000000000^6409 ≤ 6151239796771^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043458031 10000000000 6151239796771 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062254419/2000000000 : ℝ), (5396245547/10000000000 : ℝ), (-2043458031/10000000000 : ℝ)] ![(43389592761419/100000000000000 : ℝ), (44307927638239/100000000000000 : ℝ), (6151239796771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062254419/2000000000 : ℝ)|^8457 ≤ (43389592761419/100000000000000 : ℝ)^6409
        have hw : |(1062254419/2000000000 : ℝ)|=(1062254419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396245547/10000000000 : ℝ)|^8457 ≤ (44307927638239/100000000000000 : ℝ)^6409
        have hw : |(5396245547/10000000000 : ℝ)|=(5396245547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2043458031/10000000000 : ℝ)|^8457 ≤ (6151239796771/50000000000000 : ℝ)^6409
        have hw : |(-2043458031/10000000000 : ℝ)|=(2043458031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s4_7 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4347478183/10000000000 : ℝ)*x 0 + (4485917037/10000000000 : ℝ)*x 1 + (2106599983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347478183/10000000000 : ℝ)^8457 ≤ (6662940623347/20000000000000 : ℝ)^6409 := by
    have hnat : (4347478183 : ℕ)^8457*20000000000000^6409 ≤ 6662940623347^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347478183 10000000000 6662940623347 20000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4485917037/10000000000 : ℝ)^8457 ≤ (17360814020761/50000000000000 : ℝ)^6409 := by
    have hnat : (4485917037 : ℕ)^8457*50000000000000^6409 ≤ 17360814020761^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485917037 10000000000 17360814020761 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2106599983/5000000000 : ℝ)^8457 ≤ (31963668832469/100000000000000 : ℝ)^6409 := by
    have hnat : (2106599983 : ℕ)^8457*100000000000000^6409 ≤ 31963668832469^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106599983 5000000000 31963668832469 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347478183/10000000000 : ℝ), (4485917037/10000000000 : ℝ), (2106599983/5000000000 : ℝ)] ![(6662940623347/20000000000000 : ℝ), (17360814020761/50000000000000 : ℝ), (31963668832469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347478183/10000000000 : ℝ)|^8457 ≤ (6662940623347/20000000000000 : ℝ)^6409
        have hw : |(4347478183/10000000000 : ℝ)|=(4347478183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4485917037/10000000000 : ℝ)|^8457 ≤ (17360814020761/50000000000000 : ℝ)^6409
        have hw : |(4485917037/10000000000 : ℝ)|=(4485917037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2106599983/5000000000 : ℝ)|^8457 ≤ (31963668832469/100000000000000 : ℝ)^6409
        have hw : |(2106599983/5000000000 : ℝ)|=(2106599983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1264_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14681/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10967/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11387/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14239/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14681/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10967/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14681/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10967/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14681/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10967/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14681/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10967/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14681/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10967/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14681/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10967/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10967/100000 : ℝ) ^ (1057/256 : ℝ) ≤ (10879594215479389/100000000000000000000 : ℝ) := by
    have hpowers : (10967/100000 : ℝ)^1057 ≤ (10879594215479389/100000000000000000000 : ℝ)^256 := by
      have hnat : (10967 : ℕ)^1057*100000000000000000000^256 ≤ 10879594215479389^256*100000^1057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10967 100000 10879594215479389 100000000000000000000 1057 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10967/100000 : ℝ)) (X := (10879594215479389/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14681/100000 : ℝ) ^ (1057/256 : ℝ) ≤ (18137697440392653/50000000000000000000 : ℝ) := by
    have hpowers : (14681/100000 : ℝ)^1057 ≤ (18137697440392653/50000000000000000000 : ℝ)^256 := by
      have hnat : (14681 : ℕ)^1057*50000000000000000000^256 ≤ 18137697440392653^256*100000^1057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14681 100000 18137697440392653 50000000000000000000 1057 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14681/100000 : ℝ)) (X := (18137697440392653/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010879594215479389/50000000000000000000 : ℝ) ≤ (2000105390596839/2000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (50010879594215479389/50000000000000000000 : ℝ)^256 ≤ (2000105390596839/2000000000000000 : ℝ)^1057 := by
      have hnat : (50010879594215479389 : ℕ)^256*2000000000000000^1057 ≤ 2000105390596839^1057*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010879594215479389 50000000000000000000 2000105390596839 2000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000105390596839/2000000000000000 : ℝ)) (X := (50010879594215479389/50000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009430997819252939/20000000000000000000 : ℝ) ≤ (10001141865746473/10000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (20009430997819252939/20000000000000000000 : ℝ)^256 ≤ (10001141865746473/10000000000000000 : ℝ)^1057 := by
      have hnat : (20009430997819252939 : ℕ)^256*10000000000000000^1057 ≤ 10001141865746473^1057*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009430997819252939 20000000000000000000 10001141865746473 10000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001141865746473/10000000000000000 : ℝ)) (X := (20009430997819252939/20000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018137697440392653/25000000000000000000 : ℝ) ≤ (10001756778508751/10000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (25018137697440392653/25000000000000000000 : ℝ)^256 ≤ (10001756778508751/10000000000000000 : ℝ)^1057 := by
      have hnat : (25018137697440392653 : ℕ)^256*10000000000000000^1057 ≤ 10001756778508751^1057*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018137697440392653 25000000000000000000 10001756778508751 10000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001756778508751/10000000000000000 : ℝ)) (X := (25018137697440392653/25000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10879594215479389/100000000000000000000 : ℝ) ≤ ((18564234803427747289/18570000000000000000 : ℝ)+2*(307456381139/185700000000000 : ℝ)*(10967/100000 : ℝ))^(1057/256 : ℝ) := by
    rw [show (18564234803427747289/18570000000000000000 : ℝ)+2*(307456381139/185700000000000 : ℝ)*(10967/100000 : ℝ)=(2000105390596839/2000000000000000 : ℝ) by norm_num, show 1+2*(10879594215479389/100000000000000000000 : ℝ)=(50010879594215479389/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18137697440392653/50000000000000000000 : ℝ)+(10879594215479389/100000000000000000000 : ℝ) ≤ ((18564234803427747289/18570000000000000000 : ℝ)+(307456381139/185700000000000 : ℝ)*((14681/100000 : ℝ)+(10967/100000 : ℝ)))^(1057/256 : ℝ) := by
    rw [show (18564234803427747289/18570000000000000000 : ℝ)+(307456381139/185700000000000 : ℝ)*((14681/100000 : ℝ)+(10967/100000 : ℝ))=(10001141865746473/10000000000000000 : ℝ) by norm_num, show 1+(18137697440392653/50000000000000000000 : ℝ)+(10879594215479389/100000000000000000000 : ℝ)=(20009430997819252939/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18137697440392653/50000000000000000000 : ℝ) ≤ ((18564234803427747289/18570000000000000000 : ℝ)+2*(307456381139/185700000000000 : ℝ)*(14681/100000 : ℝ))^(1057/256 : ℝ) := by
    rw [show (18564234803427747289/18570000000000000000 : ℝ)+2*(307456381139/185700000000000 : ℝ)*(14681/100000 : ℝ)=(10001756778508751/10000000000000000 : ℝ) by norm_num, show 1+2*(18137697440392653/50000000000000000000 : ℝ)=(25018137697440392653/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18564234803427747289/18570000000000000000 : ℝ)*(X 1 0+X 2 0)+(307456381139/185700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (10967/100000 : ℝ)) (hi := (14681/100000 : ℝ)) (c := (18564234803427747289/18570000000000000000 : ℝ)) (alpha := (307456381139/185700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18564234803427747289/18570000000000000000 : ℝ)*(X 0 1+X 2 1)+(307456381139/185700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (10967/100000 : ℝ)) (hi := (14681/100000 : ℝ)) (c := (18564234803427747289/18570000000000000000 : ℝ)) (alpha := (307456381139/185700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18564234803427747289/18570000000000000000 : ℝ)*(X 0 2+X 1 2)+(307456381139/185700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (10967/100000 : ℝ)) (hi := (14681/100000 : ℝ)) (c := (18564234803427747289/18570000000000000000 : ℝ)) (alpha := (307456381139/185700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1054682583/5000000000 : ℝ)*X 0 0+(674577233/1250000000 : ℝ)*X 0 1+(5262005751/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069133583/2000000000 : ℝ)*X 1 0+(-2177697867/10000000000 : ℝ)*X 1 1+(5262005671/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534566801/1000000000 : ℝ)*X 2 0+(5262005539/10000000000 : ℝ)*X 2 1+(-544424479/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1086866389/2500000000 : ℝ)*X 0 0+(842488347/2000000000 : ℝ)*X 0 1+(4486672681/10000000000 : ℝ)*X 0 2+(1086866389/2500000000 : ℝ)*X 1 0+(842488347/2000000000 : ℝ)*X 1 1+(4486672681/10000000000 : ℝ)*X 1 2+(1086866389/2500000000 : ℝ)*X 2 0+(842488347/2000000000 : ℝ)*X 2 1+(4486672681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1054685683/5000000000 : ℝ)*X 0 0+(5262376183/10000000000 : ℝ)*X 0 1+(5396245809/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311272553/10000000000 : ℝ)*X 1 0+(-1021728667/5000000000 : ℝ)*X 1 1+(2698122801/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062254419/2000000000 : ℝ)*X 2 0+(5396245547/10000000000 : ℝ)*X 2 1+(-2043458031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4347478183/10000000000 : ℝ)*X 0 0+(4485917037/10000000000 : ℝ)*X 0 1+(2106599983/5000000000 : ℝ)*X 0 2+(4347478183/10000000000 : ℝ)*X 1 0+(4485917037/10000000000 : ℝ)*X 1 1+(2106599983/5000000000 : ℝ)*X 1 2+(4347478183/10000000000 : ℝ)*X 2 0+(4485917037/10000000000 : ℝ)*X 2 1+(2106599983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3067385572291858467864923199/309500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1592066461/100000000000000 : ℝ)*(base19) + (40608473/2500000000000 : ℝ)*(base23) + (43111627/20000000000000 : ℝ)*(upper3) + (833157/1562500000000 : ℝ)*(upper4) + (23323401/25000000000000 : ℝ)*(upper5) + (5537714406506397/100000000000000 : ℝ)*(major0) + (5537714406506397/100000000000000 : ℝ)*(major1) + (5537714406506397/100000000000000 : ℝ)*(major2) + (7428790416762703/100000000000000 : ℝ)*(sp0) + (7428824531731087/100000000000000 : ℝ)*(sp1) + (1857206124864657/25000000000000 : ℝ)*(sp2) + (1823290078311341/50000000000000 : ℝ)*(sp3) + (7141406969/20000000000000 : ℝ)*(sp4) + (22202233307/100000000000000 : ℝ)*(sp7) + (3646602358855989/100000000000000 : ℝ)*(f.failure) + (1857206530949387/25000000000000 : ℝ)*(f.sum) + (4853987360707/1547500000000000000000000000 : ℝ)*base66 + (5217846668765264089/619000000000000000000000000000000 : ℝ)*base68 + (17967531980579264089/619000000000000000000000000000000 : ℝ)*base70 + (8286135780083264089/619000000000000000000000000000000 : ℝ)*base72 + (4811404428061/3095000000000000000000000000 : ℝ)*base73 + (14937201893540264089/619000000000000000000000000000000 : ℝ)*base76 + (7564454001908264089/619000000000000000000000000000000 : ℝ)*base78 + (18278447979600264089/619000000000000000000000000000000 : ℝ)*base80 + (6825503267759/3095000000000000000000000000 : ℝ)*base82 + (30527193/10000000000000000000000 : ℝ)*base90 + (30527193/10000000000000000000000 : ℝ)*base92 + (30527193/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (121753286875238567311600137/15475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3046179523/100000000000000 : ℝ)*(base19) + (1097121301/50000000000000 : ℝ)*(base23) + (69688749/100000000000000 : ℝ)*(upper2) + (110989359/100000000000000 : ℝ)*(upper3) + (212069607/50000000000000 : ℝ)*(upper5) + (278418763841433/5000000000000 : ℝ)*(major0) + (278418763841433/5000000000000 : ℝ)*(major1) + (278418763841433/5000000000000 : ℝ)*(major2) + (84681863807/100000000000000 : ℝ)*(sp1) + (32333673369/100000000000000 : ℝ)*(sp2) + (933744706621763/12500000000000 : ℝ)*(sp4) + (3734934962465387/50000000000000 : ℝ)*(sp5) + (7469923125058133/100000000000000 : ℝ)*(sp6) + (916698159606297/25000000000000 : ℝ)*(sp7) + (916698159606297/25000000000000 : ℝ)*(f.failure) + (933744706621763/12500000000000 : ℝ)*(f.sum) + (44761188429/9671875000000000000000000 : ℝ)*base65 + (103888532508491621/30950000000000000000000000000000 : ℝ)*base68 + (167261156906691621/30950000000000000000000000000000 : ℝ)*base70 + (118676667300658379/30950000000000000000000000000000 : ℝ)*base71 + (730673676667/619000000000000000000000000 : ℝ)*base73 + (91126487720241621/30950000000000000000000000000000 : ℝ)*base76 + (253091715757558379/30950000000000000000000000000000 : ℝ)*base77 + (543589289937991621/30950000000000000000000000000000 : ℝ)*base80 + (2253089986823/619000000000000000000000000 : ℝ)*base82 + (14468211/2500000000000000000000 : ℝ)*base89 + (14468211/2500000000000000000000 : ℝ)*base91 + (14468211/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1264_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14681/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10967/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1264_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1264_s5_0 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2109780627/10000000000 : ℝ)*x 0 + (2695944023/5000000000 : ℝ)*x 1 + (5266462401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109780627/10000000000 : ℝ)^8457 ≤ (3208018846431/25000000000000 : ℝ)^6409 := by
    have hnat : (2109780627 : ℕ)^8457*25000000000000^6409 ≤ 3208018846431^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109780627 10000000000 3208018846431 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695944023/5000000000 : ℝ)^8457 ≤ (44260721633833/100000000000000 : ℝ)^6409 := by
    have hnat : (2695944023 : ℕ)^8457*100000000000000^6409 ≤ 44260721633833^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695944023 5000000000 44260721633833 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266462401/10000000000 : ℝ)^8457 ≤ (42907202957267/100000000000000 : ℝ)^6409 := by
    have hnat : (5266462401 : ℕ)^8457*100000000000000^6409 ≤ 42907202957267^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266462401 10000000000 42907202957267 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2109780627/10000000000 : ℝ), (2695944023/5000000000 : ℝ), (5266462401/10000000000 : ℝ)] ![(3208018846431/25000000000000 : ℝ), (44260721633833/100000000000000 : ℝ), (42907202957267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2109780627/10000000000 : ℝ)|^8457 ≤ (3208018846431/25000000000000 : ℝ)^6409
        have hw : |(-2109780627/10000000000 : ℝ)|=(2109780627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695944023/5000000000 : ℝ)|^8457 ≤ (44260721633833/100000000000000 : ℝ)^6409
        have hw : |(2695944023/5000000000 : ℝ)|=(2695944023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266462401/10000000000 : ℝ)|^8457 ≤ (42907202957267/100000000000000 : ℝ)^6409
        have hw : |(5266462401/10000000000 : ℝ)|=(5266462401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s5_1 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336117231/2500000000 : ℝ)*x 0 + (-2173384923/10000000000 : ℝ)*x 1 + (131661561/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336117231/2500000000 : ℝ)^8457 ≤ (43747806763007/100000000000000 : ℝ)^6409 := by
    have hnat : (1336117231 : ℕ)^8457*100000000000000^6409 ≤ 43747806763007^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336117231 2500000000 43747806763007 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2173384923/10000000000 : ℝ)^8457 ≤ (13344989844081/100000000000000 : ℝ)^6409 := by
    have hnat : (2173384923 : ℕ)^8457*100000000000000^6409 ≤ 13344989844081^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173384923 10000000000 13344989844081 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131661561/250000000 : ℝ)^8457 ≤ (8581440675309/20000000000000 : ℝ)^6409 := by
    have hnat : (131661561 : ℕ)^8457*20000000000000^6409 ≤ 8581440675309^6409*250000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131661561 250000000 8581440675309 20000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336117231/2500000000 : ℝ), (-2173384923/10000000000 : ℝ), (131661561/250000000 : ℝ)] ![(43747806763007/100000000000000 : ℝ), (13344989844081/100000000000000 : ℝ), (8581440675309/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336117231/2500000000 : ℝ)|^8457 ≤ (43747806763007/100000000000000 : ℝ)^6409
        have hw : |(1336117231/2500000000 : ℝ)|=(1336117231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2173384923/10000000000 : ℝ)|^8457 ≤ (13344989844081/100000000000000 : ℝ)^6409
        have hw : |(-2173384923/10000000000 : ℝ)|=(2173384923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131661561/250000000 : ℝ)|^8457 ≤ (8581440675309/20000000000000 : ℝ)^6409
        have hw : |(131661561/250000000 : ℝ)|=(131661561/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s5_2 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344469231/10000000000 : ℝ)*x 0 + (658307793/1250000000 : ℝ)*x 1 + (-2173384641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344469231/10000000000 : ℝ)^8457 ≤ (2187390503951/5000000000000 : ℝ)^6409 := by
    have hnat : (5344469231 : ℕ)^8457*5000000000000^6409 ≤ 2187390503951^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344469231 10000000000 2187390503951 5000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658307793/1250000000 : ℝ)^8457 ≤ (10726800586119/25000000000000 : ℝ)^6409 := by
    have hnat : (658307793 : ℕ)^8457*25000000000000^6409 ≤ 10726800586119^6409*1250000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658307793 1250000000 10726800586119 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2173384641/10000000000 : ℝ)^8457 ≤ (3336246889809/25000000000000 : ℝ)^6409 := by
    have hnat : (2173384641 : ℕ)^8457*25000000000000^6409 ≤ 3336246889809^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173384641 10000000000 3336246889809 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344469231/10000000000 : ℝ), (658307793/1250000000 : ℝ), (-2173384641/10000000000 : ℝ)] ![(2187390503951/5000000000000 : ℝ), (10726800586119/25000000000000 : ℝ), (3336246889809/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344469231/10000000000 : ℝ)|^8457 ≤ (2187390503951/5000000000000 : ℝ)^6409
        have hw : |(5344469231/10000000000 : ℝ)|=(5344469231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658307793/1250000000 : ℝ)|^8457 ≤ (10726800586119/25000000000000 : ℝ)^6409
        have hw : |(658307793/1250000000 : ℝ)|=(658307793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2173384641/10000000000 : ℝ)|^8457 ≤ (3336246889809/25000000000000 : ℝ)^6409
        have hw : |(-2173384641/10000000000 : ℝ)|=(2173384641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s5_3 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4347710281/10000000000 : ℝ)*x 0 + (422176811/1000000000 : ℝ)*x 1 + (4477283739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347710281/10000000000 : ℝ)^8457 ≤ (8329262511091/25000000000000 : ℝ)^6409 := by
    have hnat : (4347710281 : ℕ)^8457*25000000000000^6409 ≤ 8329262511091^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347710281 10000000000 8329262511091 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422176811/1000000000 : ℝ)^8457 ≤ (1602473551311/5000000000000 : ℝ)^6409 := by
    have hnat : (422176811 : ℕ)^8457*5000000000000^6409 ≤ 1602473551311^6409*1000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422176811 1000000000 1602473551311 5000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4477283739/10000000000 : ℝ)^8457 ≤ (17316739457573/50000000000000 : ℝ)^6409 := by
    have hnat : (4477283739 : ℕ)^8457*50000000000000^6409 ≤ 17316739457573^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477283739 10000000000 17316739457573 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347710281/10000000000 : ℝ), (422176811/1000000000 : ℝ), (4477283739/10000000000 : ℝ)] ![(8329262511091/25000000000000 : ℝ), (1602473551311/5000000000000 : ℝ), (17316739457573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347710281/10000000000 : ℝ)|^8457 ≤ (8329262511091/25000000000000 : ℝ)^6409
        have hw : |(4347710281/10000000000 : ℝ)|=(4347710281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(422176811/1000000000 : ℝ)|^8457 ≤ (1602473551311/5000000000000 : ℝ)^6409
        have hw : |(422176811/1000000000 : ℝ)|=(422176811/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4477283739/10000000000 : ℝ)|^8457 ≤ (17316739457573/50000000000000 : ℝ)^6409
        have hw : |(4477283739/10000000000 : ℝ)|=(4477283739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s5_4 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2109785503/10000000000 : ℝ)*x 0 + (526678447/1000000000 : ℝ)*x 1 + (1347891193/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109785503/10000000000 : ℝ)^8457 ≤ (6416057259649/50000000000000 : ℝ)^6409 := by
    have hnat : (2109785503 : ℕ)^8457*50000000000000^6409 ≤ 6416057259649^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109785503 10000000000 6416057259649 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526678447/1000000000 : ℝ)^8457 ≤ (42910665462543/100000000000000 : ℝ)^6409 := by
    have hnat : (526678447 : ℕ)^8457*100000000000000^6409 ≤ 42910665462543^6409*1000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526678447 1000000000 42910665462543 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347891193/2500000000 : ℝ)^8457 ≤ (22128610001733/50000000000000 : ℝ)^6409 := by
    have hnat : (1347891193 : ℕ)^8457*50000000000000^6409 ≤ 22128610001733^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347891193 2500000000 22128610001733 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2109785503/10000000000 : ℝ), (526678447/1000000000 : ℝ), (1347891193/2500000000 : ℝ)] ![(6416057259649/50000000000000 : ℝ), (42910665462543/100000000000000 : ℝ), (22128610001733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2109785503/10000000000 : ℝ)|^8457 ≤ (6416057259649/50000000000000 : ℝ)^6409
        have hw : |(-2109785503/10000000000 : ℝ)|=(2109785503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526678447/1000000000 : ℝ)|^8457 ≤ (42910665462543/100000000000000 : ℝ)^6409
        have hw : |(526678447/1000000000 : ℝ)|=(526678447/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347891193/2500000000 : ℝ)|^8457 ≤ (22128610001733/50000000000000 : ℝ)^6409
        have hw : |(1347891193/2500000000 : ℝ)|=(1347891193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s5_5 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656209657/5000000000 : ℝ)*x 0 + (-1024141221/5000000000 : ℝ)*x 1 + (5391564731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656209657/5000000000 : ℝ)^8457 ≤ (43401960047307/100000000000000 : ℝ)^6409 := by
    have hnat : (2656209657 : ℕ)^8457*100000000000000^6409 ≤ 43401960047307^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656209657 5000000000 43401960047307 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1024141221/5000000000 : ℝ)^8457 ≤ (2468164075567/20000000000000 : ℝ)^6409 := by
    have hnat : (1024141221 : ℕ)^8457*20000000000000^6409 ≤ 2468164075567^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024141221 5000000000 2468164075567 20000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391564731/10000000000 : ℝ)^8457 ≤ (5532152444921/12500000000000 : ℝ)^6409 := by
    have hnat : (5391564731 : ℕ)^8457*12500000000000^6409 ≤ 5532152444921^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391564731 10000000000 5532152444921 12500000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656209657/5000000000 : ℝ), (-1024141221/5000000000 : ℝ), (5391564731/10000000000 : ℝ)] ![(43401960047307/100000000000000 : ℝ), (2468164075567/20000000000000 : ℝ), (5532152444921/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656209657/5000000000 : ℝ)|^8457 ≤ (43401960047307/100000000000000 : ℝ)^6409
        have hw : |(2656209657/5000000000 : ℝ)|=(2656209657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1024141221/5000000000 : ℝ)|^8457 ≤ (2468164075567/20000000000000 : ℝ)^6409
        have hw : |(-1024141221/5000000000 : ℝ)|=(1024141221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391564731/10000000000 : ℝ)|^8457 ≤ (5532152444921/12500000000000 : ℝ)^6409
        have hw : |(5391564731/10000000000 : ℝ)|=(5391564731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s5_6 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664052413/1250000000 : ℝ)*x 0 + (21566259/40000000 : ℝ)*x 1 + (-204828243/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664052413/1250000000 : ℝ)^8457 ≤ (43401959939501/100000000000000 : ℝ)^6409 := by
    have hnat : (664052413 : ℕ)^8457*100000000000000^6409 ≤ 43401959939501^6409*1250000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664052413 1250000000 43401959939501 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21566259/40000000 : ℝ)^8457 ≤ (44257219765169/100000000000000 : ℝ)^6409 := by
    have hnat : (21566259 : ℕ)^8457*100000000000000^6409 ≤ 44257219765169^6409*40000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21566259 40000000 44257219765169 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204828243/1000000000 : ℝ)^8457 ≤ (192825316913/1562500000000 : ℝ)^6409 := by
    have hnat : (204828243 : ℕ)^8457*1562500000000^6409 ≤ 192825316913^6409*1000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204828243 1000000000 192825316913 1562500000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664052413/1250000000 : ℝ), (21566259/40000000 : ℝ), (-204828243/1000000000 : ℝ)] ![(43401959939501/100000000000000 : ℝ), (44257219765169/100000000000000 : ℝ), (192825316913/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664052413/1250000000 : ℝ)|^8457 ≤ (43401959939501/100000000000000 : ℝ)^6409
        have hw : |(664052413/1250000000 : ℝ)|=(664052413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21566259/40000000 : ℝ)|^8457 ≤ (44257219765169/100000000000000 : ℝ)^6409
        have hw : |(21566259/40000000 : ℝ)|=(21566259/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-204828243/1000000000 : ℝ)|^8457 ≤ (192825316913/1562500000000 : ℝ)^6409
        have hw : |(-204828243/1000000000 : ℝ)|=(204828243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s5_7 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1086930017/2500000000 : ℝ)*x 0 + (4476627867/10000000000 : ℝ)*x 1 + (4222426503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086930017/2500000000 : ℝ)^8457 ≤ (33317149009391/100000000000000 : ℝ)^6409 := by
    have hnat : (1086930017 : ℕ)^8457*100000000000000^6409 ≤ 33317149009391^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086930017 2500000000 33317149009391 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4476627867/10000000000 : ℝ)^8457 ≤ (34626784440747/100000000000000 : ℝ)^6409 := by
    have hnat : (4476627867 : ℕ)^8457*100000000000000^6409 ≤ 34626784440747^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476627867 10000000000 34626784440747 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4222426503/10000000000 : ℝ)^8457 ≤ (32056066539143/100000000000000 : ℝ)^6409 := by
    have hnat : (4222426503 : ℕ)^8457*100000000000000^6409 ≤ 32056066539143^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222426503 10000000000 32056066539143 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086930017/2500000000 : ℝ), (4476627867/10000000000 : ℝ), (4222426503/10000000000 : ℝ)] ![(33317149009391/100000000000000 : ℝ), (34626784440747/100000000000000 : ℝ), (32056066539143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086930017/2500000000 : ℝ)|^8457 ≤ (33317149009391/100000000000000 : ℝ)^6409
        have hw : |(1086930017/2500000000 : ℝ)|=(1086930017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4476627867/10000000000 : ℝ)|^8457 ≤ (34626784440747/100000000000000 : ℝ)^6409
        have hw : |(4476627867/10000000000 : ℝ)|=(4476627867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4222426503/10000000000 : ℝ)|^8457 ≤ (32056066539143/100000000000000 : ℝ)^6409
        have hw : |(4222426503/10000000000 : ℝ)|=(4222426503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1264_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5741/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14139/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11387/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11387/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11387/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11387/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11387/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11387/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11387/100000 : ℝ) ^ (1057/256 : ℝ) ≤ (1588226944432413/12500000000000000000 : ℝ) := by
    have hpowers : (11387/100000 : ℝ)^1057 ≤ (1588226944432413/12500000000000000000 : ℝ)^256 := by
      have hnat : (11387 : ℕ)^1057*12500000000000000000^256 ≤ 1588226944432413^256*100000^1057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11387 100000 1588226944432413 12500000000000000000 1057 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11387/100000 : ℝ)) (X := (1588226944432413/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14239/100000 : ℝ) ^ (1057/256 : ℝ) ≤ (7993485366988241/25000000000000000000 : ℝ) := by
    have hpowers : (14239/100000 : ℝ)^1057 ≤ (7993485366988241/25000000000000000000 : ℝ)^256 := by
      have hnat : (14239 : ℕ)^1057*25000000000000000000^256 ≤ 7993485366988241^256*100000^1057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14239 100000 7993485366988241 25000000000000000000 1057 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14239/100000 : ℝ)) (X := (7993485366988241/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251588226944432413/6250000000000000000 : ℝ) ≤ (10000615397472591/10000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (6251588226944432413/6250000000000000000 : ℝ)^256 ≤ (10000615397472591/10000000000000000 : ℝ)^1057 := by
      have hnat : (6251588226944432413 : ℕ)^256*10000000000000000^1057 ≤ 10000615397472591^1057*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251588226944432413 6250000000000000000 10000615397472591 10000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000615397472591/10000000000000000 : ℝ)) (X := (6251588226944432413/6250000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011169939255853067/25000000000000000000 : ℝ) ≤ (5000540968870927/5000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (25011169939255853067/25000000000000000000 : ℝ)^256 ≤ (5000540968870927/5000000000000000 : ℝ)^1057 := by
      have hnat : (25011169939255853067 : ℕ)^256*5000000000000000^1057 ≤ 5000540968870927^1057*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011169939255853067 25000000000000000000 5000540968870927 5000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000540968870927/5000000000000000 : ℝ)) (X := (25011169939255853067/25000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507993485366988241/12500000000000000000 : ℝ) ≤ (10001548478011117/10000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (12507993485366988241/12500000000000000000 : ℝ)^256 ≤ (10001548478011117/10000000000000000 : ℝ)^1057 := by
      have hnat : (12507993485366988241 : ℕ)^256*10000000000000000^1057 ≤ 10001548478011117^1057*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507993485366988241 12500000000000000000 10001548478011117 10000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001548478011117/10000000000000000 : ℝ)) (X := (12507993485366988241/12500000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1588226944432413/12500000000000000000 : ℝ) ≤ ((2851113012549963397/2852000000000000000 : ℝ)+2*(466540269263/285200000000000 : ℝ)*(11387/100000 : ℝ))^(1057/256 : ℝ) := by
    rw [show (2851113012549963397/2852000000000000000 : ℝ)+2*(466540269263/285200000000000 : ℝ)*(11387/100000 : ℝ)=(10000615397472591/10000000000000000 : ℝ) by norm_num, show 1+2*(1588226944432413/12500000000000000000 : ℝ)=(6251588226944432413/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7993485366988241/25000000000000000000 : ℝ)+(1588226944432413/12500000000000000000 : ℝ) ≤ ((2851113012549963397/2852000000000000000 : ℝ)+(466540269263/285200000000000 : ℝ)*((14239/100000 : ℝ)+(11387/100000 : ℝ)))^(1057/256 : ℝ) := by
    rw [show (2851113012549963397/2852000000000000000 : ℝ)+(466540269263/285200000000000 : ℝ)*((14239/100000 : ℝ)+(11387/100000 : ℝ))=(5000540968870927/5000000000000000 : ℝ) by norm_num, show 1+(7993485366988241/25000000000000000000 : ℝ)+(1588226944432413/12500000000000000000 : ℝ)=(25011169939255853067/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7993485366988241/25000000000000000000 : ℝ) ≤ ((2851113012549963397/2852000000000000000 : ℝ)+2*(466540269263/285200000000000 : ℝ)*(14239/100000 : ℝ))^(1057/256 : ℝ) := by
    rw [show (2851113012549963397/2852000000000000000 : ℝ)+2*(466540269263/285200000000000 : ℝ)*(14239/100000 : ℝ)=(10001548478011117/10000000000000000 : ℝ) by norm_num, show 1+2*(7993485366988241/25000000000000000000 : ℝ)=(12507993485366988241/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2851113012549963397/2852000000000000000 : ℝ)*(X 1 0+X 2 0)+(466540269263/285200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (11387/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (2851113012549963397/2852000000000000000 : ℝ)) (alpha := (466540269263/285200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2851113012549963397/2852000000000000000 : ℝ)*(X 0 1+X 2 1)+(466540269263/285200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (11387/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (2851113012549963397/2852000000000000000 : ℝ)) (alpha := (466540269263/285200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2851113012549963397/2852000000000000000 : ℝ)*(X 0 2+X 1 2)+(466540269263/285200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (11387/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (2851113012549963397/2852000000000000000 : ℝ)) (alpha := (466540269263/285200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2109780627/10000000000 : ℝ)*X 0 0+(2695944023/5000000000 : ℝ)*X 0 1+(5266462401/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336117231/2500000000 : ℝ)*X 1 0+(-2173384923/10000000000 : ℝ)*X 1 1+(131661561/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344469231/10000000000 : ℝ)*X 2 0+(658307793/1250000000 : ℝ)*X 2 1+(-2173384641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4347710281/10000000000 : ℝ)*X 0 0+(422176811/1000000000 : ℝ)*X 0 1+(4477283739/10000000000 : ℝ)*X 0 2+(4347710281/10000000000 : ℝ)*X 1 0+(422176811/1000000000 : ℝ)*X 1 1+(4477283739/10000000000 : ℝ)*X 1 2+(4347710281/10000000000 : ℝ)*X 2 0+(422176811/1000000000 : ℝ)*X 2 1+(4477283739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2109785503/10000000000 : ℝ)*X 0 0+(526678447/1000000000 : ℝ)*X 0 1+(1347891193/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656209657/5000000000 : ℝ)*X 1 0+(-1024141221/5000000000 : ℝ)*X 1 1+(5391564731/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664052413/1250000000 : ℝ)*X 2 0+(21566259/40000000 : ℝ)*X 2 1+(-204828243/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1086930017/2500000000 : ℝ)*X 0 0+(4476627867/10000000000 : ℝ)*X 0 1+(4222426503/10000000000 : ℝ)*X 0 2+(1086930017/2500000000 : ℝ)*X 1 0+(4476627867/10000000000 : ℝ)*X 1 1+(4222426503/10000000000 : ℝ)*X 1 2+(1086930017/2500000000 : ℝ)*X 2 0+(4476627867/10000000000 : ℝ)*X 2 1+(4222426503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1293395935352443828613096529/142600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (785630399/50000000000000 : ℝ)*(base19) + (11136437/625000000000 : ℝ)*(base23) + (8289961/6250000000000 : ℝ)*(lower2) + (44550301/12500000000000 : ℝ)*(upper5) + (5943322608693973/100000000000000 : ℝ)*(major0) + (5943322608693973/100000000000000 : ℝ)*(major1) + (5943322608693973/100000000000000 : ℝ)*(major2) + (7972886213881097/100000000000000 : ℝ)*(sp0) + (7972946580430971/100000000000000 : ℝ)*(sp1) + (7972946497143283/100000000000000 : ℝ)*(sp2) + (978419360398839/25000000000000 : ℝ)*(sp3) + (31032546053/50000000000000 : ℝ)*(sp4) + (63640717/50000000000000 : ℝ)*(sp5) + (1919448279/10000000000000 : ℝ)*(sp7) + (1956848318039073/50000000000000 : ℝ)*(f.failure) + (7972948278973203/100000000000000 : ℝ)*(f.sum) + (53647088804959/14260000000000000000000000000 : ℝ)*base65 + (795982561650903719/285200000000000000000000000000000 : ℝ)*base68 + (2951198124148103719/285200000000000000000000000000000 : ℝ)*base70 + (264506618863703719/285200000000000000000000000000000 : ℝ)*base72 + (4787531598359/14260000000000000000000000000 : ℝ)*base73 + (4938959349126103719/285200000000000000000000000000000 : ℝ)*base76 + (1992808321147303719/285200000000000000000000000000000 : ℝ)*base78 + (2025757851614903719/285200000000000000000000000000000 : ℝ)*base80 + (76197989055361/14260000000000000000000000000 : ℝ)*base82 + (7294901/5000000000000000000000 : ℝ)*base90 + (7294901/5000000000000000000000 : ℝ)*base92 + (7294901/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (192015752511215997702349251/71300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (208902801/50000000000000 : ℝ)*(base19) + (47603129/10000000000000 : ℝ)*(base23) + (40686711/100000000000000 : ℝ)*(upper3) + (1911797/6250000000000 : ℝ)*(lower4) + (34716039/100000000000000 : ℝ)*(upper5) + (5973986640211339/100000000000000 : ℝ)*(major0) + (5973986640211339/100000000000000 : ℝ)*(major1) + (5973986640211339/100000000000000 : ℝ)*(major2) + (4756049999/50000000000000 : ℝ)*(sp1) + (12119580773/100000000000000 : ℝ)*(sp2) + (4007042096674729/50000000000000 : ℝ)*(sp4) + (400703713172193/5000000000000 : ℝ)*(sp5) + (2003517899434349/25000000000000 : ℝ)*(sp6) + (491736124663033/12500000000000 : ℝ)*(sp7) + (491736124663033/12500000000000 : ℝ)*(f.failure) + (4007042096674729/50000000000000 : ℝ)*(f.sum) + (1233509410877/14260000000000000000000000000 : ℝ)*base65 + (4698280709916328583/285200000000000000000000000000000 : ℝ)*base67 + (2618556615172328583/285200000000000000000000000000000 : ℝ)*base69 + (1041959100657128583/285200000000000000000000000000000 : ℝ)*base71 + (108260142137517/14260000000000000000000000000 : ℝ)*base73 + (2722521594608471417/285200000000000000000000000000000 : ℝ)*base76 + (3369016057731128583/285200000000000000000000000000000 : ℝ)*base77 + (5432960001965928583/285200000000000000000000000000000 : ℝ)*base79 + (65443630762217/14260000000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (23865421/1250000000000000000000 : ℝ)*base90 + (23865421/1250000000000000000000 : ℝ)*base92 + (23865421/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1264_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5741/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14139/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1264_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1264_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8083/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2397/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5741/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14139/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1264_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1264_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1264_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8083/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2397/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5741/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14139/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1264_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

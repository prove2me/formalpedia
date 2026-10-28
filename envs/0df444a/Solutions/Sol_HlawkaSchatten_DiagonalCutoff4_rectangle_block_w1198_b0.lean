-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1198_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:02:12.087767+00:00
-- url     : https://prove2.me/submissions/8554ef86-3fc2-4c2f-aee6-bac263f07e36

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
theorem support_rectangle_w1198_s0_0 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-374842551/2000000000 : ℝ)*x 0 + (1510369309/2500000000 : ℝ)*x 1 + (4787513819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (374842551/2000000000 : ℝ)^8391 ≤ (2728788350931/25000000000000 : ℝ)^6343 := by
    have hnat : (374842551 : ℕ)^8391*25000000000000^6343 ≤ 2728788350931^6343*2000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374842551 2000000000 2728788350931 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1510369309/2500000000 : ℝ)^8391 ≤ (51342806236187/100000000000000 : ℝ)^6343 := by
    have hnat : (1510369309 : ℕ)^8391*100000000000000^6343 ≤ 51342806236187^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510369309 2500000000 51342806236187 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4787513819/10000000000 : ℝ)^8391 ≤ (18871020169621/50000000000000 : ℝ)^6343 := by
    have hnat : (4787513819 : ℕ)^8391*50000000000000^6343 ≤ 18871020169621^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4787513819 10000000000 18871020169621 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-374842551/2000000000 : ℝ), (1510369309/2500000000 : ℝ), (4787513819/10000000000 : ℝ)] ![(2728788350931/25000000000000 : ℝ), (51342806236187/100000000000000 : ℝ), (18871020169621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-374842551/2000000000 : ℝ)|^8391 ≤ (2728788350931/25000000000000 : ℝ)^6343
        have hw : |(-374842551/2000000000 : ℝ)|=(374842551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1510369309/2500000000 : ℝ)|^8391 ≤ (51342806236187/100000000000000 : ℝ)^6343
        have hw : |(1510369309/2500000000 : ℝ)|=(1510369309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4787513819/10000000000 : ℝ)|^8391 ≤ (18871020169621/50000000000000 : ℝ)^6343
        have hw : |(4787513819/10000000000 : ℝ)|=(4787513819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s0_1 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1378409573/2500000000 : ℝ)*x 0 + (-2592280693/10000000000 : ℝ)*x 1 + (1196878443/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1378409573/2500000000 : ℝ)^8391 ≤ (45494091424111/100000000000000 : ℝ)^6343 := by
    have hnat : (1378409573 : ℕ)^8391*100000000000000^6343 ≤ 45494091424111^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378409573 2500000000 45494091424111 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592280693/10000000000 : ℝ)^8391 ≤ (16763868714701/100000000000000 : ℝ)^6343 := by
    have hnat : (2592280693 : ℕ)^8391*100000000000000^6343 ≤ 16763868714701^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592280693 10000000000 16763868714701 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1196878443/2500000000 : ℝ)^8391 ≤ (294859686321/781250000000 : ℝ)^6343 := by
    have hnat : (1196878443 : ℕ)^8391*781250000000^6343 ≤ 294859686321^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196878443 2500000000 294859686321 781250000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1378409573/2500000000 : ℝ), (-2592280693/10000000000 : ℝ), (1196878443/2500000000 : ℝ)] ![(45494091424111/100000000000000 : ℝ), (16763868714701/100000000000000 : ℝ), (294859686321/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1378409573/2500000000 : ℝ)|^8391 ≤ (45494091424111/100000000000000 : ℝ)^6343
        have hw : |(1378409573/2500000000 : ℝ)|=(1378409573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2592280693/10000000000 : ℝ)|^8391 ≤ (16763868714701/100000000000000 : ℝ)^6343
        have hw : |(-2592280693/10000000000 : ℝ)|=(2592280693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1196878443/2500000000 : ℝ)|^8391 ≤ (294859686321/781250000000 : ℝ)^6343
        have hw : |(1196878443/2500000000 : ℝ)|=(1196878443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s0_2 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (86150603/156250000 : ℝ)*x 0 + (4787513493/10000000000 : ℝ)*x 1 + (-2592280649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86150603/156250000 : ℝ)^8391 ≤ (45494094698701/100000000000000 : ℝ)^6343 := by
    have hnat : (86150603 : ℕ)^8391*100000000000000^6343 ≤ 45494094698701^6343*156250000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86150603 156250000 45494094698701 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4787513493/10000000000 : ℝ)^8391 ≤ (37742036939453/100000000000000 : ℝ)^6343 := by
    have hnat : (4787513493 : ℕ)^8391*100000000000000^6343 ≤ 37742036939453^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4787513493 10000000000 37742036939453 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2592280649/10000000000 : ℝ)^8391 ≤ (16763868338289/100000000000000 : ℝ)^6343 := by
    have hnat : (2592280649 : ℕ)^8391*100000000000000^6343 ≤ 16763868338289^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592280649 10000000000 16763868338289 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86150603/156250000 : ℝ), (4787513493/10000000000 : ℝ), (-2592280649/10000000000 : ℝ)] ![(45494094698701/100000000000000 : ℝ), (37742036939453/100000000000000 : ℝ), (16763868338289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86150603/156250000 : ℝ)|^8391 ≤ (45494094698701/100000000000000 : ℝ)^6343
        have hw : |(86150603/156250000 : ℝ)|=(86150603/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4787513493/10000000000 : ℝ)|^8391 ≤ (37742036939453/100000000000000 : ℝ)^6343
        have hw : |(4787513493/10000000000 : ℝ)|=(4787513493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2592280649/10000000000 : ℝ)|^8391 ≤ (16763868338289/100000000000000 : ℝ)^6343
        have hw : |(-2592280649/10000000000 : ℝ)|=(2592280649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s0_3 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4196499349/10000000000 : ℝ)*x 0 + (3118625153/10000000000 : ℝ)*x 1 + (5640785021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4196499349/10000000000 : ℝ)^8391 ≤ (1981557316681/6250000000000 : ℝ)^6343 := by
    have hnat : (4196499349 : ℕ)^8391*6250000000000^6343 ≤ 1981557316681^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4196499349 10000000000 1981557316681 6250000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3118625153/10000000000 : ℝ)^8391 ≤ (10704003277627/50000000000000 : ℝ)^6343 := by
    have hnat : (3118625153 : ℕ)^8391*50000000000000^6343 ≤ 10704003277627^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3118625153 10000000000 10704003277627 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5640785021/10000000000 : ℝ)^8391 ≤ (11721769090237/25000000000000 : ℝ)^6343 := by
    have hnat : (5640785021 : ℕ)^8391*25000000000000^6343 ≤ 11721769090237^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5640785021 10000000000 11721769090237 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4196499349/10000000000 : ℝ), (3118625153/10000000000 : ℝ), (5640785021/10000000000 : ℝ)] ![(1981557316681/6250000000000 : ℝ), (10704003277627/50000000000000 : ℝ), (11721769090237/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4196499349/10000000000 : ℝ)|^8391 ≤ (1981557316681/6250000000000 : ℝ)^6343
        have hw : |(4196499349/10000000000 : ℝ)|=(4196499349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3118625153/10000000000 : ℝ)|^8391 ≤ (10704003277627/50000000000000 : ℝ)^6343
        have hw : |(3118625153/10000000000 : ℝ)|=(3118625153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5640785021/10000000000 : ℝ)|^8391 ≤ (11721769090237/25000000000000 : ℝ)^6343
        have hw : |(5640785021/10000000000 : ℝ)|=(5640785021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s0_4 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-939597739/5000000000 : ℝ)*x 0 + (4819832177/10000000000 : ℝ)*x 1 + (6008018827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (939597739/5000000000 : ℝ)^8391 ≤ (10953557977847/100000000000000 : ℝ)^6343 := by
    have hnat : (939597739 : ℕ)^8391*100000000000000^6343 ≤ 10953557977847^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939597739 5000000000 10953557977847 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4819832177/10000000000 : ℝ)^8391 ≤ (9519862195729/25000000000000 : ℝ)^6343 := by
    have hnat : (4819832177 : ℕ)^8391*25000000000000^6343 ≤ 9519862195729^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4819832177 10000000000 9519862195729 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6008018827/10000000000 : ℝ)^8391 ≤ (50966993228757/100000000000000 : ℝ)^6343 := by
    have hnat : (6008018827 : ℕ)^8391*100000000000000^6343 ≤ 50966993228757^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6008018827 10000000000 50966993228757 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-939597739/5000000000 : ℝ), (4819832177/10000000000 : ℝ), (6008018827/10000000000 : ℝ)] ![(10953557977847/100000000000000 : ℝ), (9519862195729/25000000000000 : ℝ), (50966993228757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-939597739/5000000000 : ℝ)|^8391 ≤ (10953557977847/100000000000000 : ℝ)^6343
        have hw : |(-939597739/5000000000 : ℝ)|=(939597739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4819832177/10000000000 : ℝ)|^8391 ≤ (9519862195729/25000000000000 : ℝ)^6343
        have hw : |(4819832177/10000000000 : ℝ)|=(4819832177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6008018827/10000000000 : ℝ)|^8391 ≤ (50966993228757/100000000000000 : ℝ)^6343
        have hw : |(6008018827/10000000000 : ℝ)|=(6008018827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s0_5 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (51726463/100000000 : ℝ)*x 0 + (-685887669/5000000000 : ℝ)*x 1 + (600801889/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51726463/100000000 : ℝ)^8391 ≤ (41809755004817/100000000000000 : ℝ)^6343 := by
    have hnat : (51726463 : ℕ)^8391*100000000000000^6343 ≤ 41809755004817^6343*100000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51726463 100000000 41809755004817 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (685887669/5000000000 : ℝ)^8391 ≤ (1805812762491/25000000000000 : ℝ)^6343 := by
    have hnat : (685887669 : ℕ)^8391*25000000000000^6343 ≤ 1805812762491^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685887669 5000000000 1805812762491 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (600801889/1000000000 : ℝ)^8391 ≤ (50966993935753/100000000000000 : ℝ)^6343 := by
    have hnat : (600801889 : ℕ)^8391*100000000000000^6343 ≤ 50966993935753^6343*1000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600801889 1000000000 50966993935753 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(51726463/100000000 : ℝ), (-685887669/5000000000 : ℝ), (600801889/1000000000 : ℝ)] ![(41809755004817/100000000000000 : ℝ), (1805812762491/25000000000000 : ℝ), (50966993935753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(51726463/100000000 : ℝ)|^8391 ≤ (41809755004817/100000000000000 : ℝ)^6343
        have hw : |(51726463/100000000 : ℝ)|=(51726463/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-685887669/5000000000 : ℝ)|^8391 ≤ (1805812762491/25000000000000 : ℝ)^6343
        have hw : |(-685887669/5000000000 : ℝ)|=(685887669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(600801889/1000000000 : ℝ)|^8391 ≤ (50966993935753/100000000000000 : ℝ)^6343
        have hw : |(600801889/1000000000 : ℝ)|=(600801889/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s0_6 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2586323163/5000000000 : ℝ)*x 0 + (150200471/250000000 : ℝ)*x 1 + (-1371775379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586323163/5000000000 : ℝ)^8391 ≤ (1672390211313/4000000000000 : ℝ)^6343 := by
    have hnat : (2586323163 : ℕ)^8391*4000000000000^6343 ≤ 1672390211313^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586323163 5000000000 1672390211313 4000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (150200471/250000000 : ℝ)^8391 ≤ (10193398674929/20000000000000 : ℝ)^6343 := by
    have hnat : (150200471 : ℕ)^8391*20000000000000^6343 ≤ 10193398674929^6343*250000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150200471 250000000 10193398674929 20000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1371775379/10000000000 : ℝ)^8391 ≤ (7223251335561/100000000000000 : ℝ)^6343 := by
    have hnat : (1371775379 : ℕ)^8391*100000000000000^6343 ≤ 7223251335561^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371775379 10000000000 7223251335561 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586323163/5000000000 : ℝ), (150200471/250000000 : ℝ), (-1371775379/10000000000 : ℝ)] ![(1672390211313/4000000000000 : ℝ), (10193398674929/20000000000000 : ℝ), (7223251335561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586323163/5000000000 : ℝ)|^8391 ≤ (1672390211313/4000000000000 : ℝ)^6343
        have hw : |(2586323163/5000000000 : ℝ)|=(2586323163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(150200471/250000000 : ℝ)|^8391 ≤ (10193398674929/20000000000000 : ℝ)^6343
        have hw : |(150200471/250000000 : ℝ)|=(150200471/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1371775379/10000000000 : ℝ)|^8391 ≤ (7223251335561/100000000000000 : ℝ)^6343
        have hw : |(-1371775379/10000000000 : ℝ)|=(1371775379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s0_7 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (420652151/1000000000 : ℝ)*x 0 + (5575781393/10000000000 : ℝ)*x 1 + (79648049/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420652151/1000000000 : ℝ)^8391 ≤ (31805121553117/100000000000000 : ℝ)^6343 := by
    have hnat : (420652151 : ℕ)^8391*100000000000000^6343 ≤ 31805121553117^6343*1000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420652151 1000000000 31805121553117 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5575781393/10000000000 : ℝ)^8391 ≤ (1442926037109/3125000000000 : ℝ)^6343 := by
    have hnat : (5575781393 : ℕ)^8391*3125000000000^6343 ≤ 1442926037109^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5575781393 10000000000 1442926037109 3125000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79648049/250000000 : ℝ)^8391 ≤ (22021245249923/100000000000000 : ℝ)^6343 := by
    have hnat : (79648049 : ℕ)^8391*100000000000000^6343 ≤ 22021245249923^6343*250000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79648049 250000000 22021245249923 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(420652151/1000000000 : ℝ), (5575781393/10000000000 : ℝ), (79648049/250000000 : ℝ)] ![(31805121553117/100000000000000 : ℝ), (1442926037109/3125000000000 : ℝ), (22021245249923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(420652151/1000000000 : ℝ)|^8391 ≤ (31805121553117/100000000000000 : ℝ)^6343
        have hw : |(420652151/1000000000 : ℝ)|=(420652151/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5575781393/10000000000 : ℝ)|^8391 ≤ (1442926037109/3125000000000 : ℝ)^6343
        have hw : |(5575781393/10000000000 : ℝ)|=(5575781393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(79648049/250000000 : ℝ)|^8391 ≤ (22021245249923/100000000000000 : ℝ)^6343
        have hw : |(79648049/250000000 : ℝ)|=(79648049/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1198_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (321/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13801/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4195/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4195 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4195*1^1024 ≤ 0^1024*1^4195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4195 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4195/1024 : ℝ) ≤ (292871601893323287/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4195 ≤ (292871601893323287/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4195*12500000000000000000^1024 ≤ 292871601893323287^1024*5^4195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 292871601893323287 12500000000000000000 4195 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (292871601893323287/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4195 := by
      have hnat : (1 : ℕ)^1024*1^4195 ≤ 1^4195*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12792871601893323287/12500000000000000000 : ℝ) ≤ (2011338475820701/2000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (12792871601893323287/12500000000000000000 : ℝ)^1024 ≤ (2011338475820701/2000000000000000 : ℝ)^4195 := by
      have hnat : (12792871601893323287 : ℕ)^1024*2000000000000000^4195 ≤ 2011338475820701^4195*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12792871601893323287 12500000000000000000 2011338475820701 2000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2011338475820701/2000000000000000 : ℝ)) (X := (12792871601893323287/12500000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6542871601893323287/6250000000000000000 : ℝ) ≤ (1011338475820701/1000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (6542871601893323287/6250000000000000000 : ℝ)^1024 ≤ (1011338475820701/1000000000000000 : ℝ)^4195 := by
      have hnat : (6542871601893323287 : ℕ)^1024*1000000000000000^4195 ≤ 1011338475820701^4195*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6542871601893323287 6250000000000000000 1011338475820701 1000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1011338475820701/1000000000000000 : ℝ)) (X := (6542871601893323287/6250000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11338475820701/800000000000000 : ℝ)*(0 : ℝ))^(4195/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11338475820701/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(292871601893323287/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11338475820701/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4195/1024 : ℝ) := by
    rw [show (1 : ℝ)+(11338475820701/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2011338475820701/2000000000000000 : ℝ) by norm_num, show 1+(292871601893323287/12500000000000000000 : ℝ)+(0 : ℝ)=(12792871601893323287/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(292871601893323287/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11338475820701/800000000000000 : ℝ)*(2/5 : ℝ))^(4195/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11338475820701/800000000000000 : ℝ)*(2/5 : ℝ)=(1011338475820701/1000000000000000 : ℝ) by norm_num, show 1+2*(292871601893323287/12500000000000000000 : ℝ)=(6542871601893323287/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11338475820701/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11338475820701/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11338475820701/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11338475820701/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11338475820701/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11338475820701/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-374842551/2000000000 : ℝ)*X 0 0+(1510369309/2500000000 : ℝ)*X 0 1+(4787513819/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1378409573/2500000000 : ℝ)*X 1 0+(-2592280693/10000000000 : ℝ)*X 1 1+(1196878443/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((86150603/156250000 : ℝ)*X 2 0+(4787513493/10000000000 : ℝ)*X 2 1+(-2592280649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4196499349/10000000000 : ℝ)*X 0 0+(3118625153/10000000000 : ℝ)*X 0 1+(5640785021/10000000000 : ℝ)*X 0 2+(4196499349/10000000000 : ℝ)*X 1 0+(3118625153/10000000000 : ℝ)*X 1 1+(5640785021/10000000000 : ℝ)*X 1 2+(4196499349/10000000000 : ℝ)*X 2 0+(3118625153/10000000000 : ℝ)*X 2 1+(5640785021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-939597739/5000000000 : ℝ)*X 0 0+(4819832177/10000000000 : ℝ)*X 0 1+(6008018827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((51726463/100000000 : ℝ)*X 1 0+(-685887669/5000000000 : ℝ)*X 1 1+(600801889/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2586323163/5000000000 : ℝ)*X 2 0+(150200471/250000000 : ℝ)*X 2 1+(-1371775379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((420652151/1000000000 : ℝ)*X 0 0+(5575781393/10000000000 : ℝ)*X 0 1+(79648049/250000000 : ℝ)*X 0 2+(420652151/1000000000 : ℝ)*X 1 0+(5575781393/10000000000 : ℝ)*X 1 1+(79648049/250000000 : ℝ)*X 1 2+(420652151/1000000000 : ℝ)*X 2 0+(5575781393/10000000000 : ℝ)*X 2 1+(79648049/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33230646572266879450053/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29563939/100000000000000 : ℝ)*(base1) + (792123947/100000000000000 : ℝ)*(base19) + (7688093/1000000000000 : ℝ)*(base23) + (2668227/4000000000000 : ℝ)*(base24) + (49285967/25000000000000 : ℝ)*(upper3) + (596981743927651/100000000000000 : ℝ)*(major0) + (596981743927651/100000000000000 : ℝ)*(major1) + (596981743927651/100000000000000 : ℝ)*(major2) + (398737004841141/50000000000000 : ℝ)*(sp0) + (797474809026141/100000000000000 : ℝ)*(sp1) + (398737382817557/50000000000000 : ℝ)*(sp2) + (396486334731639/100000000000000 : ℝ)*(sp3) + (324206349/20000000000000 : ℝ)*(sp4) + (176455101/12500000000000 : ℝ)*(sp7) + (198243887968193/50000000000000 : ℝ)*(f.failure) + (99684450143761/12500000000000 : ℝ)*(f.sum) + (56249690736649/40000000000000000000000000000 : ℝ)*base66 + (454800026136649/80000000000000000000000000000 : ℝ)*base68 + (346259901656649/80000000000000000000000000000 : ℝ)*base70 + (464750548936649/80000000000000000000000000000 : ℝ)*base72 + (24688831816649/40000000000000000000000000000 : ℝ)*base74 + (501971563976649/80000000000000000000000000000 : ℝ)*base76 + (600280814216649/80000000000000000000000000000 : ℝ)*base78 + (951168168936649/80000000000000000000000000000 : ℝ)*base80 + (188966827583351/40000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (13432079/5000000000000000000000 : ℝ)*base89 + (13432079/5000000000000000000000 : ℝ)*base91 + (13432079/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (69915190608407349133863/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77088051/100000000000000 : ℝ)*(base1) + (851420423/50000000000000 : ℝ)*(base19) + (853097561/50000000000000 : ℝ)*(base23) + (99220977/50000000000000 : ℝ)*(upper3) + (48520917/25000000000000 : ℝ)*(upper5) + (157506685500079/25000000000000 : ℝ)*(major0) + (157506685500079/25000000000000 : ℝ)*(major1) + (157506685500079/25000000000000 : ℝ)*(major2) + (1803828751/50000000000000 : ℝ)*(sp1) + (3594365299/100000000000000 : ℝ)*(sp2) + (420809293255983/50000000000000 : ℝ)*(sp4) + (841613198925567/100000000000000 : ℝ)*(sp5) + (420806604431747/50000000000000 : ℝ)*(sp6) + (52304333054753/12500000000000 : ℝ)*(sp7) + (16737389661043/4000000000000 : ℝ)*(f.failure) + (168323701884783/20000000000000 : ℝ)*(f.sum) + (14641939584621/10000000000000000000000000000 : ℝ)*base66 + (23671777055379/20000000000000000000000000000 : ℝ)*base67 + (208348306895379/20000000000000000000000000000 : ℝ)*base69 + (90853826855379/20000000000000000000000000000 : ℝ)*base71 + (24677993664621/10000000000000000000000000000 : ℝ)*base74 + (13642421055379/20000000000000000000000000000 : ℝ)*base75 + (18445359495379/20000000000000000000000000000 : ℝ)*base77 + (31355750644621/20000000000000000000000000000 : ℝ)*base80 + (42089187705379/10000000000000000000000000000 : ℝ)*base81 + (3114371/400000000000000000000 : ℝ)*base90 + (3114371/400000000000000000000 : ℝ)*base92 + (3114371/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1198_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (321/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13801/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1198_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1198_s1_0 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1037409483/5000000000 : ℝ)*x 0 + (1421700967/2500000000 : ℝ)*x 1 + (5013774001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037409483/5000000000 : ℝ)^8391 ≤ (3121690090107/25000000000000 : ℝ)^6343 := by
    have hnat : (1037409483 : ℕ)^8391*25000000000000^6343 ≤ 3121690090107^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037409483 5000000000 3121690090107 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1421700967/2500000000 : ℝ)^8391 ≤ (23696881183323/50000000000000 : ℝ)^6343 := by
    have hnat : (1421700967 : ℕ)^8391*50000000000000^6343 ≤ 23696881183323^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1421700967 2500000000 23696881183323 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5013774001/10000000000 : ℝ)^8391 ≤ (40119477262139/100000000000000 : ℝ)^6343 := by
    have hnat : (5013774001 : ℕ)^8391*100000000000000^6343 ≤ 40119477262139^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5013774001 10000000000 40119477262139 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1037409483/5000000000 : ℝ), (1421700967/2500000000 : ℝ), (5013774001/10000000000 : ℝ)] ![(3121690090107/25000000000000 : ℝ), (23696881183323/50000000000000 : ℝ), (40119477262139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1037409483/5000000000 : ℝ)|^8391 ≤ (3121690090107/25000000000000 : ℝ)^6343
        have hw : |(-1037409483/5000000000 : ℝ)|=(1037409483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1421700967/2500000000 : ℝ)|^8391 ≤ (23696881183323/50000000000000 : ℝ)^6343
        have hw : |(1421700967/2500000000 : ℝ)|=(1421700967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5013774001/10000000000 : ℝ)|^8391 ≤ (40119477262139/100000000000000 : ℝ)^6343
        have hw : |(5013774001/10000000000 : ℝ)|=(5013774001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s1_1 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5416056457/10000000000 : ℝ)*x 0 + (-2437001613/10000000000 : ℝ)*x 1 + (1253443593/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5416056457/10000000000 : ℝ)^8391 ≤ (44432011799209/100000000000000 : ℝ)^6343 := by
    have hnat : (5416056457 : ℕ)^8391*100000000000000^6343 ≤ 44432011799209^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416056457 10000000000 44432011799209 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2437001613/10000000000 : ℝ)^8391 ≤ (7724253497647/50000000000000 : ℝ)^6343 := by
    have hnat : (2437001613 : ℕ)^8391*50000000000000^6343 ≤ 7724253497647^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2437001613 10000000000 7724253497647 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1253443593/2500000000 : ℝ)^8391 ≤ (20059740594671/50000000000000 : ℝ)^6343 := by
    have hnat : (1253443593 : ℕ)^8391*50000000000000^6343 ≤ 20059740594671^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1253443593 2500000000 20059740594671 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5416056457/10000000000 : ℝ), (-2437001613/10000000000 : ℝ), (1253443593/2500000000 : ℝ)] ![(44432011799209/100000000000000 : ℝ), (7724253497647/50000000000000 : ℝ), (20059740594671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5416056457/10000000000 : ℝ)|^8391 ≤ (44432011799209/100000000000000 : ℝ)^6343
        have hw : |(5416056457/10000000000 : ℝ)|=(5416056457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2437001613/10000000000 : ℝ)|^8391 ≤ (7724253497647/50000000000000 : ℝ)^6343
        have hw : |(-2437001613/10000000000 : ℝ)|=(2437001613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1253443593/2500000000 : ℝ)|^8391 ≤ (20059740594671/50000000000000 : ℝ)^6343
        have hw : |(1253443593/2500000000 : ℝ)|=(1253443593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s1_2 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1354013847/2500000000 : ℝ)*x 0 + (2506887531/5000000000 : ℝ)*x 1 + (-1218501063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1354013847/2500000000 : ℝ)^8391 ≤ (44432000197833/100000000000000 : ℝ)^6343 := by
    have hnat : (1354013847 : ℕ)^8391*100000000000000^6343 ≤ 44432000197833^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354013847 2500000000 44432000197833 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2506887531/5000000000 : ℝ)^8391 ≤ (40119488493307/100000000000000 : ℝ)^6343 := by
    have hnat : (2506887531 : ℕ)^8391*100000000000000^6343 ≤ 40119488493307^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2506887531 5000000000 40119488493307 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1218501063/5000000000 : ℝ)^8391 ≤ (15448511297261/100000000000000 : ℝ)^6343 := by
    have hnat : (1218501063 : ℕ)^8391*100000000000000^6343 ≤ 15448511297261^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1218501063 5000000000 15448511297261 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1354013847/2500000000 : ℝ), (2506887531/5000000000 : ℝ), (-1218501063/5000000000 : ℝ)] ![(44432000197833/100000000000000 : ℝ), (40119488493307/100000000000000 : ℝ), (15448511297261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1354013847/2500000000 : ℝ)|^8391 ≤ (44432000197833/100000000000000 : ℝ)^6343
        have hw : |(1354013847/2500000000 : ℝ)|=(1354013847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2506887531/5000000000 : ℝ)|^8391 ≤ (40119488493307/100000000000000 : ℝ)^6343
        have hw : |(2506887531/5000000000 : ℝ)|=(2506887531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1218501063/5000000000 : ℝ)|^8391 ≤ (15448511297261/100000000000000 : ℝ)^6343
        have hw : |(-1218501063/5000000000 : ℝ)|=(1218501063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s1_3 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4312656859/10000000000 : ℝ)*x 0 + (3687436447/10000000000 : ℝ)*x 1 + (2520567767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312656859/10000000000 : ℝ)^8391 ≤ (32871001963581/100000000000000 : ℝ)^6343 := by
    have hnat : (4312656859 : ℕ)^8391*100000000000000^6343 ≤ 32871001963581^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312656859 10000000000 32871001963581 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3687436447/10000000000 : ℝ)^8391 ≤ (13359815814389/50000000000000 : ℝ)^6343 := by
    have hnat : (3687436447 : ℕ)^8391*50000000000000^6343 ≤ 13359815814389^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3687436447 10000000000 13359815814389 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2520567767/5000000000 : ℝ)^8391 ≤ (40409366389719/100000000000000 : ℝ)^6343 := by
    have hnat : (2520567767 : ℕ)^8391*100000000000000^6343 ≤ 40409366389719^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2520567767 5000000000 40409366389719 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312656859/10000000000 : ℝ), (3687436447/10000000000 : ℝ), (2520567767/5000000000 : ℝ)] ![(32871001963581/100000000000000 : ℝ), (13359815814389/50000000000000 : ℝ), (40409366389719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312656859/10000000000 : ℝ)|^8391 ≤ (32871001963581/100000000000000 : ℝ)^6343
        have hw : |(4312656859/10000000000 : ℝ)|=(4312656859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3687436447/10000000000 : ℝ)|^8391 ≤ (13359815814389/50000000000000 : ℝ)^6343
        have hw : |(3687436447/10000000000 : ℝ)|=(3687436447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2520567767/5000000000 : ℝ)|^8391 ≤ (40409366389719/100000000000000 : ℝ)^6343
        have hw : |(2520567767/5000000000 : ℝ)|=(2520567767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s1_4 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1037774511/5000000000 : ℝ)*x 0 + (2511383917/5000000000 : ℝ)*x 1 + (1135527271/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037774511/5000000000 : ℝ)^8391 ≤ (6246286473399/50000000000000 : ℝ)^6343 := by
    have hnat : (1037774511 : ℕ)^8391*50000000000000^6343 ≤ 6246286473399^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037774511 5000000000 6246286473399 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2511383917/5000000000 : ℝ)^8391 ≤ (20107354316869/50000000000000 : ℝ)^6343 := by
    have hnat : (2511383917 : ℕ)^8391*50000000000000^6343 ≤ 20107354316869^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2511383917 5000000000 20107354316869 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1135527271/2000000000 : ℝ)^8391 ≤ (15133669887/32000000000 : ℝ)^6343 := by
    have hnat : (1135527271 : ℕ)^8391*32000000000^6343 ≤ 15133669887^6343*2000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135527271 2000000000 15133669887 32000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1037774511/5000000000 : ℝ), (2511383917/5000000000 : ℝ), (1135527271/2000000000 : ℝ)] ![(6246286473399/50000000000000 : ℝ), (20107354316869/50000000000000 : ℝ), (15133669887/32000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1037774511/5000000000 : ℝ)|^8391 ≤ (6246286473399/50000000000000 : ℝ)^6343
        have hw : |(-1037774511/5000000000 : ℝ)|=(1037774511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2511383917/5000000000 : ℝ)|^8391 ≤ (20107354316869/50000000000000 : ℝ)^6343
        have hw : |(2511383917/5000000000 : ℝ)|=(2511383917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1135527271/2000000000 : ℝ)|^8391 ≤ (15133669887/32000000000 : ℝ)^6343
        have hw : |(1135527271/2000000000 : ℝ)|=(1135527271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s1_5 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2621513551/5000000000 : ℝ)*x 0 + (-221642557/1250000000 : ℝ)*x 1 + (2838817831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2621513551/5000000000 : ℝ)^8391 ≤ (8512791536453/20000000000000 : ℝ)^6343 := by
    have hnat : (2621513551 : ℕ)^8391*20000000000000^6343 ≤ 8512791536453^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621513551 5000000000 8512791536453 20000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221642557/1250000000 : ℝ)^8391 ≤ (63395822113/625000000000 : ℝ)^6343 := by
    have hnat : (221642557 : ℕ)^8391*625000000000^6343 ≤ 63395822113^6343*1250000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221642557 1250000000 63395822113 625000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2838817831/5000000000 : ℝ)^8391 ≤ (23646355380323/50000000000000 : ℝ)^6343 := by
    have hnat : (2838817831 : ℕ)^8391*50000000000000^6343 ≤ 23646355380323^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2838817831 5000000000 23646355380323 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2621513551/5000000000 : ℝ), (-221642557/1250000000 : ℝ), (2838817831/5000000000 : ℝ)] ![(8512791536453/20000000000000 : ℝ), (63395822113/625000000000 : ℝ), (23646355380323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2621513551/5000000000 : ℝ)|^8391 ≤ (8512791536453/20000000000000 : ℝ)^6343
        have hw : |(2621513551/5000000000 : ℝ)|=(2621513551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-221642557/1250000000 : ℝ)|^8391 ≤ (63395822113/625000000000 : ℝ)^6343
        have hw : |(-221642557/1250000000 : ℝ)|=(221642557/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2838817831/5000000000 : ℝ)|^8391 ≤ (23646355380323/50000000000000 : ℝ)^6343
        have hw : |(2838817831/5000000000 : ℝ)|=(2838817831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s1_6 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1310756781/2500000000 : ℝ)*x 0 + (2838818119/5000000000 : ℝ)*x 1 + (-1773139587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1310756781/2500000000 : ℝ)^8391 ≤ (42563957918531/100000000000000 : ℝ)^6343 := by
    have hnat : (1310756781 : ℕ)^8391*100000000000000^6343 ≤ 42563957918531^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310756781 2500000000 42563957918531 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2838818119/5000000000 : ℝ)^8391 ≤ (47292717107641/100000000000000 : ℝ)^6343 := by
    have hnat : (2838818119 : ℕ)^8391*100000000000000^6343 ≤ 47292717107641^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2838818119 5000000000 47292717107641 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1773139587/10000000000 : ℝ)^8391 ≤ (5071662480931/50000000000000 : ℝ)^6343 := by
    have hnat : (1773139587 : ℕ)^8391*50000000000000^6343 ≤ 5071662480931^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1773139587 10000000000 5071662480931 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1310756781/2500000000 : ℝ), (2838818119/5000000000 : ℝ), (-1773139587/10000000000 : ℝ)] ![(42563957918531/100000000000000 : ℝ), (47292717107641/100000000000000 : ℝ), (5071662480931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1310756781/2500000000 : ℝ)|^8391 ≤ (42563957918531/100000000000000 : ℝ)^6343
        have hw : |(1310756781/2500000000 : ℝ)|=(1310756781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2838818119/5000000000 : ℝ)|^8391 ≤ (47292717107641/100000000000000 : ℝ)^6343
        have hw : |(2838818119/5000000000 : ℝ)|=(2838818119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1773139587/10000000000 : ℝ)|^8391 ≤ (5071662480931/50000000000000 : ℝ)^6343
        have hw : |(-1773139587/10000000000 : ℝ)|=(1773139587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s1_7 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (67408217/156250000 : ℝ)*x 0 + (5023045293/10000000000 : ℝ)*x 1 + (741175347/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67408217/156250000 : ℝ)^8391 ≤ (16442907452351/50000000000000 : ℝ)^6343 := by
    have hnat : (67408217 : ℕ)^8391*50000000000000^6343 ≤ 16442907452351^6343*156250000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67408217 156250000 16442907452351 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5023045293/10000000000 : ℝ)^8391 ≤ (5027205923711/12500000000000 : ℝ)^6343 := by
    have hnat : (5023045293 : ℕ)^8391*12500000000000^6343 ≤ 5027205923711^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5023045293 10000000000 5027205923711 12500000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (741175347/2000000000 : ℝ)^8391 ≤ (13448268844861/50000000000000 : ℝ)^6343 := by
    have hnat : (741175347 : ℕ)^8391*50000000000000^6343 ≤ 13448268844861^6343*2000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741175347 2000000000 13448268844861 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67408217/156250000 : ℝ), (5023045293/10000000000 : ℝ), (741175347/2000000000 : ℝ)] ![(16442907452351/50000000000000 : ℝ), (5027205923711/12500000000000 : ℝ), (13448268844861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67408217/156250000 : ℝ)|^8391 ≤ (16442907452351/50000000000000 : ℝ)^6343
        have hw : |(67408217/156250000 : ℝ)|=(67408217/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5023045293/10000000000 : ℝ)|^8391 ≤ (5027205923711/12500000000000 : ℝ)^6343
        have hw : |(5023045293/10000000000 : ℝ)|=(5023045293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(741175347/2000000000 : ℝ)|^8391 ≤ (13448268844861/50000000000000 : ℝ)^6343
        have hw : |(741175347/2000000000 : ℝ)|=(741175347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1198_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13801/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (321/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5957/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5047/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13801/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (321/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13801/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (321/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13801/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (321/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13801/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (321/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13801/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (321/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13801/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (321/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (321/50000 : ℝ) ^ (4195/1024 : ℝ) ≤ (3258541869/3125000000000000000 : ℝ) := by
    have hpowers : (321/50000 : ℝ)^4195 ≤ (3258541869/3125000000000000000 : ℝ)^1024 := by
      have hnat : (321 : ℕ)^4195*3125000000000000000^1024 ≤ 3258541869^1024*50000^4195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        321 50000 3258541869 3125000000000000000 4195 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (321/50000 : ℝ)) (X := (3258541869/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13801/50000 : ℝ) ^ (4195/1024 : ℝ) ≤ (512522001386467303/100000000000000000000 : ℝ) := by
    have hpowers : (13801/50000 : ℝ)^4195 ≤ (512522001386467303/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13801 : ℕ)^4195*100000000000000000000^1024 ≤ 512522001386467303^1024*50000^4195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13801 50000 512522001386467303 100000000000000000000 4195 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13801/50000 : ℝ)) (X := (512522001386467303/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562500003258541869/1562500000000000000 : ℝ) ≤ (10000000005090627/10000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (1562500003258541869/1562500000000000000 : ℝ)^1024 ≤ (10000000005090627/10000000000000000 : ℝ)^4195 := by
      have hnat : (1562500003258541869 : ℕ)^1024*10000000000000000^4195 ≤ 10000000005090627^4195*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562500003258541869 1562500000000000000 10000000005090627 10000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000005090627/10000000000000000 : ℝ)) (X := (1562500003258541869/1562500000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100512522105659807111/100000000000000000000 : ℝ) ≤ (2503121627254279/2500000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (100512522105659807111/100000000000000000000 : ℝ)^1024 ≤ (2503121627254279/2500000000000000 : ℝ)^4195 := by
      have hnat : (100512522105659807111 : ℕ)^1024*2500000000000000^4195 ≤ 2503121627254279^4195*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100512522105659807111 100000000000000000000 2503121627254279 2500000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503121627254279/2500000000000000 : ℝ)) (X := (100512522105659807111/100000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50512522001386467303/50000000000000000000 : ℝ) ≤ (2004994602588721/2000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (50512522001386467303/50000000000000000000 : ℝ)^1024 ≤ (2004994602588721/2000000000000000 : ℝ)^4195 := by
      have hnat : (50512522001386467303 : ℕ)^1024*2000000000000000^4195 ≤ 2004994602588721^4195*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50512522001386467303 50000000000000000000 2004994602588721 2000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2004994602588721/2000000000000000 : ℝ)) (X := (50512522001386467303/50000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3258541869/3125000000000000000 : ℝ) ≤ ((67395991866550423011/67400000000000000000 : ℝ)+2*(12486503926489/2696000000000000 : ℝ)*(321/50000 : ℝ))^(4195/1024 : ℝ) := by
    rw [show (67395991866550423011/67400000000000000000 : ℝ)+2*(12486503926489/2696000000000000 : ℝ)*(321/50000 : ℝ)=(10000000005090627/10000000000000000 : ℝ) by norm_num, show 1+2*(3258541869/3125000000000000000 : ℝ)=(1562500003258541869/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(512522001386467303/100000000000000000000 : ℝ)+(3258541869/3125000000000000000 : ℝ) ≤ ((67395991866550423011/67400000000000000000 : ℝ)+(12486503926489/2696000000000000 : ℝ)*((13801/50000 : ℝ)+(321/50000 : ℝ)))^(4195/1024 : ℝ) := by
    rw [show (67395991866550423011/67400000000000000000 : ℝ)+(12486503926489/2696000000000000 : ℝ)*((13801/50000 : ℝ)+(321/50000 : ℝ))=(2503121627254279/2500000000000000 : ℝ) by norm_num, show 1+(512522001386467303/100000000000000000000 : ℝ)+(3258541869/3125000000000000000 : ℝ)=(100512522105659807111/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(512522001386467303/100000000000000000000 : ℝ) ≤ ((67395991866550423011/67400000000000000000 : ℝ)+2*(12486503926489/2696000000000000 : ℝ)*(13801/50000 : ℝ))^(4195/1024 : ℝ) := by
    rw [show (67395991866550423011/67400000000000000000 : ℝ)+2*(12486503926489/2696000000000000 : ℝ)*(13801/50000 : ℝ)=(2004994602588721/2000000000000000 : ℝ) by norm_num, show 1+2*(512522001386467303/100000000000000000000 : ℝ)=(50512522001386467303/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (67395991866550423011/67400000000000000000 : ℝ)*(X 1 0+X 2 0)+(12486503926489/2696000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (321/50000 : ℝ)) (hi := (13801/50000 : ℝ)) (c := (67395991866550423011/67400000000000000000 : ℝ)) (alpha := (12486503926489/2696000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (67395991866550423011/67400000000000000000 : ℝ)*(X 0 1+X 2 1)+(12486503926489/2696000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (321/50000 : ℝ)) (hi := (13801/50000 : ℝ)) (c := (67395991866550423011/67400000000000000000 : ℝ)) (alpha := (12486503926489/2696000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (67395991866550423011/67400000000000000000 : ℝ)*(X 0 2+X 1 2)+(12486503926489/2696000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (321/50000 : ℝ)) (hi := (13801/50000 : ℝ)) (c := (67395991866550423011/67400000000000000000 : ℝ)) (alpha := (12486503926489/2696000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1037409483/5000000000 : ℝ)*X 0 0+(1421700967/2500000000 : ℝ)*X 0 1+(5013774001/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5416056457/10000000000 : ℝ)*X 1 0+(-2437001613/10000000000 : ℝ)*X 1 1+(1253443593/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1354013847/2500000000 : ℝ)*X 2 0+(2506887531/5000000000 : ℝ)*X 2 1+(-1218501063/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4312656859/10000000000 : ℝ)*X 0 0+(3687436447/10000000000 : ℝ)*X 0 1+(2520567767/5000000000 : ℝ)*X 0 2+(4312656859/10000000000 : ℝ)*X 1 0+(3687436447/10000000000 : ℝ)*X 1 1+(2520567767/5000000000 : ℝ)*X 1 2+(4312656859/10000000000 : ℝ)*X 2 0+(3687436447/10000000000 : ℝ)*X 2 1+(2520567767/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1037774511/5000000000 : ℝ)*X 0 0+(2511383917/5000000000 : ℝ)*X 0 1+(1135527271/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2621513551/5000000000 : ℝ)*X 1 0+(-221642557/1250000000 : ℝ)*X 1 1+(2838817831/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1310756781/2500000000 : ℝ)*X 2 0+(2838818119/5000000000 : ℝ)*X 2 1+(-1773139587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((67408217/156250000 : ℝ)*X 0 0+(5023045293/10000000000 : ℝ)*X 0 1+(741175347/2000000000 : ℝ)*X 0 2+(67408217/156250000 : ℝ)*X 1 0+(5023045293/10000000000 : ℝ)*X 1 1+(741175347/2000000000 : ℝ)*X 1 2+(67408217/156250000 : ℝ)*X 2 0+(5023045293/10000000000 : ℝ)*X 2 1+(741175347/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11048695657104362159244109341/1685000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (825148609/50000000000000 : ℝ)*(base19) + (331427469/25000000000000 : ℝ)*(base23) + (327518917/100000000000000 : ℝ)*(upper3) + (16962401/100000000000000 : ℝ)*(upper4) + (18750419/50000000000000 : ℝ)*(upper5) + (1112282478233823/100000000000000 : ℝ)*(major0) + (1112282478233823/100000000000000 : ℝ)*(major1) + (1112282478233823/100000000000000 : ℝ)*(major2) + (742914829049927/50000000000000 : ℝ)*(sp0) + (297167259979913/20000000000000 : ℝ)*(sp1) + (742918312243453/50000000000000 : ℝ)*(sp2) + (147744224950963/20000000000000 : ℝ)*(sp3) + (829209693/10000000000000 : ℝ)*(sp4) + (1132589279/20000000000000 : ℝ)*(sp7) + (73872678770121/10000000000000 : ℝ)*(f.failure) + (1485837950196783/100000000000000 : ℝ)*(f.sum) + (431890791886647/134800000000000000000000000000 : ℝ)*base65 + (27258913224926123947/6740000000000000000000000000000000 : ℝ)*base68 + (14704956243893876053/6740000000000000000000000000000000 : ℝ)*base69 + (50624852679753876053/6740000000000000000000000000000000 : ℝ)*base71 + (162003805848553/134800000000000000000000000000 : ℝ)*base74 + (20285931177653876053/6740000000000000000000000000000000 : ℝ)*base75 + (33727616582733876053/6740000000000000000000000000000000 : ℝ)*base77 + (79389769667873876053/6740000000000000000000000000000000 : ℝ)*base79 + (229894615148247/134800000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (22137/1000000000000000000000 : ℝ)*base90 + (22137/1000000000000000000000 : ℝ)*base92 + (22137/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (837006678702403386033259707/168500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28150679/100000000000000 : ℝ)*(base1) + (622630527/50000000000000 : ℝ)*(base19) + (651082577/50000000000000 : ℝ)*(base23) + (63249999/100000000000000 : ℝ)*(upper3) + (27063969/20000000000000 : ℝ)*(upper5) + (57155730448221/5000000000000 : ℝ)*(major0) + (57155730448221/5000000000000 : ℝ)*(major1) + (57155730448221/5000000000000 : ℝ)*(major2) + (2660129759/50000000000000 : ℝ)*(sp1) + (6850420043/100000000000000 : ℝ)*(sp2) + (305405002353479/20000000000000 : ℝ)*(sp4) + (1527018418096143/100000000000000 : ℝ)*(sp5) + (763508415515759/50000000000000 : ℝ)*(sp6) + (759204040581483/100000000000000 : ℝ)*(sp7) + (379602034366081/50000000000000 : ℝ)*(f.failure) + (381756245904179/25000000000000 : ℝ)*(f.sum) + (13959556176291/6740000000000000000000000000 : ℝ)*base66 + (2132879295978861569/337000000000000000000000000000000 : ℝ)*base68 + (2185485452324138431/337000000000000000000000000000000 : ℝ)*base69 + (20470710957861569/337000000000000000000000000000000 : ℝ)*base72 + (50157747710911/6740000000000000000000000000 : ℝ)*base74 + (3289740383155138431/337000000000000000000000000000000 : ℝ)*base75 + (870570565494138431/337000000000000000000000000000000 : ℝ)*base77 + (482461600781138431/337000000000000000000000000000000 : ℝ)*base79 + (5404535894529/6740000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4065743/5000000000000000000000 : ℝ)*base89 + (4065743/5000000000000000000000 : ℝ)*base91 + (4065743/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1198_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13801/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (321/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5957/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5047/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1198_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1198_s2_0 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2125102683/10000000000 : ℝ)*x 0 + (1375118723/2500000000 : ℝ)*x 1 + (2584037811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125102683/10000000000 : ℝ)^8391 ≤ (12888646140293/100000000000000 : ℝ)^6343 := by
    have hnat : (2125102683 : ℕ)^8391*100000000000000^6343 ≤ 12888646140293^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125102683 10000000000 12888646140293 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1375118723/2500000000 : ℝ)^8391 ≤ (45350464353217/100000000000000 : ℝ)^6343 := by
    have hnat : (1375118723 : ℕ)^8391*100000000000000^6343 ≤ 45350464353217^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375118723 2500000000 45350464353217 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2584037811/5000000000 : ℝ)^8391 ≤ (2088044474339/5000000000000 : ℝ)^6343 := by
    have hnat : (2584037811 : ℕ)^8391*5000000000000^6343 ≤ 2088044474339^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584037811 5000000000 2088044474339 5000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2125102683/10000000000 : ℝ), (1375118723/2500000000 : ℝ), (2584037811/5000000000 : ℝ)] ![(12888646140293/100000000000000 : ℝ), (45350464353217/100000000000000 : ℝ), (2088044474339/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2125102683/10000000000 : ℝ)|^8391 ≤ (12888646140293/100000000000000 : ℝ)^6343
        have hw : |(-2125102683/10000000000 : ℝ)|=(2125102683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1375118723/2500000000 : ℝ)|^8391 ≤ (45350464353217/100000000000000 : ℝ)^6343
        have hw : |(1375118723/2500000000 : ℝ)|=(1375118723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2584037811/5000000000 : ℝ)|^8391 ≤ (2088044474339/5000000000000 : ℝ)^6343
        have hw : |(2584037811/5000000000 : ℝ)|=(2584037811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s2_1 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5371493907/10000000000 : ℝ)*x 0 + (-459509997/2000000000 : ℝ)*x 1 + (646010001/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371493907/10000000000 : ℝ)^8391 ≤ (8789807613373/20000000000000 : ℝ)^6343 := by
    have hnat : (5371493907 : ℕ)^8391*20000000000000^6343 ≤ 8789807613373^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371493907 10000000000 8789807613373 20000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (459509997/2000000000 : ℝ)^8391 ≤ (1786253192947/12500000000000 : ℝ)^6343 := by
    have hnat : (459509997 : ℕ)^8391*12500000000000^6343 ≤ 1786253192947^6343*2000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459509997 2000000000 1786253192947 12500000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (646010001/1250000000 : ℝ)^8391 ≤ (10440234092801/25000000000000 : ℝ)^6343 := by
    have hnat : (646010001 : ℕ)^8391*25000000000000^6343 ≤ 10440234092801^6343*1250000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646010001 1250000000 10440234092801 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371493907/10000000000 : ℝ), (-459509997/2000000000 : ℝ), (646010001/1250000000 : ℝ)] ![(8789807613373/20000000000000 : ℝ), (1786253192947/12500000000000 : ℝ), (10440234092801/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371493907/10000000000 : ℝ)|^8391 ≤ (8789807613373/20000000000000 : ℝ)^6343
        have hw : |(5371493907/10000000000 : ℝ)|=(5371493907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-459509997/2000000000 : ℝ)|^8391 ≤ (1786253192947/12500000000000 : ℝ)^6343
        have hw : |(-459509997/2000000000 : ℝ)|=(459509997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(646010001/1250000000 : ℝ)|^8391 ≤ (10440234092801/25000000000000 : ℝ)^6343
        have hw : |(646010001/1250000000 : ℝ)|=(646010001/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s2_2 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2685747889/5000000000 : ℝ)*x 0 + (1292019349/2500000000 : ℝ)*x 1 + (-2297550919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685747889/5000000000 : ℝ)^8391 ≤ (8789811663579/20000000000000 : ℝ)^6343 := by
    have hnat : (2685747889 : ℕ)^8391*20000000000000^6343 ≤ 8789811663579^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685747889 5000000000 8789811663579 20000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1292019349/2500000000 : ℝ)^8391 ≤ (2610056778129/6250000000000 : ℝ)^6343 := by
    have hnat : (1292019349 : ℕ)^8391*6250000000000^6343 ≤ 2610056778129^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292019349 2500000000 2610056778129 6250000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2297550919/10000000000 : ℝ)^8391 ≤ (35725083071/250000000000 : ℝ)^6343 := by
    have hnat : (2297550919 : ℕ)^8391*250000000000^6343 ≤ 35725083071^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2297550919 10000000000 35725083071 250000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685747889/5000000000 : ℝ), (1292019349/2500000000 : ℝ), (-2297550919/10000000000 : ℝ)] ![(8789811663579/20000000000000 : ℝ), (2610056778129/6250000000000 : ℝ), (35725083071/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685747889/5000000000 : ℝ)|^8391 ≤ (8789811663579/20000000000000 : ℝ)^6343
        have hw : |(2685747889/5000000000 : ℝ)|=(2685747889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1292019349/2500000000 : ℝ)|^8391 ≤ (2610056778129/6250000000000 : ℝ)^6343
        have hw : |(1292019349/2500000000 : ℝ)|=(1292019349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2297550919/10000000000 : ℝ)|^8391 ≤ (35725083071/250000000000 : ℝ)^6343
        have hw : |(-2297550919/10000000000 : ℝ)|=(2297550919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s2_3 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4347286821/10000000000 : ℝ)*x 0 + (805115451/2000000000 : ℝ)*x 1 + (234707229/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347286821/10000000000 : ℝ)^8391 ≤ (33220625504669/100000000000000 : ℝ)^6343 := by
    have hnat : (4347286821 : ℕ)^8391*100000000000000^6343 ≤ 33220625504669^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347286821 10000000000 33220625504669 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (805115451/2000000000 : ℝ)^8391 ≤ (30007983903201/100000000000000 : ℝ)^6343 := by
    have hnat : (805115451 : ℕ)^8391*100000000000000^6343 ≤ 30007983903201^6343*2000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805115451 2000000000 30007983903201 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (234707229/500000000 : ℝ)^8391 ≤ (36771390568587/100000000000000 : ℝ)^6343 := by
    have hnat : (234707229 : ℕ)^8391*100000000000000^6343 ≤ 36771390568587^6343*500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234707229 500000000 36771390568587 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347286821/10000000000 : ℝ), (805115451/2000000000 : ℝ), (234707229/500000000 : ℝ)] ![(33220625504669/100000000000000 : ℝ), (30007983903201/100000000000000 : ℝ), (36771390568587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347286821/10000000000 : ℝ)|^8391 ≤ (33220625504669/100000000000000 : ℝ)^6343
        have hw : |(4347286821/10000000000 : ℝ)|=(4347286821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(805115451/2000000000 : ℝ)|^8391 ≤ (30007983903201/100000000000000 : ℝ)^6343
        have hw : |(805115451/2000000000 : ℝ)|=(805115451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(234707229/500000000 : ℝ)|^8391 ≤ (36771390568587/100000000000000 : ℝ)^6343
        have hw : |(234707229/500000000 : ℝ)|=(234707229/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s2_4 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2125189759/10000000000 : ℝ)*x 0 + (5170280711/10000000000 : ℝ)*x 1 + (5498249391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125189759/10000000000 : ℝ)^8391 ≤ (6444672385551/50000000000000 : ℝ)^6343 := by
    have hnat : (2125189759 : ℕ)^8391*50000000000000^6343 ≤ 6444672385551^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125189759 10000000000 6444672385551 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5170280711/10000000000 : ℝ)^8391 ≤ (8356892508947/20000000000000 : ℝ)^6343 := by
    have hnat : (5170280711 : ℕ)^8391*20000000000000^6343 ≤ 8356892508947^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170280711 10000000000 8356892508947 20000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5498249391/10000000000 : ℝ)^8391 ≤ (45326192665021/100000000000000 : ℝ)^6343 := by
    have hnat : (5498249391 : ℕ)^8391*100000000000000^6343 ≤ 45326192665021^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498249391 10000000000 45326192665021 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2125189759/10000000000 : ℝ), (5170280711/10000000000 : ℝ), (5498249391/10000000000 : ℝ)] ![(6444672385551/50000000000000 : ℝ), (8356892508947/20000000000000 : ℝ), (45326192665021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2125189759/10000000000 : ℝ)|^8391 ≤ (6444672385551/50000000000000 : ℝ)^6343
        have hw : |(-2125189759/10000000000 : ℝ)|=(2125189759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5170280711/10000000000 : ℝ)|^8391 ≤ (8356892508947/20000000000000 : ℝ)^6343
        have hw : |(5170280711/10000000000 : ℝ)|=(5170280711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5498249391/10000000000 : ℝ)|^8391 ≤ (45326192665021/100000000000000 : ℝ)^6343
        have hw : |(5498249391/10000000000 : ℝ)|=(5498249391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s2_5 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2643423143/5000000000 : ℝ)*x 0 + (-98368947/500000000 : ℝ)*x 1 + (549824941/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643423143/5000000000 : ℝ)^8391 ≤ (537939774613/1250000000000 : ℝ)^6343 := by
    have hnat : (2643423143 : ℕ)^8391*1250000000000^6343 ≤ 537939774613^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643423143 5000000000 537939774613 1250000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98368947/500000000 : ℝ)^8391 ≤ (11638625141987/100000000000000 : ℝ)^6343 := by
    have hnat : (98368947 : ℕ)^8391*100000000000000^6343 ≤ 11638625141987^6343*500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98368947 500000000 11638625141987 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549824941/1000000000 : ℝ)^8391 ≤ (1813047714889/4000000000000 : ℝ)^6343 := by
    have hnat : (549824941 : ℕ)^8391*4000000000000^6343 ≤ 1813047714889^6343*1000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549824941 1000000000 1813047714889 4000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643423143/5000000000 : ℝ), (-98368947/500000000 : ℝ), (549824941/1000000000 : ℝ)] ![(537939774613/1250000000000 : ℝ), (11638625141987/100000000000000 : ℝ), (1813047714889/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643423143/5000000000 : ℝ)|^8391 ≤ (537939774613/1250000000000 : ℝ)^6343
        have hw : |(2643423143/5000000000 : ℝ)|=(2643423143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-98368947/500000000 : ℝ)|^8391 ≤ (11638625141987/100000000000000 : ℝ)^6343
        have hw : |(-98368947/500000000 : ℝ)|=(98368947/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(549824941/1000000000 : ℝ)|^8391 ≤ (1813047714889/4000000000000 : ℝ)^6343
        have hw : |(549824941/1000000000 : ℝ)|=(549824941/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s2_6 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5286846457/10000000000 : ℝ)*x 0 + (5498249427/10000000000 : ℝ)*x 1 + (-983689341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286846457/10000000000 : ℝ)^8391 ≤ (8607036762083/20000000000000 : ℝ)^6343 := by
    have hnat : (5286846457 : ℕ)^8391*20000000000000^6343 ≤ 8607036762083^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286846457 10000000000 8607036762083 20000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5498249427/10000000000 : ℝ)^8391 ≤ (22663096528809/50000000000000 : ℝ)^6343 := by
    have hnat : (5498249427 : ℕ)^8391*50000000000000^6343 ≤ 22663096528809^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498249427 10000000000 22663096528809 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (983689341/5000000000 : ℝ)^8391 ≤ (11638623122913/100000000000000 : ℝ)^6343 := by
    have hnat : (983689341 : ℕ)^8391*100000000000000^6343 ≤ 11638623122913^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983689341 5000000000 11638623122913 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286846457/10000000000 : ℝ), (5498249427/10000000000 : ℝ), (-983689341/5000000000 : ℝ)] ![(8607036762083/20000000000000 : ℝ), (22663096528809/50000000000000 : ℝ), (11638623122913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286846457/10000000000 : ℝ)|^8391 ≤ (8607036762083/20000000000000 : ℝ)^6343
        have hw : |(5286846457/10000000000 : ℝ)|=(5286846457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5498249427/10000000000 : ℝ)|^8391 ≤ (22663096528809/50000000000000 : ℝ)^6343
        have hw : |(5498249427/10000000000 : ℝ)|=(5498249427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-983689341/5000000000 : ℝ)|^8391 ≤ (11638623122913/100000000000000 : ℝ)^6343
        have hw : |(-983689341/5000000000 : ℝ)|=(983689341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s2_7 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4347464287/10000000000 : ℝ)*x 0 + (4689712109/10000000000 : ℝ)*x 1 + (2015025861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347464287/10000000000 : ℝ)^8391 ≤ (4152802440203/12500000000000 : ℝ)^6343 := by
    have hnat : (4347464287 : ℕ)^8391*12500000000000^6343 ≤ 4152802440203^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347464287 10000000000 4152802440203 12500000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4689712109/10000000000 : ℝ)^8391 ≤ (36725465238959/100000000000000 : ℝ)^6343 := by
    have hnat : (4689712109 : ℕ)^8391*100000000000000^6343 ≤ 36725465238959^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4689712109 10000000000 36725465238959 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015025861/5000000000 : ℝ)^8391 ≤ (30052115218841/100000000000000 : ℝ)^6343 := by
    have hnat : (2015025861 : ℕ)^8391*100000000000000^6343 ≤ 30052115218841^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015025861 5000000000 30052115218841 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347464287/10000000000 : ℝ), (4689712109/10000000000 : ℝ), (2015025861/5000000000 : ℝ)] ![(4152802440203/12500000000000 : ℝ), (36725465238959/100000000000000 : ℝ), (30052115218841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347464287/10000000000 : ℝ)|^8391 ≤ (4152802440203/12500000000000 : ℝ)^6343
        have hw : |(4347464287/10000000000 : ℝ)|=(4347464287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4689712109/10000000000 : ℝ)|^8391 ≤ (36725465238959/100000000000000 : ℝ)^6343
        have hw : |(4689712109/10000000000 : ℝ)|=(4689712109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2015025861/5000000000 : ℝ)|^8391 ≤ (30052115218841/100000000000000 : ℝ)^6343
        have hw : |(2015025861/5000000000 : ℝ)|=(2015025861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1198_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5047/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5957/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2329/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16341/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5047/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5957/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5047/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5957/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5047/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5957/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5047/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5957/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5047/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5957/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5047/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5957/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5957/100000 : ℝ) ^ (4195/1024 : ℝ) ≤ (958694976223421/100000000000000000000 : ℝ) := by
    have hpowers : (5957/100000 : ℝ)^4195 ≤ (958694976223421/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5957 : ℕ)^4195*100000000000000000000^1024 ≤ 958694976223421^1024*100000^4195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5957 100000 958694976223421 100000000000000000000 4195 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5957/100000 : ℝ)) (X := (958694976223421/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5047/25000 : ℝ) ^ (4195/1024 : ℝ) ≤ (14229505939317249/10000000000000000000 : ℝ) := by
    have hpowers : (5047/25000 : ℝ)^4195 ≤ (14229505939317249/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5047 : ℕ)^4195*10000000000000000000^1024 ≤ 14229505939317249^1024*25000^4195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5047 25000 14229505939317249 10000000000000000000 4195 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5047/25000 : ℝ)) (X := (14229505939317249/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000958694976223421/50000000000000000000 : ℝ) ≤ (5000023401586211/5000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (50000958694976223421/50000000000000000000 : ℝ)^1024 ≤ (5000023401586211/5000000000000000 : ℝ)^4195 := by
      have hnat : (50000958694976223421 : ℕ)^1024*5000000000000000^4195 ≤ 5000023401586211^4195*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000958694976223421 50000000000000000000 5000023401586211 5000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000023401586211/5000000000000000 : ℝ)) (X := (50000958694976223421/50000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100143253754369395911/100000000000000000000 : ℝ) ≤ (5001747467079933/5000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (100143253754369395911/100000000000000000000 : ℝ)^1024 ≤ (5001747467079933/5000000000000000 : ℝ)^4195 := by
      have hnat : (100143253754369395911 : ℕ)^1024*5000000000000000^4195 ≤ 5001747467079933^4195*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100143253754369395911 100000000000000000000 5001747467079933 5000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001747467079933/5000000000000000 : ℝ)) (X := (100143253754369395911/100000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5014229505939317249/5000000000000000000 : ℝ) ≤ (1000694306514731/1000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (5014229505939317249/5000000000000000000 : ℝ)^1024 ≤ (1000694306514731/1000000000000000 : ℝ)^4195 := by
      have hnat : (5014229505939317249 : ℕ)^1024*1000000000000000^4195 ≤ 1000694306514731^4195*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5014229505939317249 5000000000000000000 1000694306514731 1000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000694306514731/1000000000000000 : ℝ)) (X := (5014229505939317249/5000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(958694976223421/100000000000000000000 : ℝ) ≤ ((10162113215954452119/10165000000000000000 : ℝ)+2*(862032746861/355775000000000 : ℝ)*(5957/100000 : ℝ))^(4195/1024 : ℝ) := by
    rw [show (10162113215954452119/10165000000000000000 : ℝ)+2*(862032746861/355775000000000 : ℝ)*(5957/100000 : ℝ)=(5000023401586211/5000000000000000 : ℝ) by norm_num, show 1+2*(958694976223421/100000000000000000000 : ℝ)=(50000958694976223421/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14229505939317249/10000000000000000000 : ℝ)+(958694976223421/100000000000000000000 : ℝ) ≤ ((10162113215954452119/10165000000000000000 : ℝ)+(862032746861/355775000000000 : ℝ)*((5047/25000 : ℝ)+(5957/100000 : ℝ)))^(4195/1024 : ℝ) := by
    rw [show (10162113215954452119/10165000000000000000 : ℝ)+(862032746861/355775000000000 : ℝ)*((5047/25000 : ℝ)+(5957/100000 : ℝ))=(5001747467079933/5000000000000000 : ℝ) by norm_num, show 1+(14229505939317249/10000000000000000000 : ℝ)+(958694976223421/100000000000000000000 : ℝ)=(100143253754369395911/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14229505939317249/10000000000000000000 : ℝ) ≤ ((10162113215954452119/10165000000000000000 : ℝ)+2*(862032746861/355775000000000 : ℝ)*(5047/25000 : ℝ))^(4195/1024 : ℝ) := by
    rw [show (10162113215954452119/10165000000000000000 : ℝ)+2*(862032746861/355775000000000 : ℝ)*(5047/25000 : ℝ)=(1000694306514731/1000000000000000 : ℝ) by norm_num, show 1+2*(14229505939317249/10000000000000000000 : ℝ)=(5014229505939317249/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10162113215954452119/10165000000000000000 : ℝ)*(X 1 0+X 2 0)+(862032746861/355775000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (5957/100000 : ℝ)) (hi := (5047/25000 : ℝ)) (c := (10162113215954452119/10165000000000000000 : ℝ)) (alpha := (862032746861/355775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10162113215954452119/10165000000000000000 : ℝ)*(X 0 1+X 2 1)+(862032746861/355775000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (5957/100000 : ℝ)) (hi := (5047/25000 : ℝ)) (c := (10162113215954452119/10165000000000000000 : ℝ)) (alpha := (862032746861/355775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10162113215954452119/10165000000000000000 : ℝ)*(X 0 2+X 1 2)+(862032746861/355775000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (5957/100000 : ℝ)) (hi := (5047/25000 : ℝ)) (c := (10162113215954452119/10165000000000000000 : ℝ)) (alpha := (862032746861/355775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2125102683/10000000000 : ℝ)*X 0 0+(1375118723/2500000000 : ℝ)*X 0 1+(2584037811/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5371493907/10000000000 : ℝ)*X 1 0+(-459509997/2000000000 : ℝ)*X 1 1+(646010001/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2685747889/5000000000 : ℝ)*X 2 0+(1292019349/2500000000 : ℝ)*X 2 1+(-2297550919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4347286821/10000000000 : ℝ)*X 0 0+(805115451/2000000000 : ℝ)*X 0 1+(234707229/500000000 : ℝ)*X 0 2+(4347286821/10000000000 : ℝ)*X 1 0+(805115451/2000000000 : ℝ)*X 1 1+(234707229/500000000 : ℝ)*X 1 2+(4347286821/10000000000 : ℝ)*X 2 0+(805115451/2000000000 : ℝ)*X 2 1+(234707229/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2125189759/10000000000 : ℝ)*X 0 0+(5170280711/10000000000 : ℝ)*X 0 1+(5498249391/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643423143/5000000000 : ℝ)*X 1 0+(-98368947/500000000 : ℝ)*X 1 1+(549824941/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5286846457/10000000000 : ℝ)*X 2 0+(5498249427/10000000000 : ℝ)*X 2 1+(-983689341/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4347464287/10000000000 : ℝ)*X 0 0+(4689712109/10000000000 : ℝ)*X 0 1+(2015025861/5000000000 : ℝ)*X 0 2+(4347464287/10000000000 : ℝ)*X 1 0+(4689712109/10000000000 : ℝ)*X 1 1+(2015025861/5000000000 : ℝ)*X 1 2+(4347464287/10000000000 : ℝ)*X 2 0+(4689712109/10000000000 : ℝ)*X 2 1+(2015025861/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (227804039935838059517253/35577500000000000000000000000 : ℝ) := by norm_num
    linear_combination (120903303/12500000000000 : ℝ)*(base19) + (874390451/50000000000000 : ℝ)*(base23) + (111206459/100000000000000 : ℝ)*(upper2) + (602320687/100000000000000 : ℝ)*(upper3) + (127143169/50000000000000 : ℝ)*(upper4) + (2252136385865731/100000000000000 : ℝ)*(major0) + (2252136385865731/100000000000000 : ℝ)*(major1) + (2252136385865731/100000000000000 : ℝ)*(major2) + (188029464526541/6250000000000 : ℝ)*(sp0) + (15042531711333/500000000000 : ℝ)*(sp1) + (1504252780356061/50000000000000 : ℝ)*(sp2) + (747873296127991/50000000000000 : ℝ)*(sp3) + (2242316773/6250000000000 : ℝ)*(sp4) + (18656547893/100000000000000 : ℝ)*(sp7) + (747882624401937/50000000000000 : ℝ)*(f.failure) + (94015853421657/3125000000000 : ℝ)*(f.sum) + (315019538330151/71155000000000000000000000000 : ℝ)*base66 + (14669908761116737923/7115500000000000000000000000000000 : ℝ)*base67 + (3469540603307762077/7115500000000000000000000000000000 : ℝ)*base70 + (13921622982056262077/7115500000000000000000000000000000 : ℝ)*base72 + (177634146991221/71155000000000000000000000000 : ℝ)*base74 + (7877115260947762077/7115500000000000000000000000000000 : ℝ)*base76 + (3676326906245737923/7115500000000000000000000000000000 : ℝ)*base77 + (28452578809480737923/7115500000000000000000000000000000 : ℝ)*base79 + (2687739885009/1111796875000000000000000000 : ℝ)*base82 + (27546689/5000000000000000000000 : ℝ)*base90 + (27546689/5000000000000000000000 : ℝ)*base92 + (27546689/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (121208739475391331847964307/127062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9678677/2000000000000 : ℝ)*(base19) + (764072793/100000000000000 : ℝ)*(base23) + (28546439/50000000000000 : ℝ)*(upper2) + (21026557/25000000000000 : ℝ)*(upper3) + (4368387/20000000000000 : ℝ)*(upper5) + (570625328023117/25000000000000 : ℝ)*(major0) + (570625328023117/25000000000000 : ℝ)*(major1) + (570625328023117/25000000000000 : ℝ)*(major2) + (4226374543/100000000000000 : ℝ)*(sp1) + (4409275777/50000000000000 : ℝ)*(sp2) + (9528344869573/312500000000 : ℝ)*(sp4) + (1524532823977483/50000000000000 : ℝ)*(sp5) + (762265193909753/25000000000000 : ℝ)*(sp6) + (1515932234123899/100000000000000 : ℝ)*(sp7) + (1515932234123899/100000000000000 : ℝ)*(f.failure) + (9528344869573/312500000000 : ℝ)*(f.sum) + (197659867548977/71155000000000000000000000000 : ℝ)*base65 + (17280592689726280539/1778875000000000000000000000000000 : ℝ)*base68 + (21311658433213405539/1778875000000000000000000000000000 : ℝ)*base70 + (15381855026952405539/1778875000000000000000000000000000 : ℝ)*base72 + (23311241583239/8894375000000000000000000000 : ℝ)*base73 + (4549128335308905539/1778875000000000000000000000000000 : ℝ)*base76 + (17112262298838530539/1778875000000000000000000000000000 : ℝ)*base78 + (8937438660799780539/1778875000000000000000000000000000 : ℝ)*base80 + (5943740994969/8894375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (65054197/10000000000000000000000 : ℝ)*base89 + (65054197/10000000000000000000000 : ℝ)*base91 + (65054197/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1198_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5047/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5957/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2329/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16341/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1198_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1198_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2329/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16341/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1198_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1198_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1198_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2329/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16341/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1198_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

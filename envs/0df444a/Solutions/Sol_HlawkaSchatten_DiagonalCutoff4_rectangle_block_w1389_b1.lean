-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1389_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:25:05.111034+00:00
-- url     : https://prove2.me/submissions/80c237a5-152c-4565-bf2d-985c1f1d242b

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
theorem support_rectangle_w1389_s3_0 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2002716551/10000000000 : ℝ)*x 0 + (5421540093/10000000000 : ℝ)*x 1 + (1308890379/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2002716551/10000000000 : ℝ)^4349 ≤ (12205042410951/100000000000000 : ℝ)^3325 := by
    have hnat : (2002716551 : ℕ)^4349*100000000000000^3325 ≤ 12205042410951^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002716551 10000000000 12205042410951 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421540093/10000000000 : ℝ)^4349 ≤ (44899391330973/100000000000000 : ℝ)^3325 := by
    have hnat : (5421540093 : ℕ)^4349*100000000000000^3325 ≤ 44899391330973^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421540093 10000000000 44899391330973 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1308890379/2500000000 : ℝ)^4349 ≤ (2144778312421/5000000000000 : ℝ)^3325 := by
    have hnat : (1308890379 : ℕ)^4349*5000000000000^3325 ≤ 2144778312421^3325*2500000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308890379 2500000000 2144778312421 5000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2002716551/10000000000 : ℝ), (5421540093/10000000000 : ℝ), (1308890379/2500000000 : ℝ)] ![(12205042410951/100000000000000 : ℝ), (44899391330973/100000000000000 : ℝ), (2144778312421/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2002716551/10000000000 : ℝ)|^4349 ≤ (12205042410951/100000000000000 : ℝ)^3325
        have hw : |(-2002716551/10000000000 : ℝ)|=(2002716551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5421540093/10000000000 : ℝ)|^4349 ≤ (44899391330973/100000000000000 : ℝ)^3325
        have hw : |(5421540093/10000000000 : ℝ)|=(5421540093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1308890379/2500000000 : ℝ)|^4349 ≤ (2144778312421/5000000000000 : ℝ)^3325
        have hw : |(1308890379/2500000000 : ℝ)|=(1308890379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s3_1 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675513559/5000000000 : ℝ)*x 0 + (-1048830309/5000000000 : ℝ)*x 1 + (1308890411/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675513559/5000000000 : ℝ)^4349 ≤ (8827423399937/20000000000000 : ℝ)^3325 := by
    have hnat : (2675513559 : ℕ)^4349*20000000000000^3325 ≤ 8827423399937^3325*5000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675513559 5000000000 8827423399937 20000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048830309/5000000000 : ℝ)^4349 ≤ (3241828840309/25000000000000 : ℝ)^3325 := by
    have hnat : (1048830309 : ℕ)^4349*25000000000000^3325 ≤ 3241828840309^3325*5000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048830309 5000000000 3241828840309 25000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1308890411/2500000000 : ℝ)^4349 ≤ (42895567620113/100000000000000 : ℝ)^3325 := by
    have hnat : (1308890411 : ℕ)^4349*100000000000000^3325 ≤ 42895567620113^3325*2500000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308890411 2500000000 42895567620113 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675513559/5000000000 : ℝ), (-1048830309/5000000000 : ℝ), (1308890411/2500000000 : ℝ)] ![(8827423399937/20000000000000 : ℝ), (3241828840309/25000000000000 : ℝ), (42895567620113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675513559/5000000000 : ℝ)|^4349 ≤ (8827423399937/20000000000000 : ℝ)^3325
        have hw : |(2675513559/5000000000 : ℝ)|=(2675513559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1048830309/5000000000 : ℝ)|^4349 ≤ (3241828840309/25000000000000 : ℝ)^3325
        have hw : |(-1048830309/5000000000 : ℝ)|=(1048830309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1308890411/2500000000 : ℝ)|^4349 ≤ (42895567620113/100000000000000 : ℝ)^3325
        have hw : |(1308890411/2500000000 : ℝ)|=(1308890411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s3_2 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337756783/2500000000 : ℝ)*x 0 + (2617780823/5000000000 : ℝ)*x 1 + (-524415149/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337756783/2500000000 : ℝ)^4349 ≤ (1765484686029/4000000000000 : ℝ)^3325 := by
    have hnat : (1337756783 : ℕ)^4349*4000000000000^3325 ≤ 1765484686029^3325*2500000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337756783 2500000000 1765484686029 4000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2617780823/5000000000 : ℝ)^4349 ≤ (21447783820773/50000000000000 : ℝ)^3325 := by
    have hnat : (2617780823 : ℕ)^4349*50000000000000^3325 ≤ 21447783820773^3325*5000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617780823 5000000000 21447783820773 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524415149/2500000000 : ℝ)^4349 ≤ (12967315183353/100000000000000 : ℝ)^3325 := by
    have hnat : (524415149 : ℕ)^4349*100000000000000^3325 ≤ 12967315183353^3325*2500000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524415149 2500000000 12967315183353 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337756783/2500000000 : ℝ), (2617780823/5000000000 : ℝ), (-524415149/2500000000 : ℝ)] ![(1765484686029/4000000000000 : ℝ), (21447783820773/50000000000000 : ℝ), (12967315183353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337756783/2500000000 : ℝ)|^4349 ≤ (1765484686029/4000000000000 : ℝ)^3325
        have hw : |(1337756783/2500000000 : ℝ)|=(1337756783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2617780823/5000000000 : ℝ)|^4349 ≤ (21447783820773/50000000000000 : ℝ)^3325
        have hw : |(2617780823/5000000000 : ℝ)|=(2617780823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-524415149/2500000000 : ℝ)|^4349 ≤ (12967315183353/100000000000000 : ℝ)^3325
        have hw : |(-524415149/2500000000 : ℝ)|=(524415149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s3_3 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (431366489/1000000000 : ℝ)*x 0 + (2059804951/5000000000 : ℝ)*x 1 + (4516053649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431366489/1000000000 : ℝ)^4349 ≤ (8323961956497/25000000000000 : ℝ)^3325 := by
    have hnat : (431366489 : ℕ)^4349*25000000000000^3325 ≤ 8323961956497^3325*1000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431366489 1000000000 8323961956497 25000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2059804951/5000000000 : ℝ)^4349 ≤ (31350419275097/100000000000000 : ℝ)^3325 := by
    have hnat : (2059804951 : ℕ)^4349*100000000000000^3325 ≤ 31350419275097^3325*5000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059804951 5000000000 31350419275097 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4516053649/10000000000 : ℝ)^4349 ≤ (17676866439889/50000000000000 : ℝ)^3325 := by
    have hnat : (4516053649 : ℕ)^4349*50000000000000^3325 ≤ 17676866439889^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516053649 10000000000 17676866439889 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431366489/1000000000 : ℝ), (2059804951/5000000000 : ℝ), (4516053649/10000000000 : ℝ)] ![(8323961956497/25000000000000 : ℝ), (31350419275097/100000000000000 : ℝ), (17676866439889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431366489/1000000000 : ℝ)|^4349 ≤ (8323961956497/25000000000000 : ℝ)^3325
        have hw : |(431366489/1000000000 : ℝ)|=(431366489/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2059804951/5000000000 : ℝ)|^4349 ≤ (31350419275097/100000000000000 : ℝ)^3325
        have hw : |(2059804951/5000000000 : ℝ)|=(2059804951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4516053649/10000000000 : ℝ)|^4349 ≤ (17676866439889/50000000000000 : ℝ)^3325
        have hw : |(4516053649/10000000000 : ℝ)|=(4516053649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s3_4 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1001366877/5000000000 : ℝ)*x 0 + (163634921/312500000 : ℝ)*x 1 + (5420779527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1001366877/5000000000 : ℝ)^4349 ≤ (6102589768873/50000000000000 : ℝ)^3325 := by
    have hnat : (1001366877 : ℕ)^4349*50000000000000^3325 ≤ 6102589768873^3325*5000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001366877 5000000000 6102589768873 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163634921/312500000 : ℝ)^4349 ≤ (42903667517743/100000000000000 : ℝ)^3325 := by
    have hnat : (163634921 : ℕ)^4349*100000000000000^3325 ≤ 42903667517743^3325*312500000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163634921 312500000 42903667517743 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420779527/10000000000 : ℝ)^4349 ≤ (44891152927399/100000000000000 : ℝ)^3325 := by
    have hnat : (5420779527 : ℕ)^4349*100000000000000^3325 ≤ 44891152927399^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420779527 10000000000 44891152927399 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1001366877/5000000000 : ℝ), (163634921/312500000 : ℝ), (5420779527/10000000000 : ℝ)] ![(6102589768873/50000000000000 : ℝ), (42903667517743/100000000000000 : ℝ), (44891152927399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1001366877/5000000000 : ℝ)|^4349 ≤ (6102589768873/50000000000000 : ℝ)^3325
        have hw : |(-1001366877/5000000000 : ℝ)|=(1001366877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163634921/312500000 : ℝ)|^4349 ≤ (42903667517743/100000000000000 : ℝ)^3325
        have hw : |(163634921/312500000 : ℝ)|=(163634921/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420779527/10000000000 : ℝ)|^4349 ≤ (44891152927399/100000000000000 : ℝ)^3325
        have hw : |(5420779527/10000000000 : ℝ)|=(5420779527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s3_5 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165714823/312500000 : ℝ)*x 0 + (-1912442527/10000000000 : ℝ)*x 1 + (5420779649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165714823/312500000 : ℝ)^4349 ≤ (10904584470633/25000000000000 : ℝ)^3325 := by
    have hnat : (165714823 : ℕ)^4349*25000000000000^3325 ≤ 10904584470633^3325*312500000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165714823 312500000 10904584470633 25000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1912442527/10000000000 : ℝ)^4349 ≤ (2298101570159/20000000000000 : ℝ)^3325 := by
    have hnat : (1912442527 : ℕ)^4349*20000000000000^3325 ≤ 2298101570159^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912442527 10000000000 2298101570159 20000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420779649/10000000000 : ℝ)^4349 ≤ (44891154248867/100000000000000 : ℝ)^3325 := by
    have hnat : (5420779649 : ℕ)^4349*100000000000000^3325 ≤ 44891154248867^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420779649 10000000000 44891154248867 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165714823/312500000 : ℝ), (-1912442527/10000000000 : ℝ), (5420779649/10000000000 : ℝ)] ![(10904584470633/25000000000000 : ℝ), (2298101570159/20000000000000 : ℝ), (44891154248867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165714823/312500000 : ℝ)|^4349 ≤ (10904584470633/25000000000000 : ℝ)^3325
        have hw : |(165714823/312500000 : ℝ)|=(165714823/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1912442527/10000000000 : ℝ)|^4349 ≤ (2298101570159/20000000000000 : ℝ)^3325
        have hw : |(-1912442527/10000000000 : ℝ)|=(1912442527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420779649/10000000000 : ℝ)|^4349 ≤ (44891154248867/100000000000000 : ℝ)^3325
        have hw : |(5420779649/10000000000 : ℝ)|=(5420779649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s3_6 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302874551/10000000000 : ℝ)*x 0 + (169399359/312500000 : ℝ)*x 1 + (-382488491/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302874551/10000000000 : ℝ)^4349 ≤ (4361834019563/10000000000000 : ℝ)^3325 := by
    have hnat : (5302874551 : ℕ)^4349*10000000000000^3325 ≤ 4361834019563^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302874551 10000000000 4361834019563 10000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169399359/312500000 : ℝ)^4349 ≤ (44891152504963/100000000000000 : ℝ)^3325 := by
    have hnat : (169399359 : ℕ)^4349*100000000000000^3325 ≤ 44891152504963^3325*312500000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169399359 312500000 44891152504963 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (382488491/2000000000 : ℝ)^4349 ≤ (11490507284971/100000000000000 : ℝ)^3325 := by
    have hnat : (382488491 : ℕ)^4349*100000000000000^3325 ≤ 11490507284971^3325*2000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382488491 2000000000 11490507284971 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302874551/10000000000 : ℝ), (169399359/312500000 : ℝ), (-382488491/2000000000 : ℝ)] ![(4361834019563/10000000000000 : ℝ), (44891152504963/100000000000000 : ℝ), (11490507284971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302874551/10000000000 : ℝ)|^4349 ≤ (4361834019563/10000000000000 : ℝ)^3325
        have hw : |(5302874551/10000000000 : ℝ)|=(5302874551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169399359/312500000 : ℝ)|^4349 ≤ (44891152504963/100000000000000 : ℝ)^3325
        have hw : |(169399359/312500000 : ℝ)|=(169399359/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-382488491/2000000000 : ℝ)|^4349 ≤ (11490507284971/100000000000000 : ℝ)^3325
        have hw : |(-382488491/2000000000 : ℝ)|=(382488491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s3_7 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4313701287/10000000000 : ℝ)*x 0 + (4514442647/10000000000 : ℝ)*x 1 + (824246007/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313701287/10000000000 : ℝ)^4349 ≤ (6659243056777/20000000000000 : ℝ)^3325 := by
    have hnat : (4313701287 : ℕ)^4349*20000000000000^3325 ≤ 6659243056777^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313701287 10000000000 6659243056777 20000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514442647/10000000000 : ℝ)^4349 ≤ (17668619056819/50000000000000 : ℝ)^3325 := by
    have hnat : (4514442647 : ℕ)^4349*50000000000000^3325 ≤ 17668619056819^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514442647 10000000000 17668619056819 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (824246007/2000000000 : ℝ)^4349 ≤ (31366546586917/100000000000000 : ℝ)^3325 := by
    have hnat : (824246007 : ℕ)^4349*100000000000000^3325 ≤ 31366546586917^3325*2000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824246007 2000000000 31366546586917 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313701287/10000000000 : ℝ), (4514442647/10000000000 : ℝ), (824246007/2000000000 : ℝ)] ![(6659243056777/20000000000000 : ℝ), (17668619056819/50000000000000 : ℝ), (31366546586917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313701287/10000000000 : ℝ)|^4349 ≤ (6659243056777/20000000000000 : ℝ)^3325
        have hw : |(4313701287/10000000000 : ℝ)|=(4313701287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514442647/10000000000 : ℝ)|^4349 ≤ (17668619056819/50000000000000 : ℝ)^3325
        have hw : |(4514442647/10000000000 : ℝ)|=(4514442647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(824246007/2000000000 : ℝ)|^4349 ≤ (31366546586917/100000000000000 : ℝ)^3325
        have hw : |(824246007/2000000000 : ℝ)|=(824246007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1389_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78291767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1593/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5517/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14971/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1593/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10143/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1593/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10143/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1593/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10143/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1593/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10143/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1593/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10143/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1593/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10143/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10143/100000 : ℝ) ^ (1087/256 : ℝ) ≤ (6026837345312057/100000000000000000000 : ℝ) := by
    have hpowers : (10143/100000 : ℝ)^1087 ≤ (6026837345312057/100000000000000000000 : ℝ)^256 := by
      have hnat : (10143 : ℕ)^1087*100000000000000000000^256 ≤ 6026837345312057^256*100000^1087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10143 100000 6026837345312057 100000000000000000000 1087 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10143/100000 : ℝ)) (X := (6026837345312057/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1593/10000 : ℝ) ^ (1087/256 : ℝ) ≤ (4097636142679339/10000000000000000000 : ℝ) := by
    have hpowers : (1593/10000 : ℝ)^1087 ≤ (4097636142679339/10000000000000000000 : ℝ)^256 := by
      have hnat : (1593 : ℕ)^1087*10000000000000000000^256 ≤ 4097636142679339^256*10000^1087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1593 10000 4097636142679339 10000000000000000000 1087 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1593/10000 : ℝ)) (X := (4097636142679339/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006026837345312057/50000000000000000000 : ℝ) ≤ (10000283863712679/10000000000000000 : ℝ) ^ (1087/256 : ℝ) := by
    have hpowers : (50006026837345312057/50000000000000000000 : ℝ)^256 ≤ (10000283863712679/10000000000000000 : ℝ)^1087 := by
      have hnat : (50006026837345312057 : ℕ)^256*10000000000000000^1087 ≤ 10000283863712679^1087*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006026837345312057 50000000000000000000 10000283863712679 10000000000000000 256 1087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283863712679/10000000000000000 : ℝ)) (X := (50006026837345312057/50000000000000000000 : ℝ)) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047003198772105447/100000000000000000000 : ℝ) ≤ (1000110677622629/1000000000000000 : ℝ) ^ (1087/256 : ℝ) := by
    have hpowers : (100047003198772105447/100000000000000000000 : ℝ)^256 ≤ (1000110677622629/1000000000000000 : ℝ)^1087 := by
      have hnat : (100047003198772105447 : ℕ)^256*1000000000000000^1087 ≤ 1000110677622629^1087*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047003198772105447 100000000000000000000 1000110677622629 1000000000000000 256 1087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000110677622629/1000000000000000 : ℝ)) (X := (100047003198772105447/100000000000000000000 : ℝ)) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (5004097636142679339/5000000000000000000 : ℝ) ≤ (10001929688739901/10000000000000000 : ℝ) ^ (1087/256 : ℝ) := by
    have hpowers : (5004097636142679339/5000000000000000000 : ℝ)^256 ≤ (10001929688739901/10000000000000000 : ℝ)^1087 := by
      have hnat : (5004097636142679339 : ℕ)^256*10000000000000000^1087 ≤ 10001929688739901^1087*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5004097636142679339 5000000000000000000 10001929688739901 10000000000000000 256 1087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001929688739901/10000000000000000 : ℝ)) (X := (5004097636142679339/5000000000000000000 : ℝ)) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6026837345312057/100000000000000000000 : ℝ) ≤ ((6428327679561573403/6430000000000000000 : ℝ)+2*(822912513611/578700000000000 : ℝ)*(10143/100000 : ℝ))^(1087/256 : ℝ) := by
    rw [show (6428327679561573403/6430000000000000000 : ℝ)+2*(822912513611/578700000000000 : ℝ)*(10143/100000 : ℝ)=(10000283863712679/10000000000000000 : ℝ) by norm_num, show 1+2*(6026837345312057/100000000000000000000 : ℝ)=(50006026837345312057/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4097636142679339/10000000000000000000 : ℝ)+(6026837345312057/100000000000000000000 : ℝ) ≤ ((6428327679561573403/6430000000000000000 : ℝ)+(822912513611/578700000000000 : ℝ)*((1593/10000 : ℝ)+(10143/100000 : ℝ)))^(1087/256 : ℝ) := by
    rw [show (6428327679561573403/6430000000000000000 : ℝ)+(822912513611/578700000000000 : ℝ)*((1593/10000 : ℝ)+(10143/100000 : ℝ))=(1000110677622629/1000000000000000 : ℝ) by norm_num, show 1+(4097636142679339/10000000000000000000 : ℝ)+(6026837345312057/100000000000000000000 : ℝ)=(100047003198772105447/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4097636142679339/10000000000000000000 : ℝ) ≤ ((6428327679561573403/6430000000000000000 : ℝ)+2*(822912513611/578700000000000 : ℝ)*(1593/10000 : ℝ))^(1087/256 : ℝ) := by
    rw [show (6428327679561573403/6430000000000000000 : ℝ)+2*(822912513611/578700000000000 : ℝ)*(1593/10000 : ℝ)=(10001929688739901/10000000000000000 : ℝ) by norm_num, show 1+2*(4097636142679339/10000000000000000000 : ℝ)=(5004097636142679339/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6428327679561573403/6430000000000000000 : ℝ)*(X 1 0+X 2 0)+(822912513611/578700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1087/256 : ℝ)) (lo := (10143/100000 : ℝ)) (hi := (1593/10000 : ℝ)) (c := (6428327679561573403/6430000000000000000 : ℝ)) (alpha := (822912513611/578700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6428327679561573403/6430000000000000000 : ℝ)*(X 0 1+X 2 1)+(822912513611/578700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1087/256 : ℝ)) (lo := (10143/100000 : ℝ)) (hi := (1593/10000 : ℝ)) (c := (6428327679561573403/6430000000000000000 : ℝ)) (alpha := (822912513611/578700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6428327679561573403/6430000000000000000 : ℝ)*(X 0 2+X 1 2)+(822912513611/578700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1087/256 : ℝ)) (lo := (10143/100000 : ℝ)) (hi := (1593/10000 : ℝ)) (c := (6428327679561573403/6430000000000000000 : ℝ)) (alpha := (822912513611/578700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2002716551/10000000000 : ℝ)*X 0 0+(5421540093/10000000000 : ℝ)*X 0 1+(1308890379/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675513559/5000000000 : ℝ)*X 1 0+(-1048830309/5000000000 : ℝ)*X 1 1+(1308890411/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337756783/2500000000 : ℝ)*X 2 0+(2617780823/5000000000 : ℝ)*X 2 1+(-524415149/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((431366489/1000000000 : ℝ)*X 0 0+(2059804951/5000000000 : ℝ)*X 0 1+(4516053649/10000000000 : ℝ)*X 0 2+(431366489/1000000000 : ℝ)*X 1 0+(2059804951/5000000000 : ℝ)*X 1 1+(4516053649/10000000000 : ℝ)*X 1 2+(431366489/1000000000 : ℝ)*X 2 0+(2059804951/5000000000 : ℝ)*X 2 1+(4516053649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1001366877/5000000000 : ℝ)*X 0 0+(163634921/312500000 : ℝ)*X 0 1+(5420779527/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165714823/312500000 : ℝ)*X 1 0+(-1912442527/10000000000 : ℝ)*X 1 1+(5420779649/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302874551/10000000000 : ℝ)*X 2 0+(169399359/312500000 : ℝ)*X 2 1+(-382488491/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4313701287/10000000000 : ℝ)*X 0 0+(4514442647/10000000000 : ℝ)*X 0 1+(824246007/2000000000 : ℝ)*X 0 2+(4313701287/10000000000 : ℝ)*X 1 0+(4514442647/10000000000 : ℝ)*X 1 1+(824246007/2000000000 : ℝ)*X 1 2+(4313701287/10000000000 : ℝ)*X 2 0+(4514442647/10000000000 : ℝ)*X 2 1+(824246007/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (80666966274555792451264521/16075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (696060753/100000000000000 : ℝ)*(base19) + (101765783/20000000000000 : ℝ)*(base23) + (2220629/2000000000000 : ℝ)*(lower2) + (62239749/50000000000000 : ℝ)*(upper3) + (3315393/100000000000000 : ℝ)*(lower4) + (197485689816323/5000000000000 : ℝ)*(major0) + (197485689816323/5000000000000 : ℝ)*(major1) + (197485689816323/5000000000000 : ℝ)*(major2) + (5376980124056971/100000000000000 : ℝ)*(sp0) + (5376994328269221/100000000000000 : ℝ)*(sp1) + (5376994515501059/100000000000000 : ℝ)*(sp2) + (78825873114329/3125000000000 : ℝ)*(sp3) + (14900273003/100000000000000 : ℝ)*(sp4) + (4461392313/100000000000000 : ℝ)*(sp7) + (1261216200525421/50000000000000 : ℝ)*(f.failure) + (2688497512164987/50000000000000 : ℝ)*(f.sum) + (48643251887/723375000000000000000000000 : ℝ)*base65 + (4613945859870285479/289350000000000000000000000000000 : ℝ)*base68 + (3210356393247585479/289350000000000000000000000000000 : ℝ)*base70 + (4860836740117335479/289350000000000000000000000000000 : ℝ)*base72 + (17469709609669/5787000000000000000000000000 : ℝ)*base73 + (4321756024168035479/289350000000000000000000000000000 : ℝ)*base76 + (3618945877505835479/289350000000000000000000000000000 : ℝ)*base78 + (5106227545763535479/289350000000000000000000000000000 : ℝ)*base80 + (26022662544031/5787000000000000000000000000 : ℝ)*base81 + (38508907/2500000000000000000000 : ℝ)*base89 + (38508907/2500000000000000000000 : ℝ)*base91 + (38508907/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (886958339561629541915939651/120562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1704714167/100000000000000 : ℝ)*(base19) + (525090701/25000000000000 : ℝ)*(base23) + (1979209/800000000000 : ℝ)*(upper3) + (60917551/100000000000000 : ℝ)*(lower4) + (96139491/50000000000000 : ℝ)*(upper5) + (497770164205487/12500000000000 : ℝ)*(major0) + (497770164205487/12500000000000 : ℝ)*(major1) + (497770164205487/12500000000000 : ℝ)*(major2) + (32359883253/100000000000000 : ℝ)*(sp1) + (39075107423/100000000000000 : ℝ)*(sp2) + (84705746935157/1562500000000 : ℝ)*(sp4) + (5421133739252627/100000000000000 : ℝ)*(sp5) + (2710563314189911/50000000000000 : ℝ)*(sp6) + (1271577289104963/50000000000000 : ℝ)*(sp7) + (1271577289104963/50000000000000 : ℝ)*(f.failure) + (84705746935157/1562500000000 : ℝ)*(f.sum) + (50607755542753/14467500000000000000000000000 : ℝ)*base65 + (6865482976702710349/723375000000000000000000000000000 : ℝ)*base67 + (168880922035710349/723375000000000000000000000000000 : ℝ)*base69 + (11451855887906460349/723375000000000000000000000000000 : ℝ)*base71 + (7820253234491/28935000000000000000000000000 : ℝ)*base73 + (3201879159330914651/723375000000000000000000000000000 : ℝ)*base76 + (545259579458460349/723375000000000000000000000000000 : ℝ)*base77 + (7420414263398039651/723375000000000000000000000000000 : ℝ)*base80 + (19837146829859/7233750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (1739621/2500000000000000000000 : ℝ)*base89 + (1739621/2500000000000000000000 : ℝ)*base91 + (1739621/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1389_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78291767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1593/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5517/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14971/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1389_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1389_s4_0 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-500960431/2500000000 : ℝ)*x 0 + (5412114667/10000000000 : ℝ)*x 1 + (5244247037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (500960431/2500000000 : ℝ)^4349 ≤ (12214012038943/100000000000000 : ℝ)^3325 := by
    have hnat : (500960431 : ℕ)^4349*100000000000000^3325 ≤ 12214012038943^3325*2500000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500960431 2500000000 12214012038943 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412114667/10000000000 : ℝ)^4349 ≤ (44797320840687/100000000000000 : ℝ)^3325 := by
    have hnat : (5412114667 : ℕ)^4349*100000000000000^3325 ≤ 44797320840687^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412114667 10000000000 44797320840687 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244247037/10000000000 : ℝ)^4349 ≤ (42988667100619/100000000000000 : ℝ)^3325 := by
    have hnat : (5244247037 : ℕ)^4349*100000000000000^3325 ≤ 42988667100619^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244247037 10000000000 42988667100619 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-500960431/2500000000 : ℝ), (5412114667/10000000000 : ℝ), (5244247037/10000000000 : ℝ)] ![(12214012038943/100000000000000 : ℝ), (44797320840687/100000000000000 : ℝ), (42988667100619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-500960431/2500000000 : ℝ)|^4349 ≤ (12214012038943/100000000000000 : ℝ)^3325
        have hw : |(-500960431/2500000000 : ℝ)|=(500960431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412114667/10000000000 : ℝ)|^4349 ≤ (44797320840687/100000000000000 : ℝ)^3325
        have hw : |(5412114667/10000000000 : ℝ)|=(5412114667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244247037/10000000000 : ℝ)|^4349 ≤ (42988667100619/100000000000000 : ℝ)^3325
        have hw : |(5244247037/10000000000 : ℝ)|=(5244247037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s4_1 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53486083/100000000 : ℝ)*x 0 + (-2089368491/10000000000 : ℝ)*x 1 + (5244247071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53486083/100000000 : ℝ)^4349 ≤ (22055511593923/50000000000000 : ℝ)^3325 := by
    have hnat : (53486083 : ℕ)^4349*50000000000000^3325 ≤ 22055511593923^3325*100000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53486083 100000000 22055511593923 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2089368491/10000000000 : ℝ)^4349 ≤ (12900309333843/100000000000000 : ℝ)^3325 := by
    have hnat : (2089368491 : ℕ)^4349*100000000000000^3325 ≤ 12900309333843^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089368491 10000000000 12900309333843 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244247071/10000000000 : ℝ)^4349 ≤ (42988667465161/100000000000000 : ℝ)^3325 := by
    have hnat : (5244247071 : ℕ)^4349*100000000000000^3325 ≤ 42988667465161^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244247071 10000000000 42988667465161 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53486083/100000000 : ℝ), (-2089368491/10000000000 : ℝ), (5244247071/10000000000 : ℝ)] ![(22055511593923/50000000000000 : ℝ), (12900309333843/100000000000000 : ℝ), (42988667465161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53486083/100000000 : ℝ)|^4349 ≤ (22055511593923/50000000000000 : ℝ)^3325
        have hw : |(53486083/100000000 : ℝ)|=(53486083/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2089368491/10000000000 : ℝ)|^4349 ≤ (12900309333843/100000000000000 : ℝ)^3325
        have hw : |(-2089368491/10000000000 : ℝ)|=(2089368491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244247071/10000000000 : ℝ)|^4349 ≤ (42988667465161/100000000000000 : ℝ)^3325
        have hw : |(5244247071/10000000000 : ℝ)|=(5244247071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s4_2 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674304177/5000000000 : ℝ)*x 0 + (1311061767/2500000000 : ℝ)*x 1 + (-2089368423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674304177/5000000000 : ℝ)^4349 ≤ (44111023770349/100000000000000 : ℝ)^3325 := by
    have hnat : (2674304177 : ℕ)^4349*100000000000000^3325 ≤ 44111023770349^3325*5000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674304177 5000000000 44111023770349 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311061767/2500000000 : ℝ)^4349 ≤ (10747166858249/25000000000000 : ℝ)^3325 := by
    have hnat : (1311061767 : ℕ)^4349*25000000000000^3325 ≤ 10747166858249^3325*2500000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311061767 2500000000 10747166858249 25000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2089368423/10000000000 : ℝ)^4349 ≤ (3225077196173/25000000000000 : ℝ)^3325 := by
    have hnat : (2089368423 : ℕ)^4349*25000000000000^3325 ≤ 3225077196173^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089368423 10000000000 3225077196173 25000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674304177/5000000000 : ℝ), (1311061767/2500000000 : ℝ), (-2089368423/10000000000 : ℝ)] ![(44111023770349/100000000000000 : ℝ), (10747166858249/25000000000000 : ℝ), (3225077196173/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674304177/5000000000 : ℝ)|^4349 ≤ (44111023770349/100000000000000 : ℝ)^3325
        have hw : |(2674304177/5000000000 : ℝ)|=(2674304177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311061767/2500000000 : ℝ)|^4349 ≤ (10747166858249/25000000000000 : ℝ)^3325
        have hw : |(1311061767/2500000000 : ℝ)|=(1311061767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2089368423/10000000000 : ℝ)|^4349 ≤ (3225077196173/25000000000000 : ℝ)^3325
        have hw : |(-2089368423/10000000000 : ℝ)|=(2089368423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s4_3 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4314352327/10000000000 : ℝ)*x 0 + (2069414289/5000000000 : ℝ)*x 1 + (4496667119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314352327/10000000000 : ℝ)^4349 ≤ (8325697058461/25000000000000 : ℝ)^3325 := by
    have hnat : (4314352327 : ℕ)^4349*25000000000000^3325 ≤ 8325697058461^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314352327 10000000000 8325697058461 25000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069414289/5000000000 : ℝ)^4349 ≤ (6308370738311/20000000000000 : ℝ)^3325 := by
    have hnat : (2069414289 : ℕ)^4349*20000000000000^3325 ≤ 6308370738311^3325*5000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069414289 5000000000 6308370738311 20000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4496667119/10000000000 : ℝ)^4349 ≤ (8788839512979/25000000000000 : ℝ)^3325 := by
    have hnat : (4496667119 : ℕ)^4349*25000000000000^3325 ≤ 8788839512979^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496667119 10000000000 8788839512979 25000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314352327/10000000000 : ℝ), (2069414289/5000000000 : ℝ), (4496667119/10000000000 : ℝ)] ![(8325697058461/25000000000000 : ℝ), (6308370738311/20000000000000 : ℝ), (8788839512979/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314352327/10000000000 : ℝ)|^4349 ≤ (8325697058461/25000000000000 : ℝ)^3325
        have hw : |(4314352327/10000000000 : ℝ)|=(4314352327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2069414289/5000000000 : ℝ)|^4349 ≤ (6308370738311/20000000000000 : ℝ)^3325
        have hw : |(2069414289/5000000000 : ℝ)|=(2069414289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4496667119/10000000000 : ℝ)|^4349 ≤ (8788839512979/25000000000000 : ℝ)^3325
        have hw : |(4496667119/10000000000 : ℝ)|=(4496667119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s4_4 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2003854151/10000000000 : ℝ)*x 0 + (1048972647/2000000000 : ℝ)*x 1 + (2705747623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2003854151/10000000000 : ℝ)^4349 ≤ (97712888903/800000000000 : ℝ)^3325 := by
    have hnat : (2003854151 : ℕ)^4349*800000000000^3325 ≤ 97712888903^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003854151 10000000000 97712888903 800000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048972647/2000000000 : ℝ)^4349 ≤ (10748818496369/25000000000000 : ℝ)^3325 := by
    have hnat : (1048972647 : ℕ)^4349*25000000000000^3325 ≤ 10748818496369^3325*2000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048972647 2000000000 10748818496369 25000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705747623/5000000000 : ℝ)^4349 ≤ (22395307439401/50000000000000 : ℝ)^3325 := by
    have hnat : (2705747623 : ℕ)^4349*50000000000000^3325 ≤ 22395307439401^3325*5000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705747623 5000000000 22395307439401 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2003854151/10000000000 : ℝ), (1048972647/2000000000 : ℝ), (2705747623/5000000000 : ℝ)] ![(97712888903/800000000000 : ℝ), (10748818496369/25000000000000 : ℝ), (22395307439401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2003854151/10000000000 : ℝ)|^4349 ≤ (97712888903/800000000000 : ℝ)^3325
        have hw : |(-2003854151/10000000000 : ℝ)|=(2003854151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048972647/2000000000 : ℝ)|^4349 ≤ (10748818496369/25000000000000 : ℝ)^3325
        have hw : |(1048972647/2000000000 : ℝ)|=(1048972647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705747623/5000000000 : ℝ)|^4349 ≤ (22395307439401/50000000000000 : ℝ)^3325
        have hw : |(2705747623/5000000000 : ℝ)|=(2705747623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s4_5 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326286149/2500000000 : ℝ)*x 0 + (-240265031/1250000000 : ℝ)*x 1 + (541149523/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326286149/2500000000 : ℝ)^4349 ≤ (43642764299067/100000000000000 : ℝ)^3325 := by
    have hnat : (1326286149 : ℕ)^4349*100000000000000^3325 ≤ 43642764299067^3325*2500000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326286149 2500000000 43642764299067 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (240265031/1250000000 : ℝ)^4349 ≤ (11566620979513/100000000000000 : ℝ)^3325 := by
    have hnat : (240265031 : ℕ)^4349*100000000000000^3325 ≤ 11566620979513^3325*1250000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240265031 1250000000 11566620979513 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541149523/1000000000 : ℝ)^4349 ≤ (22395307352793/50000000000000 : ℝ)^3325 := by
    have hnat : (541149523 : ℕ)^4349*50000000000000^3325 ≤ 22395307352793^3325*1000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541149523 1000000000 22395307352793 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326286149/2500000000 : ℝ), (-240265031/1250000000 : ℝ), (541149523/1000000000 : ℝ)] ![(43642764299067/100000000000000 : ℝ), (11566620979513/100000000000000 : ℝ), (22395307352793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326286149/2500000000 : ℝ)|^4349 ≤ (43642764299067/100000000000000 : ℝ)^3325
        have hw : |(1326286149/2500000000 : ℝ)|=(1326286149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-240265031/1250000000 : ℝ)|^4349 ≤ (11566620979513/100000000000000 : ℝ)^3325
        have hw : |(-240265031/1250000000 : ℝ)|=(240265031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541149523/1000000000 : ℝ)|^4349 ≤ (22395307352793/50000000000000 : ℝ)^3325
        have hw : |(541149523/1000000000 : ℝ)|=(541149523/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s4_6 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305144607/10000000000 : ℝ)*x 0 + (5411495233/10000000000 : ℝ)*x 1 + (-192212023/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305144607/10000000000 : ℝ)^4349 ≤ (43642764417427/100000000000000 : ℝ)^3325 := by
    have hnat : (5305144607 : ℕ)^4349*100000000000000^3325 ≤ 43642764417427^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305144607 10000000000 43642764417427 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411495233/10000000000 : ℝ)^4349 ≤ (2799413421129/6250000000000 : ℝ)^3325 := by
    have hnat : (5411495233 : ℕ)^4349*6250000000000^3325 ≤ 2799413421129^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411495233 10000000000 2799413421129 6250000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (192212023/1000000000 : ℝ)^4349 ≤ (11566620837837/100000000000000 : ℝ)^3325 := by
    have hnat : (192212023 : ℕ)^4349*100000000000000^3325 ≤ 11566620837837^3325*1000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192212023 1000000000 11566620837837 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305144607/10000000000 : ℝ), (5411495233/10000000000 : ℝ), (-192212023/1000000000 : ℝ)] ![(43642764417427/100000000000000 : ℝ), (2799413421129/6250000000000 : ℝ), (11566620837837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305144607/10000000000 : ℝ)|^4349 ≤ (43642764417427/100000000000000 : ℝ)^3325
        have hw : |(5305144607/10000000000 : ℝ)|=(5305144607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411495233/10000000000 : ℝ)|^4349 ≤ (2799413421129/6250000000000 : ℝ)^3325
        have hw : |(5411495233/10000000000 : ℝ)|=(5411495233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-192212023/1000000000 : ℝ)|^4349 ≤ (11566620837837/100000000000000 : ℝ)^3325
        have hw : |(-192212023/1000000000 : ℝ)|=(192212023/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s4_7 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4314378853/10000000000 : ℝ)*x 0 + (2247676819/5000000000 : ℝ)*x 1 + (4140149043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314378853/10000000000 : ℝ)^4349 ≤ (33303056048859/100000000000000 : ℝ)^3325 := by
    have hnat : (4314378853 : ℕ)^4349*100000000000000^3325 ≤ 33303056048859^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314378853 10000000000 33303056048859 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247676819/5000000000 : ℝ)^4349 ≤ (17570963611703/50000000000000 : ℝ)^3325 := by
    have hnat : (2247676819 : ℕ)^4349*50000000000000^3325 ≤ 17570963611703^3325*5000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247676819 5000000000 17570963611703 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4140149043/10000000000 : ℝ)^4349 ≤ (7888754179547/25000000000000 : ℝ)^3325 := by
    have hnat : (4140149043 : ℕ)^4349*25000000000000^3325 ≤ 7888754179547^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4140149043 10000000000 7888754179547 25000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314378853/10000000000 : ℝ), (2247676819/5000000000 : ℝ), (4140149043/10000000000 : ℝ)] ![(33303056048859/100000000000000 : ℝ), (17570963611703/50000000000000 : ℝ), (7888754179547/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314378853/10000000000 : ℝ)|^4349 ≤ (33303056048859/100000000000000 : ℝ)^3325
        have hw : |(4314378853/10000000000 : ℝ)|=(4314378853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247676819/5000000000 : ℝ)|^4349 ≤ (17570963611703/50000000000000 : ℝ)^3325
        have hw : |(2247676819/5000000000 : ℝ)|=(2247676819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4140149043/10000000000 : ℝ)|^4349 ≤ (7888754179547/25000000000000 : ℝ)^3325
        have hw : |(4140149043/10000000000 : ℝ)|=(4140149043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1389_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78291767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14971/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5517/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11219/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7387/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14971/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5517/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14971/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5517/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14971/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5517/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14971/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5517/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14971/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5517/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14971/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5517/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5517/50000 : ℝ) ^ (1087/256 : ℝ) ≤ (861696814959311/10000000000000000000 : ℝ) := by
    have hpowers : (5517/50000 : ℝ)^1087 ≤ (861696814959311/10000000000000000000 : ℝ)^256 := by
      have hnat : (5517 : ℕ)^1087*10000000000000000000^256 ≤ 861696814959311^256*50000^1087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5517 50000 861696814959311 10000000000000000000 1087 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5517/50000 : ℝ)) (X := (861696814959311/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14971/100000 : ℝ) ^ (1087/256 : ℝ) ≤ (7870052495384333/25000000000000000000 : ℝ) := by
    have hpowers : (14971/100000 : ℝ)^1087 ≤ (7870052495384333/25000000000000000000 : ℝ)^256 := by
      have hnat : (14971 : ℕ)^1087*25000000000000000000^256 ≤ 7870052495384333^256*100000^1087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14971 100000 7870052495384333 25000000000000000000 1087 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14971/100000 : ℝ)) (X := (7870052495384333/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000861696814959311/5000000000000000000 : ℝ) ≤ (10000405850697827/10000000000000000 : ℝ) ^ (1087/256 : ℝ) := by
    have hpowers : (5000861696814959311/5000000000000000000 : ℝ)^256 ≤ (10000405850697827/10000000000000000 : ℝ)^1087 := by
      have hnat : (5000861696814959311 : ℕ)^256*10000000000000000^1087 ≤ 10000405850697827^1087*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000861696814959311 5000000000000000000 10000405850697827 10000000000000000 256 1087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000405850697827/10000000000000000 : ℝ)) (X := (5000861696814959311/5000000000000000000 : ℝ)) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020048589065565221/50000000000000000000 : ℝ) ≤ (2000188837252649/2000000000000000 : ℝ) ^ (1087/256 : ℝ) := by
    have hpowers : (50020048589065565221/50000000000000000000 : ℝ)^256 ≤ (2000188837252649/2000000000000000 : ℝ)^1087 := by
      have hnat : (50020048589065565221 : ℕ)^256*2000000000000000^1087 ≤ 2000188837252649^1087*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020048589065565221 50000000000000000000 2000188837252649 2000000000000000 256 1087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000188837252649/2000000000000000 : ℝ)) (X := (50020048589065565221/50000000000000000000 : ℝ)) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507870052495384333/12500000000000000000 : ℝ) ≤ (10001482521828663/10000000000000000 : ℝ) ^ (1087/256 : ℝ) := by
    have hpowers : (12507870052495384333/12500000000000000000 : ℝ)^256 ≤ (10001482521828663/10000000000000000 : ℝ)^1087 := by
      have hnat : (12507870052495384333 : ℕ)^256*10000000000000000^1087 ≤ 10001482521828663^1087*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507870052495384333 12500000000000000000 10001482521828663 10000000000000000 256 1087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001482521828663/10000000000000000 : ℝ)) (X := (12507870052495384333/12500000000000000000 : ℝ)) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(861696814959311/10000000000000000000 : ℝ) ≤ ((1574388713797588019/1574800000000000000 : ℝ)+2*(269167782709/196850000000000 : ℝ)*(5517/50000 : ℝ))^(1087/256 : ℝ) := by
    rw [show (1574388713797588019/1574800000000000000 : ℝ)+2*(269167782709/196850000000000 : ℝ)*(5517/50000 : ℝ)=(10000405850697827/10000000000000000 : ℝ) by norm_num, show 1+2*(861696814959311/10000000000000000000 : ℝ)=(5000861696814959311/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7870052495384333/25000000000000000000 : ℝ)+(861696814959311/10000000000000000000 : ℝ) ≤ ((1574388713797588019/1574800000000000000 : ℝ)+(269167782709/196850000000000 : ℝ)*((14971/100000 : ℝ)+(5517/50000 : ℝ)))^(1087/256 : ℝ) := by
    rw [show (1574388713797588019/1574800000000000000 : ℝ)+(269167782709/196850000000000 : ℝ)*((14971/100000 : ℝ)+(5517/50000 : ℝ))=(2000188837252649/2000000000000000 : ℝ) by norm_num, show 1+(7870052495384333/25000000000000000000 : ℝ)+(861696814959311/10000000000000000000 : ℝ)=(50020048589065565221/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7870052495384333/25000000000000000000 : ℝ) ≤ ((1574388713797588019/1574800000000000000 : ℝ)+2*(269167782709/196850000000000 : ℝ)*(14971/100000 : ℝ))^(1087/256 : ℝ) := by
    rw [show (1574388713797588019/1574800000000000000 : ℝ)+2*(269167782709/196850000000000 : ℝ)*(14971/100000 : ℝ)=(10001482521828663/10000000000000000 : ℝ) by norm_num, show 1+2*(7870052495384333/25000000000000000000 : ℝ)=(12507870052495384333/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1574388713797588019/1574800000000000000 : ℝ)*(X 1 0+X 2 0)+(269167782709/196850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1087/256 : ℝ)) (lo := (5517/50000 : ℝ)) (hi := (14971/100000 : ℝ)) (c := (1574388713797588019/1574800000000000000 : ℝ)) (alpha := (269167782709/196850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1574388713797588019/1574800000000000000 : ℝ)*(X 0 1+X 2 1)+(269167782709/196850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1087/256 : ℝ)) (lo := (5517/50000 : ℝ)) (hi := (14971/100000 : ℝ)) (c := (1574388713797588019/1574800000000000000 : ℝ)) (alpha := (269167782709/196850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1574388713797588019/1574800000000000000 : ℝ)*(X 0 2+X 1 2)+(269167782709/196850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1087/256 : ℝ)) (lo := (5517/50000 : ℝ)) (hi := (14971/100000 : ℝ)) (c := (1574388713797588019/1574800000000000000 : ℝ)) (alpha := (269167782709/196850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-500960431/2500000000 : ℝ)*X 0 0+(5412114667/10000000000 : ℝ)*X 0 1+(5244247037/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((53486083/100000000 : ℝ)*X 1 0+(-2089368491/10000000000 : ℝ)*X 1 1+(5244247071/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674304177/5000000000 : ℝ)*X 2 0+(1311061767/2500000000 : ℝ)*X 2 1+(-2089368423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4314352327/10000000000 : ℝ)*X 0 0+(2069414289/5000000000 : ℝ)*X 0 1+(4496667119/10000000000 : ℝ)*X 0 2+(4314352327/10000000000 : ℝ)*X 1 0+(2069414289/5000000000 : ℝ)*X 1 1+(4496667119/10000000000 : ℝ)*X 1 2+(4314352327/10000000000 : ℝ)*X 2 0+(2069414289/5000000000 : ℝ)*X 2 1+(4496667119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2003854151/10000000000 : ℝ)*X 0 0+(1048972647/2000000000 : ℝ)*X 0 1+(2705747623/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326286149/2500000000 : ℝ)*X 1 0+(-240265031/1250000000 : ℝ)*X 1 1+(541149523/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305144607/10000000000 : ℝ)*X 2 0+(5411495233/10000000000 : ℝ)*X 2 1+(-192212023/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4314378853/10000000000 : ℝ)*X 0 0+(2247676819/5000000000 : ℝ)*X 0 1+(4140149043/10000000000 : ℝ)*X 0 2+(4314378853/10000000000 : ℝ)*X 1 0+(2247676819/5000000000 : ℝ)*X 1 1+(4140149043/10000000000 : ℝ)*X 1 2+(4314378853/10000000000 : ℝ)*X 2 0+(2247676819/5000000000 : ℝ)*X 2 1+(4140149043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8705937893236807216443/984250000000000000000000000 : ℝ) := by norm_num
    linear_combination (196765131/12500000000000 : ℝ)*(base19) + (190971361/12500000000000 : ℝ)*(base23) + (56959441/100000000000000 : ℝ)*(lower2) + (187837911/100000000000000 : ℝ)*(upper3) + (40691003/20000000000000 : ℝ)*(upper5) + (437586501754487/10000000000000 : ℝ)*(major0) + (437586501754487/10000000000000 : ℝ)*(major1) + (437586501754487/10000000000000 : ℝ)*(major2) + (2978553382850069/50000000000000 : ℝ)*(sp0) + (5957139932127331/100000000000000 : ℝ)*(sp1) + (595713997847749/10000000000000 : ℝ)*(sp2) + (2794572066082827/100000000000000 : ℝ)*(sp3) + (34740548241/100000000000000 : ℝ)*(sp4) + (16167916841/100000000000000 : ℝ)*(sp7) + (698647058499917/25000000000000 : ℝ)*(f.failure) + (5957141506248379/100000000000000 : ℝ)*(f.sum) + (16013344581569/3937000000000000000000000000 : ℝ)*base65 + (24782004093304747/15748000000000000000000000000000 : ℝ)*base68 + (30594881640891253/15748000000000000000000000000000 : ℝ)*base69 + (44740567774659253/15748000000000000000000000000000 : ℝ)*base71 + (7638279548159/3937000000000000000000000000 : ℝ)*base74 + (171824305787640747/15748000000000000000000000000000 : ℝ)*base76 + (139677320262979253/15748000000000000000000000000000 : ℝ)*base77 + (145694449496276747/15748000000000000000000000000000 : ℝ)*base80 + (154760655641/393700000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3716661/1250000000000000000000 : ℝ)*base90 + (3716661/1250000000000000000000 : ℝ)*base92 + (3716661/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (349737427901515739071081623/39370000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1513579129/100000000000000 : ℝ)*(base19) + (1681570311/100000000000000 : ℝ)*(base23) + (178781727/100000000000000 : ℝ)*(upper3) + (33628707/50000000000000 : ℝ)*(lower4) + (35072287/20000000000000 : ℝ)*(upper5) + (4408262648391761/100000000000000 : ℝ)*(major0) + (4408262648391761/100000000000000 : ℝ)*(major1) + (4408262648391761/100000000000000 : ℝ)*(major2) + (15130892531/50000000000000 : ℝ)*(sp1) + (263854763/781250000000 : ℝ)*(sp2) + (6001246448846801/100000000000000 : ℝ)*(sp4) + (600121467348261/10000000000000 : ℝ)*(sp5) + (6001210993866827/100000000000000 : ℝ)*(sp6) + (1407639275912549/50000000000000 : ℝ)*(sp7) + (1407639275912549/50000000000000 : ℝ)*(f.failure) + (6001246448846801/100000000000000 : ℝ)*(f.sum) + (1946361671357/19685000000000000000000000000 : ℝ)*base66 + (226547971388983459/157480000000000000000000000000000 : ℝ)*base67 + (164119513411503459/157480000000000000000000000000000 : ℝ)*base69 + (1140689450823616541/157480000000000000000000000000000 : ℝ)*base72 + (8366662573591/2460625000000000000000000000 : ℝ)*base73 + (111490381504623459/157480000000000000000000000000000 : ℝ)*base75 + (292489590686583459/157480000000000000000000000000000 : ℝ)*base77 + (442305081921143459/157480000000000000000000000000000 : ℝ)*base79 + (35819073443839/9842500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (26315917/2500000000000000000000 : ℝ)*base90 + (26315917/2500000000000000000000 : ℝ)*base92 + (26315917/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1389_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78291767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14971/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5517/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1389_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1389_s5_0 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-400804501/2000000000 : ℝ)*x 0 + (5410540717/10000000000 : ℝ)*x 1 + (327856361/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (400804501/2000000000 : ℝ)^4349 ≤ (12215453329377/100000000000000 : ℝ)^3325 := by
    have hnat : (400804501 : ℕ)^4349*100000000000000^3325 ≤ 12215453329377^3325*2000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400804501 2000000000 12215453329377 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410540717/10000000000 : ℝ)^4349 ≤ (44780281440947/100000000000000 : ℝ)^3325 := by
    have hnat : (5410540717 : ℕ)^4349*100000000000000^3325 ≤ 44780281440947^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410540717 10000000000 44780281440947 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327856361/625000000 : ℝ)^4349 ≤ (43004265219553/100000000000000 : ℝ)^3325 := by
    have hnat : (327856361 : ℕ)^4349*100000000000000^3325 ≤ 43004265219553^3325*625000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327856361 625000000 43004265219553 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-400804501/2000000000 : ℝ), (5410540717/10000000000 : ℝ), (327856361/625000000 : ℝ)] ![(12215453329377/100000000000000 : ℝ), (44780281440947/100000000000000 : ℝ), (43004265219553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-400804501/2000000000 : ℝ)|^4349 ≤ (12215453329377/100000000000000 : ℝ)^3325
        have hw : |(-400804501/2000000000 : ℝ)|=(400804501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410540717/10000000000 : ℝ)|^4349 ≤ (44780281440947/100000000000000 : ℝ)^3325
        have hw : |(5410540717/10000000000 : ℝ)|=(5410540717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327856361/625000000 : ℝ)|^4349 ≤ (43004265219553/100000000000000 : ℝ)^3325
        have hw : |(327856361/625000000 : ℝ)|=(327856361/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s5_1 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348203127/10000000000 : ℝ)*x 0 + (-2087977843/10000000000 : ℝ)*x 1 + (5245701981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348203127/10000000000 : ℝ)^4349 ≤ (44106652603291/100000000000000 : ℝ)^3325 := by
    have hnat : (5348203127 : ℕ)^4349*100000000000000^3325 ≤ 44106652603291^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348203127 10000000000 44106652603291 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2087977843/10000000000 : ℝ)^4349 ≤ (1611134995011/12500000000000 : ℝ)^3325 := by
    have hnat : (2087977843 : ℕ)^4349*12500000000000^3325 ≤ 1611134995011^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087977843 10000000000 1611134995011 12500000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245701981/10000000000 : ℝ)^4349 ≤ (21502133708857/50000000000000 : ℝ)^3325 := by
    have hnat : (5245701981 : ℕ)^4349*50000000000000^3325 ≤ 21502133708857^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245701981 10000000000 21502133708857 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348203127/10000000000 : ℝ), (-2087977843/10000000000 : ℝ), (5245701981/10000000000 : ℝ)] ![(44106652603291/100000000000000 : ℝ), (1611134995011/12500000000000 : ℝ), (21502133708857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348203127/10000000000 : ℝ)|^4349 ≤ (44106652603291/100000000000000 : ℝ)^3325
        have hw : |(5348203127/10000000000 : ℝ)|=(5348203127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2087977843/10000000000 : ℝ)|^4349 ≤ (1611134995011/12500000000000 : ℝ)^3325
        have hw : |(-2087977843/10000000000 : ℝ)|=(2087977843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245701981/10000000000 : ℝ)|^4349 ≤ (21502133708857/50000000000000 : ℝ)^3325
        have hw : |(5245701981/10000000000 : ℝ)|=(5245701981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s5_2 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668525401/1250000000 : ℝ)*x 0 + (1049140367/2000000000 : ℝ)*x 1 + (-208797793/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668525401/1250000000 : ℝ)^4349 ≤ (1378332921157/3125000000000 : ℝ)^3325 := by
    have hnat : (668525401 : ℕ)^4349*3125000000000^3325 ≤ 1378332921157^3325*1250000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668525401 1250000000 1378332921157 3125000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049140367/2000000000 : ℝ)^4349 ≤ (21502132926097/50000000000000 : ℝ)^3325 := by
    have hnat : (1049140367 : ℕ)^4349*50000000000000^3325 ≤ 21502132926097^3325*2000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049140367 2000000000 21502132926097 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208797793/1000000000 : ℝ)^4349 ≤ (6444540331267/50000000000000 : ℝ)^3325 := by
    have hnat : (208797793 : ℕ)^4349*50000000000000^3325 ≤ 6444540331267^3325*1000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208797793 1000000000 6444540331267 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668525401/1250000000 : ℝ), (1049140367/2000000000 : ℝ), (-208797793/1000000000 : ℝ)] ![(1378332921157/3125000000000 : ℝ), (21502132926097/50000000000000 : ℝ), (6444540331267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668525401/1250000000 : ℝ)|^4349 ≤ (1378332921157/3125000000000 : ℝ)^3325
        have hw : |(668525401/1250000000 : ℝ)|=(668525401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049140367/2000000000 : ℝ)|^4349 ≤ (21502132926097/50000000000000 : ℝ)^3325
        have hw : |(1049140367/2000000000 : ℝ)|=(1049140367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-208797793/1000000000 : ℝ)|^4349 ≤ (6444540331267/50000000000000 : ℝ)^3325
        have hw : |(-208797793/1000000000 : ℝ)|=(208797793/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s5_3 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4314460449/10000000000 : ℝ)*x 0 + (4142043737/10000000000 : ℝ)*x 1 + (2246712771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314460449/10000000000 : ℝ)^4349 ≤ (33303879871459/100000000000000 : ℝ)^3325 := by
    have hnat : (4314460449 : ℕ)^4349*100000000000000^3325 ≤ 33303879871459^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314460449 10000000000 33303879871459 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4142043737/10000000000 : ℝ)^4349 ≤ (15786953096361/50000000000000 : ℝ)^3325 := by
    have hnat : (4142043737 : ℕ)^4349*50000000000000^3325 ≤ 15786953096361^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4142043737 10000000000 15786953096361 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246712771/5000000000 : ℝ)^4349 ≤ (35122213918579/100000000000000 : ℝ)^3325 := by
    have hnat : (2246712771 : ℕ)^4349*100000000000000^3325 ≤ 35122213918579^3325*5000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246712771 5000000000 35122213918579 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314460449/10000000000 : ℝ), (4142043737/10000000000 : ℝ), (2246712771/5000000000 : ℝ)] ![(33303879871459/100000000000000 : ℝ), (15786953096361/50000000000000 : ℝ), (35122213918579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314460449/10000000000 : ℝ)|^4349 ≤ (33303879871459/100000000000000 : ℝ)^3325
        have hw : |(4314460449/10000000000 : ℝ)|=(4314460449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4142043737/10000000000 : ℝ)|^4349 ≤ (15786953096361/50000000000000 : ℝ)^3325
        have hw : |(4142043737/10000000000 : ℝ)|=(4142043737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2246712771/5000000000 : ℝ)|^4349 ≤ (35122213918579/100000000000000 : ℝ)^3325
        have hw : |(2246712771/5000000000 : ℝ)|=(2246712771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s5_4 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-250504297/1250000000 : ℝ)*x 0 + (2623147899/5000000000 : ℝ)*x 1 + (1081988713/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (250504297/1250000000 : ℝ)^4349 ≤ (12215547973239/100000000000000 : ℝ)^3325 := by
    have hnat : (250504297 : ℕ)^4349*100000000000000^3325 ≤ 12215547973239^3325*1250000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250504297 1250000000 12215547973239 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623147899/5000000000 : ℝ)^4349 ≤ (1344082339777/3125000000000 : ℝ)^3325 := by
    have hnat : (2623147899 : ℕ)^4349*3125000000000^3325 ≤ 1344082339777^3325*5000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623147899 5000000000 1344082339777 3125000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081988713/2000000000 : ℝ)^4349 ≤ (11193454285557/25000000000000 : ℝ)^3325 := by
    have hnat : (1081988713 : ℕ)^4349*25000000000000^3325 ≤ 11193454285557^3325*2000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081988713 2000000000 11193454285557 25000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-250504297/1250000000 : ℝ), (2623147899/5000000000 : ℝ), (1081988713/2000000000 : ℝ)] ![(12215547973239/100000000000000 : ℝ), (1344082339777/3125000000000 : ℝ), (11193454285557/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-250504297/1250000000 : ℝ)|^4349 ≤ (12215547973239/100000000000000 : ℝ)^3325
        have hw : |(-250504297/1250000000 : ℝ)|=(250504297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623147899/5000000000 : ℝ)|^4349 ≤ (1344082339777/3125000000000 : ℝ)^3325
        have hw : |(2623147899/5000000000 : ℝ)|=(2623147899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081988713/2000000000 : ℝ)|^4349 ≤ (11193454285557/25000000000000 : ℝ)^3325
        have hw : |(1081988713/2000000000 : ℝ)|=(1081988713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s5_5 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061104787/2000000000 : ℝ)*x 0 + (-120233503/625000000 : ℝ)*x 1 + (84530363/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061104787/2000000000 : ℝ)^4349 ≤ (43646846036459/100000000000000 : ℝ)^3325 := by
    have hnat : (1061104787 : ℕ)^4349*100000000000000^3325 ≤ 43646846036459^3325*2000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061104787 2000000000 43646846036459 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (120233503/625000000 : ℝ)^4349 ≤ (11579340405587/100000000000000 : ℝ)^3325 := by
    have hnat : (120233503 : ℕ)^4349*100000000000000^3325 ≤ 11579340405587^3325*625000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120233503 625000000 11579340405587 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84530363/156250000 : ℝ)^4349 ≤ (44773813537493/100000000000000 : ℝ)^3325 := by
    have hnat : (84530363 : ℕ)^4349*100000000000000^3325 ≤ 44773813537493^3325*156250000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84530363 156250000 44773813537493 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061104787/2000000000 : ℝ), (-120233503/625000000 : ℝ), (84530363/156250000 : ℝ)] ![(43646846036459/100000000000000 : ℝ), (11579340405587/100000000000000 : ℝ), (44773813537493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061104787/2000000000 : ℝ)|^4349 ≤ (43646846036459/100000000000000 : ℝ)^3325
        have hw : |(1061104787/2000000000 : ℝ)|=(1061104787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-120233503/625000000 : ℝ)|^4349 ≤ (11579340405587/100000000000000 : ℝ)^3325
        have hw : |(-120233503/625000000 : ℝ)|=(120233503/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84530363/156250000 : ℝ)|^4349 ≤ (44773813537493/100000000000000 : ℝ)^3325
        have hw : |(84530363/156250000 : ℝ)|=(84530363/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s5_6 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106110479/200000000 : ℝ)*x 0 + (270497143/500000000 : ℝ)*x 1 + (-1923736541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106110479/200000000 : ℝ)^4349 ≤ (43646846197863/100000000000000 : ℝ)^3325 := by
    have hnat : (106110479 : ℕ)^4349*100000000000000^3325 ≤ 43646846197863^3325*200000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106110479 200000000 43646846197863 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270497143/500000000 : ℝ)^4349 ≤ (22386904755291/50000000000000 : ℝ)^3325 := by
    have hnat : (270497143 : ℕ)^4349*50000000000000^3325 ≤ 22386904755291^3325*500000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270497143 500000000 22386904755291 50000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1923736541/10000000000 : ℝ)^4349 ≤ (11579344286939/100000000000000 : ℝ)^3325 := by
    have hnat : (1923736541 : ℕ)^4349*100000000000000^3325 ≤ 11579344286939^3325*10000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923736541 10000000000 11579344286939 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106110479/200000000 : ℝ), (270497143/500000000 : ℝ), (-1923736541/10000000000 : ℝ)] ![(43646846197863/100000000000000 : ℝ), (22386904755291/50000000000000 : ℝ), (11579344286939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106110479/200000000 : ℝ)|^4349 ≤ (43646846197863/100000000000000 : ℝ)^3325
        have hw : |(106110479/200000000 : ℝ)|=(106110479/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270497143/500000000 : ℝ)|^4349 ≤ (22386904755291/50000000000000 : ℝ)^3325
        have hw : |(270497143/500000000 : ℝ)|=(270497143/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1923736541/10000000000 : ℝ)|^4349 ≤ (11579344286939/100000000000000 : ℝ)^3325
        have hw : |(-1923736541/10000000000 : ℝ)|=(1923736541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1389_s5_7 (p : ℝ) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1078621459/2500000000 : ℝ)*x 0 + (561519829/1250000000 : ℝ)*x 1 + (828663399/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078621459/2500000000 : ℝ)^4349 ≤ (8326034047183/25000000000000 : ℝ)^3325 := by
    have hnat : (1078621459 : ℕ)^4349*25000000000000^3325 ≤ 8326034047183^3325*2500000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078621459 2500000000 8326034047183 25000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561519829/1250000000 : ℝ)^4349 ≤ (877731553807/2500000000000 : ℝ)^3325 := by
    have hnat : (561519829 : ℕ)^4349*2500000000000^3325 ≤ 877731553807^3325*1250000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561519829 1250000000 877731553807 2500000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (828663399/2000000000 : ℝ)^4349 ≤ (31586601650363/100000000000000 : ℝ)^3325 := by
    have hnat : (828663399 : ℕ)^4349*100000000000000^3325 ≤ 31586601650363^3325*2000000000^4349 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828663399 2000000000 31586601650363 100000000000000 4349 3325 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4349/1024 : ℝ)) 4349 3325 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078621459/2500000000 : ℝ), (561519829/1250000000 : ℝ), (828663399/2000000000 : ℝ)] ![(8326034047183/25000000000000 : ℝ), (877731553807/2500000000000 : ℝ), (31586601650363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078621459/2500000000 : ℝ)|^4349 ≤ (8326034047183/25000000000000 : ℝ)^3325
        have hw : |(1078621459/2500000000 : ℝ)|=(1078621459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561519829/1250000000 : ℝ)|^4349 ≤ (877731553807/2500000000000 : ℝ)^3325
        have hw : |(561519829/1250000000 : ℝ)|=(561519829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(828663399/2000000000 : ℝ)|^4349 ≤ (31586601650363/100000000000000 : ℝ)^3325
        have hw : |(828663399/2000000000 : ℝ)|=(828663399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1389_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78291767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9/80 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14741/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7387/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11219/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7387/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11219/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7387/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11219/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7387/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11219/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7387/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11219/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7387/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11219/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11219/100000 : ℝ) ^ (1087/256 : ℝ) ≤ (9247327648747569/100000000000000000000 : ℝ) := by
    have hpowers : (11219/100000 : ℝ)^1087 ≤ (9247327648747569/100000000000000000000 : ℝ)^256 := by
      have hnat : (11219 : ℕ)^1087*100000000000000000000^256 ≤ 9247327648747569^256*100000^1087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11219 100000 9247327648747569 100000000000000000000 1087 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11219/100000 : ℝ)) (X := (9247327648747569/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7387/50000 : ℝ) ^ (1087/256 : ℝ) ≤ (5951700191852263/20000000000000000000 : ℝ) := by
    have hpowers : (7387/50000 : ℝ)^1087 ≤ (5951700191852263/20000000000000000000 : ℝ)^256 := by
      have hnat : (7387 : ℕ)^1087*20000000000000000000^256 ≤ 5951700191852263^256*50000^1087 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7387 50000 5951700191852263 20000000000000000000 1087 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7387/50000 : ℝ)) (X := (5951700191852263/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009247327648747569/50000000000000000000 : ℝ) ≤ (2500108884477427/2500000000000000 : ℝ) ^ (1087/256 : ℝ) := by
    have hpowers : (50009247327648747569/50000000000000000000 : ℝ)^256 ≤ (2500108884477427/2500000000000000 : ℝ)^1087 := by
      have hnat : (50009247327648747569 : ℕ)^256*2500000000000000^1087 ≤ 2500108884477427^1087*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009247327648747569 50000000000000000000 2500108884477427 2500000000000000 256 1087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500108884477427/2500000000000000 : ℝ)) (X := (50009247327648747569/50000000000000000000 : ℝ)) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009751457152002221/25000000000000000000 : ℝ) ≤ (10000918491596233/10000000000000000 : ℝ) ^ (1087/256 : ℝ) := by
    have hpowers : (25009751457152002221/25000000000000000000 : ℝ)^256 ≤ (10000918491596233/10000000000000000 : ℝ)^1087 := by
      have hnat : (25009751457152002221 : ℕ)^256*10000000000000000^1087 ≤ 10000918491596233^1087*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009751457152002221 25000000000000000000 10000918491596233 10000000000000000 256 1087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000918491596233/10000000000000000 : ℝ)) (X := (25009751457152002221/25000000000000000000 : ℝ)) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005951700191852263/10000000000000000000 : ℝ) ≤ (5000700722641379/5000000000000000 : ℝ) ^ (1087/256 : ℝ) := by
    have hpowers : (10005951700191852263/10000000000000000000 : ℝ)^256 ≤ (5000700722641379/5000000000000000 : ℝ)^1087 := by
      have hnat : (10005951700191852263 : ℕ)^256*5000000000000000^1087 ≤ 5000700722641379^1087*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005951700191852263 10000000000000000000 5000700722641379 5000000000000000 256 1087 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000700722641379/5000000000000000 : ℝ)) (X := (10005951700191852263/10000000000000000000 : ℝ)) (by norm_num) 1087 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9247327648747569/100000000000000000000 : ℝ) ≤ ((394896798027230711/395000000000000000 : ℝ)+2*(2146460829/1580000000000 : ℝ)*(11219/100000 : ℝ))^(1087/256 : ℝ) := by
    rw [show (394896798027230711/395000000000000000 : ℝ)+2*(2146460829/1580000000000 : ℝ)*(11219/100000 : ℝ)=(2500108884477427/2500000000000000 : ℝ) by norm_num, show 1+2*(9247327648747569/100000000000000000000 : ℝ)=(50009247327648747569/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5951700191852263/20000000000000000000 : ℝ)+(9247327648747569/100000000000000000000 : ℝ) ≤ ((394896798027230711/395000000000000000 : ℝ)+(2146460829/1580000000000 : ℝ)*((7387/50000 : ℝ)+(11219/100000 : ℝ)))^(1087/256 : ℝ) := by
    rw [show (394896798027230711/395000000000000000 : ℝ)+(2146460829/1580000000000 : ℝ)*((7387/50000 : ℝ)+(11219/100000 : ℝ))=(10000918491596233/10000000000000000 : ℝ) by norm_num, show 1+(5951700191852263/20000000000000000000 : ℝ)+(9247327648747569/100000000000000000000 : ℝ)=(25009751457152002221/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5951700191852263/20000000000000000000 : ℝ) ≤ ((394896798027230711/395000000000000000 : ℝ)+2*(2146460829/1580000000000 : ℝ)*(7387/50000 : ℝ))^(1087/256 : ℝ) := by
    rw [show (394896798027230711/395000000000000000 : ℝ)+2*(2146460829/1580000000000 : ℝ)*(7387/50000 : ℝ)=(5000700722641379/5000000000000000 : ℝ) by norm_num, show 1+2*(5951700191852263/20000000000000000000 : ℝ)=(10005951700191852263/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (394896798027230711/395000000000000000 : ℝ)*(X 1 0+X 2 0)+(2146460829/1580000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1087/256 : ℝ)) (lo := (11219/100000 : ℝ)) (hi := (7387/50000 : ℝ)) (c := (394896798027230711/395000000000000000 : ℝ)) (alpha := (2146460829/1580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (394896798027230711/395000000000000000 : ℝ)*(X 0 1+X 2 1)+(2146460829/1580000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1087/256 : ℝ)) (lo := (11219/100000 : ℝ)) (hi := (7387/50000 : ℝ)) (c := (394896798027230711/395000000000000000 : ℝ)) (alpha := (2146460829/1580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (394896798027230711/395000000000000000 : ℝ)*(X 0 2+X 1 2)+(2146460829/1580000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1087/256 : ℝ)) (lo := (11219/100000 : ℝ)) (hi := (7387/50000 : ℝ)) (c := (394896798027230711/395000000000000000 : ℝ)) (alpha := (2146460829/1580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-400804501/2000000000 : ℝ)*X 0 0+(5410540717/10000000000 : ℝ)*X 0 1+(327856361/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348203127/10000000000 : ℝ)*X 1 0+(-2087977843/10000000000 : ℝ)*X 1 1+(5245701981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668525401/1250000000 : ℝ)*X 2 0+(1049140367/2000000000 : ℝ)*X 2 1+(-208797793/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4314460449/10000000000 : ℝ)*X 0 0+(4142043737/10000000000 : ℝ)*X 0 1+(2246712771/5000000000 : ℝ)*X 0 2+(4314460449/10000000000 : ℝ)*X 1 0+(4142043737/10000000000 : ℝ)*X 1 1+(2246712771/5000000000 : ℝ)*X 1 2+(4314460449/10000000000 : ℝ)*X 2 0+(4142043737/10000000000 : ℝ)*X 2 1+(2246712771/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-250504297/1250000000 : ℝ)*X 0 0+(2623147899/5000000000 : ℝ)*X 0 1+(1081988713/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061104787/2000000000 : ℝ)*X 1 0+(-120233503/625000000 : ℝ)*X 1 1+(84530363/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((106110479/200000000 : ℝ)*X 2 0+(270497143/500000000 : ℝ)*X 2 1+(-1923736541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1078621459/2500000000 : ℝ)*X 0 0+(561519829/1250000000 : ℝ)*X 0 1+(828663399/2000000000 : ℝ)*X 0 2+(1078621459/2500000000 : ℝ)*X 1 0+(561519829/1250000000 : ℝ)*X 1 1+(828663399/2000000000 : ℝ)*X 1 2+(1078621459/2500000000 : ℝ)*X 2 0+(561519829/1250000000 : ℝ)*X 2 1+(828663399/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1389_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (92593514249440517777127777/9875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1684982701/100000000000000 : ℝ)*(base19) + (1619410311/100000000000000 : ℝ)*(base23) + (42104481/50000000000000 : ℝ)*(lower2) + (302808571/100000000000000 : ℝ)*(upper3) + (47697097/50000000000000 : ℝ)*(upper5) + (2228137453085577/50000000000000 : ℝ)*(major0) + (2228137453085577/50000000000000 : ℝ)*(major1) + (2228137453085577/50000000000000 : ℝ)*(major2) + (47395083164267/781250000000 : ℝ)*(sp0) + (303330343524321/5000000000000 : ℝ)*(sp1) + (606660693605881/10000000000000 : ℝ)*(sp2) + (711480496388133/25000000000000 : ℝ)*(sp3) + (7582088589/20000000000000 : ℝ)*(sp4) + (2369846087/12500000000000 : ℝ)*(sp7) + (284594094432123/10000000000000 : ℝ)*(f.failure) + (6066608555469121/100000000000000 : ℝ)*(f.sum) + (35920567327/7900000000000000000000000 : ℝ)*base65 + (124414533393305247/19750000000000000000000000000000 : ℝ)*base67 + (253332281030055247/19750000000000000000000000000000 : ℝ)*base69 + (154697152974805247/19750000000000000000000000000000 : ℝ)*base71 + (82541249441/39500000000000000000000000 : ℝ)*base73 + (446575948279805247/19750000000000000000000000000000 : ℝ)*base75 + (94190516959805247/19750000000000000000000000000000 : ℝ)*base77 + (206695738195305247/19750000000000000000000000000000 : ℝ)*base79 + (61302721911/7900000000000000000000000 : ℝ)*base81 + (1231341/500000000000000000000 : ℝ)*base89 + (1231341/500000000000000000000 : ℝ)*base91 + (1231341/500000000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3383052639302618432791677/617187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2241094703/100000000000000 : ℝ)*(base19) + (275340699/12500000000000 : ℝ)*(base23) + (81832771/100000000000000 : ℝ)*(lower4) + (345328469/100000000000000 : ℝ)*(upper5) + (280541305127921/6250000000000 : ℝ)*(major0) + (280541305127921/6250000000000 : ℝ)*(major1) + (280541305127921/6250000000000 : ℝ)*(major2) + (648964577/50000000000000 : ℝ)*(sp0) + (51540424269/100000000000000 : ℝ)*(sp1) + (25449066703/100000000000000 : ℝ)*(sp2) + (3055348232298653/50000000000000 : ℝ)*(sp4) + (6110643981007487/100000000000000 : ℝ)*(sp5) + (3055335055367083/50000000000000 : ℝ)*(sp6) + (358327977356701/12500000000000 : ℝ)*(sp7) + (358327977356701/12500000000000 : ℝ)*(f.failure) + (6110697762526461/100000000000000 : ℝ)*(f.sum) + (141179679177/39500000000000000000000000 : ℝ)*base66 + (16832376672280669/2468750000000000000000000000000 : ℝ)*base68 + (36703230605655669/2468750000000000000000000000000 : ℝ)*base70 + (2732997165593169/2468750000000000000000000000000 : ℝ)*base72 + (139320903783/79000000000000000000000000 : ℝ)*base74 + (27173217381936919/2468750000000000000000000000000 : ℝ)*base76 + (30683366067593169/2468750000000000000000000000000 : ℝ)*base78 + (31511492971061919/2468750000000000000000000000000 : ℝ)*base80 + (75909480403/19750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/50000000000000 : ℝ)*base86 + (10580667/625000000000000000000 : ℝ)*base89 + (10580667/625000000000000000000 : ℝ)*base91 + (10580667/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1389_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78291767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9/80 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1389_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1389_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78291767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1593/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9/80 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1389_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1389_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1389_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1087/256 : ℝ) ≤ p) (hpb : p ≤ (4349/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78291767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1593/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9/80 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1389_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

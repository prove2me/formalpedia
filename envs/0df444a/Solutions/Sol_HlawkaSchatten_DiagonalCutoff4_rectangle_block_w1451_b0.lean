-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1451_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:59:36.463077+00:00
-- url     : https://prove2.me/submissions/809ecf6b-5cb6-48a7-ac36-414d22adb41a

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
theorem support_rectangle_w1451_s0_0 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-174642477/1000000000 : ℝ)*x 0 + (5951155033/10000000000 : ℝ)*x 1 + (967248489/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174642477/1000000000 : ℝ)^4411 ≤ (10304506594551/100000000000000 : ℝ)^3387 := by
    have hnat : (174642477 : ℕ)^4411*100000000000000^3387 ≤ 10304506594551^3387*1000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174642477 1000000000 10304506594551 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5951155033/10000000000 : ℝ)^4411 ≤ (25434658857471/50000000000000 : ℝ)^3387 := by
    have hnat : (5951155033 : ℕ)^4411*50000000000000^3387 ≤ 25434658857471^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5951155033 10000000000 25434658857471 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (967248489/2000000000 : ℝ)^4411 ≤ (38826175668701/100000000000000 : ℝ)^3387 := by
    have hnat : (967248489 : ℕ)^4411*100000000000000^3387 ≤ 38826175668701^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967248489 2000000000 38826175668701 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-174642477/1000000000 : ℝ), (5951155033/10000000000 : ℝ), (967248489/2000000000 : ℝ)] ![(10304506594551/100000000000000 : ℝ), (25434658857471/50000000000000 : ℝ), (38826175668701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-174642477/1000000000 : ℝ)|^4411 ≤ (10304506594551/100000000000000 : ℝ)^3387
        have hw : |(-174642477/1000000000 : ℝ)|=(174642477/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5951155033/10000000000 : ℝ)|^4411 ≤ (25434658857471/50000000000000 : ℝ)^3387
        have hw : |(5951155033/10000000000 : ℝ)|=(5951155033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(967248489/2000000000 : ℝ)|^4411 ≤ (38826175668701/100000000000000 : ℝ)^3387
        have hw : |(967248489/2000000000 : ℝ)|=(967248489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s0_1 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5489655719/10000000000 : ℝ)*x 0 + (-296910213/1250000000 : ℝ)*x 1 + (4836242327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5489655719/10000000000 : ℝ)^4411 ≤ (45793215939727/100000000000000 : ℝ)^3387 := by
    have hnat : (5489655719 : ℕ)^4411*100000000000000^3387 ≤ 45793215939727^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489655719 10000000000 45793215939727 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (296910213/1250000000 : ℝ)^4411 ≤ (15380609602273/100000000000000 : ℝ)^3387 := by
    have hnat : (296910213 : ℕ)^4411*100000000000000^3387 ≤ 15380609602273^3387*1250000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296910213 1250000000 15380609602273 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4836242327/10000000000 : ℝ)^4411 ≤ (3882617443497/10000000000000 : ℝ)^3387 := by
    have hnat : (4836242327 : ℕ)^4411*10000000000000^3387 ≤ 3882617443497^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4836242327 10000000000 3882617443497 10000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5489655719/10000000000 : ℝ), (-296910213/1250000000 : ℝ), (4836242327/10000000000 : ℝ)] ![(45793215939727/100000000000000 : ℝ), (15380609602273/100000000000000 : ℝ), (3882617443497/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5489655719/10000000000 : ℝ)|^4411 ≤ (45793215939727/100000000000000 : ℝ)^3387
        have hw : |(5489655719/10000000000 : ℝ)|=(5489655719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-296910213/1250000000 : ℝ)|^4411 ≤ (15380609602273/100000000000000 : ℝ)^3387
        have hw : |(-296910213/1250000000 : ℝ)|=(296910213/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4836242327/10000000000 : ℝ)|^4411 ≤ (3882617443497/10000000000000 : ℝ)^3387
        have hw : |(4836242327/10000000000 : ℝ)|=(4836242327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s0_2 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5489655563/10000000000 : ℝ)*x 0 + (4836242291/10000000000 : ℝ)*x 1 + (-2375281951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5489655563/10000000000 : ℝ)^4411 ≤ (4579321424499/10000000000000 : ℝ)^3387 := by
    have hnat : (5489655563 : ℕ)^4411*10000000000000^3387 ≤ 4579321424499^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489655563 10000000000 4579321424499 10000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4836242291/10000000000 : ℝ)^4411 ≤ (19413087029289/50000000000000 : ℝ)^3387 := by
    have hnat : (4836242291 : ℕ)^4411*50000000000000^3387 ≤ 19413087029289^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4836242291 10000000000 19413087029289 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2375281951/10000000000 : ℝ)^4411 ≤ (480644115163/3125000000000 : ℝ)^3387 := by
    have hnat : (2375281951 : ℕ)^4411*3125000000000^3387 ≤ 480644115163^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2375281951 10000000000 480644115163 3125000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5489655563/10000000000 : ℝ), (4836242291/10000000000 : ℝ), (-2375281951/10000000000 : ℝ)] ![(4579321424499/10000000000000 : ℝ), (19413087029289/50000000000000 : ℝ), (480644115163/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5489655563/10000000000 : ℝ)|^4411 ≤ (4579321424499/10000000000000 : ℝ)^3387
        have hw : |(5489655563/10000000000 : ℝ)|=(5489655563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4836242291/10000000000 : ℝ)|^4411 ≤ (19413087029289/50000000000000 : ℝ)^3387
        have hw : |(4836242291/10000000000 : ℝ)|=(4836242291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2375281951/10000000000 : ℝ)|^4411 ≤ (480644115163/3125000000000 : ℝ)^3387
        have hw : |(-2375281951/10000000000 : ℝ)|=(2375281951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s0_3 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4162861973/10000000000 : ℝ)*x 0 + (620575691/2000000000 : ℝ)*x 1 + (5534262721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4162861973/10000000000 : ℝ)^4411 ≤ (3992380075783/12500000000000 : ℝ)^3387 := by
    have hnat : (4162861973 : ℕ)^4411*12500000000000^3387 ≤ 3992380075783^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162861973 10000000000 3992380075783 12500000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (620575691/2000000000 : ℝ)^4411 ≤ (21782552075501/100000000000000 : ℝ)^3387 := by
    have hnat : (620575691 : ℕ)^4411*100000000000000^3387 ≤ 21782552075501^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620575691 2000000000 21782552075501 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5534262721/10000000000 : ℝ)^4411 ≤ (1851136291843/4000000000000 : ℝ)^3387 := by
    have hnat : (5534262721 : ℕ)^4411*4000000000000^3387 ≤ 1851136291843^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5534262721 10000000000 1851136291843 4000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4162861973/10000000000 : ℝ), (620575691/2000000000 : ℝ), (5534262721/10000000000 : ℝ)] ![(3992380075783/12500000000000 : ℝ), (21782552075501/100000000000000 : ℝ), (1851136291843/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4162861973/10000000000 : ℝ)|^4411 ≤ (3992380075783/12500000000000 : ℝ)^3387
        have hw : |(4162861973/10000000000 : ℝ)|=(4162861973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(620575691/2000000000 : ℝ)|^4411 ≤ (21782552075501/100000000000000 : ℝ)^3387
        have hw : |(620575691/2000000000 : ℝ)|=(620575691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5534262721/10000000000 : ℝ)|^4411 ≤ (1851136291843/4000000000000 : ℝ)^3387
        have hw : |(5534262721/10000000000 : ℝ)|=(5534262721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s0_4 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1750337901/10000000000 : ℝ)*x 0 + (2432359457/5000000000 : ℝ)*x 1 + (5921661751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1750337901/10000000000 : ℝ)^4411 ≤ (1033458609131/10000000000000 : ℝ)^3387 := by
    have hnat : (1750337901 : ℕ)^4411*10000000000000^3387 ≤ 1033458609131^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1750337901 10000000000 1033458609131 10000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2432359457/5000000000 : ℝ)^4411 ≤ (39124171651693/100000000000000 : ℝ)^3387 := by
    have hnat : (2432359457 : ℕ)^4411*100000000000000^3387 ≤ 39124171651693^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2432359457 5000000000 39124171651693 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5921661751/10000000000 : ℝ)^4411 ≤ (50541242246627/100000000000000 : ℝ)^3387 := by
    have hnat : (5921661751 : ℕ)^4411*100000000000000^3387 ≤ 50541242246627^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5921661751 10000000000 50541242246627 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1750337901/10000000000 : ℝ), (2432359457/5000000000 : ℝ), (5921661751/10000000000 : ℝ)] ![(1033458609131/10000000000000 : ℝ), (39124171651693/100000000000000 : ℝ), (50541242246627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1750337901/10000000000 : ℝ)|^4411 ≤ (1033458609131/10000000000000 : ℝ)^3387
        have hw : |(-1750337901/10000000000 : ℝ)|=(1750337901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2432359457/5000000000 : ℝ)|^4411 ≤ (39124171651693/100000000000000 : ℝ)^3387
        have hw : |(2432359457/5000000000 : ℝ)|=(2432359457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5921661751/10000000000 : ℝ)|^4411 ≤ (50541242246627/100000000000000 : ℝ)^3387
        have hw : |(5921661751/10000000000 : ℝ)|=(5921661751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s0_5 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1296314247/2500000000 : ℝ)*x 0 + (-257972501/2000000000 : ℝ)*x 1 + (296083091/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1296314247/2500000000 : ℝ)^4411 ≤ (21257201635243/50000000000000 : ℝ)^3387 := by
    have hnat : (1296314247 : ℕ)^4411*50000000000000^3387 ≤ 21257201635243^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296314247 2500000000 21257201635243 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257972501/2000000000 : ℝ)^4411 ≤ (1736088425999/25000000000000 : ℝ)^3387 := by
    have hnat : (257972501 : ℕ)^4411*25000000000000^3387 ≤ 1736088425999^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257972501 2000000000 1736088425999 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (296083091/500000000 : ℝ)^4411 ≤ (12635310753397/25000000000000 : ℝ)^3387 := by
    have hnat : (296083091 : ℕ)^4411*25000000000000^3387 ≤ 12635310753397^3387*500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296083091 500000000 12635310753397 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1296314247/2500000000 : ℝ), (-257972501/2000000000 : ℝ), (296083091/500000000 : ℝ)] ![(21257201635243/50000000000000 : ℝ), (1736088425999/25000000000000 : ℝ), (12635310753397/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1296314247/2500000000 : ℝ)|^4411 ≤ (21257201635243/50000000000000 : ℝ)^3387
        have hw : |(1296314247/2500000000 : ℝ)|=(1296314247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-257972501/2000000000 : ℝ)|^4411 ≤ (1736088425999/25000000000000 : ℝ)^3387
        have hw : |(-257972501/2000000000 : ℝ)|=(257972501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(296083091/500000000 : ℝ)|^4411 ≤ (12635310753397/25000000000000 : ℝ)^3387
        have hw : |(296083091/500000000 : ℝ)|=(296083091/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s0_6 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (259262851/500000000 : ℝ)*x 0 + (185051927/312500000 : ℝ)*x 1 + (-1289862703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259262851/500000000 : ℝ)^4411 ≤ (42514403612181/100000000000000 : ℝ)^3387 := by
    have hnat : (259262851 : ℕ)^4411*100000000000000^3387 ≤ 42514403612181^3387*500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259262851 500000000 42514403612181 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (185051927/312500000 : ℝ)^4411 ≤ (50541241279589/100000000000000 : ℝ)^3387 := by
    have hnat : (185051927 : ℕ)^4411*100000000000000^3387 ≤ 50541241279589^3387*312500000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185051927 312500000 50541241279589 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1289862703/10000000000 : ℝ)^4411 ≤ (6944355092271/100000000000000 : ℝ)^3387 := by
    have hnat : (1289862703 : ℕ)^4411*100000000000000^3387 ≤ 6944355092271^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1289862703 10000000000 6944355092271 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(259262851/500000000 : ℝ), (185051927/312500000 : ℝ), (-1289862703/10000000000 : ℝ)] ![(42514403612181/100000000000000 : ℝ), (50541241279589/100000000000000 : ℝ), (6944355092271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(259262851/500000000 : ℝ)|^4411 ≤ (42514403612181/100000000000000 : ℝ)^3387
        have hw : |(259262851/500000000 : ℝ)|=(259262851/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(185051927/312500000 : ℝ)|^4411 ≤ (50541241279589/100000000000000 : ℝ)^3387
        have hw : |(185051927/312500000 : ℝ)|=(185051927/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1289862703/10000000000 : ℝ)|^4411 ≤ (6944355092271/100000000000000 : ℝ)^3387
        have hw : |(-1289862703/10000000000 : ℝ)|=(1289862703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s0_7 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4171394707/10000000000 : ℝ)*x 0 + (5472161243/10000000000 : ℝ)*x 1 + (3167197207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4171394707/10000000000 : ℝ)^4411 ≤ (8006081487517/25000000000000 : ℝ)^3387 := by
    have hnat : (4171394707 : ℕ)^4411*25000000000000^3387 ≤ 8006081487517^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171394707 10000000000 8006081487517 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5472161243/10000000000 : ℝ)^4411 ≤ (2280162638371/5000000000000 : ℝ)^3387 := by
    have hnat : (5472161243 : ℕ)^4411*5000000000000^3387 ≤ 2280162638371^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472161243 10000000000 2280162638371 5000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3167197207/10000000000 : ℝ)^4411 ≤ (4474484252917/20000000000000 : ℝ)^3387 := by
    have hnat : (3167197207 : ℕ)^4411*20000000000000^3387 ≤ 4474484252917^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3167197207 10000000000 4474484252917 20000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4171394707/10000000000 : ℝ), (5472161243/10000000000 : ℝ), (3167197207/10000000000 : ℝ)] ![(8006081487517/25000000000000 : ℝ), (2280162638371/5000000000000 : ℝ), (4474484252917/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4171394707/10000000000 : ℝ)|^4411 ≤ (8006081487517/25000000000000 : ℝ)^3387
        have hw : |(4171394707/10000000000 : ℝ)|=(4171394707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5472161243/10000000000 : ℝ)|^4411 ≤ (2280162638371/5000000000000 : ℝ)^3387
        have hw : |(5472161243/10000000000 : ℝ)|=(5472161243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3167197207/10000000000 : ℝ)|^4411 ≤ (4474484252917/20000000000000 : ℝ)^3387
        have hw : |(3167197207/10000000000 : ℝ)|=(3167197207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1451_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1101/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26107/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (2205/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2205 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2205*1^512 ≤ 0^512*1^2205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2205 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2205/512 : ℝ) ≤ (1932926732109323269/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2205 ≤ (1932926732109323269/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2205*100000000000000000000^512 ≤ 1932926732109323269^512*5^2205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1932926732109323269 100000000000000000000 2205 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1932926732109323269/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2205 := by
      have hnat : (1 : ℕ)^512*1^2205 ≤ 1^2205*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (101932926732109323269/100000000000000000000 : ℝ) ≤ (5022276581849853/5000000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (101932926732109323269/100000000000000000000 : ℝ)^512 ≤ (5022276581849853/5000000000000000 : ℝ)^2205 := by
      have hnat : (101932926732109323269 : ℕ)^512*5000000000000000^2205 ≤ 5022276581849853^2205*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101932926732109323269 100000000000000000000 5022276581849853 5000000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5022276581849853/5000000000000000 : ℝ)) (X := (101932926732109323269/100000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (51932926732109323269/50000000000000000000 : ℝ) ≤ (2522276581849853/2500000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (51932926732109323269/50000000000000000000 : ℝ)^512 ≤ (2522276581849853/2500000000000000 : ℝ)^2205 := by
      have hnat : (51932926732109323269 : ℕ)^512*2500000000000000^2205 ≤ 2522276581849853^2205*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51932926732109323269 50000000000000000000 2522276581849853 2500000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2522276581849853/2500000000000000 : ℝ)) (X := (51932926732109323269/50000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(22276581849853/2000000000000000 : ℝ)*(0 : ℝ))^(2205/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(22276581849853/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1932926732109323269/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(22276581849853/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2205/512 : ℝ) := by
    rw [show (1 : ℝ)+(22276581849853/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5022276581849853/5000000000000000 : ℝ) by norm_num, show 1+(1932926732109323269/100000000000000000000 : ℝ)+(0 : ℝ)=(101932926732109323269/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1932926732109323269/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(22276581849853/2000000000000000 : ℝ)*(2/5 : ℝ))^(2205/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(22276581849853/2000000000000000 : ℝ)*(2/5 : ℝ)=(2522276581849853/2500000000000000 : ℝ) by norm_num, show 1+2*(1932926732109323269/100000000000000000000 : ℝ)=(51932926732109323269/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(22276581849853/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (22276581849853/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(22276581849853/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (22276581849853/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(22276581849853/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (22276581849853/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-174642477/1000000000 : ℝ)*X 0 0+(5951155033/10000000000 : ℝ)*X 0 1+(967248489/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5489655719/10000000000 : ℝ)*X 1 0+(-296910213/1250000000 : ℝ)*X 1 1+(4836242327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5489655563/10000000000 : ℝ)*X 2 0+(4836242291/10000000000 : ℝ)*X 2 1+(-2375281951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4162861973/10000000000 : ℝ)*X 0 0+(620575691/2000000000 : ℝ)*X 0 1+(5534262721/10000000000 : ℝ)*X 0 2+(4162861973/10000000000 : ℝ)*X 1 0+(620575691/2000000000 : ℝ)*X 1 1+(5534262721/10000000000 : ℝ)*X 1 2+(4162861973/10000000000 : ℝ)*X 2 0+(620575691/2000000000 : ℝ)*X 2 1+(5534262721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1750337901/10000000000 : ℝ)*X 0 0+(2432359457/5000000000 : ℝ)*X 0 1+(5921661751/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1296314247/2500000000 : ℝ)*X 1 0+(-257972501/2000000000 : ℝ)*X 1 1+(296083091/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((259262851/500000000 : ℝ)*X 2 0+(185051927/312500000 : ℝ)*X 2 1+(-1289862703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4171394707/10000000000 : ℝ)*X 0 0+(5472161243/10000000000 : ℝ)*X 0 1+(3167197207/10000000000 : ℝ)*X 0 2+(4171394707/10000000000 : ℝ)*X 1 0+(5472161243/10000000000 : ℝ)*X 1 1+(3167197207/10000000000 : ℝ)*X 1 2+(4171394707/10000000000 : ℝ)*X 2 0+(5472161243/10000000000 : ℝ)*X 2 1+(3167197207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (184508416860702295513587/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3468949/2500000000000 : ℝ)*(base1) + (832390129/100000000000000 : ℝ)*(base19) + (16138037/2000000000000 : ℝ)*(base23) + (117916353/100000000000000 : ℝ)*(upper3) + (21792363/50000000000000 : ℝ)*(upper5) + (654113299690507/100000000000000 : ℝ)*(major0) + (654113299690507/100000000000000 : ℝ)*(major1) + (654113299690507/100000000000000 : ℝ)*(major2) + (35877354724231/4000000000000 : ℝ)*(sp0) + (179387010965179/20000000000000 : ℝ)*(sp1) + (448467540157087/50000000000000 : ℝ)*(sp2) + (411289269936389/100000000000000 : ℝ)*(sp3) + (134866763/6250000000000 : ℝ)*(sp4) + (9222383/781250000000 : ℝ)*(sp7) + (411290589159373/100000000000000 : ℝ)*(f.failure) + (112116985902003/12500000000000 : ℝ)*(f.sum) + (50188087254529/100000000000000000000000000000 : ℝ)*base66 + (1375605340645471/200000000000000000000000000000 : ℝ)*base67 + (1309163539445471/200000000000000000000000000000 : ℝ)*base69 + (635137049445471/200000000000000000000000000000 : ℝ)*base71 + (164244568745471/100000000000000000000000000000 : ℝ)*base73 + (130341576954529/200000000000000000000000000000 : ℝ)*base76 + (175024241954529/200000000000000000000000000000 : ℝ)*base78 + (691399151245471/200000000000000000000000000000 : ℝ)*base79 + (229561547145471/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (43144043/10000000000000000000000 : ℝ)*base90 + (43144043/10000000000000000000000 : ℝ)*base92 + (43144043/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (125342625503640078952623/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (573692933/50000000000000 : ℝ)*(base19) + (1157763851/100000000000000 : ℝ)*(base23) + (12287537/10000000000000 : ℝ)*(base32) + (6988041/4000000000000 : ℝ)*(upper3) + (50094453/50000000000000 : ℝ)*(upper5) + (344992662859303/50000000000000 : ℝ)*(major0) + (344992662859303/50000000000000 : ℝ)*(major1) + (344992662859303/50000000000000 : ℝ)*(major2) + (1380894641/50000000000000 : ℝ)*(sp1) + (2839112567/100000000000000 : ℝ)*(sp2) + (14783194290859/1562500000000 : ℝ)*(sp4) + (236530131359957/25000000000000 : ℝ)*(sp5) + (473060218869279/50000000000000 : ℝ)*(sp6) + (433845926823359/100000000000000 : ℝ)*(sp7) + (433846049698729/100000000000000 : ℝ)*(f.failure) + (14783194290859/1562500000000 : ℝ)*(f.sum) + (6685761617541/50000000000000000000000000000 : ℝ)*base66 + (1076218880132459/100000000000000000000000000000 : ℝ)*base67 + (124577881332459/100000000000000000000000000000 : ℝ)*base69 + (447263746732459/100000000000000000000000000000 : ℝ)*base71 + (273485531782459/50000000000000000000000000000 : ℝ)*base73 + (299845561532459/100000000000000000000000000000 : ℝ)*base75 + (277842190832459/100000000000000000000000000000 : ℝ)*base77 + (761883335632459/100000000000000000000000000000 : ℝ)*base79 + (101886880867541/50000000000000000000000000000 : ℝ)*base82 + (51534639/10000000000000000000000 : ℝ)*base90 + (51534639/10000000000000000000000 : ℝ)*base92 + (51534639/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1451_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1101/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26107/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1451_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1451_s1_0 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-383134511/2000000000 : ℝ)*x 0 + (699566757/1250000000 : ℝ)*x 1 + (2541162083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (383134511/2000000000 : ℝ)^4411 ≤ (11623681798677/100000000000000 : ℝ)^3387 := by
    have hnat : (383134511 : ℕ)^4411*100000000000000^3387 ≤ 11623681798677^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383134511 2000000000 11623681798677 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (699566757/1250000000 : ℝ)^4411 ≤ (46957712310503/100000000000000 : ℝ)^3387 := by
    have hnat : (699566757 : ℕ)^4411*100000000000000^3387 ≤ 46957712310503^3387*1250000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      699566757 1250000000 46957712310503 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2541162083/5000000000 : ℝ)^4411 ≤ (8283721175467/20000000000000 : ℝ)^3387 := by
    have hnat : (2541162083 : ℕ)^4411*20000000000000^3387 ≤ 8283721175467^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541162083 5000000000 8283721175467 20000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-383134511/2000000000 : ℝ), (699566757/1250000000 : ℝ), (2541162083/5000000000 : ℝ)] ![(11623681798677/100000000000000 : ℝ), (46957712310503/100000000000000 : ℝ), (8283721175467/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-383134511/2000000000 : ℝ)|^4411 ≤ (11623681798677/100000000000000 : ℝ)^3387
        have hw : |(-383134511/2000000000 : ℝ)|=(383134511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(699566757/1250000000 : ℝ)|^4411 ≤ (46957712310503/100000000000000 : ℝ)^3387
        have hw : |(699566757/1250000000 : ℝ)|=(699566757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2541162083/5000000000 : ℝ)|^4411 ≤ (8283721175467/20000000000000 : ℝ)^3387
        have hw : |(2541162083/5000000000 : ℝ)|=(2541162083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s1_1 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394614821/10000000000 : ℝ)*x 0 + (-109384849/500000000 : ℝ)*x 1 + (2541162227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394614821/10000000000 : ℝ)^4411 ≤ (8952686585289/20000000000000 : ℝ)^3387 := by
    have hnat : (5394614821 : ℕ)^4411*20000000000000^3387 ≤ 8952686585289^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394614821 10000000000 8952686585289 20000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109384849/500000000 : ℝ)^4411 ≤ (1381795812163/10000000000000 : ℝ)^3387 := by
    have hnat : (109384849 : ℕ)^4411*10000000000000^3387 ≤ 1381795812163^3387*500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109384849 500000000 1381795812163 10000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2541162227/5000000000 : ℝ)^4411 ≤ (20709304466999/50000000000000 : ℝ)^3387 := by
    have hnat : (2541162227 : ℕ)^4411*50000000000000^3387 ≤ 20709304466999^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541162227 5000000000 20709304466999 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394614821/10000000000 : ℝ), (-109384849/500000000 : ℝ), (2541162227/5000000000 : ℝ)] ![(8952686585289/20000000000000 : ℝ), (1381795812163/10000000000000 : ℝ), (20709304466999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394614821/10000000000 : ℝ)|^4411 ≤ (8952686585289/20000000000000 : ℝ)^3387
        have hw : |(5394614821/10000000000 : ℝ)|=(5394614821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-109384849/500000000 : ℝ)|^4411 ≤ (1381795812163/10000000000000 : ℝ)^3387
        have hw : |(-109384849/500000000 : ℝ)|=(109384849/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2541162227/5000000000 : ℝ)|^4411 ≤ (20709304466999/50000000000000 : ℝ)^3387
        have hw : |(2541162227/5000000000 : ℝ)|=(2541162227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s1_2 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348653763/2500000000 : ℝ)*x 0 + (1016464827/2000000000 : ℝ)*x 1 + (-2187697089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348653763/2500000000 : ℝ)^4411 ≤ (22381717711373/50000000000000 : ℝ)^3387 := by
    have hnat : (1348653763 : ℕ)^4411*50000000000000^3387 ≤ 22381717711373^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348653763 2500000000 22381717711373 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016464827/2000000000 : ℝ)^4411 ≤ (258866284677/625000000000 : ℝ)^3387 := by
    have hnat : (1016464827 : ℕ)^4411*625000000000^3387 ≤ 258866284677^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016464827 2000000000 258866284677 625000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2187697089/10000000000 : ℝ)^4411 ≤ (13817959018243/100000000000000 : ℝ)^3387 := by
    have hnat : (2187697089 : ℕ)^4411*100000000000000^3387 ≤ 13817959018243^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187697089 10000000000 13817959018243 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348653763/2500000000 : ℝ), (1016464827/2000000000 : ℝ), (-2187697089/10000000000 : ℝ)] ![(22381717711373/50000000000000 : ℝ), (258866284677/625000000000 : ℝ), (13817959018243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348653763/2500000000 : ℝ)|^4411 ≤ (22381717711373/50000000000000 : ℝ)^3387
        have hw : |(1348653763/2500000000 : ℝ)|=(1348653763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1016464827/2000000000 : ℝ)|^4411 ≤ (258866284677/625000000000 : ℝ)^3387
        have hw : |(1016464827/2000000000 : ℝ)|=(1016464827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2187697089/10000000000 : ℝ)|^4411 ≤ (13817959018243/100000000000000 : ℝ)^3387
        have hw : |(-2187697089/10000000000 : ℝ)|=(2187697089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s1_3 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068158441/2500000000 : ℝ)*x 0 + (748896097/2000000000 : ℝ)*x 1 + (1216465203/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068158441/2500000000 : ℝ)^4411 ≤ (33040224194791/100000000000000 : ℝ)^3387 := by
    have hnat : (1068158441 : ℕ)^4411*100000000000000^3387 ≤ 33040224194791^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068158441 2500000000 33040224194791 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (748896097/2000000000 : ℝ)^4411 ≤ (13911821783241/50000000000000 : ℝ)^3387 := by
    have hnat : (748896097 : ℕ)^4411*50000000000000^3387 ≤ 13911821783241^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748896097 2000000000 13911821783241 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1216465203/2500000000 : ℝ)^4411 ≤ (9784033056177/25000000000000 : ℝ)^3387 := by
    have hnat : (1216465203 : ℕ)^4411*25000000000000^3387 ≤ 9784033056177^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216465203 2500000000 9784033056177 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068158441/2500000000 : ℝ), (748896097/2000000000 : ℝ), (1216465203/2500000000 : ℝ)] ![(33040224194791/100000000000000 : ℝ), (13911821783241/50000000000000 : ℝ), (9784033056177/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068158441/2500000000 : ℝ)|^4411 ≤ (33040224194791/100000000000000 : ℝ)^3387
        have hw : |(1068158441/2500000000 : ℝ)|=(1068158441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(748896097/2000000000 : ℝ)|^4411 ≤ (13911821783241/50000000000000 : ℝ)^3387
        have hw : |(748896097/2000000000 : ℝ)|=(748896097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1216465203/2500000000 : ℝ)|^4411 ≤ (9784033056177/25000000000000 : ℝ)^3387
        have hw : |(1216465203/2500000000 : ℝ)|=(1216465203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s1_4 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-958020781/5000000000 : ℝ)*x 0 + (5088249893/10000000000 : ℝ)*x 1 + (111810193/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (958020781/5000000000 : ℝ)^4411 ≤ (11626597825713/100000000000000 : ℝ)^3387 := by
    have hnat : (958020781 : ℕ)^4411*100000000000000^3387 ≤ 11626597825713^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958020781 5000000000 11626597825713 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5088249893/10000000000 : ℝ)^4411 ≤ (41481509134347/100000000000000 : ℝ)^3387 := by
    have hnat : (5088249893 : ℕ)^4411*100000000000000^3387 ≤ 41481509134347^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5088249893 10000000000 41481509134347 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111810193/200000000 : ℝ)^4411 ≤ (46891893022487/100000000000000 : ℝ)^3387 := by
    have hnat : (111810193 : ℕ)^4411*100000000000000^3387 ≤ 46891893022487^3387*200000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111810193 200000000 46891893022487 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-958020781/5000000000 : ℝ), (5088249893/10000000000 : ℝ), (111810193/200000000 : ℝ)] ![(11626597825713/100000000000000 : ℝ), (41481509134347/100000000000000 : ℝ), (46891893022487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-958020781/5000000000 : ℝ)|^4411 ≤ (11626597825713/100000000000000 : ℝ)^3387
        have hw : |(-958020781/5000000000 : ℝ)|=(958020781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5088249893/10000000000 : ℝ)|^4411 ≤ (41481509134347/100000000000000 : ℝ)^3387
        have hw : |(5088249893/10000000000 : ℝ)|=(5088249893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(111810193/200000000 : ℝ)|^4411 ≤ (46891893022487/100000000000000 : ℝ)^3387
        have hw : |(111810193/200000000 : ℝ)|=(111810193/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s1_5 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2630024867/5000000000 : ℝ)*x 0 + (-1679511363/10000000000 : ℝ)*x 1 + (2795254841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2630024867/5000000000 : ℝ)^4411 ≤ (21657385816671/50000000000000 : ℝ)^3387 := by
    have hnat : (2630024867 : ℕ)^4411*50000000000000^3387 ≤ 21657385816671^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630024867 5000000000 21657385816671 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1679511363/10000000000 : ℝ)^4411 ≤ (9793334991023/100000000000000 : ℝ)^3387 := by
    have hnat : (1679511363 : ℕ)^4411*100000000000000^3387 ≤ 9793334991023^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1679511363 10000000000 9793334991023 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2795254841/5000000000 : ℝ)^4411 ≤ (11722973343011/25000000000000 : ℝ)^3387 := by
    have hnat : (2795254841 : ℕ)^4411*25000000000000^3387 ≤ 11722973343011^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2795254841 5000000000 11722973343011 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2630024867/5000000000 : ℝ), (-1679511363/10000000000 : ℝ), (2795254841/5000000000 : ℝ)] ![(21657385816671/50000000000000 : ℝ), (9793334991023/100000000000000 : ℝ), (11722973343011/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2630024867/5000000000 : ℝ)|^4411 ≤ (21657385816671/50000000000000 : ℝ)^3387
        have hw : |(2630024867/5000000000 : ℝ)|=(2630024867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1679511363/10000000000 : ℝ)|^4411 ≤ (9793334991023/100000000000000 : ℝ)^3387
        have hw : |(-1679511363/10000000000 : ℝ)|=(1679511363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2795254841/5000000000 : ℝ)|^4411 ≤ (11722973343011/25000000000000 : ℝ)^3387
        have hw : |(2795254841/5000000000 : ℝ)|=(2795254841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s1_6 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2630024817/5000000000 : ℝ)*x 0 + (5590509643/10000000000 : ℝ)*x 1 + (-1679511559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2630024817/5000000000 : ℝ)^4411 ≤ (21657385280457/50000000000000 : ℝ)^3387 := by
    have hnat : (2630024817 : ℕ)^4411*50000000000000^3387 ≤ 21657385280457^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630024817 5000000000 21657385280457 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5590509643/10000000000 : ℝ)^4411 ≤ (46891892946021/100000000000000 : ℝ)^3387 := by
    have hnat : (5590509643 : ℕ)^4411*100000000000000^3387 ≤ 46891892946021^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5590509643 10000000000 46891892946021 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1679511559/10000000000 : ℝ)^4411 ≤ (9793336479443/100000000000000 : ℝ)^3387 := by
    have hnat : (1679511559 : ℕ)^4411*100000000000000^3387 ≤ 9793336479443^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1679511559 10000000000 9793336479443 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2630024817/5000000000 : ℝ), (5590509643/10000000000 : ℝ), (-1679511559/10000000000 : ℝ)] ![(21657385280457/50000000000000 : ℝ), (46891892946021/100000000000000 : ℝ), (9793336479443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2630024817/5000000000 : ℝ)|^4411 ≤ (21657385280457/50000000000000 : ℝ)^3387
        have hw : |(2630024817/5000000000 : ℝ)|=(2630024817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5590509643/10000000000 : ℝ)|^4411 ≤ (46891892946021/100000000000000 : ℝ)^3387
        have hw : |(5590509643/10000000000 : ℝ)|=(5590509643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1679511559/10000000000 : ℝ)|^4411 ≤ (9793336479443/100000000000000 : ℝ)^3387
        have hw : |(-1679511559/10000000000 : ℝ)|=(1679511559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s1_7 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (170937539/400000000 : ℝ)*x 0 + (970587691/2000000000 : ℝ)*x 1 + (939404459/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170937539/400000000 : ℝ)^4411 ≤ (33048328606223/100000000000000 : ℝ)^3387 := by
    have hnat : (170937539 : ℕ)^4411*100000000000000^3387 ≤ 33048328606223^3387*400000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170937539 400000000 33048328606223 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (970587691/2000000000 : ℝ)^4411 ≤ (39000829256379/100000000000000 : ℝ)^3387 := by
    have hnat : (970587691 : ℕ)^4411*100000000000000^3387 ≤ 39000829256379^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970587691 2000000000 39000829256379 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (939404459/2500000000 : ℝ)^4411 ≤ (13975421060811/50000000000000 : ℝ)^3387 := by
    have hnat : (939404459 : ℕ)^4411*50000000000000^3387 ≤ 13975421060811^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939404459 2500000000 13975421060811 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(170937539/400000000 : ℝ), (970587691/2000000000 : ℝ), (939404459/2500000000 : ℝ)] ![(33048328606223/100000000000000 : ℝ), (39000829256379/100000000000000 : ℝ), (13975421060811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(170937539/400000000 : ℝ)|^4411 ≤ (33048328606223/100000000000000 : ℝ)^3387
        have hw : |(170937539/400000000 : ℝ)|=(170937539/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(970587691/2000000000 : ℝ)|^4411 ≤ (39000829256379/100000000000000 : ℝ)^3387
        have hw : |(970587691/2000000000 : ℝ)|=(970587691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(939404459/2500000000 : ℝ)|^4411 ≤ (13975421060811/50000000000000 : ℝ)^3387
        have hw : |(939404459/2500000000 : ℝ)|=(939404459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1451_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26107/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1101/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (783/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9351/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26107/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1101/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26107/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1101/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26107/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1101/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26107/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1101/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26107/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1101/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26107/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1101/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1101/50000 : ℝ) ^ (2205/512 : ℝ) ≤ (3648209152057/50000000000000000000 : ℝ) := by
    have hpowers : (1101/50000 : ℝ)^2205 ≤ (3648209152057/50000000000000000000 : ℝ)^512 := by
      have hnat : (1101 : ℕ)^2205*50000000000000000000^512 ≤ 3648209152057^512*50000^2205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1101 50000 3648209152057 50000000000000000000 2205 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1101/50000 : ℝ)) (X := (3648209152057/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hpowhi : (26107/100000 : ℝ) ^ (2205/512 : ℝ) ≤ (307738525925504049/100000000000000000000 : ℝ) := by
    have hpowers : (26107/100000 : ℝ)^2205 ≤ (307738525925504049/100000000000000000000 : ℝ)^512 := by
      have hnat : (26107 : ℕ)^2205*100000000000000000000^512 ≤ 307738525925504049^512*100000^2205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26107 100000 307738525925504049 100000000000000000000 2205 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26107/100000 : ℝ)) (X := (307738525925504049/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000003648209152057/25000000000000000000 : ℝ) ≤ (5000000169422493/5000000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (25000003648209152057/25000000000000000000 : ℝ)^512 ≤ (5000000169422493/5000000000000000 : ℝ)^2205 := by
      have hnat : (25000003648209152057 : ℕ)^512*5000000000000000^2205 ≤ 5000000169422493^2205*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000003648209152057 25000000000000000000 5000000169422493 5000000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000169422493/5000000000000000 : ℝ)) (X := (25000003648209152057/25000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100307745822343808163/100000000000000000000 : ℝ) ≤ (10007137416951427/10000000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (100307745822343808163/100000000000000000000 : ℝ)^512 ≤ (10007137416951427/10000000000000000 : ℝ)^2205 := by
      have hnat : (100307745822343808163 : ℕ)^512*10000000000000000^2205 ≤ 10007137416951427^2205*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100307745822343808163 100000000000000000000 10007137416951427 10000000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007137416951427/10000000000000000 : ℝ)) (X := (100307745822343808163/100000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50307738525925504049/50000000000000000000 : ℝ) ≤ (2503568623764467/2500000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (50307738525925504049/50000000000000000000 : ℝ)^512 ≤ (2503568623764467/2500000000000000 : ℝ)^2205 := by
      have hnat : (50307738525925504049 : ℕ)^512*2500000000000000^2205 ≤ 2503568623764467^2205*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50307738525925504049 50000000000000000000 2503568623764467 2500000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503568623764467/2500000000000000 : ℝ)) (X := (50307738525925504049/50000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3648209152057/50000000000000000000 : ℝ) ≤ ((119509288204054312083/119525000000000000000 : ℝ)+2*(7137078106441/2390500000000000 : ℝ)*(1101/50000 : ℝ))^(2205/512 : ℝ) := by
    rw [show (119509288204054312083/119525000000000000000 : ℝ)+2*(7137078106441/2390500000000000 : ℝ)*(1101/50000 : ℝ)=(5000000169422493/5000000000000000 : ℝ) by norm_num, show 1+2*(3648209152057/50000000000000000000 : ℝ)=(25000003648209152057/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(307738525925504049/100000000000000000000 : ℝ)+(3648209152057/50000000000000000000 : ℝ) ≤ ((119509288204054312083/119525000000000000000 : ℝ)+(7137078106441/2390500000000000 : ℝ)*((26107/100000 : ℝ)+(1101/50000 : ℝ)))^(2205/512 : ℝ) := by
    rw [show (119509288204054312083/119525000000000000000 : ℝ)+(7137078106441/2390500000000000 : ℝ)*((26107/100000 : ℝ)+(1101/50000 : ℝ))=(10007137416951427/10000000000000000 : ℝ) by norm_num, show 1+(307738525925504049/100000000000000000000 : ℝ)+(3648209152057/50000000000000000000 : ℝ)=(100307745822343808163/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(307738525925504049/100000000000000000000 : ℝ) ≤ ((119509288204054312083/119525000000000000000 : ℝ)+2*(7137078106441/2390500000000000 : ℝ)*(26107/100000 : ℝ))^(2205/512 : ℝ) := by
    rw [show (119509288204054312083/119525000000000000000 : ℝ)+2*(7137078106441/2390500000000000 : ℝ)*(26107/100000 : ℝ)=(2503568623764467/2500000000000000 : ℝ) by norm_num, show 1+2*(307738525925504049/100000000000000000000 : ℝ)=(50307738525925504049/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (119509288204054312083/119525000000000000000 : ℝ)*(X 1 0+X 2 0)+(7137078106441/2390500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (1101/50000 : ℝ)) (hi := (26107/100000 : ℝ)) (c := (119509288204054312083/119525000000000000000 : ℝ)) (alpha := (7137078106441/2390500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (119509288204054312083/119525000000000000000 : ℝ)*(X 0 1+X 2 1)+(7137078106441/2390500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (1101/50000 : ℝ)) (hi := (26107/100000 : ℝ)) (c := (119509288204054312083/119525000000000000000 : ℝ)) (alpha := (7137078106441/2390500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (119509288204054312083/119525000000000000000 : ℝ)*(X 0 2+X 1 2)+(7137078106441/2390500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (1101/50000 : ℝ)) (hi := (26107/100000 : ℝ)) (c := (119509288204054312083/119525000000000000000 : ℝ)) (alpha := (7137078106441/2390500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-383134511/2000000000 : ℝ)*X 0 0+(699566757/1250000000 : ℝ)*X 0 1+(2541162083/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5394614821/10000000000 : ℝ)*X 1 0+(-109384849/500000000 : ℝ)*X 1 1+(2541162227/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1348653763/2500000000 : ℝ)*X 2 0+(1016464827/2000000000 : ℝ)*X 2 1+(-2187697089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1068158441/2500000000 : ℝ)*X 0 0+(748896097/2000000000 : ℝ)*X 0 1+(1216465203/2500000000 : ℝ)*X 0 2+(1068158441/2500000000 : ℝ)*X 1 0+(748896097/2000000000 : ℝ)*X 1 1+(1216465203/2500000000 : ℝ)*X 1 2+(1068158441/2500000000 : ℝ)*X 2 0+(748896097/2000000000 : ℝ)*X 2 1+(1216465203/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-958020781/5000000000 : ℝ)*X 0 0+(5088249893/10000000000 : ℝ)*X 0 1+(111810193/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2630024867/5000000000 : ℝ)*X 1 0+(-1679511363/10000000000 : ℝ)*X 1 1+(2795254841/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2630024817/5000000000 : ℝ)*X 2 0+(5590509643/10000000000 : ℝ)*X 2 1+(-1679511559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((170937539/400000000 : ℝ)*X 0 0+(970587691/2000000000 : ℝ)*X 0 1+(939404459/2500000000 : ℝ)*X 0 2+(170937539/400000000 : ℝ)*X 1 0+(970587691/2000000000 : ℝ)*X 1 1+(939404459/2500000000 : ℝ)*X 1 2+(170937539/400000000 : ℝ)*X 2 0+(970587691/2000000000 : ℝ)*X 2 1+(939404459/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (260192153492951901460991139/42687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2079473/5000000000000 : ℝ)*(base1) + (1091209343/100000000000000 : ℝ)*(base19) + (58724217/5000000000000 : ℝ)*(base23) + (141501891/100000000000000 : ℝ)*(upper3) + (108934287/100000000000000 : ℝ)*(upper5) + (70912846584223/5000000000000 : ℝ)*(major0) + (70912846584223/5000000000000 : ℝ)*(major1) + (70912846584223/5000000000000 : ℝ)*(major2) + (1944739656004577/100000000000000 : ℝ)*(sp0) + (194474698450791/10000000000000 : ℝ)*(sp1) + (121546681327057/6250000000000 : ℝ)*(sp2) + (178352329765099/20000000000000 : ℝ)*(sp3) + (1692260427/20000000000000 : ℝ)*(sp4) + (778812159/20000000000000 : ℝ)*(sp7) + (3567062337903/400000000000 : ℝ)*(f.failure) + (486187018929313/25000000000000 : ℝ)*(f.sum) + (654198144337/426875000000000000000000000 : ℝ)*base65 + (93823983141048787/85375000000000000000000000000000 : ℝ)*base67 + (182714774731673787/85375000000000000000000000000000 : ℝ)*base69 + (12587608781951213/85375000000000000000000000000000 : ℝ)*base72 + (2966597946299/853750000000000000000000000 : ℝ)*base73 + (173522709676326213/85375000000000000000000000000000 : ℝ)*base76 + (349807298035298787/85375000000000000000000000000000 : ℝ)*base77 + (368122310916173787/85375000000000000000000000000000 : ℝ)*base79 + (1476186600379/853750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (161273/40000000000000000000 : ℝ)*base90 + (161273/40000000000000000000 : ℝ)*base92 + (161273/40000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5988032881753935594822400053/1494062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17535613/100000000000000 : ℝ)*(base1) + (962509489/100000000000000 : ℝ)*(base19) + (912319041/100000000000000 : ℝ)*(base23) + (109676547/100000000000000 : ℝ)*(upper3) + (8917849/12500000000000 : ℝ)*(upper5) + (725993986491197/50000000000000 : ℝ)*(major0) + (725993986491197/50000000000000 : ℝ)*(major1) + (725993986491197/50000000000000 : ℝ)*(major2) + (245035837/4000000000000 : ℝ)*(sp1) + (2821778017/50000000000000 : ℝ)*(sp2) + (1991000984196543/100000000000000 : ℝ)*(sp4) + (497748469563879/25000000000000 : ℝ)*(sp5) + (995497205392927/50000000000000 : ℝ)*(sp6) + (456487414086011/50000000000000 : ℝ)*(sp7) + (228243711426909/25000000000000 : ℝ)*(f.failure) + (199100096666093/10000000000000 : ℝ)*(f.sum) + (3996552797673/59762500000000000000000000000 : ℝ)*base66 + (25935267439897166649/5976250000000000000000000000000000 : ℝ)*base68 + (43448061075113416649/5976250000000000000000000000000000 : ℝ)*base70 + (30028745954284666649/5976250000000000000000000000000000 : ℝ)*base72 + (3134099236897/3735156250000000000000000000 : ℝ)*base73 + (59083221419203416649/5976250000000000000000000000000000 : ℝ)*base76 + (33486389268453416649/5976250000000000000000000000000000 : ℝ)*base78 + (8683052263911583351/5976250000000000000000000000000000 : ℝ)*base79 + (46899256467373/59762500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (18674981/2500000000000000000000 : ℝ)*base89 + (18674981/2500000000000000000000 : ℝ)*base91 + (18674981/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1451_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26107/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1101/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (783/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9351/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1451_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1451_s2_0 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1947198297/10000000000 : ℝ)*x 0 + (1090673109/2000000000 : ℝ)*x 1 + (1041035099/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1947198297/10000000000 : ℝ)^4411 ≤ (5936709882871/50000000000000 : ℝ)^3387 := by
    have hnat : (1947198297 : ℕ)^4411*50000000000000^3387 ≤ 5936709882871^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947198297 10000000000 5936709882871 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090673109/2000000000 : ℝ)^4411 ≤ (2837460302251/6250000000000 : ℝ)^3387 := by
    have hnat : (1090673109 : ℕ)^4411*6250000000000^3387 ≤ 2837460302251^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090673109 2000000000 2837460302251 6250000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041035099/2000000000 : ℝ)^4411 ≤ (42727215379983/100000000000000 : ℝ)^3387 := by
    have hnat : (1041035099 : ℕ)^4411*100000000000000^3387 ≤ 42727215379983^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041035099 2000000000 42727215379983 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1947198297/10000000000 : ℝ), (1090673109/2000000000 : ℝ), (1041035099/2000000000 : ℝ)] ![(5936709882871/50000000000000 : ℝ), (2837460302251/6250000000000 : ℝ), (42727215379983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1947198297/10000000000 : ℝ)|^4411 ≤ (5936709882871/50000000000000 : ℝ)^3387
        have hw : |(-1947198297/10000000000 : ℝ)|=(1947198297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090673109/2000000000 : ℝ)|^4411 ≤ (2837460302251/6250000000000 : ℝ)^3387
        have hw : |(1090673109/2000000000 : ℝ)|=(1090673109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1041035099/2000000000 : ℝ)|^4411 ≤ (42727215379983/100000000000000 : ℝ)^3387
        have hw : |(1041035099/2000000000 : ℝ)|=(1041035099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s2_1 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679382139/5000000000 : ℝ)*x 0 + (-1037385027/5000000000 : ℝ)*x 1 + (5205175521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679382139/5000000000 : ℝ)^4411 ≤ (11094101014997/25000000000000 : ℝ)^3387 := by
    have hnat : (2679382139 : ℕ)^4411*25000000000000^3387 ≤ 11094101014997^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679382139 5000000000 11094101014997 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037385027/5000000000 : ℝ)^4411 ≤ (1612047534017/12500000000000 : ℝ)^3387 := by
    have hnat : (1037385027 : ℕ)^4411*12500000000000^3387 ≤ 1612047534017^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037385027 5000000000 1612047534017 12500000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5205175521/10000000000 : ℝ)^4411 ≤ (10681803914483/25000000000000 : ℝ)^3387 := by
    have hnat : (5205175521 : ℕ)^4411*25000000000000^3387 ≤ 10681803914483^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205175521 10000000000 10681803914483 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679382139/5000000000 : ℝ), (-1037385027/5000000000 : ℝ), (5205175521/10000000000 : ℝ)] ![(11094101014997/25000000000000 : ℝ), (1612047534017/12500000000000 : ℝ), (10681803914483/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679382139/5000000000 : ℝ)|^4411 ≤ (11094101014997/25000000000000 : ℝ)^3387
        have hw : |(2679382139/5000000000 : ℝ)|=(2679382139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1037385027/5000000000 : ℝ)|^4411 ≤ (1612047534017/12500000000000 : ℝ)^3387
        have hw : |(-1037385027/5000000000 : ℝ)|=(1037385027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5205175521/10000000000 : ℝ)|^4411 ≤ (10681803914483/25000000000000 : ℝ)^3387
        have hw : |(5205175521/10000000000 : ℝ)|=(5205175521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s2_2 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358764473/10000000000 : ℝ)*x 0 + (650646911/1250000000 : ℝ)*x 1 + (-1037385051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358764473/10000000000 : ℝ)^4411 ≤ (4437640616301/10000000000000 : ℝ)^3387 := by
    have hnat : (5358764473 : ℕ)^4411*10000000000000^3387 ≤ 4437640616301^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358764473 10000000000 4437640616301 10000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (650646911/1250000000 : ℝ)^4411 ≤ (8545442633417/20000000000000 : ℝ)^3387 := by
    have hnat : (650646911 : ℕ)^4411*20000000000000^3387 ≤ 8545442633417^3387*1250000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650646911 1250000000 8545442633417 20000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037385051/5000000000 : ℝ)^4411 ≤ (12896380660699/100000000000000 : ℝ)^3387 := by
    have hnat : (1037385051 : ℕ)^4411*100000000000000^3387 ≤ 12896380660699^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037385051 5000000000 12896380660699 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358764473/10000000000 : ℝ), (650646911/1250000000 : ℝ), (-1037385051/5000000000 : ℝ)] ![(4437640616301/10000000000000 : ℝ), (8545442633417/20000000000000 : ℝ), (12896380660699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358764473/10000000000 : ℝ)|^4411 ≤ (4437640616301/10000000000000 : ℝ)^3387
        have hw : |(5358764473/10000000000 : ℝ)|=(5358764473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(650646911/1250000000 : ℝ)|^4411 ≤ (8545442633417/20000000000000 : ℝ)^3387
        have hw : |(650646911/1250000000 : ℝ)|=(650646911/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1037385051/5000000000 : ℝ)|^4411 ≤ (12896380660699/100000000000000 : ℝ)^3387
        have hw : |(-1037385051/5000000000 : ℝ)|=(1037385051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s2_3 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134216779/312500000 : ℝ)*x 0 + (4031894557/10000000000 : ℝ)*x 1 + (914628691/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134216779/312500000 : ℝ)^4411 ≤ (32485365837/97656250000 : ℝ)^3387 := by
    have hnat : (134216779 : ℕ)^4411*97656250000^3387 ≤ 32485365837^3387*312500000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134216779 312500000 32485365837 97656250000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4031894557/10000000000 : ℝ)^4411 ≤ (15318343032563/50000000000000 : ℝ)^3387 := by
    have hnat : (4031894557 : ℕ)^4411*50000000000000^3387 ≤ 15318343032563^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031894557 10000000000 15318343032563 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (914628691/2000000000 : ℝ)^4411 ≤ (36098299291979/100000000000000 : ℝ)^3387 := by
    have hnat : (914628691 : ℕ)^4411*100000000000000^3387 ≤ 36098299291979^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914628691 2000000000 36098299291979 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134216779/312500000 : ℝ), (4031894557/10000000000 : ℝ), (914628691/2000000000 : ℝ)] ![(32485365837/97656250000 : ℝ), (15318343032563/50000000000000 : ℝ), (36098299291979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134216779/312500000 : ℝ)|^4411 ≤ (32485365837/97656250000 : ℝ)^3387
        have hw : |(134216779/312500000 : ℝ)|=(134216779/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4031894557/10000000000 : ℝ)|^4411 ≤ (15318343032563/50000000000000 : ℝ)^3387
        have hw : |(4031894557/10000000000 : ℝ)|=(4031894557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(914628691/2000000000 : ℝ)|^4411 ≤ (36098299291979/100000000000000 : ℝ)^3387
        have hw : |(914628691/2000000000 : ℝ)|=(914628691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s2_4 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1947239271/10000000000 : ℝ)*x 0 + (2603282979/5000000000 : ℝ)*x 1 + (1090392881/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1947239271/10000000000 : ℝ)^4411 ≤ (11873745150531/100000000000000 : ℝ)^3387 := by
    have hnat : (1947239271 : ℕ)^4411*100000000000000^3387 ≤ 11873745150531^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947239271 10000000000 11873745150531 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2603282979/5000000000 : ℝ)^4411 ≤ (21371040243621/50000000000000 : ℝ)^3387 := by
    have hnat : (2603282979 : ℕ)^4411*50000000000000^3387 ≤ 21371040243621^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603282979 5000000000 21371040243621 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090392881/2000000000 : ℝ)^4411 ≤ (11346043587313/25000000000000 : ℝ)^3387 := by
    have hnat : (1090392881 : ℕ)^4411*25000000000000^3387 ≤ 11346043587313^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090392881 2000000000 11346043587313 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1947239271/10000000000 : ℝ), (2603282979/5000000000 : ℝ), (1090392881/2000000000 : ℝ)] ![(11873745150531/100000000000000 : ℝ), (21371040243621/50000000000000 : ℝ), (11346043587313/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1947239271/10000000000 : ℝ)|^4411 ≤ (11873745150531/100000000000000 : ℝ)^3387
        have hw : |(-1947239271/10000000000 : ℝ)|=(1947239271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2603282979/5000000000 : ℝ)|^4411 ≤ (21371040243621/50000000000000 : ℝ)^3387
        have hw : |(2603282979/5000000000 : ℝ)|=(2603282979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1090392881/2000000000 : ℝ)|^4411 ≤ (11346043587313/25000000000000 : ℝ)^3387
        have hw : |(1090392881/2000000000 : ℝ)|=(1090392881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s2_5 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323523833/2500000000 : ℝ)*x 0 + (-1827979593/10000000000 : ℝ)*x 1 + (2725982903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323523833/2500000000 : ℝ)^4411 ≤ (43680242770499/100000000000000 : ℝ)^3387 := by
    have hnat : (1323523833 : ℕ)^4411*100000000000000^3387 ≤ 43680242770499^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323523833 2500000000 43680242770499 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1827979593/10000000000 : ℝ)^4411 ≤ (273389192057/2500000000000 : ℝ)^3387 := by
    have hnat : (1827979593 : ℕ)^4411*2500000000000^3387 ≤ 273389192057^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1827979593 10000000000 273389192057 2500000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725982903/5000000000 : ℝ)^4411 ≤ (45384189537631/100000000000000 : ℝ)^3387 := by
    have hnat : (2725982903 : ℕ)^4411*100000000000000^3387 ≤ 45384189537631^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725982903 5000000000 45384189537631 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323523833/2500000000 : ℝ), (-1827979593/10000000000 : ℝ), (2725982903/5000000000 : ℝ)] ![(43680242770499/100000000000000 : ℝ), (273389192057/2500000000000 : ℝ), (45384189537631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323523833/2500000000 : ℝ)|^4411 ≤ (43680242770499/100000000000000 : ℝ)^3387
        have hw : |(1323523833/2500000000 : ℝ)|=(1323523833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1827979593/10000000000 : ℝ)|^4411 ≤ (273389192057/2500000000000 : ℝ)^3387
        have hw : |(-1827979593/10000000000 : ℝ)|=(1827979593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725982903/5000000000 : ℝ)|^4411 ≤ (45384189537631/100000000000000 : ℝ)^3387
        have hw : |(2725982903/5000000000 : ℝ)|=(2725982903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s2_6 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294094271/10000000000 : ℝ)*x 0 + (136299131/250000000 : ℝ)*x 1 + (-1827981843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294094271/10000000000 : ℝ)^4411 ≤ (1747209254793/4000000000000 : ℝ)^3387 := by
    have hnat : (5294094271 : ℕ)^4411*4000000000000^3387 ≤ 1747209254793^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294094271 10000000000 1747209254793 4000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136299131/250000000 : ℝ)^4411 ≤ (45384183401569/100000000000000 : ℝ)^3387 := by
    have hnat : (136299131 : ℕ)^4411*100000000000000^3387 ≤ 45384183401569^3387*250000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136299131 250000000 45384183401569 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1827981843/10000000000 : ℝ)^4411 ≤ (10935585211979/100000000000000 : ℝ)^3387 := by
    have hnat : (1827981843 : ℕ)^4411*100000000000000^3387 ≤ 10935585211979^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1827981843 10000000000 10935585211979 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294094271/10000000000 : ℝ), (136299131/250000000 : ℝ), (-1827981843/10000000000 : ℝ)] ![(1747209254793/4000000000000 : ℝ), (45384183401569/100000000000000 : ℝ), (10935585211979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294094271/10000000000 : ℝ)|^4411 ≤ (1747209254793/4000000000000 : ℝ)^3387
        have hw : |(5294094271/10000000000 : ℝ)|=(5294094271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136299131/250000000 : ℝ)|^4411 ≤ (45384183401569/100000000000000 : ℝ)^3387
        have hw : |(136299131/250000000 : ℝ)|=(136299131/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1827981843/10000000000 : ℝ)|^4411 ≤ (10935585211979/100000000000000 : ℝ)^3387
        have hw : |(-1827981843/10000000000 : ℝ)|=(1827981843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s2_7 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2147513827/5000000000 : ℝ)*x 0 + (4570114589/10000000000 : ℝ)*x 1 + (4034947857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147513827/5000000000 : ℝ)^4411 ≤ (33265929753719/100000000000000 : ℝ)^3387 := by
    have hnat : (2147513827 : ℕ)^4411*100000000000000^3387 ≤ 33265929753719^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147513827 5000000000 33265929753719 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4570114589/10000000000 : ℝ)^4411 ≤ (7213433123973/20000000000000 : ℝ)^3387 := by
    have hnat : (4570114589 : ℕ)^4411*20000000000000^3387 ≤ 7213433123973^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4570114589 10000000000 7213433123973 20000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4034947857/10000000000 : ℝ)^4411 ≤ (30666904618101/100000000000000 : ℝ)^3387 := by
    have hnat : (4034947857 : ℕ)^4411*100000000000000^3387 ≤ 30666904618101^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4034947857 10000000000 30666904618101 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2147513827/5000000000 : ℝ), (4570114589/10000000000 : ℝ), (4034947857/10000000000 : ℝ)] ![(33265929753719/100000000000000 : ℝ), (7213433123973/20000000000000 : ℝ), (30666904618101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2147513827/5000000000 : ℝ)|^4411 ≤ (33265929753719/100000000000000 : ℝ)^3387
        have hw : |(2147513827/5000000000 : ℝ)|=(2147513827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4570114589/10000000000 : ℝ)|^4411 ≤ (7213433123973/20000000000000 : ℝ)^3387
        have hw : |(4570114589/10000000000 : ℝ)|=(4570114589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4034947857/10000000000 : ℝ)|^4411 ≤ (30666904618101/100000000000000 : ℝ)^3387
        have hw : |(4034947857/10000000000 : ℝ)|=(4034947857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1451_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9351/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (783/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (5241/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7867/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9351/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (783/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9351/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (783/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9351/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (783/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9351/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (783/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9351/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (783/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9351/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (783/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (783/10000 : ℝ) ^ (2205/512 : ℝ) ≤ (860596286757783/50000000000000000000 : ℝ) := by
    have hpowers : (783/10000 : ℝ)^2205 ≤ (860596286757783/50000000000000000000 : ℝ)^512 := by
      have hnat : (783 : ℕ)^2205*50000000000000000000^512 ≤ 860596286757783^512*10000^2205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        783 10000 860596286757783 50000000000000000000 2205 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (783/10000 : ℝ)) (X := (860596286757783/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hpowhi : (9351/50000 : ℝ) ^ (2205/512 : ℝ) ≤ (14632330558236209/20000000000000000000 : ℝ) := by
    have hpowers : (9351/50000 : ℝ)^2205 ≤ (14632330558236209/20000000000000000000 : ℝ)^512 := by
      have hnat : (9351 : ℕ)^2205*20000000000000000000^512 ≤ 14632330558236209^512*50000^2205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9351 50000 14632330558236209 20000000000000000000 2205 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9351/50000 : ℝ)) (X := (14632330558236209/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000860596286757783/25000000000000000000 : ℝ) ≤ (10000079930970691/10000000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (25000860596286757783/25000000000000000000 : ℝ)^512 ≤ (10000079930970691/10000000000000000 : ℝ)^2205 := by
      have hnat : (25000860596286757783 : ℕ)^512*10000000000000000^2205 ≤ 10000079930970691^2205*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000860596286757783 25000000000000000000 10000079930970691 10000000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000079930970691/10000000000000000 : ℝ)) (X := (25000860596286757783/25000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100074882845364696611/100000000000000000000 : ℝ) ≤ (5000869138319173/5000000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (100074882845364696611/100000000000000000000 : ℝ)^512 ≤ (5000869138319173/5000000000000000 : ℝ)^2205 := by
      have hnat : (100074882845364696611 : ℕ)^512*5000000000000000^2205 ≤ 5000869138319173^2205*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100074882845364696611 100000000000000000000 5000869138319173 5000000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000869138319173/5000000000000000 : ℝ)) (X := (100074882845364696611/100000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10014632330558236209/10000000000000000000 : ℝ) ≤ (10003396622306001/10000000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (10014632330558236209/10000000000000000000 : ℝ)^512 ≤ (10003396622306001/10000000000000000 : ℝ)^2205 := by
      have hnat : (10014632330558236209 : ℕ)^512*10000000000000000^2205 ≤ 10003396622306001^2205*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10014632330558236209 10000000000000000000 10003396622306001 10000000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003396622306001/10000000000000000 : ℝ)) (X := (10014632330558236209/10000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(860596286757783/50000000000000000000 : ℝ) ≤ ((3019302758787718757/3020000000000000000 : ℝ)+2*(331669133531/217440000000000 : ℝ)*(783/10000 : ℝ))^(2205/512 : ℝ) := by
    rw [show (3019302758787718757/3020000000000000000 : ℝ)+2*(331669133531/217440000000000 : ℝ)*(783/10000 : ℝ)=(10000079930970691/10000000000000000 : ℝ) by norm_num, show 1+2*(860596286757783/50000000000000000000 : ℝ)=(25000860596286757783/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14632330558236209/20000000000000000000 : ℝ)+(860596286757783/50000000000000000000 : ℝ) ≤ ((3019302758787718757/3020000000000000000 : ℝ)+(331669133531/217440000000000 : ℝ)*((9351/50000 : ℝ)+(783/10000 : ℝ)))^(2205/512 : ℝ) := by
    rw [show (3019302758787718757/3020000000000000000 : ℝ)+(331669133531/217440000000000 : ℝ)*((9351/50000 : ℝ)+(783/10000 : ℝ))=(5000869138319173/5000000000000000 : ℝ) by norm_num, show 1+(14632330558236209/20000000000000000000 : ℝ)+(860596286757783/50000000000000000000 : ℝ)=(100074882845364696611/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14632330558236209/20000000000000000000 : ℝ) ≤ ((3019302758787718757/3020000000000000000 : ℝ)+2*(331669133531/217440000000000 : ℝ)*(9351/50000 : ℝ))^(2205/512 : ℝ) := by
    rw [show (3019302758787718757/3020000000000000000 : ℝ)+2*(331669133531/217440000000000 : ℝ)*(9351/50000 : ℝ)=(10003396622306001/10000000000000000 : ℝ) by norm_num, show 1+2*(14632330558236209/20000000000000000000 : ℝ)=(10014632330558236209/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3019302758787718757/3020000000000000000 : ℝ)*(X 1 0+X 2 0)+(331669133531/217440000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (783/10000 : ℝ)) (hi := (9351/50000 : ℝ)) (c := (3019302758787718757/3020000000000000000 : ℝ)) (alpha := (331669133531/217440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3019302758787718757/3020000000000000000 : ℝ)*(X 0 1+X 2 1)+(331669133531/217440000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (783/10000 : ℝ)) (hi := (9351/50000 : ℝ)) (c := (3019302758787718757/3020000000000000000 : ℝ)) (alpha := (331669133531/217440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3019302758787718757/3020000000000000000 : ℝ)*(X 0 2+X 1 2)+(331669133531/217440000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (783/10000 : ℝ)) (hi := (9351/50000 : ℝ)) (c := (3019302758787718757/3020000000000000000 : ℝ)) (alpha := (331669133531/217440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1947198297/10000000000 : ℝ)*X 0 0+(1090673109/2000000000 : ℝ)*X 0 1+(1041035099/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2679382139/5000000000 : ℝ)*X 1 0+(-1037385027/5000000000 : ℝ)*X 1 1+(5205175521/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5358764473/10000000000 : ℝ)*X 2 0+(650646911/1250000000 : ℝ)*X 2 1+(-1037385051/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((134216779/312500000 : ℝ)*X 0 0+(4031894557/10000000000 : ℝ)*X 0 1+(914628691/2000000000 : ℝ)*X 0 2+(134216779/312500000 : ℝ)*X 1 0+(4031894557/10000000000 : ℝ)*X 1 1+(914628691/2000000000 : ℝ)*X 1 2+(134216779/312500000 : ℝ)*X 2 0+(4031894557/10000000000 : ℝ)*X 2 1+(914628691/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1947239271/10000000000 : ℝ)*X 0 0+(2603282979/5000000000 : ℝ)*X 0 1+(1090392881/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323523833/2500000000 : ℝ)*X 1 0+(-1827979593/10000000000 : ℝ)*X 1 1+(2725982903/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294094271/10000000000 : ℝ)*X 2 0+(136299131/250000000 : ℝ)*X 2 1+(-1827981843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2147513827/5000000000 : ℝ)*X 0 0+(4570114589/10000000000 : ℝ)*X 0 1+(4034947857/10000000000 : ℝ)*X 0 2+(2147513827/5000000000 : ℝ)*X 1 0+(4570114589/10000000000 : ℝ)*X 1 1+(4034947857/10000000000 : ℝ)*X 1 2+(2147513827/5000000000 : ℝ)*X 2 0+(4570114589/10000000000 : ℝ)*X 2 1+(4034947857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (415427808913302505613932493/75500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (627083447/50000000000000 : ℝ)*(base19) + (661955971/50000000000000 : ℝ)*(base23) + (41194773/100000000000000 : ℝ)*(lower2) + (172464761/100000000000000 : ℝ)*(upper3) + (48049957/50000000000000 : ℝ)*(upper5) + (1469200481757361/50000000000000 : ℝ)*(major0) + (1469200481757361/50000000000000 : ℝ)*(major1) + (1469200481757361/50000000000000 : ℝ)*(major2) + (805837726473069/20000000000000 : ℝ)*(sp0) + (402920518135613/10000000000000 : ℝ)*(sp1) + (2014602555805541/50000000000000 : ℝ)*(sp2) + (230948294124541/12500000000000 : ℝ)*(sp3) + (17803157679/100000000000000 : ℝ)*(sp4) + (4477549123/50000000000000 : ℝ)*(sp7) + (923797654047287/50000000000000 : ℝ)*(f.failure) + (251825402220189/6250000000000 : ℝ)*(f.sum) + (4365000084493/5436000000000000000000000000 : ℝ)*base66 + (18360576700118942507/1359000000000000000000000000000000 : ℝ)*base68 + (15107948457983942507/1359000000000000000000000000000000 : ℝ)*base70 + (14414302050767942507/1359000000000000000000000000000000 : ℝ)*base72 + (24103663902829/5436000000000000000000000000 : ℝ)*base74 + (19548694266623942507/1359000000000000000000000000000000 : ℝ)*base76 + (7584464963681942507/1359000000000000000000000000000000 : ℝ)*base78 + (25468978556249942507/1359000000000000000000000000000000 : ℝ)*base80 + (24784007178637/5436000000000000000000000000 : ℝ)*base82 + (73075983/5000000000000000000000 : ℝ)*base89 + (73075983/5000000000000000000000 : ℝ)*base91 + (73075983/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (90065776385441007358386323/18875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7369413/25000000000000 : ℝ)*(base8) + (191695059/50000000000000 : ℝ)*(base21) + (9824807/12500000000000 : ℝ)*(upper2) + (347381277/100000000000000 : ℝ)*(lower4) + (742949737091313/25000000000000 : ℝ)*(major0) + (742949737091313/25000000000000 : ℝ)*(major1) + (742949737091313/25000000000000 : ℝ)*(major2) + (156410683/5000000000000 : ℝ)*(sp0) + (26912721341/100000000000000 : ℝ)*(sp1) + (5475015489/50000000000000 : ℝ)*(sp3) + (407499942847803/10000000000000 : ℝ)*(sp4) + (509371959181/12500000000 : ℝ)*(sp5) + (509375275347403/12500000000000 : ℝ)*(sp6) + (467146050368403/25000000000000 : ℝ)*(sp7) + (1868595151504591/100000000000000 : ℝ)*(f.failure) + (4075002586169341/100000000000000 : ℝ)*(f.sum) + (19967334479509/906000000000000000000000000 : ℝ)*base65 + (2111220348840301177/226500000000000000000000000000000 : ℝ)*base68 + (2369843183595301177/226500000000000000000000000000000 : ℝ)*base70 + (3222434499095698823/226500000000000000000000000000000 : ℝ)*base71 + (3013757730601/906000000000000000000000000 : ℝ)*base73 + (1632766387786801177/226500000000000000000000000000000 : ℝ)*base76 + (1532351554113301177/226500000000000000000000000000000 : ℝ)*base78 + (2802255160320301177/226500000000000000000000000000000 : ℝ)*base80 + (5115095315749/906000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (112508519/10000000000000000000000 : ℝ)*base89 + (112508519/10000000000000000000000 : ℝ)*base91 + (112508519/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1451_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9351/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (783/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5241/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7867/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1451_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1451_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5241/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7867/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1451_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1451_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1451_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5241/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7867/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1451_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

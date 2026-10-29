-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1364_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:18:46.76336+00:00
-- url     : https://prove2.me/submissions/1fe7130f-7515-45b1-bb1f-31ba8883fda2

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
theorem support_rectangle_w1364_s3_0 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2023568061/10000000000 : ℝ)*x 0 + (678055577/1250000000 : ℝ)*x 1 + (5233404471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2023568061/10000000000 : ℝ)^1081 ≤ (12325486540103/100000000000000 : ℝ)^825 := by
    have hnat : (2023568061 : ℕ)^1081*100000000000000^825 ≤ 12325486540103^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023568061 10000000000 12325486540103 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678055577/1250000000 : ℝ)^1081 ≤ (4486678158969/10000000000000 : ℝ)^825 := by
    have hnat : (678055577 : ℕ)^1081*10000000000000^825 ≤ 4486678158969^825*1250000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678055577 1250000000 4486678158969 10000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5233404471/10000000000 : ℝ)^1081 ≤ (17123092741/40000000000 : ℝ)^825 := by
    have hnat : (5233404471 : ℕ)^1081*40000000000^825 ≤ 17123092741^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233404471 10000000000 17123092741 40000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2023568061/10000000000 : ℝ), (678055577/1250000000 : ℝ), (5233404471/10000000000 : ℝ)] ![(12325486540103/100000000000000 : ℝ), (4486678158969/10000000000000 : ℝ), (17123092741/40000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2023568061/10000000000 : ℝ)|^1081 ≤ (12325486540103/100000000000000 : ℝ)^825
        have hw : |(-2023568061/10000000000 : ℝ)|=(2023568061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678055577/1250000000 : ℝ)|^1081 ≤ (4486678158969/10000000000000 : ℝ)^825
        have hw : |(678055577/1250000000 : ℝ)|=(678055577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5233404471/10000000000 : ℝ)|^1081 ≤ (17123092741/40000000000 : ℝ)^825
        have hw : |(5233404471/10000000000 : ℝ)|=(5233404471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s3_1 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5351901331/10000000000 : ℝ)*x 0 + (-2121150813/10000000000 : ℝ)*x 1 + (2616702277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351901331/10000000000 : ℝ)^1081 ≤ (11020551968719/25000000000000 : ℝ)^825 := by
    have hnat : (5351901331 : ℕ)^1081*25000000000000^825 ≤ 11020551968719^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351901331 10000000000 11020551968719 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2121150813/10000000000 : ℝ)^1081 ≤ (327751484201/2500000000000 : ℝ)^825 := by
    have hnat : (2121150813 : ℕ)^1081*2500000000000^825 ≤ 327751484201^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121150813 10000000000 327751484201 2500000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2616702277/5000000000 : ℝ)^1081 ≤ (8561546548417/20000000000000 : ℝ)^825 := by
    have hnat : (2616702277 : ℕ)^1081*20000000000000^825 ≤ 8561546548417^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616702277 5000000000 8561546548417 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351901331/10000000000 : ℝ), (-2121150813/10000000000 : ℝ), (2616702277/5000000000 : ℝ)] ![(11020551968719/25000000000000 : ℝ), (327751484201/2500000000000 : ℝ), (8561546548417/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351901331/10000000000 : ℝ)|^1081 ≤ (11020551968719/25000000000000 : ℝ)^825
        have hw : |(5351901331/10000000000 : ℝ)|=(5351901331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2121150813/10000000000 : ℝ)|^1081 ≤ (327751484201/2500000000000 : ℝ)^825
        have hw : |(-2121150813/10000000000 : ℝ)|=(2121150813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2616702277/5000000000 : ℝ)|^1081 ≤ (8561546548417/20000000000000 : ℝ)^825
        have hw : |(2616702277/5000000000 : ℝ)|=(2616702277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s3_2 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2675950599/5000000000 : ℝ)*x 0 + (2616702393/5000000000 : ℝ)*x 1 + (-2121150683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675950599/5000000000 : ℝ)^1081 ≤ (22041103219729/50000000000000 : ℝ)^825 := by
    have hnat : (2675950599 : ℕ)^1081*50000000000000^825 ≤ 22041103219729^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675950599 5000000000 22041103219729 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2616702393/5000000000 : ℝ)^1081 ≤ (21403867614319/50000000000000 : ℝ)^825 := by
    have hnat : (2616702393 : ℕ)^1081*50000000000000^825 ≤ 21403867614319^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616702393 5000000000 21403867614319 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121150683/10000000000 : ℝ)^1081 ≤ (2622011663047/20000000000000 : ℝ)^825 := by
    have hnat : (2121150683 : ℕ)^1081*20000000000000^825 ≤ 2622011663047^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121150683 10000000000 2622011663047 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675950599/5000000000 : ℝ), (2616702393/5000000000 : ℝ), (-2121150683/10000000000 : ℝ)] ![(22041103219729/50000000000000 : ℝ), (21403867614319/50000000000000 : ℝ), (2622011663047/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675950599/5000000000 : ℝ)|^1081 ≤ (22041103219729/50000000000000 : ℝ)^825
        have hw : |(2675950599/5000000000 : ℝ)|=(2675950599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2616702393/5000000000 : ℝ)|^1081 ≤ (21403867614319/50000000000000 : ℝ)^825
        have hw : |(2616702393/5000000000 : ℝ)|=(2616702393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2121150683/10000000000 : ℝ)|^1081 ≤ (2622011663047/20000000000000 : ℝ)^825
        have hw : |(-2121150683/10000000000 : ℝ)|=(2121150683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s3_3 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4319960499/10000000000 : ℝ)*x 0 + (4122587333/10000000000 : ℝ)*x 1 + (2263024123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319960499/10000000000 : ℝ)^1081 ≤ (2080884919723/6250000000000 : ℝ)^825 := by
    have hnat : (4319960499 : ℕ)^1081*6250000000000^825 ≤ 2080884919723^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319960499 10000000000 2080884919723 6250000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4122587333/10000000000 : ℝ)^1081 ≤ (1565762587107/5000000000000 : ℝ)^825 := by
    have hnat : (4122587333 : ℕ)^1081*5000000000000^825 ≤ 1565762587107^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4122587333 10000000000 1565762587107 5000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2263024123/5000000000 : ℝ)^1081 ≤ (17695294763101/50000000000000 : ℝ)^825 := by
    have hnat : (2263024123 : ℕ)^1081*50000000000000^825 ≤ 17695294763101^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263024123 5000000000 17695294763101 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319960499/10000000000 : ℝ), (4122587333/10000000000 : ℝ), (2263024123/5000000000 : ℝ)] ![(2080884919723/6250000000000 : ℝ), (1565762587107/5000000000000 : ℝ), (17695294763101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319960499/10000000000 : ℝ)|^1081 ≤ (2080884919723/6250000000000 : ℝ)^825
        have hw : |(4319960499/10000000000 : ℝ)|=(4319960499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4122587333/10000000000 : ℝ)|^1081 ≤ (1565762587107/5000000000000 : ℝ)^825
        have hw : |(4122587333/10000000000 : ℝ)|=(4122587333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2263024123/5000000000 : ℝ)|^1081 ≤ (17695294763101/50000000000000 : ℝ)^825
        have hw : |(2263024123/5000000000 : ℝ)|=(2263024123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s3_4 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-404717187/2000000000 : ℝ)*x 0 + (654273883/1250000000 : ℝ)*x 1 + (677956691/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (404717187/2000000000 : ℝ)^1081 ≤ (12325629192919/100000000000000 : ℝ)^825 := by
    have hnat : (404717187 : ℕ)^1081*100000000000000^825 ≤ 12325629192919^825*2000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404717187 2000000000 12325629192919 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654273883/1250000000 : ℝ)^1081 ≤ (42816162673453/100000000000000 : ℝ)^825 := by
    have hnat : (654273883 : ℕ)^1081*100000000000000^825 ≤ 42816162673453^825*1250000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654273883 1250000000 42816162673453 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677956691/1250000000 : ℝ)^1081 ≤ (8971641625041/20000000000000 : ℝ)^825 := by
    have hnat : (677956691 : ℕ)^1081*20000000000000^825 ≤ 8971641625041^825*1250000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677956691 1250000000 8971641625041 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-404717187/2000000000 : ℝ), (654273883/1250000000 : ℝ), (677956691/1250000000 : ℝ)] ![(12325629192919/100000000000000 : ℝ), (42816162673453/100000000000000 : ℝ), (8971641625041/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-404717187/2000000000 : ℝ)|^1081 ≤ (12325629192919/100000000000000 : ℝ)^825
        have hw : |(-404717187/2000000000 : ℝ)|=(404717187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654273883/1250000000 : ℝ)|^1081 ≤ (42816162673453/100000000000000 : ℝ)^825
        have hw : |(654273883/1250000000 : ℝ)|=(654273883/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677956691/1250000000 : ℝ)|^1081 ≤ (8971641625041/20000000000000 : ℝ)^825
        have hw : |(677956691/1250000000 : ℝ)|=(677956691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s3_5 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1325642677/2500000000 : ℝ)*x 0 + (-1930901911/10000000000 : ℝ)*x 1 + (5423653523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325642677/2500000000 : ℝ)^1081 ≤ (8710112819209/20000000000000 : ℝ)^825 := by
    have hnat : (1325642677 : ℕ)^1081*20000000000000^825 ≤ 8710112819209^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325642677 2500000000 8710112819209 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1930901911/10000000000 : ℝ)^1081 ≤ (11591227823603/100000000000000 : ℝ)^825 := by
    have hnat : (1930901911 : ℕ)^1081*100000000000000^825 ≤ 11591227823603^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930901911 10000000000 11591227823603 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423653523/10000000000 : ℝ)^1081 ≤ (22429104035509/50000000000000 : ℝ)^825 := by
    have hnat : (5423653523 : ℕ)^1081*50000000000000^825 ≤ 22429104035509^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423653523 10000000000 22429104035509 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325642677/2500000000 : ℝ), (-1930901911/10000000000 : ℝ), (5423653523/10000000000 : ℝ)] ![(8710112819209/20000000000000 : ℝ), (11591227823603/100000000000000 : ℝ), (22429104035509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325642677/2500000000 : ℝ)|^1081 ≤ (8710112819209/20000000000000 : ℝ)^825
        have hw : |(1325642677/2500000000 : ℝ)|=(1325642677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1930901911/10000000000 : ℝ)|^1081 ≤ (11591227823603/100000000000000 : ℝ)^825
        have hw : |(-1930901911/10000000000 : ℝ)|=(1930901911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423653523/10000000000 : ℝ)|^1081 ≤ (22429104035509/50000000000000 : ℝ)^825
        have hw : |(5423653523/10000000000 : ℝ)|=(5423653523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s3_6 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5302570591/10000000000 : ℝ)*x 0 + (5423653607/10000000000 : ℝ)*x 1 + (-965450977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302570591/10000000000 : ℝ)^1081 ≤ (43550562836931/100000000000000 : ℝ)^825 := by
    have hnat : (5302570591 : ℕ)^1081*100000000000000^825 ≤ 43550562836931^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302570591 10000000000 43550562836931 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423653607/10000000000 : ℝ)^1081 ≤ (44858208981353/100000000000000 : ℝ)^825 := by
    have hnat : (5423653607 : ℕ)^1081*100000000000000^825 ≤ 44858208981353^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423653607 10000000000 44858208981353 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (965450977/5000000000 : ℝ)^1081 ≤ (11591228161831/100000000000000 : ℝ)^825 := by
    have hnat : (965450977 : ℕ)^1081*100000000000000^825 ≤ 11591228161831^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965450977 5000000000 11591228161831 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302570591/10000000000 : ℝ), (5423653607/10000000000 : ℝ), (-965450977/5000000000 : ℝ)] ![(43550562836931/100000000000000 : ℝ), (44858208981353/100000000000000 : ℝ), (11591228161831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302570591/10000000000 : ℝ)|^1081 ≤ (43550562836931/100000000000000 : ℝ)^825
        have hw : |(5302570591/10000000000 : ℝ)|=(5302570591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423653607/10000000000 : ℝ)|^1081 ≤ (44858208981353/100000000000000 : ℝ)^825
        have hw : |(5423653607/10000000000 : ℝ)|=(5423653607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-965450977/5000000000 : ℝ)|^1081 ≤ (11591228161831/100000000000000 : ℝ)^825
        have hw : |(-965450977/5000000000 : ℝ)|=(965450977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s3_7 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1079999733/2500000000 : ℝ)*x 0 + (4524387617/10000000000 : ℝ)*x 1 + (4124257581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079999733/2500000000 : ℝ)^1081 ≤ (6658909366913/20000000000000 : ℝ)^825 := by
    have hnat : (1079999733 : ℕ)^1081*20000000000000^825 ≤ 6658909366913^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079999733 2500000000 6658909366913 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4524387617/10000000000 : ℝ)^1081 ≤ (884339405953/2500000000000 : ℝ)^825 := by
    have hnat : (4524387617 : ℕ)^1081*2500000000000^825 ≤ 884339405953^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524387617 10000000000 884339405953 2500000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4124257581/10000000000 : ℝ)^1081 ≤ (7832969227553/25000000000000 : ℝ)^825 := by
    have hnat : (4124257581 : ℕ)^1081*25000000000000^825 ≤ 7832969227553^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124257581 10000000000 7832969227553 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079999733/2500000000 : ℝ), (4524387617/10000000000 : ℝ), (4124257581/10000000000 : ℝ)] ![(6658909366913/20000000000000 : ℝ), (884339405953/2500000000000 : ℝ), (7832969227553/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079999733/2500000000 : ℝ)|^1081 ≤ (6658909366913/20000000000000 : ℝ)^825
        have hw : |(1079999733/2500000000 : ℝ)|=(1079999733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4524387617/10000000000 : ℝ)|^1081 ≤ (884339405953/2500000000000 : ℝ)^825
        have hw : |(4524387617/10000000000 : ℝ)|=(4524387617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4124257581/10000000000 : ℝ)|^1081 ≤ (7832969227553/25000000000000 : ℝ)^825
        have hw : |(4124257581/10000000000 : ℝ)|=(4124257581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1364_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (801/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1249/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10947/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1499/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (801/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1249/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (801/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1249/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (801/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1249/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (801/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1249/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (801/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1249/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (801/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1249/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1249/12500 : ℝ) ^ (4323/1024 : ℝ) ≤ (5982090290122693/100000000000000000000 : ℝ) := by
    have hpowers : (1249/12500 : ℝ)^4323 ≤ (5982090290122693/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1249 : ℕ)^4323*100000000000000000000^1024 ≤ 5982090290122693^1024*12500^4323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1249 12500 5982090290122693 100000000000000000000 4323 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1249/12500 : ℝ)) (X := (5982090290122693/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (801/5000 : ℝ) ^ (4323/1024 : ℝ) ≤ (1371481339152001/3125000000000000000 : ℝ) := by
    have hpowers : (801/5000 : ℝ)^4323 ≤ (1371481339152001/3125000000000000000 : ℝ)^1024 := by
      have hnat : (801 : ℕ)^4323*3125000000000000000^1024 ≤ 1371481339152001^1024*5000^4323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        801 5000 1371481339152001 3125000000000000000 4323 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (801/5000 : ℝ)) (X := (1371481339152001/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005982090290122693/50000000000000000000 : ℝ) ≤ (5000141692825223/5000000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (50005982090290122693/50000000000000000000 : ℝ)^1024 ≤ (5000141692825223/5000000000000000 : ℝ)^4323 := by
      have hnat : (50005982090290122693 : ℕ)^1024*5000000000000000^4323 ≤ 5000141692825223^4323*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005982090290122693 50000000000000000000 5000141692825223 5000000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000141692825223/5000000000000000 : ℝ)) (X := (50005982090290122693/50000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001994779725719469/4000000000000000000 : ℝ) ≤ (10001181046650919/10000000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (4001994779725719469/4000000000000000000 : ℝ)^1024 ≤ (10001181046650919/10000000000000000 : ℝ)^4323 := by
      have hnat : (4001994779725719469 : ℕ)^1024*10000000000000000^4323 ≤ 10001181046650919^4323*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001994779725719469 4000000000000000000 10001181046650919 10000000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001181046650919/10000000000000000 : ℝ)) (X := (4001994779725719469/4000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563871481339152001/1562500000000000000 : ℝ) ≤ (156282479807053/156250000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (1563871481339152001/1562500000000000000 : ℝ)^1024 ≤ (156282479807053/156250000000000 : ℝ)^4323 := by
      have hnat : (1563871481339152001 : ℕ)^1024*156250000000000^4323 ≤ 156282479807053^4323*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563871481339152001 1562500000000000000 156282479807053 156250000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156282479807053/156250000000000 : ℝ)) (X := (1563871481339152001/1562500000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5982090290122693/100000000000000000000 : ℝ) ≤ ((7532971173908429507/7535000000000000000 : ℝ)+2*(897661000473/602800000000000 : ℝ)*(1249/12500 : ℝ))^(4323/1024 : ℝ) := by
    rw [show (7532971173908429507/7535000000000000000 : ℝ)+2*(897661000473/602800000000000 : ℝ)*(1249/12500 : ℝ)=(5000141692825223/5000000000000000 : ℝ) by norm_num, show 1+2*(5982090290122693/100000000000000000000 : ℝ)=(50005982090290122693/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1371481339152001/3125000000000000000 : ℝ)+(5982090290122693/100000000000000000000 : ℝ) ≤ ((7532971173908429507/7535000000000000000 : ℝ)+(897661000473/602800000000000 : ℝ)*((801/5000 : ℝ)+(1249/12500 : ℝ)))^(4323/1024 : ℝ) := by
    rw [show (7532971173908429507/7535000000000000000 : ℝ)+(897661000473/602800000000000 : ℝ)*((801/5000 : ℝ)+(1249/12500 : ℝ))=(10001181046650919/10000000000000000 : ℝ) by norm_num, show 1+(1371481339152001/3125000000000000000 : ℝ)+(5982090290122693/100000000000000000000 : ℝ)=(4001994779725719469/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1371481339152001/3125000000000000000 : ℝ) ≤ ((7532971173908429507/7535000000000000000 : ℝ)+2*(897661000473/602800000000000 : ℝ)*(801/5000 : ℝ))^(4323/1024 : ℝ) := by
    rw [show (7532971173908429507/7535000000000000000 : ℝ)+2*(897661000473/602800000000000 : ℝ)*(801/5000 : ℝ)=(156282479807053/156250000000000 : ℝ) by norm_num, show 1+2*(1371481339152001/3125000000000000000 : ℝ)=(1563871481339152001/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7532971173908429507/7535000000000000000 : ℝ)*(X 1 0+X 2 0)+(897661000473/602800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (1249/12500 : ℝ)) (hi := (801/5000 : ℝ)) (c := (7532971173908429507/7535000000000000000 : ℝ)) (alpha := (897661000473/602800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7532971173908429507/7535000000000000000 : ℝ)*(X 0 1+X 2 1)+(897661000473/602800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (1249/12500 : ℝ)) (hi := (801/5000 : ℝ)) (c := (7532971173908429507/7535000000000000000 : ℝ)) (alpha := (897661000473/602800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7532971173908429507/7535000000000000000 : ℝ)*(X 0 2+X 1 2)+(897661000473/602800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (1249/12500 : ℝ)) (hi := (801/5000 : ℝ)) (c := (7532971173908429507/7535000000000000000 : ℝ)) (alpha := (897661000473/602800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2023568061/10000000000 : ℝ)*X 0 0+(678055577/1250000000 : ℝ)*X 0 1+(5233404471/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351901331/10000000000 : ℝ)*X 1 0+(-2121150813/10000000000 : ℝ)*X 1 1+(2616702277/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675950599/5000000000 : ℝ)*X 2 0+(2616702393/5000000000 : ℝ)*X 2 1+(-2121150683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4319960499/10000000000 : ℝ)*X 0 0+(4122587333/10000000000 : ℝ)*X 0 1+(2263024123/5000000000 : ℝ)*X 0 2+(4319960499/10000000000 : ℝ)*X 1 0+(4122587333/10000000000 : ℝ)*X 1 1+(2263024123/5000000000 : ℝ)*X 1 2+(4319960499/10000000000 : ℝ)*X 2 0+(4122587333/10000000000 : ℝ)*X 2 1+(2263024123/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-404717187/2000000000 : ℝ)*X 0 0+(654273883/1250000000 : ℝ)*X 0 1+(677956691/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325642677/2500000000 : ℝ)*X 1 0+(-1930901911/10000000000 : ℝ)*X 1 1+(5423653523/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302570591/10000000000 : ℝ)*X 2 0+(5423653607/10000000000 : ℝ)*X 2 1+(-965450977/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1079999733/2500000000 : ℝ)*X 0 0+(4524387617/10000000000 : ℝ)*X 0 1+(4124257581/10000000000 : ℝ)*X 0 2+(1079999733/2500000000 : ℝ)*X 1 0+(4524387617/10000000000 : ℝ)*X 1 1+(4124257581/10000000000 : ℝ)*X 1 2+(1079999733/2500000000 : ℝ)*X 2 0+(4524387617/10000000000 : ℝ)*X 2 1+(4124257581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (210047112606190516459447371/188375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (785718441/100000000000000 : ℝ)*(base19) + (45331273/12500000000000 : ℝ)*(base23) + (20499219/20000000000000 : ℝ)*(upper3) + (1960033/1250000000000 : ℝ)*(upper4) + (442367/4000000000000 : ℝ)*(upper5) + (1928274799103149/50000000000000 : ℝ)*(major0) + (1928274799103149/50000000000000 : ℝ)*(major1) + (1928274799103149/50000000000000 : ℝ)*(major2) + (5234518921927587/100000000000000 : ℝ)*(sp0) + (1046906943639283/20000000000000 : ℝ)*(sp1) + (163579223164521/3125000000000 : ℝ)*(sp2) + (1239279181557881/50000000000000 : ℝ)*(sp3) + (16581987269/100000000000000 : ℝ)*(sp4) + (1058442743/20000000000000 : ℝ)*(sp7) + (619640913832369/25000000000000 : ℝ)*(f.failure) + (654316937989357/12500000000000 : ℝ)*(f.sum) + (39437215061243/15070000000000000000000000000 : ℝ)*base66 + (1103943251190930043/376750000000000000000000000000000 : ℝ)*base67 + (1397824200148680043/376750000000000000000000000000000 : ℝ)*base69 + (6719259299538569957/376750000000000000000000000000000 : ℝ)*base72 + (46282493984057/15070000000000000000000000000 : ℝ)*base73 + (1992901804321930043/376750000000000000000000000000000 : ℝ)*base75 + (4441409468872819957/376750000000000000000000000000000 : ℝ)*base78 + (1054236972018930043/376750000000000000000000000000000 : ℝ)*base79 + (81954218012107/15070000000000000000000000000 : ℝ)*base81 + (2053019/2500000000000000000000 : ℝ)*base90 + (2053019/2500000000000000000000 : ℝ)*base92 + (2053019/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (368769032918842482593212911/47093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (72291341/5000000000000 : ℝ)*(base19) + (35931427/2500000000000 : ℝ)*(base23) + (15114967/10000000000000 : ℝ)*(upper3) + (14550971/25000000000000 : ℝ)*(lower4) + (43121607/25000000000000 : ℝ)*(upper5) + (972159484923659/25000000000000 : ℝ)*(major0) + (972159484923659/25000000000000 : ℝ)*(major1) + (972159484923659/25000000000000 : ℝ)*(major2) + (13347555503/50000000000000 : ℝ)*(sp1) + (26493536267/100000000000000 : ℝ)*(sp2) + (5278089125205459/100000000000000 : ℝ)*(sp4) + (5278060984267633/100000000000000 : ℝ)*(sp5) + (5278061194412111/100000000000000 : ℝ)*(sp6) + (1249593246583061/50000000000000 : ℝ)*(sp7) + (1249593246583061/50000000000000 : ℝ)*(f.failure) + (5278089125205459/100000000000000 : ℝ)*(f.sum) + (6143757579671/3767500000000000000000000000 : ℝ)*base65 + (1324077156293093613/188375000000000000000000000000000 : ℝ)*base67 + (784847009967906387/188375000000000000000000000000000 : ℝ)*base70 + (1456223122239593613/188375000000000000000000000000000 : ℝ)*base71 + (77948135967/29433593750000000000000000 : ℝ)*base73 + (2568033392817468613/188375000000000000000000000000000 : ℝ)*base75 + (2180688447024718613/188375000000000000000000000000000 : ℝ)*base77 + (1099875140850468613/188375000000000000000000000000000 : ℝ)*base79 + (12642591404369/3767500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (99767911/5000000000000000000000 : ℝ)*base90 + (99767911/5000000000000000000000 : ℝ)*base92 + (99767911/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1364_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (801/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1249/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10947/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1499/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1364_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1364_s4_0 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2024860893/10000000000 : ℝ)*x 0 + (169180033/312500000 : ℝ)*x 1 + (81925603/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2024860893/10000000000 : ℝ)^1081 ≤ (308395141783/2500000000000 : ℝ)^825 := by
    have hnat : (2024860893 : ℕ)^1081*2500000000000^825 ≤ 308395141783^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024860893 10000000000 308395141783 2500000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169180033/312500000 : ℝ)^1081 ≤ (11187757658371/25000000000000 : ℝ)^825 := by
    have hnat : (169180033 : ℕ)^1081*25000000000000^825 ≤ 11187757658371^825*312500000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169180033 312500000 11187757658371 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81925603/156250000 : ℝ)^1081 ≤ (5364145460571/12500000000000 : ℝ)^825 := by
    have hnat : (81925603 : ℕ)^1081*12500000000000^825 ≤ 5364145460571^825*156250000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81925603 156250000 5364145460571 12500000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2024860893/10000000000 : ℝ), (169180033/312500000 : ℝ), (81925603/156250000 : ℝ)] ![(308395141783/2500000000000 : ℝ), (11187757658371/25000000000000 : ℝ), (5364145460571/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2024860893/10000000000 : ℝ)|^1081 ≤ (308395141783/2500000000000 : ℝ)^825
        have hw : |(-2024860893/10000000000 : ℝ)|=(2024860893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169180033/312500000 : ℝ)|^1081 ≤ (11187757658371/25000000000000 : ℝ)^825
        have hw : |(169180033/312500000 : ℝ)|=(169180033/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81925603/156250000 : ℝ)|^1081 ≤ (5364145460571/12500000000000 : ℝ)^825
        have hw : |(81925603/156250000 : ℝ)|=(81925603/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s4_1 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (106983391/200000000 : ℝ)*x 0 + (-422353461/2000000000 : ℝ)*x 1 + (5243237657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106983391/200000000 : ℝ)^1081 ≤ (44052727129039/100000000000000 : ℝ)^825 := by
    have hnat : (106983391 : ℕ)^1081*100000000000000^825 ≤ 44052727129039^825*200000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106983391 200000000 44052727129039 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422353461/2000000000 : ℝ)^1081 ≤ (325852979809/2500000000000 : ℝ)^825 := by
    have hnat : (422353461 : ℕ)^1081*2500000000000^825 ≤ 325852979809^825*2000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422353461 2000000000 325852979809 2500000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243237657/10000000000 : ℝ)^1081 ≤ (42913153657493/100000000000000 : ℝ)^825 := by
    have hnat : (5243237657 : ℕ)^1081*100000000000000^825 ≤ 42913153657493^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243237657 10000000000 42913153657493 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106983391/200000000 : ℝ), (-422353461/2000000000 : ℝ), (5243237657/10000000000 : ℝ)] ![(44052727129039/100000000000000 : ℝ), (325852979809/2500000000000 : ℝ), (42913153657493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106983391/200000000 : ℝ)|^1081 ≤ (44052727129039/100000000000000 : ℝ)^825
        have hw : |(106983391/200000000 : ℝ)|=(106983391/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-422353461/2000000000 : ℝ)|^1081 ≤ (325852979809/2500000000000 : ℝ)^825
        have hw : |(-422353461/2000000000 : ℝ)|=(422353461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243237657/10000000000 : ℝ)|^1081 ≤ (42913153657493/100000000000000 : ℝ)^825
        have hw : |(5243237657/10000000000 : ℝ)|=(5243237657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s4_2 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2674584511/5000000000 : ℝ)*x 0 + (5243238549/10000000000 : ℝ)*x 1 + (-527941707/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674584511/5000000000 : ℝ)^1081 ≤ (44052721431437/100000000000000 : ℝ)^825 := by
    have hnat : (2674584511 : ℕ)^1081*100000000000000^825 ≤ 44052721431437^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674584511 5000000000 44052721431437 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243238549/10000000000 : ℝ)^1081 ≤ (42913163223429/100000000000000 : ℝ)^825 := by
    have hnat : (5243238549 : ℕ)^1081*100000000000000^825 ≤ 42913163223429^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243238549 10000000000 42913163223429 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527941707/2500000000 : ℝ)^1081 ≤ (3258528833671/25000000000000 : ℝ)^825 := by
    have hnat : (527941707 : ℕ)^1081*25000000000000^825 ≤ 3258528833671^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527941707 2500000000 3258528833671 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674584511/5000000000 : ℝ), (5243238549/10000000000 : ℝ), (-527941707/2500000000 : ℝ)] ![(44052721431437/100000000000000 : ℝ), (42913163223429/100000000000000 : ℝ), (3258528833671/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674584511/5000000000 : ℝ)|^1081 ≤ (44052721431437/100000000000000 : ℝ)^825
        have hw : |(2674584511/5000000000 : ℝ)|=(2674584511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243238549/10000000000 : ℝ)|^1081 ≤ (42913163223429/100000000000000 : ℝ)^825
        have hw : |(5243238549/10000000000 : ℝ)|=(5243238549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-527941707/2500000000 : ℝ)|^1081 ≤ (3258528833671/25000000000000 : ℝ)^825
        have hw : |(-527941707/2500000000 : ℝ)|=(527941707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s4_3 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (540093461/1250000000 : ℝ)*x 0 + (4144156529/10000000000 : ℝ)*x 1 + (4504285847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540093461/1250000000 : ℝ)^1081 ≤ (8325527106499/25000000000000 : ℝ)^825 := by
    have hnat : (540093461 : ℕ)^1081*25000000000000^825 ≤ 8325527106499^825*1250000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540093461 1250000000 8325527106499 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4144156529/10000000000 : ℝ)^1081 ≤ (31530105877023/100000000000000 : ℝ)^825 := by
    have hnat : (4144156529 : ℕ)^1081*100000000000000^825 ≤ 31530105877023^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144156529 10000000000 31530105877023 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504285847/10000000000 : ℝ)^1081 ≤ (219798660561/625000000000 : ℝ)^825 := by
    have hnat : (4504285847 : ℕ)^1081*625000000000^825 ≤ 219798660561^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504285847 10000000000 219798660561 625000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540093461/1250000000 : ℝ), (4144156529/10000000000 : ℝ), (4504285847/10000000000 : ℝ)] ![(8325527106499/25000000000000 : ℝ), (31530105877023/100000000000000 : ℝ), (219798660561/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540093461/1250000000 : ℝ)|^1081 ≤ (8325527106499/25000000000000 : ℝ)^825
        have hw : |(540093461/1250000000 : ℝ)|=(540093461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4144156529/10000000000 : ℝ)|^1081 ≤ (31530105877023/100000000000000 : ℝ)^825
        have hw : |(4144156529/10000000000 : ℝ)|=(4144156529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504285847/10000000000 : ℝ)|^1081 ≤ (219798660561/625000000000 : ℝ)^825
        have hw : |(4504285847/10000000000 : ℝ)|=(4504285847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s4_4 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2024874123/10000000000 : ℝ)*x 0 + (2621932669/5000000000 : ℝ)*x 1 + (541313073/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2024874123/10000000000 : ℝ)^1081 ≤ (12335911281153/100000000000000 : ℝ)^825 := by
    have hnat : (2024874123 : ℕ)^1081*100000000000000^825 ≤ 12335911281153^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024874123 10000000000 12335911281153 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621932669/5000000000 : ℝ)^1081 ≤ (42919885123899/100000000000000 : ℝ)^825 := by
    have hnat : (2621932669 : ℕ)^1081*100000000000000^825 ≤ 42919885123899^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621932669 5000000000 42919885123899 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541313073/1000000000 : ℝ)^1081 ≤ (11186050895887/25000000000000 : ℝ)^825 := by
    have hnat : (541313073 : ℕ)^1081*25000000000000^825 ≤ 11186050895887^825*1000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541313073 1000000000 11186050895887 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2024874123/10000000000 : ℝ), (2621932669/5000000000 : ℝ), (541313073/1000000000 : ℝ)] ![(12335911281153/100000000000000 : ℝ), (42919885123899/100000000000000 : ℝ), (11186050895887/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2024874123/10000000000 : ℝ)|^1081 ≤ (12335911281153/100000000000000 : ℝ)^825
        have hw : |(-2024874123/10000000000 : ℝ)|=(2024874123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621932669/5000000000 : ℝ)|^1081 ≤ (42919885123899/100000000000000 : ℝ)^825
        have hw : |(2621932669/5000000000 : ℝ)|=(2621932669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541313073/1000000000 : ℝ)|^1081 ≤ (11186050895887/25000000000000 : ℝ)^825
        have hw : |(541313073/1000000000 : ℝ)|=(541313073/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s4_5 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305137457/10000000000 : ℝ)*x 0 + (-485468581/2500000000 : ℝ)*x 1 + (5413130501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305137457/10000000000 : ℝ)^1081 ≤ (43578188637307/100000000000000 : ℝ)^825 := by
    have hnat : (5305137457 : ℕ)^1081*100000000000000^825 ≤ 43578188637307^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305137457 10000000000 43578188637307 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (485468581/2500000000 : ℝ)^1081 ≤ (2335522048097/20000000000000 : ℝ)^825 := by
    have hnat : (485468581 : ℕ)^1081*20000000000000^825 ≤ 2335522048097^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485468581 2500000000 2335522048097 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413130501/10000000000 : ℝ)^1081 ≤ (22372100551649/50000000000000 : ℝ)^825 := by
    have hnat : (5413130501 : ℕ)^1081*50000000000000^825 ≤ 22372100551649^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413130501 10000000000 22372100551649 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305137457/10000000000 : ℝ), (-485468581/2500000000 : ℝ), (5413130501/10000000000 : ℝ)] ![(43578188637307/100000000000000 : ℝ), (2335522048097/20000000000000 : ℝ), (22372100551649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305137457/10000000000 : ℝ)|^1081 ≤ (43578188637307/100000000000000 : ℝ)^825
        have hw : |(5305137457/10000000000 : ℝ)|=(5305137457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-485468581/2500000000 : ℝ)|^1081 ≤ (2335522048097/20000000000000 : ℝ)^825
        have hw : |(-485468581/2500000000 : ℝ)|=(485468581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413130501/10000000000 : ℝ)|^1081 ≤ (22372100551649/50000000000000 : ℝ)^825
        have hw : |(5413130501/10000000000 : ℝ)|=(5413130501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s4_6 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (165785541/312500000 : ℝ)*x 0 + (1353282669/2500000000 : ℝ)*x 1 + (-970937141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165785541/312500000 : ℝ)^1081 ≤ (43578187076633/100000000000000 : ℝ)^825 := by
    have hnat : (165785541 : ℕ)^1081*100000000000000^825 ≤ 43578187076633^825*312500000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165785541 312500000 43578187076633 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353282669/2500000000 : ℝ)^1081 ≤ (22372101499343/50000000000000 : ℝ)^825 := by
    have hnat : (1353282669 : ℕ)^1081*50000000000000^825 ≤ 22372101499343^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353282669 2500000000 22372101499343 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (970937141/5000000000 : ℝ)^1081 ≤ (11677609909541/100000000000000 : ℝ)^825 := by
    have hnat : (970937141 : ℕ)^1081*100000000000000^825 ≤ 11677609909541^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970937141 5000000000 11677609909541 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165785541/312500000 : ℝ), (1353282669/2500000000 : ℝ), (-970937141/5000000000 : ℝ)] ![(43578187076633/100000000000000 : ℝ), (22372101499343/50000000000000 : ℝ), (11677609909541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165785541/312500000 : ℝ)|^1081 ≤ (43578187076633/100000000000000 : ℝ)^825
        have hw : |(165785541/312500000 : ℝ)|=(165785541/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353282669/2500000000 : ℝ)|^1081 ≤ (22372101499343/50000000000000 : ℝ)^825
        have hw : |(1353282669/2500000000 : ℝ)|=(1353282669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-970937141/5000000000 : ℝ)|^1081 ≤ (11677609909541/100000000000000 : ℝ)^825
        have hw : |(-970937141/5000000000 : ℝ)|=(970937141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s4_7 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4320775339/10000000000 : ℝ)*x 0 + (4502962143/10000000000 : ℝ)*x 1 + (4145486767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320775339/10000000000 : ℝ)^1081 ≤ (33302387677707/100000000000000 : ℝ)^825 := by
    have hnat : (4320775339 : ℕ)^1081*100000000000000^825 ≤ 33302387677707^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320775339 10000000000 33302387677707 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502962143/10000000000 : ℝ)^1081 ≤ (1757712217081/5000000000000 : ℝ)^825 := by
    have hnat : (4502962143 : ℕ)^1081*5000000000000^825 ≤ 1757712217081^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502962143 10000000000 1757712217081 5000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4145486767/10000000000 : ℝ)^1081 ≤ (31543367967923/100000000000000 : ℝ)^825 := by
    have hnat : (4145486767 : ℕ)^1081*100000000000000^825 ≤ 31543367967923^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145486767 10000000000 31543367967923 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320775339/10000000000 : ℝ), (4502962143/10000000000 : ℝ), (4145486767/10000000000 : ℝ)] ![(33302387677707/100000000000000 : ℝ), (1757712217081/5000000000000 : ℝ), (31543367967923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320775339/10000000000 : ℝ)|^1081 ≤ (33302387677707/100000000000000 : ℝ)^825
        have hw : |(4320775339/10000000000 : ℝ)|=(4320775339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502962143/10000000000 : ℝ)|^1081 ≤ (1757712217081/5000000000000 : ℝ)^825
        have hw : |(4502962143/10000000000 : ℝ)|=(4502962143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4145486767/10000000000 : ℝ)|^1081 ≤ (31543367967923/100000000000000 : ℝ)^825
        have hw : |(4145486767/10000000000 : ℝ)|=(4145486767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1364_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1499/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10947/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2789/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14767/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1499/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10947/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1499/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10947/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1499/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10947/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1499/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10947/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1499/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10947/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1499/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10947/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10947/100000 : ℝ) ^ (4323/1024 : ℝ) ≤ (87945113622077/1000000000000000000 : ℝ) := by
    have hpowers : (10947/100000 : ℝ)^4323 ≤ (87945113622077/1000000000000000000 : ℝ)^1024 := by
      have hnat : (10947 : ℕ)^4323*1000000000000000000^1024 ≤ 87945113622077^1024*100000^4323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10947 100000 87945113622077 1000000000000000000 4323 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10947/100000 : ℝ)) (X := (87945113622077/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1499/10000 : ℝ) ^ (4323/1024 : ℝ) ≤ (33151142093598651/100000000000000000000 : ℝ) := by
    have hpowers : (1499/10000 : ℝ)^4323 ≤ (33151142093598651/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1499 : ℕ)^4323*100000000000000000000^1024 ≤ 33151142093598651^1024*10000^4323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1499 10000 33151142093598651 100000000000000000000 4323 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1499/10000 : ℝ)) (X := (33151142093598651/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (500087945113622077/500000000000000000 : ℝ) ≤ (10000416607693867/10000000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (500087945113622077/500000000000000000 : ℝ)^1024 ≤ (10000416607693867/10000000000000000 : ℝ)^4323 := by
      have hnat : (500087945113622077 : ℕ)^1024*10000000000000000^4323 ≤ 10000416607693867^4323*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500087945113622077 500000000000000000 10000416607693867 10000000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000416607693867/10000000000000000 : ℝ)) (X := (500087945113622077/500000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041945653455806351/100000000000000000000 : ℝ) ≤ (10000993418374631/10000000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (100041945653455806351/100000000000000000000 : ℝ)^1024 ≤ (10000993418374631/10000000000000000 : ℝ)^4323 := by
      have hnat : (100041945653455806351 : ℕ)^1024*10000000000000000^4323 ≤ 10000993418374631^4323*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041945653455806351 100000000000000000000 10000993418374631 10000000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000993418374631/10000000000000000 : ℝ)) (X := (100041945653455806351/100000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033151142093598651/50000000000000000000 : ℝ) ≤ (2000314045811079/2000000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (50033151142093598651/50000000000000000000 : ℝ)^1024 ≤ (2000314045811079/2000000000000000 : ℝ)^4323 := by
      have hnat : (50033151142093598651 : ℕ)^1024*2000000000000000^4323 ≤ 2000314045811079^4323*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033151142093598651 50000000000000000000 2000314045811079 2000000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000314045811079/2000000000000000 : ℝ)) (X := (50033151142093598651/50000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(87945113622077/1000000000000000000 : ℝ) ≤ ((8083811130372331453/8086000000000000000 : ℝ)+2*(144202670191/101075000000000 : ℝ)*(10947/100000 : ℝ))^(4323/1024 : ℝ) := by
    rw [show (8083811130372331453/8086000000000000000 : ℝ)+2*(144202670191/101075000000000 : ℝ)*(10947/100000 : ℝ)=(10000416607693867/10000000000000000 : ℝ) by norm_num, show 1+2*(87945113622077/1000000000000000000 : ℝ)=(500087945113622077/500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33151142093598651/100000000000000000000 : ℝ)+(87945113622077/1000000000000000000 : ℝ) ≤ ((8083811130372331453/8086000000000000000 : ℝ)+(144202670191/101075000000000 : ℝ)*((1499/10000 : ℝ)+(10947/100000 : ℝ)))^(4323/1024 : ℝ) := by
    rw [show (8083811130372331453/8086000000000000000 : ℝ)+(144202670191/101075000000000 : ℝ)*((1499/10000 : ℝ)+(10947/100000 : ℝ))=(10000993418374631/10000000000000000 : ℝ) by norm_num, show 1+(33151142093598651/100000000000000000000 : ℝ)+(87945113622077/1000000000000000000 : ℝ)=(100041945653455806351/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33151142093598651/100000000000000000000 : ℝ) ≤ ((8083811130372331453/8086000000000000000 : ℝ)+2*(144202670191/101075000000000 : ℝ)*(1499/10000 : ℝ))^(4323/1024 : ℝ) := by
    rw [show (8083811130372331453/8086000000000000000 : ℝ)+2*(144202670191/101075000000000 : ℝ)*(1499/10000 : ℝ)=(2000314045811079/2000000000000000 : ℝ) by norm_num, show 1+2*(33151142093598651/100000000000000000000 : ℝ)=(50033151142093598651/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8083811130372331453/8086000000000000000 : ℝ)*(X 1 0+X 2 0)+(144202670191/101075000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (10947/100000 : ℝ)) (hi := (1499/10000 : ℝ)) (c := (8083811130372331453/8086000000000000000 : ℝ)) (alpha := (144202670191/101075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8083811130372331453/8086000000000000000 : ℝ)*(X 0 1+X 2 1)+(144202670191/101075000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (10947/100000 : ℝ)) (hi := (1499/10000 : ℝ)) (c := (8083811130372331453/8086000000000000000 : ℝ)) (alpha := (144202670191/101075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8083811130372331453/8086000000000000000 : ℝ)*(X 0 2+X 1 2)+(144202670191/101075000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (10947/100000 : ℝ)) (hi := (1499/10000 : ℝ)) (c := (8083811130372331453/8086000000000000000 : ℝ)) (alpha := (144202670191/101075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2024860893/10000000000 : ℝ)*X 0 0+(169180033/312500000 : ℝ)*X 0 1+(81925603/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((106983391/200000000 : ℝ)*X 1 0+(-422353461/2000000000 : ℝ)*X 1 1+(5243237657/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674584511/5000000000 : ℝ)*X 2 0+(5243238549/10000000000 : ℝ)*X 2 1+(-527941707/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((540093461/1250000000 : ℝ)*X 0 0+(4144156529/10000000000 : ℝ)*X 0 1+(4504285847/10000000000 : ℝ)*X 0 2+(540093461/1250000000 : ℝ)*X 1 0+(4144156529/10000000000 : ℝ)*X 1 1+(4504285847/10000000000 : ℝ)*X 1 2+(540093461/1250000000 : ℝ)*X 2 0+(4144156529/10000000000 : ℝ)*X 2 1+(4504285847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2024874123/10000000000 : ℝ)*X 0 0+(2621932669/5000000000 : ℝ)*X 0 1+(541313073/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305137457/10000000000 : ℝ)*X 1 0+(-485468581/2500000000 : ℝ)*X 1 1+(5413130501/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165785541/312500000 : ℝ)*X 2 0+(1353282669/2500000000 : ℝ)*X 2 1+(-970937141/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4320775339/10000000000 : ℝ)*X 0 0+(4502962143/10000000000 : ℝ)*X 0 1+(4145486767/10000000000 : ℝ)*X 0 2+(4320775339/10000000000 : ℝ)*X 1 0+(4502962143/10000000000 : ℝ)*X 1 1+(4145486767/10000000000 : ℝ)*X 1 2+(4320775339/10000000000 : ℝ)*X 2 0+(4502962143/10000000000 : ℝ)*X 2 1+(4145486767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (294476959547765125976817/20215000000000000000000000000 : ℝ) := by norm_num
    linear_combination (831054663/50000000000000 : ℝ)*(base19) + (986287203/100000000000000 : ℝ)*(base23) + (42133927/50000000000000 : ℝ)*(lower2) + (23023053/20000000000000 : ℝ)*(upper5) + (4320581761322373/100000000000000 : ℝ)*(major0) + (4320581761322373/100000000000000 : ℝ)*(major1) + (4320581761322373/100000000000000 : ℝ)*(major2) + (2932174598010597/50000000000000 : ℝ)*(sp0) + (5864361796358381/100000000000000 : ℝ)*(sp1) + (1466092457491457/25000000000000 : ℝ)*(sp2) + (1388393840602243/50000000000000 : ℝ)*(sp3) + (5405057959/25000000000000 : ℝ)*(sp4) + (7357785323/100000000000000 : ℝ)*(sp5) + (4539612221/100000000000000 : ℝ)*(sp7) + (694198055204177/25000000000000 : ℝ)*(f.failure) + (586437081625303/10000000000000 : ℝ)*(f.sum) + (14570180546317/20215000000000000000000000000 : ℝ)*base65 + (4817481486690537969/808600000000000000000000000000000 : ℝ)*base67 + (5455411782217737969/808600000000000000000000000000000 : ℝ)*base69 + (498196952052862031/808600000000000000000000000000000 : ℝ)*base72 + (19535281870593/5053750000000000000000000000 : ℝ)*base73 + (3788441633914537969/808600000000000000000000000000000 : ℝ)*base75 + (3984506623325862031/808600000000000000000000000000000 : ℝ)*base78 + (3405966071713462031/808600000000000000000000000000000 : ℝ)*base80 + (104059249486497/20215000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (24914373/2500000000000000000000 : ℝ)*base89 + (24914373/2500000000000000000000 : ℝ)*base91 + (24914373/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1024336259750063338448601537/101075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (982901519/50000000000000 : ℝ)*(base19) + (74580527/4000000000000 : ℝ)*(base23) + (13395681/50000000000000 : ℝ)*(upper2) + (64515939/50000000000000 : ℝ)*(upper3) + (37670747/25000000000000 : ℝ)*(upper5) + (2176319026624943/50000000000000 : ℝ)*(major0) + (2176319026624943/50000000000000 : ℝ)*(major1) + (2176319026624943/50000000000000 : ℝ)*(major2) + (37515755543/100000000000000 : ℝ)*(sp1) + (38682792109/100000000000000 : ℝ)*(sp2) + (2953940653973203/50000000000000 : ℝ)*(sp4) + (236313673055513/4000000000000 : ℝ)*(sp5) + (2953920380320561/50000000000000 : ℝ)*(sp6) + (34967430759243/1250000000000 : ℝ)*(sp7) + (34967430759243/1250000000000 : ℝ)*(f.failure) + (2953940653973203/50000000000000 : ℝ)*(f.sum) + (3910764482413/10107500000000000000000000000 : ℝ)*base66 + (849766986305872179/404300000000000000000000000000000 : ℝ)*base67 + (3323640670855727821/404300000000000000000000000000000 : ℝ)*base70 + (3031574340748227821/404300000000000000000000000000000 : ℝ)*base72 + (139404825796829/20215000000000000000000000000 : ℝ)*base73 + (297445749048527821/404300000000000000000000000000000 : ℝ)*base76 + (612653419132327821/404300000000000000000000000000000 : ℝ)*base78 + (2142858817959627821/404300000000000000000000000000000 : ℝ)*base80 + (7114933792407/2526875000000000000000000000 : ℝ)*base82 + (544793/125000000000000000000 : ℝ)*base90 + (544793/125000000000000000000 : ℝ)*base92 + (544793/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1364_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1499/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10947/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1364_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1364_s5_0 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-101253901/500000000 : ℝ)*x 0 + (541189451/1000000000 : ℝ)*x 1 + (1048992391/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (101253901/500000000 : ℝ)^1081 ≤ (3084384734241/25000000000000 : ℝ)^825 := by
    have hnat : (101253901 : ℕ)^1081*25000000000000^825 ≤ 3084384734241^825*500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101253901 500000000 3084384734241 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541189451/1000000000 : ℝ)^1081 ≤ (22365407411287/50000000000000 : ℝ)^825 := by
    have hnat : (541189451 : ℕ)^1081*50000000000000^825 ≤ 22365407411287^825*1000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541189451 1000000000 22365407411287 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048992391/2000000000 : ℝ)^1081 ≤ (858632924417/2000000000000 : ℝ)^825 := by
    have hnat : (1048992391 : ℕ)^1081*2000000000000^825 ≤ 858632924417^825*2000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048992391 2000000000 858632924417 2000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-101253901/500000000 : ℝ), (541189451/1000000000 : ℝ), (1048992391/2000000000 : ℝ)] ![(3084384734241/25000000000000 : ℝ), (22365407411287/50000000000000 : ℝ), (858632924417/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-101253901/500000000 : ℝ)|^1081 ≤ (3084384734241/25000000000000 : ℝ)^825
        have hw : |(-101253901/500000000 : ℝ)|=(101253901/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541189451/1000000000 : ℝ)|^1081 ≤ (22365407411287/50000000000000 : ℝ)^825
        have hw : |(541189451/1000000000 : ℝ)|=(541189451/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048992391/2000000000 : ℝ)|^1081 ≤ (858632924417/2000000000000 : ℝ)^825
        have hw : |(1048992391/2000000000 : ℝ)|=(1048992391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s5_1 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5348690397/10000000000 : ℝ)*x 0 + (-527529941/2500000000 : ℝ)*x 1 + (1311240501/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348690397/10000000000 : ℝ)^1081 ≤ (22023778351343/50000000000000 : ℝ)^825 := by
    have hnat : (5348690397 : ℕ)^1081*50000000000000^825 ≤ 22023778351343^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348690397 10000000000 22023778351343 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527529941/2500000000 : ℝ)^1081 ≤ (3255199132503/25000000000000 : ℝ)^825 := by
    have hnat : (527529941 : ℕ)^1081*25000000000000^825 ≤ 3255199132503^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527529941 2500000000 3255199132503 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311240501/2500000000 : ℝ)^1081 ≤ (42931646746387/100000000000000 : ℝ)^825 := by
    have hnat : (1311240501 : ℕ)^1081*100000000000000^825 ≤ 42931646746387^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311240501 2500000000 42931646746387 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348690397/10000000000 : ℝ), (-527529941/2500000000 : ℝ), (1311240501/2500000000 : ℝ)] ![(22023778351343/50000000000000 : ℝ), (3255199132503/25000000000000 : ℝ), (42931646746387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348690397/10000000000 : ℝ)|^1081 ≤ (22023778351343/50000000000000 : ℝ)^825
        have hw : |(5348690397/10000000000 : ℝ)|=(5348690397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-527529941/2500000000 : ℝ)|^1081 ≤ (3255199132503/25000000000000 : ℝ)^825
        have hw : |(-527529941/2500000000 : ℝ)|=(527529941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311240501/2500000000 : ℝ)|^1081 ≤ (42931646746387/100000000000000 : ℝ)^825
        have hw : |(1311240501/2500000000 : ℝ)|=(1311240501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s5_2 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (668586291/1250000000 : ℝ)*x 0 + (5244962129/10000000000 : ℝ)*x 1 + (-2110119691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668586291/1250000000 : ℝ)^1081 ≤ (22023777979067/50000000000000 : ℝ)^825 := by
    have hnat : (668586291 : ℕ)^1081*50000000000000^825 ≤ 22023777979067^825*1250000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668586291 1250000000 22023777979067 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244962129/10000000000 : ℝ)^1081 ≤ (21465824043521/50000000000000 : ℝ)^825 := by
    have hnat : (5244962129 : ℕ)^1081*50000000000000^825 ≤ 21465824043521^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244962129 10000000000 21465824043521 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2110119691/10000000000 : ℝ)^1081 ≤ (13020795939777/100000000000000 : ℝ)^825 := by
    have hnat : (2110119691 : ℕ)^1081*100000000000000^825 ≤ 13020795939777^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110119691 10000000000 13020795939777 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668586291/1250000000 : ℝ), (5244962129/10000000000 : ℝ), (-2110119691/10000000000 : ℝ)] ![(22023777979067/50000000000000 : ℝ), (21465824043521/50000000000000 : ℝ), (13020795939777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668586291/1250000000 : ℝ)|^1081 ≤ (22023777979067/50000000000000 : ℝ)^825
        have hw : |(668586291/1250000000 : ℝ)|=(668586291/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244962129/10000000000 : ℝ)|^1081 ≤ (21465824043521/50000000000000 : ℝ)^825
        have hw : |(5244962129/10000000000 : ℝ)|=(5244962129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2110119691/10000000000 : ℝ)|^1081 ≤ (13020795939777/100000000000000 : ℝ)^825
        have hw : |(-2110119691/10000000000 : ℝ)|=(2110119691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s5_3 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4320877241/10000000000 : ℝ)*x 0 + (32405709/78125000 : ℝ)*x 1 + (2250239527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320877241/10000000000 : ℝ)^1081 ≤ (66606833613/200000000000 : ℝ)^825 := by
    have hnat : (4320877241 : ℕ)^1081*200000000000^825 ≤ 66606833613^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320877241 10000000000 66606833613 200000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32405709/78125000 : ℝ)^1081 ≤ (31567737238403/100000000000000 : ℝ)^825 := by
    have hnat : (32405709 : ℕ)^1081*100000000000000^825 ≤ 31567737238403^825*78125000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32405709 78125000 31567737238403 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2250239527/5000000000 : ℝ)^1081 ≤ (35128845942719/100000000000000 : ℝ)^825 := by
    have hnat : (2250239527 : ℕ)^1081*100000000000000^825 ≤ 35128845942719^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250239527 5000000000 35128845942719 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320877241/10000000000 : ℝ), (32405709/78125000 : ℝ), (2250239527/5000000000 : ℝ)] ![(66606833613/200000000000 : ℝ), (31567737238403/100000000000000 : ℝ), (35128845942719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320877241/10000000000 : ℝ)|^1081 ≤ (66606833613/200000000000 : ℝ)^825
        have hw : |(4320877241/10000000000 : ℝ)|=(4320877241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32405709/78125000 : ℝ)|^1081 ≤ (31567737238403/100000000000000 : ℝ)^825
        have hw : |(32405709/78125000 : ℝ)|=(32405709/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2250239527/5000000000 : ℝ)|^1081 ≤ (35128845942719/100000000000000 : ℝ)^825
        have hw : |(2250239527/5000000000 : ℝ)|=(2250239527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s5_4 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2025089851/10000000000 : ℝ)*x 0 + (209822531/400000000 : ℝ)*x 1 + (2705645133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2025089851/10000000000 : ℝ)^1081 ≤ (3084408345567/25000000000000 : ℝ)^825 := by
    have hnat : (2025089851 : ℕ)^1081*25000000000000^825 ≤ 3084408345567^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025089851 10000000000 3084408345567 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209822531/400000000 : ℝ)^1081 ≤ (2146904781789/5000000000000 : ℝ)^825 := by
    have hnat : (209822531 : ℕ)^1081*5000000000000^825 ≤ 2146904781789^825*400000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209822531 400000000 2146904781789 5000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705645133/5000000000 : ℝ)^1081 ≤ (44724270961731/100000000000000 : ℝ)^825 := by
    have hnat : (2705645133 : ℕ)^1081*100000000000000^825 ≤ 44724270961731^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705645133 5000000000 44724270961731 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2025089851/10000000000 : ℝ), (209822531/400000000 : ℝ), (2705645133/5000000000 : ℝ)] ![(3084408345567/25000000000000 : ℝ), (2146904781789/5000000000000 : ℝ), (44724270961731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2025089851/10000000000 : ℝ)|^1081 ≤ (3084408345567/25000000000000 : ℝ)^825
        have hw : |(-2025089851/10000000000 : ℝ)|=(2025089851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209822531/400000000 : ℝ)|^1081 ≤ (2146904781789/5000000000000 : ℝ)^825
        have hw : |(209822531/400000000 : ℝ)|=(209822531/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705645133/5000000000 : ℝ)|^1081 ≤ (44724270961731/100000000000000 : ℝ)^825
        have hw : |(2705645133/5000000000 : ℝ)|=(2705645133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s5_5 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (663198119/1250000000 : ℝ)*x 0 + (-1943791627/10000000000 : ℝ)*x 1 + (1352822651/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663198119/1250000000 : ℝ)^1081 ≤ (21791502605169/50000000000000 : ℝ)^825 := by
    have hnat : (663198119 : ℕ)^1081*50000000000000^825 ≤ 21791502605169^825*1250000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663198119 1250000000 21791502605169 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1943791627/10000000000 : ℝ)^1081 ≤ (2338544029991/20000000000000 : ℝ)^825 := by
    have hnat : (1943791627 : ℕ)^1081*20000000000000^825 ≤ 2338544029991^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943791627 10000000000 2338544029991 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352822651/2500000000 : ℝ)^1081 ≤ (44724274622151/100000000000000 : ℝ)^825 := by
    have hnat : (1352822651 : ℕ)^1081*100000000000000^825 ≤ 44724274622151^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352822651 2500000000 44724274622151 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663198119/1250000000 : ℝ), (-1943791627/10000000000 : ℝ), (1352822651/2500000000 : ℝ)] ![(21791502605169/50000000000000 : ℝ), (2338544029991/20000000000000 : ℝ), (44724274622151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663198119/1250000000 : ℝ)|^1081 ≤ (21791502605169/50000000000000 : ℝ)^825
        have hw : |(663198119/1250000000 : ℝ)|=(663198119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1943791627/10000000000 : ℝ)|^1081 ≤ (2338544029991/20000000000000 : ℝ)^825
        have hw : |(-1943791627/10000000000 : ℝ)|=(1943791627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352822651/2500000000 : ℝ)|^1081 ≤ (44724274622151/100000000000000 : ℝ)^825
        have hw : |(1352822651/2500000000 : ℝ)|=(1352822651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s5_6 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305584699/10000000000 : ℝ)*x 0 + (1352822733/2500000000 : ℝ)*x 1 + (-971895761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305584699/10000000000 : ℝ)^1081 ≤ (43583002487159/100000000000000 : ℝ)^825 := by
    have hnat : (5305584699 : ℕ)^1081*100000000000000^825 ≤ 43583002487159^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305584699 10000000000 43583002487159 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352822733/2500000000 : ℝ)^1081 ≤ (22362139087137/50000000000000 : ℝ)^825 := by
    have hnat : (1352822733 : ℕ)^1081*50000000000000^825 ≤ 22362139087137^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352822733 2500000000 22362139087137 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (971895761/5000000000 : ℝ)^1081 ≤ (11692719322343/100000000000000 : ℝ)^825 := by
    have hnat : (971895761 : ℕ)^1081*100000000000000^825 ≤ 11692719322343^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971895761 5000000000 11692719322343 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305584699/10000000000 : ℝ), (1352822733/2500000000 : ℝ), (-971895761/5000000000 : ℝ)] ![(43583002487159/100000000000000 : ℝ), (22362139087137/50000000000000 : ℝ), (11692719322343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305584699/10000000000 : ℝ)|^1081 ≤ (43583002487159/100000000000000 : ℝ)^825
        have hw : |(5305584699/10000000000 : ℝ)|=(5305584699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352822733/2500000000 : ℝ)|^1081 ≤ (22362139087137/50000000000000 : ℝ)^825
        have hw : |(1352822733/2500000000 : ℝ)|=(1352822733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-971895761/5000000000 : ℝ)|^1081 ≤ (11692719322343/100000000000000 : ℝ)^825
        have hw : |(-971895761/5000000000 : ℝ)|=(971895761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s5_7 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (27005641/62500000 : ℝ)*x 0 + (4499210141/10000000000 : ℝ)*x 1 + (2074603217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27005641/62500000 : ℝ)^1081 ≤ (16651836254671/50000000000000 : ℝ)^825 := by
    have hnat : (27005641 : ℕ)^1081*50000000000000^825 ≤ 16651836254671^825*62500000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27005641 62500000 16651836254671 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4499210141/10000000000 : ℝ)^1081 ≤ (3511586848179/10000000000000 : ℝ)^825 := by
    have hnat : (4499210141 : ℕ)^1081*10000000000000^825 ≤ 3511586848179^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499210141 10000000000 3511586848179 10000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2074603217/5000000000 : ℝ)^1081 ≤ (31580458988191/100000000000000 : ℝ)^825 := by
    have hnat : (2074603217 : ℕ)^1081*100000000000000^825 ≤ 31580458988191^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074603217 5000000000 31580458988191 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(27005641/62500000 : ℝ), (4499210141/10000000000 : ℝ), (2074603217/5000000000 : ℝ)] ![(16651836254671/50000000000000 : ℝ), (3511586848179/10000000000000 : ℝ), (31580458988191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(27005641/62500000 : ℝ)|^1081 ≤ (16651836254671/50000000000000 : ℝ)^825
        have hw : |(27005641/62500000 : ℝ)|=(27005641/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4499210141/10000000000 : ℝ)|^1081 ≤ (3511586848179/10000000000000 : ℝ)^825
        have hw : |(4499210141/10000000000 : ℝ)|=(4499210141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2074603217/5000000000 : ℝ)|^1081 ≤ (31580458988191/100000000000000 : ℝ)^825
        have hw : |(2074603217/5000000000 : ℝ)|=(2074603217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1364_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11193/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1841/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2789/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2789/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2789/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2789/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2789/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2789/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2789/25000 : ℝ) ^ (4323/1024 : ℝ) ≤ (2381365262686893/25000000000000000000 : ℝ) := by
    have hpowers : (2789/25000 : ℝ)^4323 ≤ (2381365262686893/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2789 : ℕ)^4323*25000000000000000000^1024 ≤ 2381365262686893^1024*25000^4323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2789 25000 2381365262686893 25000000000000000000 4323 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2789/25000 : ℝ)) (X := (2381365262686893/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14767/100000 : ℝ) ^ (4323/1024 : ℝ) ≤ (6223691631157581/20000000000000000000 : ℝ) := by
    have hpowers : (14767/100000 : ℝ)^4323 ≤ (6223691631157581/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14767 : ℕ)^4323*20000000000000000000^1024 ≤ 6223691631157581^1024*100000^4323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14767 100000 6223691631157581 20000000000000000000 4323 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14767/100000 : ℝ)) (X := (6223691631157581/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502381365262686893/12500000000000000000 : ℝ) ≤ (2500112807808907/2500000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (12502381365262686893/12500000000000000000 : ℝ)^1024 ≤ (2500112807808907/2500000000000000 : ℝ)^4323 := by
      have hnat : (12502381365262686893 : ℕ)^1024*2500000000000000^4323 ≤ 2500112807808907^4323*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502381365262686893 12500000000000000000 2500112807808907 2500000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500112807808907/2500000000000000 : ℝ)) (X := (12502381365262686893/12500000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040643919206535477/100000000000000000000 : ℝ) ≤ (10000962593577939/10000000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (100040643919206535477/100000000000000000000 : ℝ)^1024 ≤ (10000962593577939/10000000000000000 : ℝ)^4323 := by
      have hnat : (100040643919206535477 : ℕ)^1024*10000000000000000^4323 ≤ 10000962593577939^4323*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040643919206535477 100000000000000000000 10000962593577939 10000000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000962593577939/10000000000000000 : ℝ)) (X := (100040643919206535477/100000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006223691631157581/10000000000000000000 : ℝ) ≤ (40005895823681/40000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (10006223691631157581/10000000000000000000 : ℝ)^1024 ≤ (40005895823681/40000000000000 : ℝ)^4323 := by
      have hnat : (10006223691631157581 : ℕ)^1024*40000000000000^4323 ≤ 40005895823681^4323*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006223691631157581 10000000000000000000 40005895823681 40000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40005895823681/40000000000000 : ℝ)) (X := (10006223691631157581/10000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2381365262686893/25000000000000000000 : ℝ) ≤ ((9025054969852552419/9027500000000000000 : ℝ)+2*(511362342311/361100000000000 : ℝ)*(2789/25000 : ℝ))^(4323/1024 : ℝ) := by
    rw [show (9025054969852552419/9027500000000000000 : ℝ)+2*(511362342311/361100000000000 : ℝ)*(2789/25000 : ℝ)=(2500112807808907/2500000000000000 : ℝ) by norm_num, show 1+2*(2381365262686893/25000000000000000000 : ℝ)=(12502381365262686893/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6223691631157581/20000000000000000000 : ℝ)+(2381365262686893/25000000000000000000 : ℝ) ≤ ((9025054969852552419/9027500000000000000 : ℝ)+(511362342311/361100000000000 : ℝ)*((14767/100000 : ℝ)+(2789/25000 : ℝ)))^(4323/1024 : ℝ) := by
    rw [show (9025054969852552419/9027500000000000000 : ℝ)+(511362342311/361100000000000 : ℝ)*((14767/100000 : ℝ)+(2789/25000 : ℝ))=(10000962593577939/10000000000000000 : ℝ) by norm_num, show 1+(6223691631157581/20000000000000000000 : ℝ)+(2381365262686893/25000000000000000000 : ℝ)=(100040643919206535477/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6223691631157581/20000000000000000000 : ℝ) ≤ ((9025054969852552419/9027500000000000000 : ℝ)+2*(511362342311/361100000000000 : ℝ)*(14767/100000 : ℝ))^(4323/1024 : ℝ) := by
    rw [show (9025054969852552419/9027500000000000000 : ℝ)+2*(511362342311/361100000000000 : ℝ)*(14767/100000 : ℝ)=(40005895823681/40000000000000 : ℝ) by norm_num, show 1+2*(6223691631157581/20000000000000000000 : ℝ)=(10006223691631157581/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9025054969852552419/9027500000000000000 : ℝ)*(X 1 0+X 2 0)+(511362342311/361100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (2789/25000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (9025054969852552419/9027500000000000000 : ℝ)) (alpha := (511362342311/361100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9025054969852552419/9027500000000000000 : ℝ)*(X 0 1+X 2 1)+(511362342311/361100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (2789/25000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (9025054969852552419/9027500000000000000 : ℝ)) (alpha := (511362342311/361100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9025054969852552419/9027500000000000000 : ℝ)*(X 0 2+X 1 2)+(511362342311/361100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (2789/25000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (9025054969852552419/9027500000000000000 : ℝ)) (alpha := (511362342311/361100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-101253901/500000000 : ℝ)*X 0 0+(541189451/1000000000 : ℝ)*X 0 1+(1048992391/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348690397/10000000000 : ℝ)*X 1 0+(-527529941/2500000000 : ℝ)*X 1 1+(1311240501/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668586291/1250000000 : ℝ)*X 2 0+(5244962129/10000000000 : ℝ)*X 2 1+(-2110119691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4320877241/10000000000 : ℝ)*X 0 0+(32405709/78125000 : ℝ)*X 0 1+(2250239527/5000000000 : ℝ)*X 0 2+(4320877241/10000000000 : ℝ)*X 1 0+(32405709/78125000 : ℝ)*X 1 1+(2250239527/5000000000 : ℝ)*X 1 2+(4320877241/10000000000 : ℝ)*X 2 0+(32405709/78125000 : ℝ)*X 2 1+(2250239527/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2025089851/10000000000 : ℝ)*X 0 0+(209822531/400000000 : ℝ)*X 0 1+(2705645133/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663198119/1250000000 : ℝ)*X 1 0+(-1943791627/10000000000 : ℝ)*X 1 1+(1352822651/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305584699/10000000000 : ℝ)*X 2 0+(1352822733/2500000000 : ℝ)*X 2 1+(-971895761/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((27005641/62500000 : ℝ)*X 0 0+(4499210141/10000000000 : ℝ)*X 0 1+(2074603217/5000000000 : ℝ)*X 0 2+(27005641/62500000 : ℝ)*X 1 0+(4499210141/10000000000 : ℝ)*X 1 1+(2074603217/5000000000 : ℝ)*X 1 2+(27005641/62500000 : ℝ)*X 2 0+(4499210141/10000000000 : ℝ)*X 2 1+(2074603217/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2013007953087373566139831917/225687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (96954721/5000000000000 : ℝ)*(base19) + (1841273263/100000000000000 : ℝ)*(base23) + (190302777/100000000000000 : ℝ)*(upper3) + (10986847/100000000000000 : ℝ)*(upper4) + (252578147/100000000000000 : ℝ)*(upper5) + (2206765659547873/50000000000000 : ℝ)*(major0) + (2206765659547873/50000000000000 : ℝ)*(major1) + (2206765659547873/50000000000000 : ℝ)*(major2) + (5990486663189331/100000000000000 : ℝ)*(sp0) + (1497632620711771/25000000000000 : ℝ)*(sp1) + (5990530580668241/100000000000000 : ℝ)*(sp2) + (177281926549067/6250000000000 : ℝ)*(sp3) + (22879376087/50000000000000 : ℝ)*(sp4) + (19094149969/100000000000000 : ℝ)*(sp7) + (2836529918935041/100000000000000 : ℝ)*(f.failure) + (23400517273209/390625000000 : ℝ)*(f.sum) + (6981425981077/2256875000000000000000000000 : ℝ)*base65 + (1461440600989654787/451375000000000000000000000000000 : ℝ)*base67 + (1515664103703404787/451375000000000000000000000000000 : ℝ)*base69 + (6393043375842529787/451375000000000000000000000000000 : ℝ)*base71 + (20008936924829/18055000000000000000000000000 : ℝ)*base74 + (3414708888126279787/451375000000000000000000000000000 : ℝ)*base75 + (5037464632380029787/451375000000000000000000000000000 : ℝ)*base77 + (5854329334599779787/451375000000000000000000000000000 : ℝ)*base79 + (40778457534659/18055000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (39242891/10000000000000000000000 : ℝ)*base90 + (39242891/10000000000000000000000 : ℝ)*base92 + (39242891/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1545138594400236601900839351/112843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (991351227/100000000000000 : ℝ)*(base19) + (209099153/20000000000000 : ℝ)*(base23) + (343508297/100000000000000 : ℝ)*(upper3) + (23163943/20000000000000 : ℝ)*(lower4) + (41360507/50000000000000 : ℝ)*(upper5) + (2222780401522693/50000000000000 : ℝ)*(major0) + (2222780401522693/50000000000000 : ℝ)*(major1) + (2222780401522693/50000000000000 : ℝ)*(major2) + (4739764879/25000000000000 : ℝ)*(sp1) + (34169859961/100000000000000 : ℝ)*(sp2) + (754250777501593/12500000000000 : ℝ)*(sp4) + (3016993134801001/50000000000000 : ℝ)*(sp5) + (3016985502328509/50000000000000 : ℝ)*(sp6) + (2857114929653809/100000000000000 : ℝ)*(sp7) + (2857114929653809/100000000000000 : ℝ)*(f.failure) + (754250777501593/12500000000000 : ℝ)*(f.sum) + (1915329777383/9027500000000000000000000000 : ℝ)*base65 + (1482695668056255633/451375000000000000000000000000000 : ℝ)*base68 + (3075238451100130633/451375000000000000000000000000000 : ℝ)*base70 + (2652767604005880633/451375000000000000000000000000000 : ℝ)*base72 + (19333121381541/18055000000000000000000000000 : ℝ)*base73 + (3632085962081130633/451375000000000000000000000000000 : ℝ)*base76 + (2083124695977630633/451375000000000000000000000000000 : ℝ)*base78 + (3033942615119369367/451375000000000000000000000000000 : ℝ)*base79 + (48778428486199/18055000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (16418459/10000000000000000000000 : ℝ)*base90 + (16418459/10000000000000000000000 : ℝ)*base92 + (16418459/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1364_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11193/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1364_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1364_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (801/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1249/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11193/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1364_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1364_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1364_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (801/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1249/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11193/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1364_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

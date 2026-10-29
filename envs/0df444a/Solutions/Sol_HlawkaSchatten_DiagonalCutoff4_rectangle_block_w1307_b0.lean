-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1307_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:38:05.853204+00:00
-- url     : https://prove2.me/submissions/657c5b84-6a92-4f6b-93f0-69d620273edd

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
theorem support_rectangle_w1307_s0_0 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1830019289/10000000000 : ℝ)*x 0 + (6012170887/10000000000 : ℝ)*x 1 + (960498009/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1830019289/10000000000 : ℝ)^4267 ≤ (1338076314899/12500000000000 : ℝ)^3243 := by
    have hnat : (1830019289 : ℕ)^4267*12500000000000^3243 ≤ 1338076314899^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1830019289 10000000000 1338076314899 12500000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6012170887/10000000000 : ℝ)^4267 ≤ (12799674128421/25000000000000 : ℝ)^3243 := by
    have hnat : (6012170887 : ℕ)^4267*25000000000000^3243 ≤ 12799674128421^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6012170887 10000000000 12799674128421 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (960498009/2000000000 : ℝ)^4267 ≤ (19048346477951/50000000000000 : ℝ)^3243 := by
    have hnat : (960498009 : ℕ)^4267*50000000000000^3243 ≤ 19048346477951^3243*2000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960498009 2000000000 19048346477951 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1830019289/10000000000 : ℝ), (6012170887/10000000000 : ℝ), (960498009/2000000000 : ℝ)] ![(1338076314899/12500000000000 : ℝ), (12799674128421/25000000000000 : ℝ), (19048346477951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1830019289/10000000000 : ℝ)|^4267 ≤ (1338076314899/12500000000000 : ℝ)^3243
        have hw : |(-1830019289/10000000000 : ℝ)|=(1830019289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6012170887/10000000000 : ℝ)|^4267 ≤ (12799674128421/25000000000000 : ℝ)^3243
        have hw : |(6012170887/10000000000 : ℝ)|=(6012170887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(960498009/2000000000 : ℝ)|^4267 ≤ (19048346477951/50000000000000 : ℝ)^3243
        have hw : |(960498009/2000000000 : ℝ)|=(960498009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s0_1 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1376433947/2500000000 : ℝ)*x 0 + (-1259682363/5000000000 : ℝ)*x 1 + (480249007/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1376433947/2500000000 : ℝ)^4267 ≤ (5700146440979/12500000000000 : ℝ)^3243 := by
    have hnat : (1376433947 : ℕ)^4267*12500000000000^3243 ≤ 5700146440979^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376433947 2500000000 5700146440979 12500000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1259682363/5000000000 : ℝ)^4267 ≤ (16302135242249/100000000000000 : ℝ)^3243 := by
    have hnat : (1259682363 : ℕ)^4267*100000000000000^3243 ≤ 16302135242249^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1259682363 5000000000 16302135242249 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (480249007/1000000000 : ℝ)^4267 ≤ (38096693216839/100000000000000 : ℝ)^3243 := by
    have hnat : (480249007 : ℕ)^4267*100000000000000^3243 ≤ 38096693216839^3243*1000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480249007 1000000000 38096693216839 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1376433947/2500000000 : ℝ), (-1259682363/5000000000 : ℝ), (480249007/1000000000 : ℝ)] ![(5700146440979/12500000000000 : ℝ), (16302135242249/100000000000000 : ℝ), (38096693216839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1376433947/2500000000 : ℝ)|^4267 ≤ (5700146440979/12500000000000 : ℝ)^3243
        have hw : |(1376433947/2500000000 : ℝ)|=(1376433947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1259682363/5000000000 : ℝ)|^4267 ≤ (16302135242249/100000000000000 : ℝ)^3243
        have hw : |(-1259682363/5000000000 : ℝ)|=(1259682363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(480249007/1000000000 : ℝ)|^4267 ≤ (38096693216839/100000000000000 : ℝ)^3243
        have hw : |(480249007/1000000000 : ℝ)|=(480249007/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s0_2 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1376433859/2500000000 : ℝ)*x 0 + (4802490443/10000000000 : ℝ)*x 1 + (-1259682359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1376433859/2500000000 : ℝ)^4267 ≤ (45601167691829/100000000000000 : ℝ)^3243 := by
    have hnat : (1376433859 : ℕ)^4267*100000000000000^3243 ≤ 45601167691829^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376433859 2500000000 45601167691829 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4802490443/10000000000 : ℝ)^4267 ≤ (38096697110027/100000000000000 : ℝ)^3243 := by
    have hnat : (4802490443 : ℕ)^4267*100000000000000^3243 ≤ 38096697110027^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4802490443 10000000000 38096697110027 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1259682359/5000000000 : ℝ)^4267 ≤ (8151067587069/50000000000000 : ℝ)^3243 := by
    have hnat : (1259682359 : ℕ)^4267*50000000000000^3243 ≤ 8151067587069^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1259682359 5000000000 8151067587069 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1376433859/2500000000 : ℝ), (4802490443/10000000000 : ℝ), (-1259682359/5000000000 : ℝ)] ![(45601167691829/100000000000000 : ℝ), (38096697110027/100000000000000 : ℝ), (8151067587069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1376433859/2500000000 : ℝ)|^4267 ≤ (45601167691829/100000000000000 : ℝ)^3243
        have hw : |(1376433859/2500000000 : ℝ)|=(1376433859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4802490443/10000000000 : ℝ)|^4267 ≤ (38096697110027/100000000000000 : ℝ)^3243
        have hw : |(4802490443/10000000000 : ℝ)|=(4802490443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1259682359/5000000000 : ℝ)|^4267 ≤ (8151067587069/50000000000000 : ℝ)^3243
        have hw : |(-1259682359/5000000000 : ℝ)|=(1259682359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s0_3 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16736141/40000000 : ℝ)*x 0 + (1554245169/5000000000 : ℝ)*x 1 + (5608928117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16736141/40000000 : ℝ)^4267 ≤ (7944222802637/25000000000000 : ℝ)^3243 := by
    have hnat : (16736141 : ℕ)^4267*25000000000000^3243 ≤ 7944222802637^3243*40000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16736141 40000000 7944222802637 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1554245169/5000000000 : ℝ)^4267 ≤ (2149406082319/10000000000000 : ℝ)^3243 := by
    have hnat : (1554245169 : ℕ)^4267*10000000000000^3243 ≤ 2149406082319^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1554245169 5000000000 2149406082319 10000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5608928117/10000000000 : ℝ)^4267 ≤ (46729047948089/100000000000000 : ℝ)^3243 := by
    have hnat : (5608928117 : ℕ)^4267*100000000000000^3243 ≤ 46729047948089^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5608928117 10000000000 46729047948089 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16736141/40000000 : ℝ), (1554245169/5000000000 : ℝ), (5608928117/10000000000 : ℝ)] ![(7944222802637/25000000000000 : ℝ), (2149406082319/10000000000000 : ℝ), (46729047948089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16736141/40000000 : ℝ)|^4267 ≤ (7944222802637/25000000000000 : ℝ)^3243
        have hw : |(16736141/40000000 : ℝ)|=(16736141/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1554245169/5000000000 : ℝ)|^4267 ≤ (2149406082319/10000000000000 : ℝ)^3243
        have hw : |(1554245169/5000000000 : ℝ)|=(1554245169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5608928117/10000000000 : ℝ)|^4267 ≤ (46729047948089/100000000000000 : ℝ)^3243
        have hw : |(5608928117/10000000000 : ℝ)|=(5608928117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s0_4 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-91733121/500000000 : ℝ)*x 0 + (966737001/2000000000 : ℝ)*x 1 + (597986429/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (91733121/500000000 : ℝ)^4267 ≤ (5370180243869/50000000000000 : ℝ)^3243 := by
    have hnat : (91733121 : ℕ)^4267*50000000000000^3243 ≤ 5370180243869^3243*500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91733121 500000000 5370180243869 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (966737001/2000000000 : ℝ)^4267 ≤ (19211311884673/50000000000000 : ℝ)^3243 := by
    have hnat : (966737001 : ℕ)^4267*50000000000000^3243 ≤ 19211311884673^3243*2000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966737001 2000000000 19211311884673 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (597986429/1000000000 : ℝ)^4267 ≤ (50837015720317/100000000000000 : ℝ)^3243 := by
    have hnat : (597986429 : ℕ)^4267*100000000000000^3243 ≤ 50837015720317^3243*1000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597986429 1000000000 50837015720317 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-91733121/500000000 : ℝ), (966737001/2000000000 : ℝ), (597986429/1000000000 : ℝ)] ![(5370180243869/50000000000000 : ℝ), (19211311884673/50000000000000 : ℝ), (50837015720317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-91733121/500000000 : ℝ)|^4267 ≤ (5370180243869/50000000000000 : ℝ)^3243
        have hw : |(-91733121/500000000 : ℝ)|=(91733121/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(966737001/2000000000 : ℝ)|^4267 ≤ (19211311884673/50000000000000 : ℝ)^3243
        have hw : |(966737001/2000000000 : ℝ)|=(966737001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(597986429/1000000000 : ℝ)|^4267 ≤ (50837015720317/100000000000000 : ℝ)^3243
        have hw : |(597986429/1000000000 : ℝ)|=(597986429/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s0_5 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5176298097/10000000000 : ℝ)*x 0 + (-670995493/5000000000 : ℝ)*x 1 + (59798643/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5176298097/10000000000 : ℝ)^4267 ≤ (525567949593/1250000000000 : ℝ)^3243 := by
    have hnat : (5176298097 : ℕ)^4267*1250000000000^3243 ≤ 525567949593^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176298097 10000000000 525567949593 1250000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (670995493/5000000000 : ℝ)^4267 ≤ (1779387044823/25000000000000 : ℝ)^3243 := by
    have hnat : (670995493 : ℕ)^4267*25000000000000^3243 ≤ 1779387044823^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670995493 5000000000 1779387044823 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59798643/100000000 : ℝ)^4267 ≤ (25418507916087/50000000000000 : ℝ)^3243 := by
    have hnat : (59798643 : ℕ)^4267*50000000000000^3243 ≤ 25418507916087^3243*100000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59798643 100000000 25418507916087 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5176298097/10000000000 : ℝ), (-670995493/5000000000 : ℝ), (59798643/100000000 : ℝ)] ![(525567949593/1250000000000 : ℝ), (1779387044823/25000000000000 : ℝ), (25418507916087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5176298097/10000000000 : ℝ)|^4267 ≤ (525567949593/1250000000000 : ℝ)^3243
        have hw : |(5176298097/10000000000 : ℝ)|=(5176298097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-670995493/5000000000 : ℝ)|^4267 ≤ (1779387044823/25000000000000 : ℝ)^3243
        have hw : |(-670995493/5000000000 : ℝ)|=(670995493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(59798643/100000000 : ℝ)|^4267 ≤ (25418507916087/50000000000000 : ℝ)^3243
        have hw : |(59798643/100000000 : ℝ)|=(59798643/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s0_6 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2588149043/5000000000 : ℝ)*x 0 + (2989932149/5000000000 : ℝ)*x 1 + (-1341991007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2588149043/5000000000 : ℝ)^4267 ≤ (42045435849877/100000000000000 : ℝ)^3243 := by
    have hnat : (2588149043 : ℕ)^4267*100000000000000^3243 ≤ 42045435849877^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588149043 5000000000 42045435849877 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2989932149/5000000000 : ℝ)^4267 ≤ (50837015809803/100000000000000 : ℝ)^3243 := by
    have hnat : (2989932149 : ℕ)^4267*100000000000000^3243 ≤ 50837015809803^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2989932149 5000000000 50837015809803 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1341991007/10000000000 : ℝ)^4267 ≤ (3558774162919/50000000000000 : ℝ)^3243 := by
    have hnat : (1341991007 : ℕ)^4267*50000000000000^3243 ≤ 3558774162919^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341991007 10000000000 3558774162919 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2588149043/5000000000 : ℝ), (2989932149/5000000000 : ℝ), (-1341991007/10000000000 : ℝ)] ![(42045435849877/100000000000000 : ℝ), (50837015809803/100000000000000 : ℝ), (3558774162919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2588149043/5000000000 : ℝ)|^4267 ≤ (42045435849877/100000000000000 : ℝ)^3243
        have hw : |(2588149043/5000000000 : ℝ)|=(2588149043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2989932149/5000000000 : ℝ)|^4267 ≤ (50837015809803/100000000000000 : ℝ)^3243
        have hw : |(2989932149/5000000000 : ℝ)|=(2989932149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1341991007/10000000000 : ℝ)|^4267 ≤ (3558774162919/50000000000000 : ℝ)^3243
        have hw : |(-1341991007/10000000000 : ℝ)|=(1341991007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s0_7 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4193632077/10000000000 : ℝ)*x 0 + (5544447977/10000000000 : ℝ)*x 1 + (1587634371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4193632077/10000000000 : ℝ)^4267 ≤ (31872826102251/100000000000000 : ℝ)^3243 := by
    have hnat : (4193632077 : ℕ)^4267*100000000000000^3243 ≤ 31872826102251^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4193632077 10000000000 31872826102251 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5544447977/10000000000 : ℝ)^4267 ≤ (23011757177501/50000000000000 : ℝ)^3243 := by
    have hnat : (5544447977 : ℕ)^4267*50000000000000^3243 ≤ 23011757177501^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5544447977 10000000000 23011757177501 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1587634371/5000000000 : ℝ)^4267 ≤ (22103659520241/100000000000000 : ℝ)^3243 := by
    have hnat : (1587634371 : ℕ)^4267*100000000000000^3243 ≤ 22103659520241^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1587634371 5000000000 22103659520241 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4193632077/10000000000 : ℝ), (5544447977/10000000000 : ℝ), (1587634371/5000000000 : ℝ)] ![(31872826102251/100000000000000 : ℝ), (23011757177501/50000000000000 : ℝ), (22103659520241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4193632077/10000000000 : ℝ)|^4267 ≤ (31872826102251/100000000000000 : ℝ)^3243
        have hw : |(4193632077/10000000000 : ℝ)|=(4193632077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5544447977/10000000000 : ℝ)|^4267 ≤ (23011757177501/50000000000000 : ℝ)^3243
        have hw : |(5544447977/10000000000 : ℝ)|=(5544447977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1587634371/5000000000 : ℝ)|^4267 ≤ (22103659520241/100000000000000 : ℝ)^3243
        have hw : |(1587634371/5000000000 : ℝ)|=(1587634371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1307_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (287/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (217/800 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2133/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2133 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2133*1^512 ≤ 0^512*1^2133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2133 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2133/512 : ℝ) ≤ (2198749258775213793/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2133 ≤ (2198749258775213793/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2133*100000000000000000000^512 ≤ 2198749258775213793^512*5^2133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2198749258775213793 100000000000000000000 2133 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2198749258775213793/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2133 := by
      have hnat : (1 : ℕ)^512*1^2133 ≤ 1^2133*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (102198749258775213793/100000000000000000000 : ℝ) ≤ (5026171439207717/5000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (102198749258775213793/100000000000000000000 : ℝ)^512 ≤ (5026171439207717/5000000000000000 : ℝ)^2133 := by
      have hnat : (102198749258775213793 : ℕ)^512*5000000000000000^2133 ≤ 5026171439207717^2133*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102198749258775213793 100000000000000000000 5026171439207717 5000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5026171439207717/5000000000000000 : ℝ)) (X := (102198749258775213793/100000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (52198749258775213793/50000000000000000000 : ℝ) ≤ (2526171439207717/2500000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (52198749258775213793/50000000000000000000 : ℝ)^512 ≤ (2526171439207717/2500000000000000 : ℝ)^2133 := by
      have hnat : (52198749258775213793 : ℕ)^512*2500000000000000^2133 ≤ 2526171439207717^2133*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52198749258775213793 50000000000000000000 2526171439207717 2500000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2526171439207717/2500000000000000 : ℝ)) (X := (52198749258775213793/50000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(26171439207717/2000000000000000 : ℝ)*(0 : ℝ))^(2133/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(26171439207717/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2198749258775213793/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(26171439207717/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2133/512 : ℝ) := by
    rw [show (1 : ℝ)+(26171439207717/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5026171439207717/5000000000000000 : ℝ) by norm_num, show 1+(2198749258775213793/100000000000000000000 : ℝ)+(0 : ℝ)=(102198749258775213793/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2198749258775213793/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(26171439207717/2000000000000000 : ℝ)*(2/5 : ℝ))^(2133/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(26171439207717/2000000000000000 : ℝ)*(2/5 : ℝ)=(2526171439207717/2500000000000000 : ℝ) by norm_num, show 1+2*(2198749258775213793/100000000000000000000 : ℝ)=(52198749258775213793/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(26171439207717/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26171439207717/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(26171439207717/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26171439207717/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(26171439207717/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26171439207717/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1830019289/10000000000 : ℝ)*X 0 0+(6012170887/10000000000 : ℝ)*X 0 1+(960498009/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1376433947/2500000000 : ℝ)*X 1 0+(-1259682363/5000000000 : ℝ)*X 1 1+(480249007/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1376433859/2500000000 : ℝ)*X 2 0+(4802490443/10000000000 : ℝ)*X 2 1+(-1259682359/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((16736141/40000000 : ℝ)*X 0 0+(1554245169/5000000000 : ℝ)*X 0 1+(5608928117/10000000000 : ℝ)*X 0 2+(16736141/40000000 : ℝ)*X 1 0+(1554245169/5000000000 : ℝ)*X 1 1+(5608928117/10000000000 : ℝ)*X 1 2+(16736141/40000000 : ℝ)*X 2 0+(1554245169/5000000000 : ℝ)*X 2 1+(5608928117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-91733121/500000000 : ℝ)*X 0 0+(966737001/2000000000 : ℝ)*X 0 1+(597986429/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5176298097/10000000000 : ℝ)*X 1 0+(-670995493/5000000000 : ℝ)*X 1 1+(59798643/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2588149043/5000000000 : ℝ)*X 2 0+(2989932149/5000000000 : ℝ)*X 2 1+(-1341991007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4193632077/10000000000 : ℝ)*X 0 0+(5544447977/10000000000 : ℝ)*X 0 1+(1587634371/5000000000 : ℝ)*X 0 2+(4193632077/10000000000 : ℝ)*X 1 0+(5544447977/10000000000 : ℝ)*X 1 1+(1587634371/5000000000 : ℝ)*X 1 2+(4193632077/10000000000 : ℝ)*X 2 0+(5544447977/10000000000 : ℝ)*X 2 1+(1587634371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (633485927078510630048919/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27852813/25000000000000 : ℝ)*(base1) + (1684436727/100000000000000 : ℝ)*(base19) + (407896191/25000000000000 : ℝ)*(base23) + (12202541/6250000000000 : ℝ)*(upper3) + (5617471/3125000000000 : ℝ)*(upper5) + (613304999225523/100000000000000 : ℝ)*(major0) + (613304999225523/100000000000000 : ℝ)*(major1) + (613304999225523/100000000000000 : ℝ)*(major2) + (165333908784297/20000000000000 : ℝ)*(sp0) + (206668272210971/25000000000000 : ℝ)*(sp1) + (103334142711981/12500000000000 : ℝ)*(sp2) + (399932362793649/100000000000000 : ℝ)*(sp3) + (2670385189/50000000000000 : ℝ)*(sp4) + (2539803551/100000000000000 : ℝ)*(sp7) + (399935014008451/100000000000000 : ℝ)*(f.failure) + (826674773280611/100000000000000 : ℝ)*(f.sum) + (305729650239009/100000000000000000000000000000 : ℝ)*base66 + (1531282029839009/200000000000000000000000000000 : ℝ)*base68 + (232531680960991/200000000000000000000000000000 : ℝ)*base69 + (768628928839009/200000000000000000000000000000 : ℝ)*base72 + (648357665539009/100000000000000000000000000000 : ℝ)*base74 + (612291006039009/200000000000000000000000000000 : ℝ)*base76 + (1525418756039009/200000000000000000000000000000 : ℝ)*base78 + (2254320345639009/200000000000000000000000000000 : ℝ)*base80 + (225187633860991/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (8328259/2500000000000000000000 : ℝ)*base90 + (8328259/2500000000000000000000 : ℝ)*base92 + (8328259/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (107527583688649831419843/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (515213529/50000000000000 : ℝ)*(base19) + (518483073/50000000000000 : ℝ)*(base23) + (4406511/6250000000000 : ℝ)*(base32) + (146843847/100000000000000 : ℝ)*(upper3) + (97586191/100000000000000 : ℝ)*(upper5) + (323637674796893/50000000000000 : ℝ)*(major0) + (323637674796893/50000000000000 : ℝ)*(major1) + (323637674796893/50000000000000 : ℝ)*(major2) + (2278581183/100000000000000 : ℝ)*(sp1) + (2410460983/100000000000000 : ℝ)*(sp2) + (872463541470579/100000000000000 : ℝ)*(sp4) + (436230116231169/50000000000000 : ℝ)*(sp5) + (17449201880869/2000000000000 : ℝ)*(sp6) + (422086943842703/100000000000000 : ℝ)*(sp7) + (422087014346879/100000000000000 : ℝ)*(f.failure) + (872463541470579/100000000000000 : ℝ)*(f.sum) + (63622665673281/50000000000000000000000000000 : ℝ)*base65 + (492118159376719/100000000000000000000000000000 : ℝ)*base68 + (195406540376719/100000000000000000000000000000 : ℝ)*base70 + (216888398876719/100000000000000000000000000000 : ℝ)*base72 + (95391472026719/50000000000000000000000000000 : ℝ)*base74 + (365342770376719/100000000000000000000000000000 : ℝ)*base76 + (68316628676719/100000000000000000000000000000 : ℝ)*base78 + (475784726776719/100000000000000000000000000000 : ℝ)*base80 + (2052929123281/50000000000000000000000000000 : ℝ)*base81 + (1395711/2500000000000000000000 : ℝ)*base90 + (1395711/2500000000000000000000 : ℝ)*base92 + (1395711/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1307_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (287/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (217/800 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1307_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1307_s1_0 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-403978907/2000000000 : ℝ)*x 0 + (5658199667/10000000000 : ℝ)*x 1 + (157340391/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (403978907/2000000000 : ℝ)^4267 ≤ (6094686349991/50000000000000 : ℝ)^3243 := by
    have hnat : (403978907 : ℕ)^4267*50000000000000^3243 ≤ 6094686349991^3243*2000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403978907 2000000000 6094686349991 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5658199667/10000000000 : ℝ)^4267 ≤ (23634950742753/50000000000000 : ℝ)^3243 := by
    have hnat : (5658199667 : ℕ)^4267*50000000000000^3243 ≤ 23634950742753^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5658199667 10000000000 23634950742753 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157340391/312500000 : ℝ)^4267 ≤ (40540725796253/100000000000000 : ℝ)^3243 := by
    have hnat : (157340391 : ℕ)^4267*100000000000000^3243 ≤ 40540725796253^3243*312500000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157340391 312500000 40540725796253 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-403978907/2000000000 : ℝ), (5658199667/10000000000 : ℝ), (157340391/312500000 : ℝ)] ![(6094686349991/50000000000000 : ℝ), (23634950742753/50000000000000 : ℝ), (40540725796253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-403978907/2000000000 : ℝ)|^4267 ≤ (6094686349991/50000000000000 : ℝ)^3243
        have hw : |(-403978907/2000000000 : ℝ)|=(403978907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5658199667/10000000000 : ℝ)|^4267 ≤ (23634950742753/50000000000000 : ℝ)^3243
        have hw : |(5658199667/10000000000 : ℝ)|=(5658199667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(157340391/312500000 : ℝ)|^4267 ≤ (40540725796253/100000000000000 : ℝ)^3243
        have hw : |(157340391/312500000 : ℝ)|=(157340391/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s1_1 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5409394131/10000000000 : ℝ)*x 0 + (-2353525441/10000000000 : ℝ)*x 1 + (5034892713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5409394131/10000000000 : ℝ)^4267 ≤ (44554177632649/100000000000000 : ℝ)^3243 := by
    have hnat : (5409394131 : ℕ)^4267*100000000000000^3243 ≤ 44554177632649^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409394131 10000000000 44554177632649 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2353525441/10000000000 : ℝ)^4267 ≤ (7452547211903/50000000000000 : ℝ)^3243 := by
    have hnat : (2353525441 : ℕ)^4267*50000000000000^3243 ≤ 7452547211903^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2353525441 10000000000 7452547211903 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5034892713/10000000000 : ℝ)^4267 ≤ (4054072792573/10000000000000 : ℝ)^3243 := by
    have hnat : (5034892713 : ℕ)^4267*10000000000000^3243 ≤ 4054072792573^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5034892713 10000000000 4054072792573 10000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5409394131/10000000000 : ℝ), (-2353525441/10000000000 : ℝ), (5034892713/10000000000 : ℝ)] ![(44554177632649/100000000000000 : ℝ), (7452547211903/50000000000000 : ℝ), (4054072792573/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5409394131/10000000000 : ℝ)|^4267 ≤ (44554177632649/100000000000000 : ℝ)^3243
        have hw : |(5409394131/10000000000 : ℝ)|=(5409394131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2353525441/10000000000 : ℝ)|^4267 ≤ (7452547211903/50000000000000 : ℝ)^3243
        have hw : |(-2353525441/10000000000 : ℝ)|=(2353525441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5034892713/10000000000 : ℝ)|^4267 ≤ (4054072792573/10000000000000 : ℝ)^3243
        have hw : |(5034892713/10000000000 : ℝ)|=(5034892713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s1_2 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1352348603/2500000000 : ℝ)*x 0 + (2517446129/5000000000 : ℝ)*x 1 + (-470705131/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1352348603/2500000000 : ℝ)^4267 ≤ (44554180677891/100000000000000 : ℝ)^3243 := by
    have hnat : (1352348603 : ℕ)^4267*100000000000000^3243 ≤ 44554180677891^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352348603 2500000000 44554180677891 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2517446129/5000000000 : ℝ)^4267 ≤ (40540723105271/100000000000000 : ℝ)^3243 := by
    have hnat : (2517446129 : ℕ)^4267*100000000000000^3243 ≤ 40540723105271^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2517446129 5000000000 40540723105271 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (470705131/2000000000 : ℝ)^4267 ≤ (14905096207027/100000000000000 : ℝ)^3243 := by
    have hnat : (470705131 : ℕ)^4267*100000000000000^3243 ≤ 14905096207027^3243*2000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470705131 2000000000 14905096207027 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1352348603/2500000000 : ℝ), (2517446129/5000000000 : ℝ), (-470705131/2000000000 : ℝ)] ![(44554180677891/100000000000000 : ℝ), (40540723105271/100000000000000 : ℝ), (14905096207027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1352348603/2500000000 : ℝ)|^4267 ≤ (44554180677891/100000000000000 : ℝ)^3243
        have hw : |(1352348603/2500000000 : ℝ)|=(1352348603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2517446129/5000000000 : ℝ)|^4267 ≤ (40540723105271/100000000000000 : ℝ)^3243
        have hw : |(2517446129/5000000000 : ℝ)|=(2517446129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-470705131/2000000000 : ℝ)|^4267 ≤ (14905096207027/100000000000000 : ℝ)^3243
        have hw : |(-470705131/2000000000 : ℝ)|=(470705131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s1_3 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4298507269/10000000000 : ℝ)*x 0 + (1849869611/5000000000 : ℝ)*x 1 + (99762593/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298507269/10000000000 : ℝ)^4267 ≤ (32925709796981/100000000000000 : ℝ)^3243 := by
    have hnat : (4298507269 : ℕ)^4267*100000000000000^3243 ≤ 32925709796981^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298507269 10000000000 32925709796981 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1849869611/5000000000 : ℝ)^4267 ≤ (27028261586997/100000000000000 : ℝ)^3243 := by
    have hnat : (1849869611 : ℕ)^4267*100000000000000^3243 ≤ 27028261586997^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1849869611 5000000000 27028261586997 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (99762593/200000000 : ℝ)^4267 ≤ (8009205720303/20000000000000 : ℝ)^3243 := by
    have hnat : (99762593 : ℕ)^4267*20000000000000^3243 ≤ 8009205720303^3243*200000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99762593 200000000 8009205720303 20000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298507269/10000000000 : ℝ), (1849869611/5000000000 : ℝ), (99762593/200000000 : ℝ)] ![(32925709796981/100000000000000 : ℝ), (27028261586997/100000000000000 : ℝ), (8009205720303/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298507269/10000000000 : ℝ)|^4267 ≤ (32925709796981/100000000000000 : ℝ)^3243
        have hw : |(4298507269/10000000000 : ℝ)|=(4298507269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1849869611/5000000000 : ℝ)|^4267 ≤ (27028261586997/100000000000000 : ℝ)^3243
        have hw : |(1849869611/5000000000 : ℝ)|=(1849869611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(99762593/200000000 : ℝ)|^4267 ≤ (8009205720303/20000000000000 : ℝ)^3243
        have hw : |(99762593/200000000 : ℝ)|=(99762593/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s1_4 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1010249879/5000000000 : ℝ)*x 0 + (630365823/1250000000 : ℝ)*x 1 + (1130003053/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1010249879/5000000000 : ℝ)^4267 ≤ (12194178484817/100000000000000 : ℝ)^3243 := by
    have hnat : (1010249879 : ℕ)^4267*100000000000000^3243 ≤ 12194178484817^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010249879 5000000000 12194178484817 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (630365823/1250000000 : ℝ)^4267 ≤ (40625863529913/100000000000000 : ℝ)^3243 := by
    have hnat : (630365823 : ℕ)^4267*100000000000000^3243 ≤ 40625863529913^3243*1250000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      630365823 1250000000 40625863529913 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130003053/2000000000 : ℝ)^4267 ≤ (9435991594211/20000000000000 : ℝ)^3243 := by
    have hnat : (1130003053 : ℕ)^4267*20000000000000^3243 ≤ 9435991594211^3243*2000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130003053 2000000000 9435991594211 20000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1010249879/5000000000 : ℝ), (630365823/1250000000 : ℝ), (1130003053/2000000000 : ℝ)] ![(12194178484817/100000000000000 : ℝ), (40625863529913/100000000000000 : ℝ), (9435991594211/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1010249879/5000000000 : ℝ)|^4267 ≤ (12194178484817/100000000000000 : ℝ)^3243
        have hw : |(-1010249879/5000000000 : ℝ)|=(1010249879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(630365823/1250000000 : ℝ)|^4267 ≤ (40625863529913/100000000000000 : ℝ)^3243
        have hw : |(630365823/1250000000 : ℝ)|=(630365823/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1130003053/2000000000 : ℝ)|^4267 ≤ (9435991594211/20000000000000 : ℝ)^3243
        have hw : |(1130003053/2000000000 : ℝ)|=(1130003053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s1_5 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328008699/625000000 : ℝ)*x 0 + (-1738401979/10000000000 : ℝ)*x 1 + (5650016063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328008699/625000000 : ℝ)^4267 ≤ (171259652663/400000000000 : ℝ)^3243 := by
    have hnat : (328008699 : ℕ)^4267*400000000000^3243 ≤ 171259652663^3243*625000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328008699 625000000 171259652663 400000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1738401979/10000000000 : ℝ)^4267 ≤ (5002560040321/50000000000000 : ℝ)^3243 := by
    have hnat : (1738401979 : ℕ)^4267*50000000000000^3243 ≤ 5002560040321^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1738401979 10000000000 5002560040321 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5650016063/10000000000 : ℝ)^4267 ≤ (11794991684693/25000000000000 : ℝ)^3243 := by
    have hnat : (5650016063 : ℕ)^4267*25000000000000^3243 ≤ 11794991684693^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5650016063 10000000000 11794991684693 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328008699/625000000 : ℝ), (-1738401979/10000000000 : ℝ), (5650016063/10000000000 : ℝ)] ![(171259652663/400000000000 : ℝ), (5002560040321/50000000000000 : ℝ), (11794991684693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328008699/625000000 : ℝ)|^4267 ≤ (171259652663/400000000000 : ℝ)^3243
        have hw : |(328008699/625000000 : ℝ)|=(328008699/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1738401979/10000000000 : ℝ)|^4267 ≤ (5002560040321/50000000000000 : ℝ)^3243
        have hw : |(-1738401979/10000000000 : ℝ)|=(1738401979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5650016063/10000000000 : ℝ)|^4267 ≤ (11794991684693/25000000000000 : ℝ)^3243
        have hw : |(5650016063/10000000000 : ℝ)|=(5650016063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s1_6 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5248139107/10000000000 : ℝ)*x 0 + (113000313/200000000 : ℝ)*x 1 + (-1738402687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5248139107/10000000000 : ℝ)^4267 ≤ (1712596493569/4000000000000 : ℝ)^3243 := by
    have hnat : (5248139107 : ℕ)^4267*4000000000000^3243 ≤ 1712596493569^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5248139107 10000000000 1712596493569 4000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113000313/200000000 : ℝ)^4267 ≤ (23589981100547/50000000000000 : ℝ)^3243 := by
    have hnat : (113000313 : ℕ)^4267*50000000000000^3243 ≤ 23589981100547^3243*200000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113000313 200000000 23589981100547 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1738402687/10000000000 : ℝ)^4267 ≤ (10005125442077/100000000000000 : ℝ)^3243 := by
    have hnat : (1738402687 : ℕ)^4267*100000000000000^3243 ≤ 10005125442077^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1738402687 10000000000 10005125442077 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5248139107/10000000000 : ℝ), (113000313/200000000 : ℝ), (-1738402687/10000000000 : ℝ)] ![(1712596493569/4000000000000 : ℝ), (23589981100547/50000000000000 : ℝ), (10005125442077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5248139107/10000000000 : ℝ)|^4267 ≤ (1712596493569/4000000000000 : ℝ)^3243
        have hw : |(5248139107/10000000000 : ℝ)|=(5248139107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(113000313/200000000 : ℝ)|^4267 ≤ (23589981100547/50000000000000 : ℝ)^3243
        have hw : |(113000313/200000000 : ℝ)|=(113000313/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1738402687/10000000000 : ℝ)|^4267 ≤ (10005125442077/100000000000000 : ℝ)^3243
        have hw : |(-1738402687/10000000000 : ℝ)|=(1738402687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s1_7 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2149878627/5000000000 : ℝ)*x 0 + (4971523577/10000000000 : ℝ)*x 1 + (3716655857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149878627/5000000000 : ℝ)^4267 ≤ (32938308270081/100000000000000 : ℝ)^3243 := by
    have hnat : (2149878627 : ℕ)^4267*100000000000000^3243 ≤ 32938308270081^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149878627 5000000000 32938308270081 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4971523577/10000000000 : ℝ)^4267 ≤ (19935353413051/50000000000000 : ℝ)^3243 := by
    have hnat : (4971523577 : ℕ)^4267*50000000000000^3243 ≤ 19935353413051^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4971523577 10000000000 19935353413051 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3716655857/10000000000 : ℝ)^4267 ≤ (5438196977381/20000000000000 : ℝ)^3243 := by
    have hnat : (3716655857 : ℕ)^4267*20000000000000^3243 ≤ 5438196977381^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3716655857 10000000000 5438196977381 20000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2149878627/5000000000 : ℝ), (4971523577/10000000000 : ℝ), (3716655857/10000000000 : ℝ)] ![(32938308270081/100000000000000 : ℝ), (19935353413051/50000000000000 : ℝ), (5438196977381/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2149878627/5000000000 : ℝ)|^4267 ≤ (32938308270081/100000000000000 : ℝ)^3243
        have hw : |(2149878627/5000000000 : ℝ)|=(2149878627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4971523577/10000000000 : ℝ)|^4267 ≤ (19935353413051/50000000000000 : ℝ)^3243
        have hw : |(4971523577/10000000000 : ℝ)|=(4971523577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3716655857/10000000000 : ℝ)|^4267 ≤ (5438196977381/20000000000000 : ℝ)^3243
        have hw : |(3716655857/10000000000 : ℝ)|=(3716655857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1307_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (217/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (287/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1639/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19731/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (217/800 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (287/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (217/800 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (287/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (217/800 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (287/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (217/800 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (287/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (217/800 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (287/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (217/800 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (287/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (287/25000 : ℝ) ^ (2133/512 : ℝ) ≤ (827346801479/100000000000000000000 : ℝ) := by
    have hpowers : (287/25000 : ℝ)^2133 ≤ (827346801479/100000000000000000000 : ℝ)^512 := by
      have hnat : (287 : ℕ)^2133*100000000000000000000^512 ≤ 827346801479^512*25000^2133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        287 25000 827346801479 100000000000000000000 2133 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (287/25000 : ℝ)) (X := (827346801479/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hpowhi : (217/800 : ℝ) ^ (2133/512 : ℝ) ≤ (21796136354420887/5000000000000000000 : ℝ) := by
    have hpowers : (217/800 : ℝ)^2133 ≤ (21796136354420887/5000000000000000000 : ℝ)^512 := by
      have hnat : (217 : ℕ)^2133*5000000000000000000^512 ≤ 21796136354420887^512*800^2133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        217 800 21796136354420887 5000000000000000000 2133 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (217/800 : ℝ)) (X := (21796136354420887/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000827346801479/50000000000000000000 : ℝ) ≤ (10000000039718853/10000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (50000000827346801479/50000000000000000000 : ℝ)^512 ≤ (10000000039718853/10000000000000000 : ℝ)^2133 := by
      have hnat : (50000000827346801479 : ℕ)^512*10000000000000000^2133 ≤ 10000000039718853^2133*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000827346801479 50000000000000000000 10000000039718853 10000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000039718853/10000000000000000 : ℝ)) (X := (50000000827346801479/50000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100435923554435219219/100000000000000000000 : ℝ) ≤ (10010446511938697/10000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (100435923554435219219/100000000000000000000 : ℝ)^512 ≤ (10010446511938697/10000000000000000 : ℝ)^2133 := by
      have hnat : (100435923554435219219 : ℕ)^512*10000000000000000^2133 ≤ 10010446511938697^2133*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100435923554435219219 100000000000000000000 10010446511938697 10000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010446511938697/10000000000000000 : ℝ)) (X := (100435923554435219219/100000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2521796136354420887/2500000000000000000 : ℝ) ≤ (10020892984158541/10000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (2521796136354420887/2500000000000000000 : ℝ)^512 ≤ (10020892984158541/10000000000000000 : ℝ)^2133 := by
      have hnat : (2521796136354420887 : ℕ)^512*10000000000000000^2133 ≤ 10020892984158541^2133*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2521796136354420887 2500000000000000000 10020892984158541 10000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10020892984158541/10000000000000000 : ℝ)) (X := (2521796136354420887/2500000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(827346801479/100000000000000000000 : ℝ) ≤ ((37106573704508554651/37110000000000000000 : ℝ)+2*(2611618054961/649425000000000 : ℝ)*(287/25000 : ℝ))^(2133/512 : ℝ) := by
    rw [show (37106573704508554651/37110000000000000000 : ℝ)+2*(2611618054961/649425000000000 : ℝ)*(287/25000 : ℝ)=(10000000039718853/10000000000000000 : ℝ) by norm_num, show 1+2*(827346801479/100000000000000000000 : ℝ)=(50000000827346801479/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21796136354420887/5000000000000000000 : ℝ)+(827346801479/100000000000000000000 : ℝ) ≤ ((37106573704508554651/37110000000000000000 : ℝ)+(2611618054961/649425000000000 : ℝ)*((217/800 : ℝ)+(287/25000 : ℝ)))^(2133/512 : ℝ) := by
    rw [show (37106573704508554651/37110000000000000000 : ℝ)+(2611618054961/649425000000000 : ℝ)*((217/800 : ℝ)+(287/25000 : ℝ))=(10010446511938697/10000000000000000 : ℝ) by norm_num, show 1+(21796136354420887/5000000000000000000 : ℝ)+(827346801479/100000000000000000000 : ℝ)=(100435923554435219219/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21796136354420887/5000000000000000000 : ℝ) ≤ ((37106573704508554651/37110000000000000000 : ℝ)+2*(2611618054961/649425000000000 : ℝ)*(217/800 : ℝ))^(2133/512 : ℝ) := by
    rw [show (37106573704508554651/37110000000000000000 : ℝ)+2*(2611618054961/649425000000000 : ℝ)*(217/800 : ℝ)=(10020892984158541/10000000000000000 : ℝ) by norm_num, show 1+2*(21796136354420887/5000000000000000000 : ℝ)=(2521796136354420887/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37106573704508554651/37110000000000000000 : ℝ)*(X 1 0+X 2 0)+(2611618054961/649425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (287/25000 : ℝ)) (hi := (217/800 : ℝ)) (c := (37106573704508554651/37110000000000000000 : ℝ)) (alpha := (2611618054961/649425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37106573704508554651/37110000000000000000 : ℝ)*(X 0 1+X 2 1)+(2611618054961/649425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (287/25000 : ℝ)) (hi := (217/800 : ℝ)) (c := (37106573704508554651/37110000000000000000 : ℝ)) (alpha := (2611618054961/649425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37106573704508554651/37110000000000000000 : ℝ)*(X 0 2+X 1 2)+(2611618054961/649425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (287/25000 : ℝ)) (hi := (217/800 : ℝ)) (c := (37106573704508554651/37110000000000000000 : ℝ)) (alpha := (2611618054961/649425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-403978907/2000000000 : ℝ)*X 0 0+(5658199667/10000000000 : ℝ)*X 0 1+(157340391/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5409394131/10000000000 : ℝ)*X 1 0+(-2353525441/10000000000 : ℝ)*X 1 1+(5034892713/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1352348603/2500000000 : ℝ)*X 2 0+(2517446129/5000000000 : ℝ)*X 2 1+(-470705131/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4298507269/10000000000 : ℝ)*X 0 0+(1849869611/5000000000 : ℝ)*X 0 1+(99762593/200000000 : ℝ)*X 0 2+(4298507269/10000000000 : ℝ)*X 1 0+(1849869611/5000000000 : ℝ)*X 1 1+(99762593/200000000 : ℝ)*X 1 2+(4298507269/10000000000 : ℝ)*X 2 0+(1849869611/5000000000 : ℝ)*X 2 1+(99762593/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1010249879/5000000000 : ℝ)*X 0 0+(630365823/1250000000 : ℝ)*X 0 1+(1130003053/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((328008699/625000000 : ℝ)*X 1 0+(-1738401979/10000000000 : ℝ)*X 1 1+(5650016063/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5248139107/10000000000 : ℝ)*X 2 0+(113000313/200000000 : ℝ)*X 2 1+(-1738402687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2149878627/5000000000 : ℝ)*X 0 0+(4971523577/10000000000 : ℝ)*X 0 1+(3716655857/10000000000 : ℝ)*X 0 2+(2149878627/5000000000 : ℝ)*X 1 0+(4971523577/10000000000 : ℝ)*X 1 1+(3716655857/10000000000 : ℝ)*X 1 2+(2149878627/5000000000 : ℝ)*X 2 0+(4971523577/10000000000 : ℝ)*X 2 1+(3716655857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61285112484276110062827/6185000000000000000000000000 : ℝ) := by norm_num
    linear_combination (106425313/100000000000000 : ℝ)*(base1) + (359583963/20000000000000 : ℝ)*(base19) + (1881261163/100000000000000 : ℝ)*(base23) + (51578081/20000000000000 : ℝ)*(upper3) + (194305557/100000000000000 : ℝ)*(upper5) + (1190269006559227/100000000000000 : ℝ)*(major0) + (1190269006559227/100000000000000 : ℝ)*(major1) + (1190269006559227/100000000000000 : ℝ)*(major2) + (1604355679402421/100000000000000 : ℝ)*(sp0) + (2566981996837/160000000000 : ℝ)*(sp1) + (802181832340889/50000000000000 : ℝ)*(sp2) + (155233375666909/20000000000000 : ℝ)*(sp3) + (9972965831/100000000000000 : ℝ)*(sp4) + (5152126713/100000000000000 : ℝ)*(sp7) + (776172136886569/100000000000000 : ℝ)*(f.failure) + (80218277297147/5000000000000 : ℝ)*(f.sum) + (41034288387743/9277500000000000000000000000 : ℝ)*base66 + (4098935669494738259/1237000000000000000000000000000000 : ℝ)*base67 + (765650397277261741/1237000000000000000000000000000000 : ℝ)*base70 + (2772885794965261741/1237000000000000000000000000000000 : ℝ)*base72 + (19486531025273/9277500000000000000000000000 : ℝ)*base74 + (4656112737876738259/1237000000000000000000000000000000 : ℝ)*base75 + (1625706640877738259/1237000000000000000000000000000000 : ℝ)*base77 + (1283411661786261741/1237000000000000000000000000000000 : ℝ)*base80 + (96050829266971/18555000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (1970921/2500000000000000000000 : ℝ)*base90 + (1970921/2500000000000000000000 : ℝ)*base92 + (1970921/2500000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2808700744715923206459603341/309250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1715523889/100000000000000 : ℝ)*(base19) + (1695464281/100000000000000 : ℝ)*(base23) + (10006793/50000000000000 : ℝ)*(upper2) + (27902713/10000000000000 : ℝ)*(upper3) + (94195893/50000000000000 : ℝ)*(upper5) + (611025452415191/50000000000000 : ℝ)*(major0) + (611025452415191/50000000000000 : ℝ)*(major1) + (611025452415191/50000000000000 : ℝ)*(major2) + (608282389/6250000000000 : ℝ)*(sp1) + (4312539809/50000000000000 : ℝ)*(sp2) + (823602227554373/50000000000000 : ℝ)*(sp4) + (1647193007066633/100000000000000 : ℝ)*(sp5) + (823597067282423/50000000000000 : ℝ)*(sp6) + (398448525904369/50000000000000 : ℝ)*(sp7) + (398448525904369/50000000000000 : ℝ)*(f.failure) + (823602227554373/50000000000000 : ℝ)*(f.sum) + (16197213476071/16235625000000000000000000000 : ℝ)*base65 + (2333405150293958871/4329500000000000000000000000000000 : ℝ)*base68 + (11059801030740958871/4329500000000000000000000000000000 : ℝ)*base70 + (11912669720644958871/4329500000000000000000000000000000 : ℝ)*base72 + (310116513368933/129885000000000000000000000000 : ℝ)*base73 + (19647883392120458871/4329500000000000000000000000000000 : ℝ)*base76 + (26698086973256041129/4329500000000000000000000000000000 : ℝ)*base77 + (578903682146041129/4329500000000000000000000000000000 : ℝ)*base79 + (26736916155041/64942500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (9708879/1250000000000000000000 : ℝ)*base89 + (9708879/1250000000000000000000 : ℝ)*base91 + (9708879/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1307_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (217/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (287/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1639/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19731/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1307_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1307_s2_0 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-515796443/2500000000 : ℝ)*x 0 + (548973141/1000000000 : ℝ)*x 1 + (1035137139/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (515796443/2500000000 : ℝ)^4267 ≤ (1253426881791/10000000000000 : ℝ)^3243 := by
    have hnat : (515796443 : ℕ)^4267*10000000000000^3243 ≤ 1253426881791^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515796443 2500000000 1253426881791 10000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548973141/1000000000 : ℝ)^4267 ≤ (22713420059617/50000000000000 : ℝ)^3243 := by
    have hnat : (548973141 : ℕ)^4267*50000000000000^3243 ≤ 22713420059617^3243*1000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548973141 1000000000 22713420059617 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035137139/2000000000 : ℝ)^4267 ≤ (8407778211233/20000000000000 : ℝ)^3243 := by
    have hnat : (1035137139 : ℕ)^4267*20000000000000^3243 ≤ 8407778211233^3243*2000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035137139 2000000000 8407778211233 20000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-515796443/2500000000 : ℝ), (548973141/1000000000 : ℝ), (1035137139/2000000000 : ℝ)] ![(1253426881791/10000000000000 : ℝ), (22713420059617/50000000000000 : ℝ), (8407778211233/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-515796443/2500000000 : ℝ)|^4267 ≤ (1253426881791/10000000000000 : ℝ)^3243
        have hw : |(-515796443/2500000000 : ℝ)|=(515796443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548973141/1000000000 : ℝ)|^4267 ≤ (22713420059617/50000000000000 : ℝ)^3243
        have hw : |(548973141/1000000000 : ℝ)|=(548973141/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035137139/2000000000 : ℝ)|^4267 ≤ (8407778211233/20000000000000 : ℝ)^3243
        have hw : |(1035137139/2000000000 : ℝ)|=(1035137139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s2_1 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368472967/10000000000 : ℝ)*x 0 + (-2225782421/10000000000 : ℝ)*x 1 + (1293921349/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368472967/10000000000 : ℝ)^4267 ≤ (44111238978273/100000000000000 : ℝ)^3243 := by
    have hnat : (5368472967 : ℕ)^4267*100000000000000^3243 ≤ 44111238978273^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368472967 10000000000 44111238978273 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2225782421/10000000000 : ℝ)^4267 ≤ (13849873147631/100000000000000 : ℝ)^3243 := by
    have hnat : (2225782421 : ℕ)^4267*100000000000000^3243 ≤ 13849873147631^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2225782421 10000000000 13849873147631 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293921349/2500000000 : ℝ)^4267 ≤ (42038887860729/100000000000000 : ℝ)^3243 := by
    have hnat : (1293921349 : ℕ)^4267*100000000000000^3243 ≤ 42038887860729^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293921349 2500000000 42038887860729 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368472967/10000000000 : ℝ), (-2225782421/10000000000 : ℝ), (1293921349/2500000000 : ℝ)] ![(44111238978273/100000000000000 : ℝ), (13849873147631/100000000000000 : ℝ), (42038887860729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368472967/10000000000 : ℝ)|^4267 ≤ (44111238978273/100000000000000 : ℝ)^3243
        have hw : |(5368472967/10000000000 : ℝ)|=(5368472967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2225782421/10000000000 : ℝ)|^4267 ≤ (13849873147631/100000000000000 : ℝ)^3243
        have hw : |(-2225782421/10000000000 : ℝ)|=(2225782421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1293921349/2500000000 : ℝ)|^4267 ≤ (42038887860729/100000000000000 : ℝ)^3243
        have hw : |(1293921349/2500000000 : ℝ)|=(1293921349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s2_2 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073694507/2000000000 : ℝ)*x 0 + (207027431/400000000 : ℝ)*x 1 + (-2225782497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073694507/2000000000 : ℝ)^4267 ≤ (5513904288479/12500000000000 : ℝ)^3243 := by
    have hnat : (1073694507 : ℕ)^4267*12500000000000^3243 ≤ 5513904288479^3243*2000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073694507 2000000000 5513904288479 12500000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207027431/400000000 : ℝ)^4267 ≤ (10509722977783/25000000000000 : ℝ)^3243 := by
    have hnat : (207027431 : ℕ)^4267*25000000000000^3243 ≤ 10509722977783^3243*400000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207027431 400000000 10509722977783 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2225782497/10000000000 : ℝ)^4267 ≤ (13849873769863/100000000000000 : ℝ)^3243 := by
    have hnat : (2225782497 : ℕ)^4267*100000000000000^3243 ≤ 13849873769863^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2225782497 10000000000 13849873769863 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073694507/2000000000 : ℝ), (207027431/400000000 : ℝ), (-2225782497/10000000000 : ℝ)] ![(5513904288479/12500000000000 : ℝ), (10509722977783/25000000000000 : ℝ), (13849873769863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073694507/2000000000 : ℝ)|^4267 ≤ (5513904288479/12500000000000 : ℝ)^3243
        have hw : |(1073694507/2000000000 : ℝ)|=(1073694507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207027431/400000000 : ℝ)|^4267 ≤ (10509722977783/25000000000000 : ℝ)^3243
        have hw : |(207027431/400000000 : ℝ)|=(207027431/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2225782497/10000000000 : ℝ)|^4267 ≤ (13849873769863/100000000000000 : ℝ)^3243
        have hw : |(-2225782497/10000000000 : ℝ)|=(2225782497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s2_3 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4328656929/10000000000 : ℝ)*x 0 + (4015599973/10000000000 : ℝ)*x 1 + (2332373919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328656929/10000000000 : ℝ)^4267 ≤ (4153738398111/12500000000000 : ℝ)^3243 := by
    have hnat : (4328656929 : ℕ)^4267*12500000000000^3243 ≤ 4153738398111^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328656929 10000000000 4153738398111 12500000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4015599973/10000000000 : ℝ)^4267 ≤ (3010453096321/10000000000000 : ℝ)^3243 := by
    have hnat : (4015599973 : ℕ)^4267*10000000000000^3243 ≤ 3010453096321^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4015599973 10000000000 3010453096321 10000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2332373919/5000000000 : ℝ)^4267 ≤ (4583195229759/12500000000000 : ℝ)^3243 := by
    have hnat : (2332373919 : ℕ)^4267*12500000000000^3243 ≤ 4583195229759^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2332373919 5000000000 4583195229759 12500000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328656929/10000000000 : ℝ), (4015599973/10000000000 : ℝ), (2332373919/5000000000 : ℝ)] ![(4153738398111/12500000000000 : ℝ), (3010453096321/10000000000000 : ℝ), (4583195229759/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328656929/10000000000 : ℝ)|^4267 ≤ (4153738398111/12500000000000 : ℝ)^3243
        have hw : |(4328656929/10000000000 : ℝ)|=(4328656929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4015599973/10000000000 : ℝ)|^4267 ≤ (3010453096321/10000000000000 : ℝ)^3243
        have hw : |(4015599973/10000000000 : ℝ)|=(4015599973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2332373919/5000000000 : ℝ)|^4267 ≤ (4583195229759/12500000000000 : ℝ)^3243
        have hw : |(2332373919/5000000000 : ℝ)|=(2332373919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s2_4 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2063262631/10000000000 : ℝ)*x 0 + (5177734367/10000000000 : ℝ)*x 1 + (1097532763/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2063262631/10000000000 : ℝ)^4267 ≤ (12534883193071/100000000000000 : ℝ)^3243 := by
    have hnat : (2063262631 : ℕ)^4267*100000000000000^3243 ≤ 12534883193071^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063262631 10000000000 12534883193071 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177734367/10000000000 : ℝ)^4267 ≤ (4206078674533/10000000000000 : ℝ)^3243 := by
    have hnat : (5177734367 : ℕ)^4267*10000000000000^3243 ≤ 4206078674533^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177734367 10000000000 4206078674533 10000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097532763/2000000000 : ℝ)^4267 ≤ (45404330053031/100000000000000 : ℝ)^3243 := by
    have hnat : (1097532763 : ℕ)^4267*100000000000000^3243 ≤ 45404330053031^3243*2000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097532763 2000000000 45404330053031 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2063262631/10000000000 : ℝ), (5177734367/10000000000 : ℝ), (1097532763/2000000000 : ℝ)] ![(12534883193071/100000000000000 : ℝ), (4206078674533/10000000000000 : ℝ), (45404330053031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2063262631/10000000000 : ℝ)|^4267 ≤ (12534883193071/100000000000000 : ℝ)^3243
        have hw : |(-2063262631/10000000000 : ℝ)|=(2063262631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177734367/10000000000 : ℝ)|^4267 ≤ (4206078674533/10000000000000 : ℝ)^3243
        have hw : |(5177734367/10000000000 : ℝ)|=(5177734367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1097532763/2000000000 : ℝ)|^4267 ≤ (45404330053031/100000000000000 : ℝ)^3243
        have hw : |(1097532763/2000000000 : ℝ)|=(1097532763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s2_5 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643921389/5000000000 : ℝ)*x 0 + (-191380349/1000000000 : ℝ)*x 1 + (5487663917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643921389/5000000000 : ℝ)^4267 ≤ (43241603452451/100000000000000 : ℝ)^3243 := by
    have hnat : (2643921389 : ℕ)^4267*100000000000000^3243 ≤ 43241603452451^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643921389 5000000000 43241603452451 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (191380349/1000000000 : ℝ)^4267 ≤ (11354065374031/100000000000000 : ℝ)^3243 := by
    have hnat : (191380349 : ℕ)^4267*100000000000000^3243 ≤ 11354065374031^3243*1000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191380349 1000000000 11354065374031 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5487663917/10000000000 : ℝ)^4267 ≤ (45404331163447/100000000000000 : ℝ)^3243 := by
    have hnat : (5487663917 : ℕ)^4267*100000000000000^3243 ≤ 45404331163447^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487663917 10000000000 45404331163447 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643921389/5000000000 : ℝ), (-191380349/1000000000 : ℝ), (5487663917/10000000000 : ℝ)] ![(43241603452451/100000000000000 : ℝ), (11354065374031/100000000000000 : ℝ), (45404331163447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643921389/5000000000 : ℝ)|^4267 ≤ (43241603452451/100000000000000 : ℝ)^3243
        have hw : |(2643921389/5000000000 : ℝ)|=(2643921389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-191380349/1000000000 : ℝ)|^4267 ≤ (11354065374031/100000000000000 : ℝ)^3243
        have hw : |(-191380349/1000000000 : ℝ)|=(191380349/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5487663917/10000000000 : ℝ)|^4267 ≤ (45404331163447/100000000000000 : ℝ)^3243
        have hw : |(5487663917/10000000000 : ℝ)|=(5487663917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s2_6 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1321960727/2500000000 : ℝ)*x 0 + (2743831911/5000000000 : ℝ)*x 1 + (-1913803443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321960727/2500000000 : ℝ)^4267 ≤ (5405200606401/12500000000000 : ℝ)^3243 := by
    have hnat : (1321960727 : ℕ)^4267*12500000000000^3243 ≤ 5405200606401^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321960727 2500000000 5405200606401 12500000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2743831911/5000000000 : ℝ)^4267 ≤ (11351082532309/25000000000000 : ℝ)^3243 := by
    have hnat : (2743831911 : ℕ)^4267*25000000000000^3243 ≤ 11351082532309^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743831911 5000000000 11351082532309 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1913803443/10000000000 : ℝ)^4267 ≤ (2838516251787/25000000000000 : ℝ)^3243 := by
    have hnat : (1913803443 : ℕ)^4267*25000000000000^3243 ≤ 2838516251787^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913803443 10000000000 2838516251787 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321960727/2500000000 : ℝ), (2743831911/5000000000 : ℝ), (-1913803443/10000000000 : ℝ)] ![(5405200606401/12500000000000 : ℝ), (11351082532309/25000000000000 : ℝ), (2838516251787/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321960727/2500000000 : ℝ)|^4267 ≤ (5405200606401/12500000000000 : ℝ)^3243
        have hw : |(1321960727/2500000000 : ℝ)|=(1321960727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2743831911/5000000000 : ℝ)|^4267 ≤ (11351082532309/25000000000000 : ℝ)^3243
        have hw : |(2743831911/5000000000 : ℝ)|=(2743831911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1913803443/10000000000 : ℝ)|^4267 ≤ (2838516251787/25000000000000 : ℝ)^3243
        have hw : |(-1913803443/10000000000 : ℝ)|=(1913803443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s2_7 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1082203683/2500000000 : ℝ)*x 0 + (4660511187/10000000000 : ℝ)*x 1 + (2009939477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082203683/2500000000 : ℝ)^4267 ≤ (4153937639437/12500000000000 : ℝ)^3243 := by
    have hnat : (1082203683 : ℕ)^4267*12500000000000^3243 ≤ 4153937639437^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082203683 2500000000 4153937639437 12500000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4660511187/10000000000 : ℝ)^4267 ≤ (9155438135739/25000000000000 : ℝ)^3243 := by
    have hnat : (4660511187 : ℕ)^4267*25000000000000^3243 ≤ 9155438135739^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4660511187 10000000000 9155438135739 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2009939477/5000000000 : ℝ)^4267 ≤ (15073373162417/50000000000000 : ℝ)^3243 := by
    have hnat : (2009939477 : ℕ)^4267*50000000000000^3243 ≤ 15073373162417^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009939477 5000000000 15073373162417 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082203683/2500000000 : ℝ), (4660511187/10000000000 : ℝ), (2009939477/5000000000 : ℝ)] ![(4153937639437/12500000000000 : ℝ), (9155438135739/25000000000000 : ℝ), (15073373162417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082203683/2500000000 : ℝ)|^4267 ≤ (4153937639437/12500000000000 : ℝ)^3243
        have hw : |(1082203683/2500000000 : ℝ)|=(1082203683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4660511187/10000000000 : ℝ)|^4267 ≤ (9155438135739/25000000000000 : ℝ)^3243
        have hw : |(4660511187/10000000000 : ℝ)|=(4660511187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2009939477/5000000000 : ℝ)|^4267 ≤ (15073373162417/50000000000000 : ℝ)^3243
        have hw : |(2009939477/5000000000 : ℝ)|=(2009939477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1307_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1639/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (9613/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13/80 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19731/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1639/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19731/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1639/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19731/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1639/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19731/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1639/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19731/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1639/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19731/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1639/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1639/25000 : ℝ) ^ (2133/512 : ℝ) ≤ (235033273877273/20000000000000000000 : ℝ) := by
    have hpowers : (1639/25000 : ℝ)^2133 ≤ (235033273877273/20000000000000000000 : ℝ)^512 := by
      have hnat : (1639 : ℕ)^2133*20000000000000000000^512 ≤ 235033273877273^512*25000^2133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1639 25000 235033273877273 20000000000000000000 2133 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1639/25000 : ℝ)) (X := (235033273877273/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hpowhi : (19731/100000 : ℝ) ^ (2133/512 : ℝ) ≤ (23153151776194983/20000000000000000000 : ℝ) := by
    have hpowers : (19731/100000 : ℝ)^2133 ≤ (23153151776194983/20000000000000000000 : ℝ)^512 := by
      have hnat : (19731 : ℕ)^2133*20000000000000000000^512 ≤ 23153151776194983^512*100000^2133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19731 100000 23153151776194983 20000000000000000000 2133 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19731/100000 : ℝ)) (X := (23153151776194983/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000235033273877273/10000000000000000000 : ℝ) ≤ (2000011283259403/2000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (10000235033273877273/10000000000000000000 : ℝ)^512 ≤ (2000011283259403/2000000000000000 : ℝ)^2133 := by
      have hnat : (10000235033273877273 : ℕ)^512*2000000000000000^2133 ≤ 2000011283259403^2133*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000235033273877273 10000000000000000000 2000011283259403 2000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000011283259403/2000000000000000 : ℝ)) (X := (10000235033273877273/10000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (312865440391407379/312500000000000000 : ℝ) ≤ (10002805774348263/10000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (312865440391407379/312500000000000000 : ℝ)^512 ≤ (10002805774348263/10000000000000000 : ℝ)^2133 := by
      have hnat : (312865440391407379 : ℕ)^512*10000000000000000^2133 ≤ 10002805774348263^2133*312500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312865440391407379 312500000000000000 10002805774348263 10000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002805774348263/10000000000000000 : ℝ)) (X := (312865440391407379/312500000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10023153151776194983/10000000000000000000 : ℝ) ≤ (10005555132399511/10000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (10023153151776194983/10000000000000000000 : ℝ)^512 ≤ (10005555132399511/10000000000000000 : ℝ)^2133 := by
      have hnat : (10023153151776194983 : ℕ)^512*10000000000000000^2133 ≤ 10005555132399511^2133*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10023153151776194983 10000000000000000000 10005555132399511 10000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005555132399511/10000000000000000 : ℝ)) (X := (10023153151776194983/10000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(235033273877273/20000000000000000000 : ℝ) ≤ ((131714693701945208849/131750000000000000000 : ℝ)+2*(171834878203/82343750000000 : ℝ)*(1639/25000 : ℝ))^(2133/512 : ℝ) := by
    rw [show (131714693701945208849/131750000000000000000 : ℝ)+2*(171834878203/82343750000000 : ℝ)*(1639/25000 : ℝ)=(2000011283259403/2000000000000000 : ℝ) by norm_num, show 1+2*(235033273877273/20000000000000000000 : ℝ)=(10000235033273877273/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23153151776194983/20000000000000000000 : ℝ)+(235033273877273/20000000000000000000 : ℝ) ≤ ((131714693701945208849/131750000000000000000 : ℝ)+(171834878203/82343750000000 : ℝ)*((19731/100000 : ℝ)+(1639/25000 : ℝ)))^(2133/512 : ℝ) := by
    rw [show (131714693701945208849/131750000000000000000 : ℝ)+(171834878203/82343750000000 : ℝ)*((19731/100000 : ℝ)+(1639/25000 : ℝ))=(10002805774348263/10000000000000000 : ℝ) by norm_num, show 1+(23153151776194983/20000000000000000000 : ℝ)+(235033273877273/20000000000000000000 : ℝ)=(312865440391407379/312500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23153151776194983/20000000000000000000 : ℝ) ≤ ((131714693701945208849/131750000000000000000 : ℝ)+2*(171834878203/82343750000000 : ℝ)*(19731/100000 : ℝ))^(2133/512 : ℝ) := by
    rw [show (131714693701945208849/131750000000000000000 : ℝ)+2*(171834878203/82343750000000 : ℝ)*(19731/100000 : ℝ)=(10005555132399511/10000000000000000 : ℝ) by norm_num, show 1+2*(23153151776194983/20000000000000000000 : ℝ)=(10023153151776194983/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (131714693701945208849/131750000000000000000 : ℝ)*(X 1 0+X 2 0)+(171834878203/82343750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (1639/25000 : ℝ)) (hi := (19731/100000 : ℝ)) (c := (131714693701945208849/131750000000000000000 : ℝ)) (alpha := (171834878203/82343750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (131714693701945208849/131750000000000000000 : ℝ)*(X 0 1+X 2 1)+(171834878203/82343750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (1639/25000 : ℝ)) (hi := (19731/100000 : ℝ)) (c := (131714693701945208849/131750000000000000000 : ℝ)) (alpha := (171834878203/82343750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (131714693701945208849/131750000000000000000 : ℝ)*(X 0 2+X 1 2)+(171834878203/82343750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (1639/25000 : ℝ)) (hi := (19731/100000 : ℝ)) (c := (131714693701945208849/131750000000000000000 : ℝ)) (alpha := (171834878203/82343750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-515796443/2500000000 : ℝ)*X 0 0+(548973141/1000000000 : ℝ)*X 0 1+(1035137139/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5368472967/10000000000 : ℝ)*X 1 0+(-2225782421/10000000000 : ℝ)*X 1 1+(1293921349/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1073694507/2000000000 : ℝ)*X 2 0+(207027431/400000000 : ℝ)*X 2 1+(-2225782497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4328656929/10000000000 : ℝ)*X 0 0+(4015599973/10000000000 : ℝ)*X 0 1+(2332373919/5000000000 : ℝ)*X 0 2+(4328656929/10000000000 : ℝ)*X 1 0+(4015599973/10000000000 : ℝ)*X 1 1+(2332373919/5000000000 : ℝ)*X 1 2+(4328656929/10000000000 : ℝ)*X 2 0+(4015599973/10000000000 : ℝ)*X 2 1+(2332373919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2063262631/10000000000 : ℝ)*X 0 0+(5177734367/10000000000 : ℝ)*X 0 1+(1097532763/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643921389/5000000000 : ℝ)*X 1 0+(-191380349/1000000000 : ℝ)*X 1 1+(5487663917/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1321960727/2500000000 : ℝ)*X 2 0+(2743831911/5000000000 : ℝ)*X 2 1+(-1913803443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1082203683/2500000000 : ℝ)*X 0 0+(4660511187/10000000000 : ℝ)*X 0 1+(2009939477/5000000000 : ℝ)*X 0 2+(1082203683/2500000000 : ℝ)*X 1 0+(4660511187/10000000000 : ℝ)*X 1 1+(2009939477/5000000000 : ℝ)*X 1 2+(1082203683/2500000000 : ℝ)*X 2 0+(4660511187/10000000000 : ℝ)*X 2 1+(2009939477/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19314037396169984284076707473/6587500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (776607971/50000000000000 : ℝ)*(base19) + (889538489/100000000000000 : ℝ)*(base23) + (218733359/100000000000000 : ℝ)*(lower2) + (582417451/100000000000000 : ℝ)*(upper3) + (27513709/20000000000000 : ℝ)*(upper5) + (2362384249620341/100000000000000 : ℝ)*(major0) + (2362384249620341/100000000000000 : ℝ)*(major1) + (2362384249620341/100000000000000 : ℝ)*(major2) + (3184259864080021/100000000000000 : ℝ)*(sp0) + (3184260608888901/100000000000000 : ℝ)*(sp1) + (1592130636283177/50000000000000 : ℝ)*(sp2) + (770245728670303/50000000000000 : ℝ)*(sp3) + (1149012411/50000000000000 : ℝ)*(sp4) + (1478206449/10000000000000 : ℝ)*(sp7) + (192563279925637/12500000000000 : ℝ)*(f.failure) + (3184262162104843/100000000000000 : ℝ)*(f.sum) + (7535312731527/4117187500000000000000000000 : ℝ)*base66 + (46745036513160397509/13175000000000000000000000000000000 : ℝ)*base67 + (61458580575514602491/13175000000000000000000000000000000 : ℝ)*base70 + (3766943201585397509/13175000000000000000000000000000000 : ℝ)*base71 + (123389476226943/65875000000000000000000000000 : ℝ)*base73 + (43862708404060397509/13175000000000000000000000000000000 : ℝ)*base75 + (68553900818939602491/13175000000000000000000000000000000 : ℝ)*base78 + (86061910168610397509/13175000000000000000000000000000000 : ℝ)*base79 + (121684905222841/32937500000000000000000000000 : ℝ)*base82 + (1222867/312500000000000000000 : ℝ)*base89 + (1222867/312500000000000000000 : ℝ)*base91 + (1222867/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (113129389584925707199895811/26562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (851447221/100000000000000 : ℝ)*(base19) + (221766141/20000000000000 : ℝ)*(base23) + (142527463/100000000000000 : ℝ)*(upper3) + (31913641/50000000000000 : ℝ)*(lower4) + (31684193/100000000000000 : ℝ)*(upper5) + (299218578374003/12500000000000 : ℝ)*(major0) + (299218578374003/12500000000000 : ℝ)*(major1) + (299218578374003/12500000000000 : ℝ)*(major2) + (8801401711/100000000000000 : ℝ)*(sp1) + (12562868923/100000000000000 : ℝ)*(sp2) + (806634555567113/25000000000000 : ℝ)*(sp4) + (3226528569419519/100000000000000 : ℝ)*(sp5) + (403315568821103/12500000000000 : ℝ)*(sp6) + (1560958889749297/100000000000000 : ℝ)*(sp7) + (1560958889749297/100000000000000 : ℝ)*(f.failure) + (806634555567113/25000000000000 : ℝ)*(f.sum) + (527273898887/132812500000000000000000000 : ℝ)*base65 + (378819397129405563/53125000000000000000000000000000 : ℝ)*base68 + (56535499698719437/53125000000000000000000000000000 : ℝ)*base69 + (27068056816905563/53125000000000000000000000000000 : ℝ)*base72 + (1600075496529/1062500000000000000000000000 : ℝ)*base74 + (441827531939344437/53125000000000000000000000000000 : ℝ)*base75 + (286179914710655563/53125000000000000000000000000000 : ℝ)*base78 + (77402266107530563/53125000000000000000000000000000 : ℝ)*base80 + (8712914193317/2125000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (9217073/2500000000000000000000 : ℝ)*base90 + (9217073/2500000000000000000000 : ℝ)*base92 + (9217073/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1307_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1639/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9613/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13/80 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1307_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1307_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9613/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13/80 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1307_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1307_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1307_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9613/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13/80 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1307_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1440_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:56:41.427784+00:00
-- url     : https://prove2.me/submissions/58e12962-d19b-4bcf-b8a8-b318fe5e5de1

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
theorem support_rectangle_w1440_s0_0 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1752602859/10000000000 : ℝ)*x 0 + (744456839/1250000000 : ℝ)*x 1 + (4833747103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1752602859/10000000000 : ℝ)^275 ≤ (10334261902831/100000000000000 : ℝ)^211 := by
    have hnat : (1752602859 : ℕ)^275*100000000000000^211 ≤ 10334261902831^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1752602859 10000000000 10334261902831 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (744456839/1250000000 : ℝ)^275 ≤ (50893425712873/100000000000000 : ℝ)^211 := by
    have hnat : (744456839 : ℕ)^275*100000000000000^211 ≤ 50893425712873^211*1250000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744456839 1250000000 50893425712873 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4833747103/10000000000 : ℝ)^275 ≤ (19386156182817/50000000000000 : ℝ)^211 := by
    have hnat : (4833747103 : ℕ)^275*50000000000000^211 ≤ 19386156182817^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4833747103 10000000000 19386156182817 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1752602859/10000000000 : ℝ), (744456839/1250000000 : ℝ), (4833747103/10000000000 : ℝ)] ![(10334261902831/100000000000000 : ℝ), (50893425712873/100000000000000 : ℝ), (19386156182817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1752602859/10000000000 : ℝ)|^275 ≤ (10334261902831/100000000000000 : ℝ)^211
        have hw : |(-1752602859/10000000000 : ℝ)|=(1752602859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(744456839/1250000000 : ℝ)|^275 ≤ (50893425712873/100000000000000 : ℝ)^211
        have hw : |(744456839/1250000000 : ℝ)|=(744456839/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4833747103/10000000000 : ℝ)|^275 ≤ (19386156182817/50000000000000 : ℝ)^211
        have hw : |(4833747103/10000000000 : ℝ)|=(4833747103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s0_1 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (109817531/200000000 : ℝ)*x 0 + (-149117707/625000000 : ℝ)*x 1 + (4833747283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109817531/200000000 : ℝ)^275 ≤ (11444858939919/25000000000000 : ℝ)^211 := by
    have hnat : (109817531 : ℕ)^275*25000000000000^211 ≤ 11444858939919^211*200000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109817531 200000000 11444858939919 25000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149117707/625000000 : ℝ)^275 ≤ (7724124989909/50000000000000 : ℝ)^211 := by
    have hnat : (149117707 : ℕ)^275*50000000000000^211 ≤ 7724124989909^211*625000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149117707 625000000 7724124989909 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4833747283/10000000000 : ℝ)^275 ≤ (19386157123689/50000000000000 : ℝ)^211 := by
    have hnat : (4833747283 : ℕ)^275*50000000000000^211 ≤ 19386157123689^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4833747283 10000000000 19386157123689 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(109817531/200000000 : ℝ), (-149117707/625000000 : ℝ), (4833747283/10000000000 : ℝ)] ![(11444858939919/25000000000000 : ℝ), (7724124989909/50000000000000 : ℝ), (19386157123689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(109817531/200000000 : ℝ)|^275 ≤ (11444858939919/25000000000000 : ℝ)^211
        have hw : |(109817531/200000000 : ℝ)|=(109817531/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-149117707/625000000 : ℝ)|^275 ≤ (7724124989909/50000000000000 : ℝ)^211
        have hw : |(-149117707/625000000 : ℝ)|=(149117707/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4833747283/10000000000 : ℝ)|^275 ≤ (19386157123689/50000000000000 : ℝ)^211
        have hw : |(4833747283/10000000000 : ℝ)|=(4833747283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s0_2 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (343179793/625000000 : ℝ)*x 0 + (4833747283/10000000000 : ℝ)*x 1 + (-1192941567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343179793/625000000 : ℝ)^275 ≤ (2861214828701/6250000000000 : ℝ)^211 := by
    have hnat : (343179793 : ℕ)^275*6250000000000^211 ≤ 2861214828701^211*625000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343179793 625000000 2861214828701 6250000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4833747283/10000000000 : ℝ)^275 ≤ (19386157123689/50000000000000 : ℝ)^211 := by
    have hnat : (4833747283 : ℕ)^275*50000000000000^211 ≤ 19386157123689^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4833747283 10000000000 19386157123689 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1192941567/5000000000 : ℝ)^275 ≤ (15448248477713/100000000000000 : ℝ)^211 := by
    have hnat : (1192941567 : ℕ)^275*100000000000000^211 ≤ 15448248477713^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192941567 5000000000 15448248477713 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(343179793/625000000 : ℝ), (4833747283/10000000000 : ℝ), (-1192941567/5000000000 : ℝ)] ![(2861214828701/6250000000000 : ℝ), (19386157123689/50000000000000 : ℝ), (15448248477713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(343179793/625000000 : ℝ)|^275 ≤ (2861214828701/6250000000000 : ℝ)^211
        have hw : |(343179793/625000000 : ℝ)|=(343179793/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4833747283/10000000000 : ℝ)|^275 ≤ (19386157123689/50000000000000 : ℝ)^211
        have hw : |(4833747283/10000000000 : ℝ)|=(4833747283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1192941567/5000000000 : ℝ)|^275 ≤ (15448248477713/100000000000000 : ℝ)^211
        have hw : |(-1192941567/5000000000 : ℝ)|=(1192941567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s0_3 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4164427073/10000000000 : ℝ)*x 0 + (1551551163/5000000000 : ℝ)*x 1 + (5539948273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4164427073/10000000000 : ℝ)^275 ≤ (31927116765021/100000000000000 : ℝ)^211 := by
    have hnat : (4164427073 : ℕ)^275*100000000000000^211 ≤ 31927116765021^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164427073 10000000000 31927116765021 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1551551163/5000000000 : ℝ)^275 ≤ (870380059467/4000000000000 : ℝ)^211 := by
    have hnat : (1551551163 : ℕ)^275*4000000000000^211 ≤ 870380059467^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1551551163 5000000000 870380059467 4000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5539948273/10000000000 : ℝ)^275 ≤ (46313381733873/100000000000000 : ℝ)^211 := by
    have hnat : (5539948273 : ℕ)^275*100000000000000^211 ≤ 46313381733873^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5539948273 10000000000 46313381733873 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4164427073/10000000000 : ℝ), (1551551163/5000000000 : ℝ), (5539948273/10000000000 : ℝ)] ![(31927116765021/100000000000000 : ℝ), (870380059467/4000000000000 : ℝ), (46313381733873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4164427073/10000000000 : ℝ)|^275 ≤ (31927116765021/100000000000000 : ℝ)^211
        have hw : |(4164427073/10000000000 : ℝ)|=(4164427073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1551551163/5000000000 : ℝ)|^275 ≤ (870380059467/4000000000000 : ℝ)^211
        have hw : |(1551551163/5000000000 : ℝ)|=(1551551163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5539948273/10000000000 : ℝ)|^275 ≤ (46313381733873/100000000000000 : ℝ)^211
        have hw : |(5539948273/10000000000 : ℝ)|=(5539948273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s0_4 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1756567371/10000000000 : ℝ)*x 0 + (4862427697/10000000000 : ℝ)*x 1 + (1481487581/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1756567371/10000000000 : ℝ)^275 ≤ (2591184946673/25000000000000 : ℝ)^211 := by
    have hnat : (1756567371 : ℕ)^275*25000000000000^211 ≤ 2591184946673^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1756567371 10000000000 2591184946673 25000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4862427697/10000000000 : ℝ)^275 ≤ (3907241253971/10000000000000 : ℝ)^211 := by
    have hnat : (4862427697 : ℕ)^275*10000000000000^211 ≤ 3907241253971^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4862427697 10000000000 3907241253971 10000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1481487581/2500000000 : ℝ)^275 ≤ (50562847665659/100000000000000 : ℝ)^211 := by
    have hnat : (1481487581 : ℕ)^275*100000000000000^211 ≤ 50562847665659^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1481487581 2500000000 50562847665659 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1756567371/10000000000 : ℝ), (4862427697/10000000000 : ℝ), (1481487581/2500000000 : ℝ)] ![(2591184946673/25000000000000 : ℝ), (3907241253971/10000000000000 : ℝ), (50562847665659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1756567371/10000000000 : ℝ)|^275 ≤ (2591184946673/25000000000000 : ℝ)^211
        have hw : |(-1756567371/10000000000 : ℝ)|=(1756567371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4862427697/10000000000 : ℝ)|^275 ≤ (3907241253971/10000000000000 : ℝ)^211
        have hw : |(4862427697/10000000000 : ℝ)|=(4862427697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1481487581/2500000000 : ℝ)|^275 ≤ (50562847665659/100000000000000 : ℝ)^211
        have hw : |(1481487581/2500000000 : ℝ)|=(1481487581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s0_5 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (518461501/1000000000 : ℝ)*x 0 + (-1293679791/10000000000 : ℝ)*x 1 + (5925950393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518461501/1000000000 : ℝ)^275 ≤ (42480050914131/100000000000000 : ℝ)^211 := by
    have hnat : (518461501 : ℕ)^275*100000000000000^211 ≤ 42480050914131^211*1000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518461501 1000000000 42480050914131 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1293679791/10000000000 : ℝ)^275 ≤ (6957100642043/100000000000000 : ℝ)^211 := by
    have hnat : (1293679791 : ℕ)^275*100000000000000^211 ≤ 6957100642043^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293679791 10000000000 6957100642043 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5925950393/10000000000 : ℝ)^275 ≤ (12640712108243/25000000000000 : ℝ)^211 := by
    have hnat : (5925950393 : ℕ)^275*25000000000000^211 ≤ 12640712108243^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5925950393 10000000000 12640712108243 25000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518461501/1000000000 : ℝ), (-1293679791/10000000000 : ℝ), (5925950393/10000000000 : ℝ)] ![(42480050914131/100000000000000 : ℝ), (6957100642043/100000000000000 : ℝ), (12640712108243/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518461501/1000000000 : ℝ)|^275 ≤ (42480050914131/100000000000000 : ℝ)^211
        have hw : |(518461501/1000000000 : ℝ)|=(518461501/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1293679791/10000000000 : ℝ)|^275 ≤ (6957100642043/100000000000000 : ℝ)^211
        have hw : |(-1293679791/10000000000 : ℝ)|=(1293679791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5925950393/10000000000 : ℝ)|^275 ≤ (12640712108243/25000000000000 : ℝ)^211
        have hw : |(5925950393/10000000000 : ℝ)|=(5925950393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s0_6 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5184615037/10000000000 : ℝ)*x 0 + (2962975119/5000000000 : ℝ)*x 1 + (-323419999/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5184615037/10000000000 : ℝ)^275 ≤ (5310006400307/12500000000000 : ℝ)^211 := by
    have hnat : (5184615037 : ℕ)^275*12500000000000^211 ≤ 5310006400307^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184615037 10000000000 5310006400307 12500000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2962975119/5000000000 : ℝ)^275 ≤ (50562846709297/100000000000000 : ℝ)^211 := by
    have hnat : (2962975119 : ℕ)^275*100000000000000^211 ≤ 50562846709297^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2962975119 5000000000 50562846709297 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323419999/2500000000 : ℝ)^275 ≤ (3478551039437/50000000000000 : ℝ)^211 := by
    have hnat : (323419999 : ℕ)^275*50000000000000^211 ≤ 3478551039437^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323419999 2500000000 3478551039437 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5184615037/10000000000 : ℝ), (2962975119/5000000000 : ℝ), (-323419999/2500000000 : ℝ)] ![(5310006400307/12500000000000 : ℝ), (50562846709297/100000000000000 : ℝ), (3478551039437/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5184615037/10000000000 : ℝ)|^275 ≤ (5310006400307/12500000000000 : ℝ)^211
        have hw : |(5184615037/10000000000 : ℝ)|=(5184615037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2962975119/5000000000 : ℝ)|^275 ≤ (50562846709297/100000000000000 : ℝ)^211
        have hw : |(2962975119/5000000000 : ℝ)|=(2962975119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-323419999/2500000000 : ℝ)|^275 ≤ (3478551039437/50000000000000 : ℝ)^211
        have hw : |(-323419999/2500000000 : ℝ)|=(323419999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s0_7 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2086519911/5000000000 : ℝ)*x 0 + (2738826367/5000000000 : ℝ)*x 1 + (791905467/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086519911/5000000000 : ℝ)^275 ≤ (16006601389701/50000000000000 : ℝ)^211 := by
    have hnat : (2086519911 : ℕ)^275*50000000000000^211 ≤ 16006601389701^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086519911 5000000000 16006601389701 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738826367/5000000000 : ℝ)^275 ≤ (1825431808497/4000000000000 : ℝ)^211 := by
    have hnat : (2738826367 : ℕ)^275*4000000000000^211 ≤ 1825431808497^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738826367 5000000000 1825431808497 4000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (791905467/2500000000 : ℝ)^275 ≤ (11175500997919/50000000000000 : ℝ)^211 := by
    have hnat : (791905467 : ℕ)^275*50000000000000^211 ≤ 11175500997919^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      791905467 2500000000 11175500997919 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2086519911/5000000000 : ℝ), (2738826367/5000000000 : ℝ), (791905467/2500000000 : ℝ)] ![(16006601389701/50000000000000 : ℝ), (1825431808497/4000000000000 : ℝ), (11175500997919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2086519911/5000000000 : ℝ)|^275 ≤ (16006601389701/50000000000000 : ℝ)^211
        have hw : |(2086519911/5000000000 : ℝ)|=(2086519911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738826367/5000000000 : ℝ)|^275 ≤ (1825431808497/4000000000000 : ℝ)^211
        have hw : |(2738826367/5000000000 : ℝ)|=(2738826367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(791905467/2500000000 : ℝ)|^275 ≤ (11175500997919/50000000000000 : ℝ)^211
        have hw : |(791905467/2500000000 : ℝ)|=(791905467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1440_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (17/800 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13091/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4399/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4399 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4399*1^1024 ≤ 0^1024*1^4399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4399/1024 : ℝ) ≤ (78081856346213921/4000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4399 ≤ (78081856346213921/4000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4399*4000000000000000000^1024 ≤ 78081856346213921^1024*5^4399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 78081856346213921 4000000000000000000 4399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (78081856346213921/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4399 := by
      have hnat : (1 : ℕ)^1024*1^4399 ≤ 1^4399*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4078081856346213921/4000000000000000000 : ℝ) ≤ (10045103367461813/10000000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (4078081856346213921/4000000000000000000 : ℝ)^1024 ≤ (10045103367461813/10000000000000000 : ℝ)^4399 := by
      have hnat : (4078081856346213921 : ℕ)^1024*10000000000000000^4399 ≤ 10045103367461813^4399*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4078081856346213921 4000000000000000000 10045103367461813 10000000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10045103367461813/10000000000000000 : ℝ)) (X := (4078081856346213921/4000000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2078081856346213921/2000000000000000000 : ℝ) ≤ (5045103367461813/5000000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (2078081856346213921/2000000000000000000 : ℝ)^1024 ≤ (5045103367461813/5000000000000000 : ℝ)^4399 := by
      have hnat : (2078081856346213921 : ℕ)^1024*5000000000000000^4399 ≤ 5045103367461813^4399*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2078081856346213921 2000000000000000000 5045103367461813 5000000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5045103367461813/5000000000000000 : ℝ)) (X := (2078081856346213921/2000000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(45103367461813/4000000000000000 : ℝ)*(0 : ℝ))^(4399/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(45103367461813/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(78081856346213921/4000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(45103367461813/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4399/1024 : ℝ) := by
    rw [show (1 : ℝ)+(45103367461813/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10045103367461813/10000000000000000 : ℝ) by norm_num, show 1+(78081856346213921/4000000000000000000 : ℝ)+(0 : ℝ)=(4078081856346213921/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(78081856346213921/4000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(45103367461813/4000000000000000 : ℝ)*(2/5 : ℝ))^(4399/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(45103367461813/4000000000000000 : ℝ)*(2/5 : ℝ)=(5045103367461813/5000000000000000 : ℝ) by norm_num, show 1+2*(78081856346213921/4000000000000000000 : ℝ)=(2078081856346213921/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(45103367461813/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45103367461813/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(45103367461813/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45103367461813/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(45103367461813/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45103367461813/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1752602859/10000000000 : ℝ)*X 0 0+(744456839/1250000000 : ℝ)*X 0 1+(4833747103/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((109817531/200000000 : ℝ)*X 1 0+(-149117707/625000000 : ℝ)*X 1 1+(4833747283/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((343179793/625000000 : ℝ)*X 2 0+(4833747283/10000000000 : ℝ)*X 2 1+(-1192941567/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4164427073/10000000000 : ℝ)*X 0 0+(1551551163/5000000000 : ℝ)*X 0 1+(5539948273/10000000000 : ℝ)*X 0 2+(4164427073/10000000000 : ℝ)*X 1 0+(1551551163/5000000000 : ℝ)*X 1 1+(5539948273/10000000000 : ℝ)*X 1 2+(4164427073/10000000000 : ℝ)*X 2 0+(1551551163/5000000000 : ℝ)*X 2 1+(5539948273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1756567371/10000000000 : ℝ)*X 0 0+(4862427697/10000000000 : ℝ)*X 0 1+(1481487581/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((518461501/1000000000 : ℝ)*X 1 0+(-1293679791/10000000000 : ℝ)*X 1 1+(5925950393/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5184615037/10000000000 : ℝ)*X 2 0+(2962975119/5000000000 : ℝ)*X 2 1+(-323419999/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2086519911/5000000000 : ℝ)*X 0 0+(2738826367/5000000000 : ℝ)*X 0 1+(791905467/2500000000 : ℝ)*X 0 2+(2086519911/5000000000 : ℝ)*X 1 0+(2738826367/5000000000 : ℝ)*X 1 1+(791905467/2500000000 : ℝ)*X 1 2+(2086519911/5000000000 : ℝ)*X 2 0+(2738826367/5000000000 : ℝ)*X 2 1+(791905467/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (503522961062332673856279/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37850693/3125000000000 : ℝ)*(base19) + (75484867/6250000000000 : ℝ)*(base23) + (149045069/100000000000000 : ℝ)*(upper3) + (2840557/20000000000000 : ℝ)*(upper4) + (180596383/100000000000000 : ℝ)*(upper5) + (650859035975561/100000000000000 : ℝ)*(major0) + (650859035975561/100000000000000 : ℝ)*(major1) + (650859035975561/100000000000000 : ℝ)*(major2) + (445671486959621/50000000000000 : ℝ)*(sp0) + (445673137097107/50000000000000 : ℝ)*(sp1) + (445673138829259/50000000000000 : ℝ)*(sp2) + (205184226970039/50000000000000 : ℝ)*(sp3) + (4511497147/100000000000000 : ℝ)*(sp4) + (7674819/390625000000 : ℝ)*(sp7) + (205185209346871/50000000000000 : ℝ)*(f.failure) + (89134748541639/10000000000000 : ℝ)*(f.sum) + (83452348647907/200000000000000000000000000000 : ℝ)*base66 + (2140159841952093/400000000000000000000000000000 : ℝ)*base67 + (1077078388752093/400000000000000000000000000000 : ℝ)*base69 + (1321346387952093/400000000000000000000000000000 : ℝ)*base71 + (449801538447907/200000000000000000000000000000 : ℝ)*base74 + (672377214447907/400000000000000000000000000000 : ℝ)*base76 + (556327714352093/400000000000000000000000000000 : ℝ)*base77 + (159943290447907/400000000000000000000000000000 : ℝ)*base80 + (379899978047907/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (408373/1000000000000000000000 : ℝ)*base89 + (408373/1000000000000000000000 : ℝ)*base91 + (408373/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (552374644582004493/200000000000000000000000 : ℝ) := by norm_num
    linear_combination (314904867/50000000000000 : ℝ)*(base19) + (635177041/100000000000000 : ℝ)*(base23) + (95306219/100000000000000 : ℝ)*(base32) + (99372373/100000000000000 : ℝ)*(upper3) + (1401797/3125000000000 : ℝ)*(upper5) + (17164570905299/2500000000000 : ℝ)*(major0) + (17164570905299/2500000000000 : ℝ)*(major1) + (17164570905299/2500000000000 : ℝ)*(major2) + (1498833929/100000000000000 : ℝ)*(sp1) + (1506800807/100000000000000 : ℝ)*(sp2) + (235067774309747/25000000000000 : ℝ)*(sp4) + (470134484297663/50000000000000 : ℝ)*(sp5) + (940268955261141/100000000000000 : ℝ)*(sp6) + (86578877563253/20000000000000 : ℝ)*(sp7) + (108223620780621/25000000000000 : ℝ)*(f.failure) + (235067774309747/25000000000000 : ℝ)*(f.sum) + (9746999562913/5000000000000000000000000000 : ℝ)*base66 + (107561530387087/10000000000000000000000000000 : ℝ)*base67 + (2784070527087/10000000000000000000000000000 : ℝ)*base69 + (1523091447087/10000000000000000000000000000 : ℝ)*base71 + (21509377867087/5000000000000000000000000000 : ℝ)*base73 + (20171888602913/10000000000000000000000000000 : ℝ)*base76 + (25319529217087/10000000000000000000000000000 : ℝ)*base77 + (4839552642913/10000000000000000000000000000 : ℝ)*base80 + (29941570382913/5000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2390377/500000000000000000000 : ℝ)*base90 + (2390377/500000000000000000000 : ℝ)*base92 + (2390377/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1440_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (17/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13091/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1440_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1440_s1_0 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1923404213/10000000000 : ℝ)*x 0 + (5600843363/10000000000 : ℝ)*x 1 + (1269760619/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1923404213/10000000000 : ℝ)^275 ≤ (2333171195727/20000000000000 : ℝ)^211 := by
    have hnat : (1923404213 : ℕ)^275*20000000000000^211 ≤ 2333171195727^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923404213 10000000000 2333171195727 20000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5600843363/10000000000 : ℝ)^275 ≤ (46977973326583/100000000000000 : ℝ)^211 := by
    have hnat : (5600843363 : ℕ)^275*100000000000000^211 ≤ 46977973326583^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5600843363 10000000000 46977973326583 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1269760619/2500000000 : ℝ)^275 ≤ (20678085344201/50000000000000 : ℝ)^211 := by
    have hnat : (1269760619 : ℕ)^275*50000000000000^211 ≤ 20678085344201^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269760619 2500000000 20678085344201 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1923404213/10000000000 : ℝ), (5600843363/10000000000 : ℝ), (1269760619/2500000000 : ℝ)] ![(2333171195727/20000000000000 : ℝ), (46977973326583/100000000000000 : ℝ), (20678085344201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1923404213/10000000000 : ℝ)|^275 ≤ (2333171195727/20000000000000 : ℝ)^211
        have hw : |(-1923404213/10000000000 : ℝ)|=(1923404213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5600843363/10000000000 : ℝ)|^275 ≤ (46977973326583/100000000000000 : ℝ)^211
        have hw : |(5600843363/10000000000 : ℝ)|=(5600843363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1269760619/2500000000 : ℝ)|^275 ≤ (20678085344201/50000000000000 : ℝ)^211
        have hw : |(1269760619/2500000000 : ℝ)|=(1269760619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s1_1 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2697853733/5000000000 : ℝ)*x 0 + (-137479331/625000000 : ℝ)*x 1 + (634880497/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697853733/5000000000 : ℝ)^275 ≤ (22374017840357/50000000000000 : ℝ)^211 := by
    have hnat : (2697853733 : ℕ)^275*50000000000000^211 ≤ 22374017840357^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697853733 5000000000 22374017840357 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137479331/625000000 : ℝ)^275 ≤ (13895777702457/100000000000000 : ℝ)^211 := by
    have hnat : (137479331 : ℕ)^275*100000000000000^211 ≤ 13895777702457^211*625000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137479331 625000000 13895777702457 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (634880497/1250000000 : ℝ)^275 ≤ (41356186606823/100000000000000 : ℝ)^211 := by
    have hnat : (634880497 : ℕ)^275*100000000000000^211 ≤ 41356186606823^211*1250000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634880497 1250000000 41356186606823 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697853733/5000000000 : ℝ), (-137479331/625000000 : ℝ), (634880497/1250000000 : ℝ)] ![(22374017840357/50000000000000 : ℝ), (13895777702457/100000000000000 : ℝ), (41356186606823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697853733/5000000000 : ℝ)|^275 ≤ (22374017840357/50000000000000 : ℝ)^211
        have hw : |(2697853733/5000000000 : ℝ)|=(2697853733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-137479331/625000000 : ℝ)|^275 ≤ (13895777702457/100000000000000 : ℝ)^211
        have hw : |(-137479331/625000000 : ℝ)|=(137479331/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(634880497/1250000000 : ℝ)|^275 ≤ (41356186606823/100000000000000 : ℝ)^211
        have hw : |(634880497/1250000000 : ℝ)|=(634880497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s1_2 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5395708679/10000000000 : ℝ)*x 0 + (1269760651/2500000000 : ℝ)*x 1 + (-2199669471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395708679/10000000000 : ℝ)^275 ≤ (44748048791739/100000000000000 : ℝ)^211 := by
    have hnat : (5395708679 : ℕ)^275*100000000000000^211 ≤ 44748048791739^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395708679 10000000000 44748048791739 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1269760651/2500000000 : ℝ)^275 ≤ (20678086023387/50000000000000 : ℝ)^211 := by
    have hnat : (1269760651 : ℕ)^275*50000000000000^211 ≤ 20678086023387^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269760651 2500000000 20678086023387 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2199669471/10000000000 : ℝ)^275 ≤ (13895779143291/100000000000000 : ℝ)^211 := by
    have hnat : (2199669471 : ℕ)^275*100000000000000^211 ≤ 13895779143291^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199669471 10000000000 13895779143291 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395708679/10000000000 : ℝ), (1269760651/2500000000 : ℝ), (-2199669471/10000000000 : ℝ)] ![(44748048791739/100000000000000 : ℝ), (20678086023387/50000000000000 : ℝ), (13895779143291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395708679/10000000000 : ℝ)|^275 ≤ (44748048791739/100000000000000 : ℝ)^211
        have hw : |(5395708679/10000000000 : ℝ)|=(5395708679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1269760651/2500000000 : ℝ)|^275 ≤ (20678086023387/50000000000000 : ℝ)^211
        have hw : |(1269760651/2500000000 : ℝ)|=(1269760651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2199669471/10000000000 : ℝ)|^275 ≤ (13895779143291/100000000000000 : ℝ)^211
        have hw : |(-2199669471/10000000000 : ℝ)|=(2199669471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s1_3 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2137319247/5000000000 : ℝ)*x 0 + (3741326463/10000000000 : ℝ)*x 1 + (2437351999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2137319247/5000000000 : ℝ)^275 ≤ (3303274810979/10000000000000 : ℝ)^211 := by
    have hnat : (2137319247 : ℕ)^275*10000000000000^211 ≤ 3303274810979^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137319247 5000000000 3303274810979 10000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3741326463/10000000000 : ℝ)^275 ≤ (27766221561087/100000000000000 : ℝ)^211 := by
    have hnat : (3741326463 : ℕ)^275*100000000000000^211 ≤ 27766221561087^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3741326463 10000000000 27766221561087 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2437351999/5000000000 : ℝ)^275 ≤ (39201030316637/100000000000000 : ℝ)^211 := by
    have hnat : (2437351999 : ℕ)^275*100000000000000^211 ≤ 39201030316637^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2437351999 5000000000 39201030316637 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2137319247/5000000000 : ℝ), (3741326463/10000000000 : ℝ), (2437351999/5000000000 : ℝ)] ![(3303274810979/10000000000000 : ℝ), (27766221561087/100000000000000 : ℝ), (39201030316637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2137319247/5000000000 : ℝ)|^275 ≤ (3303274810979/10000000000000 : ℝ)^211
        have hw : |(2137319247/5000000000 : ℝ)|=(2137319247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3741326463/10000000000 : ℝ)|^275 ≤ (27766221561087/100000000000000 : ℝ)^211
        have hw : |(3741326463/10000000000 : ℝ)|=(3741326463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2437351999/5000000000 : ℝ)|^275 ≤ (39201030316637/100000000000000 : ℝ)^211
        have hw : |(2437351999/5000000000 : ℝ)|=(2437351999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s1_4 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-961893761/5000000000 : ℝ)*x 0 + (635638573/1250000000 : ℝ)*x 1 + (5594675269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (961893761/5000000000 : ℝ)^275 ≤ (2333777217773/20000000000000 : ℝ)^211 := by
    have hnat : (961893761 : ℕ)^275*20000000000000^211 ≤ 2333777217773^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961893761 5000000000 2333777217773 20000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (635638573/1250000000 : ℝ)^275 ≤ (5177569698011/12500000000000 : ℝ)^211 := by
    have hnat : (635638573 : ℕ)^275*12500000000000^211 ≤ 5177569698011^211*1250000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635638573 1250000000 5177569698011 12500000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5594675269/10000000000 : ℝ)^275 ≤ (1876422252509/4000000000000 : ℝ)^211 := by
    have hnat : (5594675269 : ℕ)^275*4000000000000^211 ≤ 1876422252509^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5594675269 10000000000 1876422252509 4000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-961893761/5000000000 : ℝ), (635638573/1250000000 : ℝ), (5594675269/10000000000 : ℝ)] ![(2333777217773/20000000000000 : ℝ), (5177569698011/12500000000000 : ℝ), (1876422252509/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-961893761/5000000000 : ℝ)|^275 ≤ (2333777217773/20000000000000 : ℝ)^211
        have hw : |(-961893761/5000000000 : ℝ)|=(961893761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(635638573/1250000000 : ℝ)|^275 ≤ (5177569698011/12500000000000 : ℝ)^211
        have hw : |(635638573/1250000000 : ℝ)|=(635638573/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5594675269/10000000000 : ℝ)|^275 ≤ (1876422252509/4000000000000 : ℝ)^211
        have hw : |(5594675269/10000000000 : ℝ)|=(5594675269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s1_5 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5259265229/10000000000 : ℝ)*x 0 + (-1684037503/10000000000 : ℝ)*x 1 + (5594675293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5259265229/10000000000 : ℝ)^275 ≤ (21639476915393/50000000000000 : ℝ)^211 := by
    have hnat : (5259265229 : ℕ)^275*50000000000000^211 ≤ 21639476915393^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259265229 10000000000 21639476915393 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1684037503/10000000000 : ℝ)^275 ≤ (7848391667/80000000000 : ℝ)^211 := by
    have hnat : (1684037503 : ℕ)^275*80000000000^211 ≤ 7848391667^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1684037503 10000000000 7848391667 80000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5594675293/10000000000 : ℝ)^275 ≤ (1876422263/4000000000 : ℝ)^211 := by
    have hnat : (5594675293 : ℕ)^275*4000000000^211 ≤ 1876422263^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5594675293 10000000000 1876422263 4000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5259265229/10000000000 : ℝ), (-1684037503/10000000000 : ℝ), (5594675293/10000000000 : ℝ)] ![(21639476915393/50000000000000 : ℝ), (7848391667/80000000000 : ℝ), (1876422263/4000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5259265229/10000000000 : ℝ)|^275 ≤ (21639476915393/50000000000000 : ℝ)^211
        have hw : |(5259265229/10000000000 : ℝ)|=(5259265229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1684037503/10000000000 : ℝ)|^275 ≤ (7848391667/80000000000 : ℝ)^211
        have hw : |(-1684037503/10000000000 : ℝ)|=(1684037503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5594675293/10000000000 : ℝ)|^275 ≤ (1876422263/4000000000 : ℝ)^211
        have hw : |(5594675293/10000000000 : ℝ)|=(5594675293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s1_6 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1314816289/2500000000 : ℝ)*x 0 + (5594675253/10000000000 : ℝ)*x 1 + (-52626177/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314816289/2500000000 : ℝ)^275 ≤ (43278953047853/100000000000000 : ℝ)^211 := by
    have hnat : (1314816289 : ℕ)^275*100000000000000^211 ≤ 43278953047853^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314816289 2500000000 43278953047853 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5594675253/10000000000 : ℝ)^275 ≤ (23455278068937/50000000000000 : ℝ)^211 := by
    have hnat : (5594675253 : ℕ)^275*50000000000000^211 ≤ 23455278068937^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5594675253 10000000000 23455278068937 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52626177/312500000 : ℝ)^275 ≤ (1962098161231/20000000000000 : ℝ)^211 := by
    have hnat : (52626177 : ℕ)^275*20000000000000^211 ≤ 1962098161231^211*312500000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52626177 312500000 1962098161231 20000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314816289/2500000000 : ℝ), (5594675253/10000000000 : ℝ), (-52626177/312500000 : ℝ)] ![(43278953047853/100000000000000 : ℝ), (23455278068937/50000000000000 : ℝ), (1962098161231/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314816289/2500000000 : ℝ)|^275 ≤ (43278953047853/100000000000000 : ℝ)^211
        have hw : |(1314816289/2500000000 : ℝ)|=(1314816289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5594675253/10000000000 : ℝ)|^275 ≤ (23455278068937/50000000000000 : ℝ)^211
        have hw : |(5594675253/10000000000 : ℝ)|=(5594675253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-52626177/312500000 : ℝ)|^275 ≤ (1962098161231/20000000000000 : ℝ)^211
        have hw : |(-52626177/312500000 : ℝ)|=(52626177/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s1_7 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (267216971/625000000 : ℝ)*x 0 + (4861529419/10000000000 : ℝ)*x 1 + (150188861/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267216971/625000000 : ℝ)^275 ≤ (8260284591799/25000000000000 : ℝ)^211 := by
    have hnat : (267216971 : ℕ)^275*25000000000000^211 ≤ 8260284591799^211*625000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267216971 625000000 8260284591799 25000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4861529419/10000000000 : ℝ)^275 ≤ (39063005219983/100000000000000 : ℝ)^211 := by
    have hnat : (4861529419 : ℕ)^275*100000000000000^211 ≤ 39063005219983^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4861529419 10000000000 39063005219983 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (150188861/400000000 : ℝ)^275 ≤ (27895856390561/100000000000000 : ℝ)^211 := by
    have hnat : (150188861 : ℕ)^275*100000000000000^211 ≤ 27895856390561^211*400000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150188861 400000000 27895856390561 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267216971/625000000 : ℝ), (4861529419/10000000000 : ℝ), (150188861/400000000 : ℝ)] ![(8260284591799/25000000000000 : ℝ), (39063005219983/100000000000000 : ℝ), (27895856390561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267216971/625000000 : ℝ)|^275 ≤ (8260284591799/25000000000000 : ℝ)^211
        have hw : |(267216971/625000000 : ℝ)|=(267216971/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4861529419/10000000000 : ℝ)|^275 ≤ (39063005219983/100000000000000 : ℝ)^211
        have hw : |(4861529419/10000000000 : ℝ)|=(4861529419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(150188861/400000000 : ℝ)|^275 ≤ (27895856390561/100000000000000 : ℝ)^211
        have hw : |(150188861/400000000 : ℝ)|=(150188861/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1440_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13091/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (17/800 : ℝ)*pair X i i ≤ pair X i h) :
    (3871/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9387/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13091/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (17/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13091/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (17/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13091/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (17/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13091/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (17/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13091/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (17/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13091/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (17/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (17/800 : ℝ) ^ (4399/1024 : ℝ) ≤ (3261924194761/50000000000000000000 : ℝ) := by
    have hpowers : (17/800 : ℝ)^4399 ≤ (3261924194761/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17 : ℕ)^4399*50000000000000000000^1024 ≤ 3261924194761^1024*800^4399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17 800 3261924194761 50000000000000000000 4399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17/800 : ℝ)) (X := (3261924194761/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13091/50000 : ℝ) ^ (4399/1024 : ℝ) ≤ (316081601746040431/100000000000000000000 : ℝ) := by
    have hpowers : (13091/50000 : ℝ)^4399 ≤ (316081601746040431/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13091 : ℕ)^4399*100000000000000000000^1024 ≤ 316081601746040431^1024*50000^4399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13091 50000 316081601746040431 100000000000000000000 4399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13091/50000 : ℝ)) (X := (316081601746040431/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000003261924194761/25000000000000000000 : ℝ) ≤ (5000000151862251/5000000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (25000003261924194761/25000000000000000000 : ℝ)^1024 ≤ (5000000151862251/5000000000000000 : ℝ)^4399 := by
      have hnat : (25000003261924194761 : ℕ)^1024*5000000000000000^4399 ≤ 5000000151862251^4399*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000003261924194761 25000000000000000000 5000000151862251 5000000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000151862251/5000000000000000 : ℝ)) (X := (25000003261924194761/25000000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100316088125594429953/100000000000000000000 : ℝ) ≤ (5003674499887303/5000000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (100316088125594429953/100000000000000000000 : ℝ)^1024 ≤ (5003674499887303/5000000000000000 : ℝ)^4399 := by
      have hnat : (100316088125594429953 : ℕ)^1024*5000000000000000^4399 ≤ 5003674499887303^4399*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100316088125594429953 100000000000000000000 5003674499887303 5000000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003674499887303/5000000000000000 : ℝ)) (X := (100316088125594429953/100000000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50316081601746040431/50000000000000000000 : ℝ) ≤ (1001469769582471/1000000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (50316081601746040431/50000000000000000000 : ℝ)^1024 ≤ (1001469769582471/1000000000000000 : ℝ)^4399 := by
      have hnat : (50316081601746040431 : ℕ)^1024*1000000000000000^4399 ≤ 1001469769582471^4399*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50316081601746040431 50000000000000000000 1001469769582471 1000000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001469769582471/1000000000000000 : ℝ)) (X := (50316081601746040431/50000000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3261924194761/50000000000000000000 : ℝ) ≤ ((120269387674243701307/120285000000000000000 : ℝ)+2*(918587006263/300712500000000 : ℝ)*(17/800 : ℝ))^(4399/1024 : ℝ) := by
    rw [show (120269387674243701307/120285000000000000000 : ℝ)+2*(918587006263/300712500000000 : ℝ)*(17/800 : ℝ)=(5000000151862251/5000000000000000 : ℝ) by norm_num, show 1+2*(3261924194761/50000000000000000000 : ℝ)=(25000003261924194761/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(316081601746040431/100000000000000000000 : ℝ)+(3261924194761/50000000000000000000 : ℝ) ≤ ((120269387674243701307/120285000000000000000 : ℝ)+(918587006263/300712500000000 : ℝ)*((13091/50000 : ℝ)+(17/800 : ℝ)))^(4399/1024 : ℝ) := by
    rw [show (120269387674243701307/120285000000000000000 : ℝ)+(918587006263/300712500000000 : ℝ)*((13091/50000 : ℝ)+(17/800 : ℝ))=(5003674499887303/5000000000000000 : ℝ) by norm_num, show 1+(316081601746040431/100000000000000000000 : ℝ)+(3261924194761/50000000000000000000 : ℝ)=(100316088125594429953/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(316081601746040431/100000000000000000000 : ℝ) ≤ ((120269387674243701307/120285000000000000000 : ℝ)+2*(918587006263/300712500000000 : ℝ)*(13091/50000 : ℝ))^(4399/1024 : ℝ) := by
    rw [show (120269387674243701307/120285000000000000000 : ℝ)+2*(918587006263/300712500000000 : ℝ)*(13091/50000 : ℝ)=(1001469769582471/1000000000000000 : ℝ) by norm_num, show 1+2*(316081601746040431/100000000000000000000 : ℝ)=(50316081601746040431/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (120269387674243701307/120285000000000000000 : ℝ)*(X 1 0+X 2 0)+(918587006263/300712500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (17/800 : ℝ)) (hi := (13091/50000 : ℝ)) (c := (120269387674243701307/120285000000000000000 : ℝ)) (alpha := (918587006263/300712500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (120269387674243701307/120285000000000000000 : ℝ)*(X 0 1+X 2 1)+(918587006263/300712500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (17/800 : ℝ)) (hi := (13091/50000 : ℝ)) (c := (120269387674243701307/120285000000000000000 : ℝ)) (alpha := (918587006263/300712500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (120269387674243701307/120285000000000000000 : ℝ)*(X 0 2+X 1 2)+(918587006263/300712500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (17/800 : ℝ)) (hi := (13091/50000 : ℝ)) (c := (120269387674243701307/120285000000000000000 : ℝ)) (alpha := (918587006263/300712500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1923404213/10000000000 : ℝ)*X 0 0+(5600843363/10000000000 : ℝ)*X 0 1+(1269760619/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2697853733/5000000000 : ℝ)*X 1 0+(-137479331/625000000 : ℝ)*X 1 1+(634880497/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5395708679/10000000000 : ℝ)*X 2 0+(1269760651/2500000000 : ℝ)*X 2 1+(-2199669471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2137319247/5000000000 : ℝ)*X 0 0+(3741326463/10000000000 : ℝ)*X 0 1+(2437351999/5000000000 : ℝ)*X 0 2+(2137319247/5000000000 : ℝ)*X 1 0+(3741326463/10000000000 : ℝ)*X 1 1+(2437351999/5000000000 : ℝ)*X 1 2+(2137319247/5000000000 : ℝ)*X 2 0+(3741326463/10000000000 : ℝ)*X 2 1+(2437351999/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-961893761/5000000000 : ℝ)*X 0 0+(635638573/1250000000 : ℝ)*X 0 1+(5594675269/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5259265229/10000000000 : ℝ)*X 1 0+(-1684037503/10000000000 : ℝ)*X 1 1+(5594675293/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1314816289/2500000000 : ℝ)*X 2 0+(5594675253/10000000000 : ℝ)*X 2 1+(-52626177/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((267216971/625000000 : ℝ)*X 0 0+(4861529419/10000000000 : ℝ)*X 0 1+(150188861/400000000 : ℝ)*X 0 2+(267216971/625000000 : ℝ)*X 1 0+(4861529419/10000000000 : ℝ)*X 1 1+(150188861/400000000 : ℝ)*X 1 2+(267216971/625000000 : ℝ)*X 2 0+(4861529419/10000000000 : ℝ)*X 2 1+(150188861/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (148117183639500668155034147/62648437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (5470947/2000000000000 : ℝ)*(base19) + (685365139/100000000000000 : ℝ)*(base23) + (3500727/25000000000000 : ℝ)*(upper2) + (24263967/100000000000000 : ℝ)*(upper4) + (56081/10000000000000 : ℝ)*(lower5) + (87461806330621/6250000000000 : ℝ)*(major0) + (87461806330621/6250000000000 : ℝ)*(major1) + (87461806330621/6250000000000 : ℝ)*(major2) + (1916446673100131/100000000000000 : ℝ)*(sp0) + (1916454585216741/100000000000000 : ℝ)*(sp1) + (239556771674869/12500000000000 : ℝ)*(sp2) + (441160207179217/50000000000000 : ℝ)*(sp3) + (204641599/2500000000000 : ℝ)*(sp4) + (1225324341/50000000000000 : ℝ)*(sp7) + (220580716251779/25000000000000 : ℝ)*(f.failure) + (191645485876409/10000000000000 : ℝ)*(f.sum) + (144872354199719/120285000000000000000000000000 : ℝ)*base65 + (1584120577993384603/751781250000000000000000000000000 : ℝ)*base68 + (3502546708319790853/751781250000000000000000000000000 : ℝ)*base70 + (118562943176084147/751781250000000000000000000000000 : ℝ)*base71 + (2008570279901/30071250000000000000000000000 : ℝ)*base73 + (1791216393924165853/751781250000000000000000000000000 : ℝ)*base76 + (2583350974505603353/751781250000000000000000000000000 : ℝ)*base78 + (3550583222226353353/751781250000000000000000000000000 : ℝ)*base80 + (31672200144097/60142500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (368423/500000000000000000000 : ℝ)*base90 + (368423/500000000000000000000 : ℝ)*base92 + (368423/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19706116223527880963790329029/2004750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20647373/25000000000000 : ℝ)*(base1) + (1027680111/50000000000000 : ℝ)*(base19) + (2017799983/100000000000000 : ℝ)*(base23) + (237586303/100000000000000 : ℝ)*(upper3) + (13047357/6250000000000 : ℝ)*(upper5) + (1432975392396847/100000000000000 : ℝ)*(major0) + (1432975392396847/100000000000000 : ℝ)*(major1) + (1432975392396847/100000000000000 : ℝ)*(major2) + (94903437/781250000000 : ℝ)*(sp1) + (2349940327/20000000000000 : ℝ)*(sp2) + (245306399520433/12500000000000 : ℝ)*(sp4) + (245304613821727/12500000000000 : ℝ)*(sp5) + (392487469214471/20000000000000 : ℝ)*(sp6) + (180699852194627/20000000000000 : ℝ)*(sp7) + (451749671781313/50000000000000 : ℝ)*(f.failure) + (1962451113573973/100000000000000 : ℝ)*(f.sum) + (17186409503279/15035625000000000000000000000 : ℝ)*base66 + (2409743289337520971/12028500000000000000000000000000000 : ℝ)*base68 + (44683408139887479029/12028500000000000000000000000000000 : ℝ)*base69 + (119382790346319020971/12028500000000000000000000000000000 : ℝ)*base72 + (240559317664703/120285000000000000000000000000 : ℝ)*base73 + (59526485637640520971/12028500000000000000000000000000000 : ℝ)*base76 + (26706391318288479029/12028500000000000000000000000000000 : ℝ)*base77 + (15229879518639020971/12028500000000000000000000000000000 : ℝ)*base80 + (157626045803569/60142500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (8760781/1000000000000000000000 : ℝ)*base90 + (8760781/1000000000000000000000 : ℝ)*base92 + (8760781/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1440_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13091/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (17/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3871/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9387/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1440_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1440_s2_0 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-977859809/5000000000 : ℝ)*x 0 + (5455740719/10000000000 : ℝ)*x 1 + (5203331943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (977859809/5000000000 : ℝ)^275 ≤ (11921954343799/100000000000000 : ℝ)^211 := by
    have hnat : (977859809 : ℕ)^275*100000000000000^211 ≤ 11921954343799^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977859809 5000000000 11921954343799 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5455740719/10000000000 : ℝ)^275 ≤ (45398012716513/100000000000000 : ℝ)^211 := by
    have hnat : (5455740719 : ℕ)^275*100000000000000^211 ≤ 45398012716513^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455740719 10000000000 45398012716513 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5203331943/10000000000 : ℝ)^275 ≤ (1707201317407/4000000000000 : ℝ)^211 := by
    have hnat : (5203331943 : ℕ)^275*4000000000000^211 ≤ 1707201317407^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203331943 10000000000 1707201317407 4000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-977859809/5000000000 : ℝ), (5455740719/10000000000 : ℝ), (5203331943/10000000000 : ℝ)] ![(11921954343799/100000000000000 : ℝ), (45398012716513/100000000000000 : ℝ), (1707201317407/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-977859809/5000000000 : ℝ)|^275 ≤ (11921954343799/100000000000000 : ℝ)^211
        have hw : |(-977859809/5000000000 : ℝ)|=(977859809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5455740719/10000000000 : ℝ)|^275 ≤ (45398012716513/100000000000000 : ℝ)^211
        have hw : |(5455740719/10000000000 : ℝ)|=(5455740719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5203331943/10000000000 : ℝ)|^275 ≤ (1707201317407/4000000000000 : ℝ)^211
        have hw : |(5203331943/10000000000 : ℝ)|=(5203331943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s2_1 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5359448983/10000000000 : ℝ)*x 0 + (-2085520769/10000000000 : ℝ)*x 1 + (5203331761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5359448983/10000000000 : ℝ)^275 ≤ (11089131630191/25000000000000 : ℝ)^211 := by
    have hnat : (5359448983 : ℕ)^275*25000000000000^211 ≤ 11089131630191^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359448983 10000000000 11089131630191 25000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085520769/10000000000 : ℝ)^275 ≤ (6481721238597/50000000000000 : ℝ)^211 := by
    have hnat : (2085520769 : ℕ)^275*50000000000000^211 ≤ 6481721238597^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085520769 10000000000 6481721238597 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5203331761/10000000000 : ℝ)^275 ≤ (10670007747381/25000000000000 : ℝ)^211 := by
    have hnat : (5203331761 : ℕ)^275*25000000000000^211 ≤ 10670007747381^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203331761 10000000000 10670007747381 25000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5359448983/10000000000 : ℝ), (-2085520769/10000000000 : ℝ), (5203331761/10000000000 : ℝ)] ![(11089131630191/25000000000000 : ℝ), (6481721238597/50000000000000 : ℝ), (10670007747381/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5359448983/10000000000 : ℝ)|^275 ≤ (11089131630191/25000000000000 : ℝ)^211
        have hw : |(5359448983/10000000000 : ℝ)|=(5359448983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2085520769/10000000000 : ℝ)|^275 ≤ (6481721238597/50000000000000 : ℝ)^211
        have hw : |(-2085520769/10000000000 : ℝ)|=(2085520769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5203331761/10000000000 : ℝ)|^275 ≤ (10670007747381/25000000000000 : ℝ)^211
        have hw : |(5203331761/10000000000 : ℝ)|=(5203331761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s2_2 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2679724253/5000000000 : ℝ)*x 0 + (2601666131/5000000000 : ℝ)*x 1 + (-2085520743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679724253/5000000000 : ℝ)^275 ≤ (277228258597/625000000000 : ℝ)^211 := by
    have hnat : (2679724253 : ℕ)^275*625000000000^211 ≤ 277228258597^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679724253 5000000000 277228258597 625000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2601666131/5000000000 : ℝ)^275 ≤ (666875567897/1562500000000 : ℝ)^211 := by
    have hnat : (2601666131 : ℕ)^275*1562500000000^211 ≤ 666875567897^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601666131 5000000000 666875567897 1562500000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085520743/10000000000 : ℝ)^275 ≤ (12963442266559/100000000000000 : ℝ)^211 := by
    have hnat : (2085520743 : ℕ)^275*100000000000000^211 ≤ 12963442266559^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085520743 10000000000 12963442266559 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679724253/5000000000 : ℝ), (2601666131/5000000000 : ℝ), (-2085520743/10000000000 : ℝ)] ![(277228258597/625000000000 : ℝ), (666875567897/1562500000000 : ℝ), (12963442266559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679724253/5000000000 : ℝ)|^275 ≤ (277228258597/625000000000 : ℝ)^211
        have hw : |(2679724253/5000000000 : ℝ)|=(2679724253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2601666131/5000000000 : ℝ)|^275 ≤ (666875567897/1562500000000 : ℝ)^211
        have hw : |(2601666131/5000000000 : ℝ)|=(2601666131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2085520743/10000000000 : ℝ)|^275 ≤ (12963442266559/100000000000000 : ℝ)^211
        have hw : |(-2085520743/10000000000 : ℝ)|=(2085520743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s2_3 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4297478489/10000000000 : ℝ)*x 0 + (1007791569/2500000000 : ℝ)*x 1 + (572426641/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297478489/10000000000 : ℝ)^275 ≤ (8315742007909/25000000000000 : ℝ)^211 := by
    have hnat : (4297478489 : ℕ)^275*25000000000000^211 ≤ 8315742007909^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297478489 10000000000 8315742007909 25000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007791569/2500000000 : ℝ)^275 ≤ (612041574617/2000000000000 : ℝ)^211 := by
    have hnat : (1007791569 : ℕ)^275*2000000000000^211 ≤ 612041574617^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007791569 2500000000 612041574617 2000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (572426641/1250000000 : ℝ)^275 ≤ (36134953218097/100000000000000 : ℝ)^211 := by
    have hnat : (572426641 : ℕ)^275*100000000000000^211 ≤ 36134953218097^211*1250000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572426641 1250000000 36134953218097 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297478489/10000000000 : ℝ), (1007791569/2500000000 : ℝ), (572426641/1250000000 : ℝ)] ![(8315742007909/25000000000000 : ℝ), (612041574617/2000000000000 : ℝ), (36134953218097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297478489/10000000000 : ℝ)|^275 ≤ (8315742007909/25000000000000 : ℝ)^211
        have hw : |(4297478489/10000000000 : ℝ)|=(4297478489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1007791569/2500000000 : ℝ)|^275 ≤ (612041574617/2000000000000 : ℝ)^211
        have hw : |(1007791569/2500000000 : ℝ)|=(1007791569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(572426641/1250000000 : ℝ)|^275 ≤ (36134953218097/100000000000000 : ℝ)^211
        have hw : |(572426641/1250000000 : ℝ)|=(572426641/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s2_4 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1955762969/10000000000 : ℝ)*x 0 + (81324383/156250000 : ℝ)*x 1 + (5454300653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1955762969/10000000000 : ℝ)^275 ≤ (11922298766431/100000000000000 : ℝ)^211 := by
    have hnat : (1955762969 : ℕ)^275*100000000000000^211 ≤ 11922298766431^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955762969 10000000000 11922298766431 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81324383/156250000 : ℝ)^275 ≤ (10673826381841/25000000000000 : ℝ)^211 := by
    have hnat : (81324383 : ℕ)^275*25000000000000^211 ≤ 10673826381841^211*156250000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81324383 156250000 10673826381841 25000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5454300653/10000000000 : ℝ)^275 ≤ (9076479137851/20000000000000 : ℝ)^211 := by
    have hnat : (5454300653 : ℕ)^275*20000000000000^211 ≤ 9076479137851^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454300653 10000000000 9076479137851 20000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1955762969/10000000000 : ℝ), (81324383/156250000 : ℝ), (5454300653/10000000000 : ℝ)] ![(11922298766431/100000000000000 : ℝ), (10673826381841/25000000000000 : ℝ), (9076479137851/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1955762969/10000000000 : ℝ)|^275 ≤ (11922298766431/100000000000000 : ℝ)^211
        have hw : |(-1955762969/10000000000 : ℝ)|=(1955762969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81324383/156250000 : ℝ)|^275 ≤ (10673826381841/25000000000000 : ℝ)^211
        have hw : |(81324383/156250000 : ℝ)|=(81324383/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5454300653/10000000000 : ℝ)|^275 ≤ (9076479137851/20000000000000 : ℝ)^211
        have hw : |(5454300653/10000000000 : ℝ)|=(5454300653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s2_5 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (33085917/62500000 : ℝ)*x 0 + (-917275563/5000000000 : ℝ)*x 1 + (2727150757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33085917/62500000 : ℝ)^275 ≤ (21824569457839/50000000000000 : ℝ)^211 := by
    have hnat : (33085917 : ℕ)^275*50000000000000^211 ≤ 21824569457839^211*62500000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33085917 62500000 21824569457839 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (917275563/5000000000 : ℝ)^275 ≤ (5484228022001/50000000000000 : ℝ)^211 := by
    have hnat : (917275563 : ℕ)^275*50000000000000^211 ≤ 5484228022001^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917275563 5000000000 5484228022001 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727150757/5000000000 : ℝ)^275 ≤ (22691202513067/50000000000000 : ℝ)^211 := by
    have hnat : (2727150757 : ℕ)^275*50000000000000^211 ≤ 22691202513067^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727150757 5000000000 22691202513067 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33085917/62500000 : ℝ), (-917275563/5000000000 : ℝ), (2727150757/5000000000 : ℝ)] ![(21824569457839/50000000000000 : ℝ), (5484228022001/50000000000000 : ℝ), (22691202513067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33085917/62500000 : ℝ)|^275 ≤ (21824569457839/50000000000000 : ℝ)^211
        have hw : |(33085917/62500000 : ℝ)|=(33085917/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-917275563/5000000000 : ℝ)|^275 ≤ (5484228022001/50000000000000 : ℝ)^211
        have hw : |(-917275563/5000000000 : ℝ)|=(917275563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727150757/5000000000 : ℝ)|^275 ≤ (22691202513067/50000000000000 : ℝ)^211
        have hw : |(2727150757/5000000000 : ℝ)|=(2727150757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s2_6 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5293746269/10000000000 : ℝ)*x 0 + (218172057/400000000 : ℝ)*x 1 + (-28664873/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293746269/10000000000 : ℝ)^275 ≤ (8729826813811/20000000000000 : ℝ)^211 := by
    have hnat : (5293746269 : ℕ)^275*20000000000000^211 ≤ 8729826813811^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293746269 10000000000 8729826813811 20000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218172057/400000000 : ℝ)^275 ≤ (22691202030499/50000000000000 : ℝ)^211 := by
    have hnat : (218172057 : ℕ)^275*50000000000000^211 ≤ 22691202030499^211*400000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218172057 400000000 22691202030499 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28664873/156250000 : ℝ)^275 ≤ (5484230928531/50000000000000 : ℝ)^211 := by
    have hnat : (28664873 : ℕ)^275*50000000000000^211 ≤ 5484230928531^211*156250000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28664873 156250000 5484230928531 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293746269/10000000000 : ℝ), (218172057/400000000 : ℝ), (-28664873/156250000 : ℝ)] ![(8729826813811/20000000000000 : ℝ), (22691202030499/50000000000000 : ℝ), (5484230928531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293746269/10000000000 : ℝ)|^275 ≤ (8729826813811/20000000000000 : ℝ)^211
        have hw : |(5293746269/10000000000 : ℝ)|=(5293746269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218172057/400000000 : ℝ)|^275 ≤ (22691202030499/50000000000000 : ℝ)^211
        have hw : |(218172057/400000000 : ℝ)|=(218172057/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-28664873/156250000 : ℝ)|^275 ≤ (5484230928531/50000000000000 : ℝ)^211
        have hw : |(-28664873/156250000 : ℝ)|=(28664873/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s2_7 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (537196611/1250000000 : ℝ)*x 0 + (572038899/1250000000 : ℝ)*x 1 + (403429359/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537196611/1250000000 : ℝ)^275 ≤ (3326392031537/10000000000000 : ℝ)^211 := by
    have hnat : (537196611 : ℕ)^275*10000000000000^211 ≤ 3326392031537^211*1250000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537196611 1250000000 3326392031537 10000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (572038899/1250000000 : ℝ)^275 ≤ (7220611151349/20000000000000 : ℝ)^211 := by
    have hnat : (572038899 : ℕ)^275*20000000000000^211 ≤ 7220611151349^211*1250000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572038899 1250000000 7220611151349 20000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403429359/1000000000 : ℝ)^275 ≤ (7658255977977/25000000000000 : ℝ)^211 := by
    have hnat : (403429359 : ℕ)^275*25000000000000^211 ≤ 7658255977977^211*1000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403429359 1000000000 7658255977977 25000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537196611/1250000000 : ℝ), (572038899/1250000000 : ℝ), (403429359/1000000000 : ℝ)] ![(3326392031537/10000000000000 : ℝ), (7220611151349/20000000000000 : ℝ), (7658255977977/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537196611/1250000000 : ℝ)|^275 ≤ (3326392031537/10000000000000 : ℝ)^211
        have hw : |(537196611/1250000000 : ℝ)|=(537196611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(572038899/1250000000 : ℝ)|^275 ≤ (7220611151349/20000000000000 : ℝ)^211
        have hw : |(572038899/1250000000 : ℝ)|=(572038899/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(403429359/1000000000 : ℝ)|^275 ≤ (7658255977977/25000000000000 : ℝ)^211
        have hw : |(403429359/1000000000 : ℝ)|=(403429359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1440_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3871/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (417/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7883/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9387/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3871/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9387/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3871/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9387/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3871/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9387/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3871/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9387/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3871/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9387/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3871/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (3871/50000 : ℝ) ^ (4399/1024 : ℝ) ≤ (842550732586031/50000000000000000000 : ℝ) := by
    have hpowers : (3871/50000 : ℝ)^4399 ≤ (842550732586031/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4399*50000000000000000000^1024 ≤ 842550732586031^1024*50000^4399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 50000 842550732586031 50000000000000000000 4399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/50000 : ℝ)) (X := (842550732586031/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9387/50000 : ℝ) ^ (4399/1024 : ℝ) ≤ (75731027682179727/100000000000000000000 : ℝ) := by
    have hpowers : (9387/50000 : ℝ)^4399 ≤ (75731027682179727/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9387 : ℕ)^4399*100000000000000000000^1024 ≤ 75731027682179727^1024*50000^4399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9387 50000 75731027682179727 100000000000000000000 4399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9387/50000 : ℝ)) (X := (75731027682179727/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000842550732586031/25000000000000000000 : ℝ) ≤ (5000039225314667/5000000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (25000842550732586031/25000000000000000000 : ℝ)^1024 ≤ (5000039225314667/5000000000000000 : ℝ)^4399 := by
      have hnat : (25000842550732586031 : ℕ)^1024*5000000000000000^4399 ≤ 5000039225314667^4399*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000842550732586031 25000000000000000000 5000039225314667 5000000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000039225314667/5000000000000000 : ℝ)) (X := (25000842550732586031/25000000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100077416129147351789/100000000000000000000 : ℝ) ≤ (10001801559092337/10000000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (100077416129147351789/100000000000000000000 : ℝ)^1024 ≤ (10001801559092337/10000000000000000 : ℝ)^4399 := by
      have hnat : (100077416129147351789 : ℕ)^1024*10000000000000000^4399 ≤ 10001801559092337^4399*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100077416129147351789 100000000000000000000 10001801559092337 10000000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001801559092337/10000000000000000 : ℝ)) (X := (100077416129147351789/100000000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50075731027682179727/50000000000000000000 : ℝ) ≤ (500176233377767/500000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (50075731027682179727/50000000000000000000 : ℝ)^1024 ≤ (500176233377767/500000000000000 : ℝ)^4399 := by
      have hnat : (50075731027682179727 : ℕ)^1024*500000000000000^4399 ≤ 500176233377767^4399*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50075731027682179727 50000000000000000000 500176233377767 500000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500176233377767/500000000000000 : ℝ)) (X := (50075731027682179727/50000000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(842550732586031/50000000000000000000 : ℝ) ≤ ((3939078030567916937/3940000000000000000 : ℝ)+2*(1723108463003/1103200000000000 : ℝ)*(3871/50000 : ℝ))^(4399/1024 : ℝ) := by
    rw [show (3939078030567916937/3940000000000000000 : ℝ)+2*(1723108463003/1103200000000000 : ℝ)*(3871/50000 : ℝ)=(5000039225314667/5000000000000000 : ℝ) by norm_num, show 1+2*(842550732586031/50000000000000000000 : ℝ)=(25000842550732586031/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(75731027682179727/100000000000000000000 : ℝ)+(842550732586031/50000000000000000000 : ℝ) ≤ ((3939078030567916937/3940000000000000000 : ℝ)+(1723108463003/1103200000000000 : ℝ)*((9387/50000 : ℝ)+(3871/50000 : ℝ)))^(4399/1024 : ℝ) := by
    rw [show (3939078030567916937/3940000000000000000 : ℝ)+(1723108463003/1103200000000000 : ℝ)*((9387/50000 : ℝ)+(3871/50000 : ℝ))=(10001801559092337/10000000000000000 : ℝ) by norm_num, show 1+(75731027682179727/100000000000000000000 : ℝ)+(842550732586031/50000000000000000000 : ℝ)=(100077416129147351789/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(75731027682179727/100000000000000000000 : ℝ) ≤ ((3939078030567916937/3940000000000000000 : ℝ)+2*(1723108463003/1103200000000000 : ℝ)*(9387/50000 : ℝ))^(4399/1024 : ℝ) := by
    rw [show (3939078030567916937/3940000000000000000 : ℝ)+2*(1723108463003/1103200000000000 : ℝ)*(9387/50000 : ℝ)=(500176233377767/500000000000000 : ℝ) by norm_num, show 1+2*(75731027682179727/100000000000000000000 : ℝ)=(50075731027682179727/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3939078030567916937/3940000000000000000 : ℝ)*(X 1 0+X 2 0)+(1723108463003/1103200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (3871/50000 : ℝ)) (hi := (9387/50000 : ℝ)) (c := (3939078030567916937/3940000000000000000 : ℝ)) (alpha := (1723108463003/1103200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3939078030567916937/3940000000000000000 : ℝ)*(X 0 1+X 2 1)+(1723108463003/1103200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (3871/50000 : ℝ)) (hi := (9387/50000 : ℝ)) (c := (3939078030567916937/3940000000000000000 : ℝ)) (alpha := (1723108463003/1103200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3939078030567916937/3940000000000000000 : ℝ)*(X 0 2+X 1 2)+(1723108463003/1103200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (3871/50000 : ℝ)) (hi := (9387/50000 : ℝ)) (c := (3939078030567916937/3940000000000000000 : ℝ)) (alpha := (1723108463003/1103200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-977859809/5000000000 : ℝ)*X 0 0+(5455740719/10000000000 : ℝ)*X 0 1+(5203331943/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5359448983/10000000000 : ℝ)*X 1 0+(-2085520769/10000000000 : ℝ)*X 1 1+(5203331761/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2679724253/5000000000 : ℝ)*X 2 0+(2601666131/5000000000 : ℝ)*X 2 1+(-2085520743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4297478489/10000000000 : ℝ)*X 0 0+(1007791569/2500000000 : ℝ)*X 0 1+(572426641/1250000000 : ℝ)*X 0 2+(4297478489/10000000000 : ℝ)*X 1 0+(1007791569/2500000000 : ℝ)*X 1 1+(572426641/1250000000 : ℝ)*X 1 2+(4297478489/10000000000 : ℝ)*X 2 0+(1007791569/2500000000 : ℝ)*X 2 1+(572426641/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1955762969/10000000000 : ℝ)*X 0 0+(81324383/156250000 : ℝ)*X 0 1+(5454300653/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((33085917/62500000 : ℝ)*X 1 0+(-917275563/5000000000 : ℝ)*X 1 1+(2727150757/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293746269/10000000000 : ℝ)*X 2 0+(218172057/400000000 : ℝ)*X 2 1+(-28664873/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((537196611/1250000000 : ℝ)*X 0 0+(572038899/1250000000 : ℝ)*X 0 1+(403429359/1000000000 : ℝ)*X 0 2+(537196611/1250000000 : ℝ)*X 1 0+(572038899/1250000000 : ℝ)*X 1 1+(403429359/1000000000 : ℝ)*X 1 2+(537196611/1250000000 : ℝ)*X 2 0+(572038899/1250000000 : ℝ)*X 2 1+(403429359/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24009906909550633786461/1970000000000000000000000000 : ℝ) := by norm_num
    linear_combination (378398871/20000000000000 : ℝ)*(base19) + (1241899817/100000000000000 : ℝ)*(base23) + (9964609/6250000000000 : ℝ)*(lower2) + (48574637/12500000000000 : ℝ)*(upper3) + (110024299/100000000000000 : ℝ)*(upper5) + (723235964591833/25000000000000 : ℝ)*(major0) + (723235964591833/25000000000000 : ℝ)*(major1) + (723235964591833/25000000000000 : ℝ)*(major2) + (1980925764522403/50000000000000 : ℝ)*(sp0) + (1980933720507591/50000000000000 : ℝ)*(sp1) + (3961868091109721/100000000000000 : ℝ)*(sp2) + (912002730119367/50000000000000 : ℝ)*(sp3) + (4450991183/25000000000000 : ℝ)*(sp4) + (12517227387/100000000000000 : ℝ)*(sp7) + (45600449436653/2500000000000 : ℝ)*(f.failure) + (1980934666504769/50000000000000 : ℝ)*(f.sum) + (821042199337/1970000000000000000000000000 : ℝ)*base65 + (549553576159499479/98500000000000000000000000000000 : ℝ)*base68 + (670431707434499479/98500000000000000000000000000000 : ℝ)*base70 + (331304003906499479/98500000000000000000000000000000 : ℝ)*base72 + (9998930175743/1970000000000000000000000000 : ℝ)*base74 + (756913328937500521/98500000000000000000000000000000 : ℝ)*base75 + (19546404473500521/98500000000000000000000000000000 : ℝ)*base77 + (116582164346500521/98500000000000000000000000000000 : ℝ)*base79 + (15050742324273/1970000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4361/50000000000000000000 : ℝ)*base90 + (4361/50000000000000000000 : ℝ)*base92 + (4361/50000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13305836037663823451717091/4309375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47306379/25000000000000 : ℝ)*(base21) + (27326451/20000000000000 : ℝ)*(base29) + (4780367/50000000000000 : ℝ)*(upper3) + (14489563/10000000000000 : ℝ)*(lower4) + (731541680042171/25000000000000 : ℝ)*(major0) + (1463083428400469/50000000000000 : ℝ)*(major1) + (1463083428400469/50000000000000 : ℝ)*(major2) + (10406183753/100000000000000 : ℝ)*(sp1) + (2306364339/100000000000000 : ℝ)*(sp2) + (1910689301/50000000000000 : ℝ)*(sp3) + (1001842084727353/25000000000000 : ℝ)*(sp4) + (1001839449023351/25000000000000 : ℝ)*(sp5) + (4007365706687301/100000000000000 : ℝ)*(sp6) + (184496145039223/10000000000000 : ℝ)*(sp7) + (1844965271770831/100000000000000 : ℝ)*(f.failure) + (1001842084727353/25000000000000 : ℝ)*(f.sum) + (208039713447793/27580000000000000000000000000 : ℝ)*base66 + (13815261169166920829/1379000000000000000000000000000000 : ℝ)*base68 + (13259435273310920829/1379000000000000000000000000000000 : ℝ)*base70 + (5937998674730360911/689500000000000000000000000000000 : ℝ)*base72 + (236764457413727/55160000000000000000000000000 : ℝ)*base74 + (17051677601532445829/1379000000000000000000000000000000 : ℝ)*base76 + (6488253752578360911/689500000000000000000000000000000 : ℝ)*base78 + (6390335715722445829/1379000000000000000000000000000000 : ℝ)*base80 + (520050003462687/55160000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (13702147/2000000000000000000000 : ℝ)*base90 + (6297853/2000000000000000000000 : ℝ)*base91 + (6297853/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1440_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3871/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (417/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7883/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1440_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1440_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (417/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7883/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1440_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1440_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1440_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (417/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7883/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1440_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

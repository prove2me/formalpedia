-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1100_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:00:26.621072+00:00
-- url     : https://prove2.me/submissions/2894075d-4b3c-4d16-a136-86eee9002dd9

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
theorem support_rectangle_w1100_s6_0 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1093547161/5000000000 : ℝ)*x 0 + (1078845573/2000000000 : ℝ)*x 1 + (1316154769/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093547161/5000000000 : ℝ)^8293 ≤ (3321407179851/25000000000000 : ℝ)^6245 := by
    have hnat : (1093547161 : ℕ)^8293*25000000000000^6245 ≤ 3321407179851^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093547161 5000000000 3321407179851 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078845573/2000000000 : ℝ)^8293 ≤ (8811453293977/20000000000000 : ℝ)^6245 := by
    have hnat : (1078845573 : ℕ)^8293*20000000000000^6245 ≤ 8811453293977^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078845573 2000000000 8811453293977 20000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316154769/2500000000 : ℝ)^8293 ≤ (5332138098589/12500000000000 : ℝ)^6245 := by
    have hnat : (1316154769 : ℕ)^8293*12500000000000^6245 ≤ 5332138098589^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316154769 2500000000 5332138098589 12500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1093547161/5000000000 : ℝ), (1078845573/2000000000 : ℝ), (1316154769/2500000000 : ℝ)] ![(3321407179851/25000000000000 : ℝ), (8811453293977/20000000000000 : ℝ), (5332138098589/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1093547161/5000000000 : ℝ)|^8293 ≤ (3321407179851/25000000000000 : ℝ)^6245
        have hw : |(-1093547161/5000000000 : ℝ)|=(1093547161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078845573/2000000000 : ℝ)|^8293 ≤ (8811453293977/20000000000000 : ℝ)^6245
        have hw : |(1078845573/2000000000 : ℝ)|=(1078845573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316154769/2500000000 : ℝ)|^8293 ≤ (5332138098589/12500000000000 : ℝ)^6245
        have hw : |(1316154769/2500000000 : ℝ)|=(1316154769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s6_1 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069001567/2000000000 : ℝ)*x 0 + (-450570273/2000000000 : ℝ)*x 1 + (2632309541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069001567/2000000000 : ℝ)^8293 ≤ (10881057244271/25000000000000 : ℝ)^6245 := by
    have hnat : (1069001567 : ℕ)^8293*25000000000000^6245 ≤ 10881057244271^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069001567 2000000000 10881057244271 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450570273/2000000000 : ℝ)^8293 ≤ (6909333078343/50000000000000 : ℝ)^6245 := by
    have hnat : (450570273 : ℕ)^8293*50000000000000^6245 ≤ 6909333078343^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450570273 2000000000 6909333078343 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632309541/5000000000 : ℝ)^8293 ≤ (42657104853271/100000000000000 : ℝ)^6245 := by
    have hnat : (2632309541 : ℕ)^8293*100000000000000^6245 ≤ 42657104853271^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632309541 5000000000 42657104853271 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069001567/2000000000 : ℝ), (-450570273/2000000000 : ℝ), (2632309541/5000000000 : ℝ)] ![(10881057244271/25000000000000 : ℝ), (6909333078343/50000000000000 : ℝ), (42657104853271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069001567/2000000000 : ℝ)|^8293 ≤ (10881057244271/25000000000000 : ℝ)^6245
        have hw : |(1069001567/2000000000 : ℝ)|=(1069001567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-450570273/2000000000 : ℝ)|^8293 ≤ (6909333078343/50000000000000 : ℝ)^6245
        have hw : |(-450570273/2000000000 : ℝ)|=(450570273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632309541/5000000000 : ℝ)|^8293 ≤ (42657104853271/100000000000000 : ℝ)^6245
        have hw : |(2632309541/5000000000 : ℝ)|=(2632309541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s6_2 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345007831/10000000000 : ℝ)*x 0 + (2632309541/5000000000 : ℝ)*x 1 + (-225285137/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345007831/10000000000 : ℝ)^8293 ≤ (4352422893383/10000000000000 : ℝ)^6245 := by
    have hnat : (5345007831 : ℕ)^8293*10000000000000^6245 ≤ 4352422893383^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345007831 10000000000 4352422893383 10000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632309541/5000000000 : ℝ)^8293 ≤ (42657104853271/100000000000000 : ℝ)^6245 := by
    have hnat : (2632309541 : ℕ)^8293*100000000000000^6245 ≤ 42657104853271^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632309541 5000000000 42657104853271 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225285137/1000000000 : ℝ)^8293 ≤ (13818666197413/100000000000000 : ℝ)^6245 := by
    have hnat : (225285137 : ℕ)^8293*100000000000000^6245 ≤ 13818666197413^6245*1000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225285137 1000000000 13818666197413 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345007831/10000000000 : ℝ), (2632309541/5000000000 : ℝ), (-225285137/1000000000 : ℝ)] ![(4352422893383/10000000000000 : ℝ), (42657104853271/100000000000000 : ℝ), (13818666197413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345007831/10000000000 : ℝ)|^8293 ≤ (4352422893383/10000000000000 : ℝ)^6245
        have hw : |(5345007831/10000000000 : ℝ)|=(5345007831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632309541/5000000000 : ℝ)|^8293 ≤ (42657104853271/100000000000000 : ℝ)^6245
        have hw : |(2632309541/5000000000 : ℝ)|=(2632309541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-225285137/1000000000 : ℝ)|^8293 ≤ (13818666197413/100000000000000 : ℝ)^6245
        have hw : |(-225285137/1000000000 : ℝ)|=(225285137/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s6_3 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (546325223/1250000000 : ℝ)*x 0 + (2122308031/5000000000 : ℝ)*x 1 + (4500346883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546325223/1250000000 : ℝ)^8293 ≤ (3331650883749/10000000000000 : ℝ)^6245 := by
    have hnat : (546325223 : ℕ)^8293*10000000000000^6245 ≤ 3331650883749^6245*1250000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546325223 1250000000 3331650883749 10000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2122308031/5000000000 : ℝ)^8293 ≤ (16023628616767/50000000000000 : ℝ)^6245 := by
    have hnat : (2122308031 : ℕ)^8293*50000000000000^6245 ≤ 16023628616767^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122308031 5000000000 16023628616767 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500346883/10000000000 : ℝ)^8293 ≤ (34636233909199/100000000000000 : ℝ)^6245 := by
    have hnat : (4500346883 : ℕ)^8293*100000000000000^6245 ≤ 34636233909199^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500346883 10000000000 34636233909199 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546325223/1250000000 : ℝ), (2122308031/5000000000 : ℝ), (4500346883/10000000000 : ℝ)] ![(3331650883749/10000000000000 : ℝ), (16023628616767/50000000000000 : ℝ), (34636233909199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546325223/1250000000 : ℝ)|^8293 ≤ (3331650883749/10000000000000 : ℝ)^6245
        have hw : |(546325223/1250000000 : ℝ)|=(546325223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2122308031/5000000000 : ℝ)|^8293 ≤ (16023628616767/50000000000000 : ℝ)^6245
        have hw : |(2122308031/5000000000 : ℝ)|=(2122308031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500346883/10000000000 : ℝ)|^8293 ≤ (34636233909199/100000000000000 : ℝ)^6245
        have hw : |(4500346883/10000000000 : ℝ)|=(4500346883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s6_4 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-546774863/2500000000 : ℝ)*x 0 + (2632473177/5000000000 : ℝ)*x 1 + (2696949683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546774863/2500000000 : ℝ)^8293 ≤ (830354381337/6250000000000 : ℝ)^6245 := by
    have hnat : (546774863 : ℕ)^8293*6250000000000^6245 ≤ 830354381337^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546774863 2500000000 830354381337 6250000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632473177/5000000000 : ℝ)^8293 ≤ (5332578283243/12500000000000 : ℝ)^6245 := by
    have hnat : (2632473177 : ℕ)^8293*12500000000000^6245 ≤ 5332578283243^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632473177 5000000000 5332578283243 12500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696949683/5000000000 : ℝ)^8293 ≤ (22026851811341/50000000000000 : ℝ)^6245 := by
    have hnat : (2696949683 : ℕ)^8293*50000000000000^6245 ≤ 22026851811341^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696949683 5000000000 22026851811341 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-546774863/2500000000 : ℝ), (2632473177/5000000000 : ℝ), (2696949683/5000000000 : ℝ)] ![(830354381337/6250000000000 : ℝ), (5332578283243/12500000000000 : ℝ), (22026851811341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-546774863/2500000000 : ℝ)|^8293 ≤ (830354381337/6250000000000 : ℝ)^6245
        have hw : |(-546774863/2500000000 : ℝ)|=(546774863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632473177/5000000000 : ℝ)|^8293 ≤ (5332578283243/12500000000000 : ℝ)^6245
        have hw : |(2632473177/5000000000 : ℝ)|=(2632473177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696949683/5000000000 : ℝ)|^8293 ≤ (22026851811341/50000000000000 : ℝ)^6245
        have hw : |(2696949683/5000000000 : ℝ)|=(2696949683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s6_5 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656137509/5000000000 : ℝ)*x 0 + (-424714211/2000000000 : ℝ)*x 1 + (337118709/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656137509/5000000000 : ℝ)^8293 ≤ (10792658024109/25000000000000 : ℝ)^6245 := by
    have hnat : (2656137509 : ℕ)^8293*25000000000000^6245 ≤ 10792658024109^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656137509 5000000000 10792658024109 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424714211/2000000000 : ℝ)^8293 ≤ (12775664507043/100000000000000 : ℝ)^6245 := by
    have hnat : (424714211 : ℕ)^8293*100000000000000^6245 ≤ 12775664507043^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424714211 2000000000 12775664507043 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337118709/625000000 : ℝ)^8293 ≤ (11013425846019/25000000000000 : ℝ)^6245 := by
    have hnat : (337118709 : ℕ)^8293*25000000000000^6245 ≤ 11013425846019^6245*625000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337118709 625000000 11013425846019 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656137509/5000000000 : ℝ), (-424714211/2000000000 : ℝ), (337118709/625000000 : ℝ)] ![(10792658024109/25000000000000 : ℝ), (12775664507043/100000000000000 : ℝ), (11013425846019/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656137509/5000000000 : ℝ)|^8293 ≤ (10792658024109/25000000000000 : ℝ)^6245
        have hw : |(2656137509/5000000000 : ℝ)|=(2656137509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-424714211/2000000000 : ℝ)|^8293 ≤ (12775664507043/100000000000000 : ℝ)^6245
        have hw : |(-424714211/2000000000 : ℝ)|=(424714211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337118709/625000000 : ℝ)|^8293 ≤ (11013425846019/25000000000000 : ℝ)^6245
        have hw : |(337118709/625000000 : ℝ)|=(337118709/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s6_6 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312275017/10000000000 : ℝ)*x 0 + (1348474833/2500000000 : ℝ)*x 1 + (-2123571073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312275017/10000000000 : ℝ)^8293 ≤ (10792658021411/25000000000000 : ℝ)^6245 := by
    have hnat : (5312275017 : ℕ)^8293*25000000000000^6245 ≤ 10792658021411^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312275017 10000000000 10792658021411 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348474833/2500000000 : ℝ)^8293 ≤ (44053703253927/100000000000000 : ℝ)^6245 := by
    have hnat : (1348474833 : ℕ)^8293*100000000000000^6245 ≤ 44053703253927^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348474833 2500000000 44053703253927 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123571073/10000000000 : ℝ)^8293 ≤ (6387832325423/50000000000000 : ℝ)^6245 := by
    have hnat : (2123571073 : ℕ)^8293*50000000000000^6245 ≤ 6387832325423^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123571073 10000000000 6387832325423 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312275017/10000000000 : ℝ), (1348474833/2500000000 : ℝ), (-2123571073/10000000000 : ℝ)] ![(10792658021411/25000000000000 : ℝ), (44053703253927/100000000000000 : ℝ), (6387832325423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312275017/10000000000 : ℝ)|^8293 ≤ (10792658021411/25000000000000 : ℝ)^6245
        have hw : |(5312275017/10000000000 : ℝ)|=(5312275017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348474833/2500000000 : ℝ)|^8293 ≤ (44053703253927/100000000000000 : ℝ)^6245
        have hw : |(1348474833/2500000000 : ℝ)|=(1348474833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2123571073/10000000000 : ℝ)|^8293 ≤ (6387832325423/50000000000000 : ℝ)^6245
        have hw : |(-2123571073/10000000000 : ℝ)|=(2123571073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s6_7 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370611843/10000000000 : ℝ)*x 0 + (899940211/2000000000 : ℝ)*x 1 + (4245264213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370611843/10000000000 : ℝ)^8293 ≤ (16658305331013/50000000000000 : ℝ)^6245 := by
    have hnat : (4370611843 : ℕ)^8293*50000000000000^6245 ≤ 16658305331013^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370611843 10000000000 16658305331013 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899940211/2000000000 : ℝ)^8293 ≤ (1385185340191/4000000000000 : ℝ)^6245 := by
    have hnat : (899940211 : ℕ)^8293*4000000000000^6245 ≤ 1385185340191^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899940211 2000000000 1385185340191 4000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4245264213/10000000000 : ℝ)^8293 ≤ (32053755817651/100000000000000 : ℝ)^6245 := by
    have hnat : (4245264213 : ℕ)^8293*100000000000000^6245 ≤ 32053755817651^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245264213 10000000000 32053755817651 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370611843/10000000000 : ℝ), (899940211/2000000000 : ℝ), (4245264213/10000000000 : ℝ)] ![(16658305331013/50000000000000 : ℝ), (1385185340191/4000000000000 : ℝ), (32053755817651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370611843/10000000000 : ℝ)|^8293 ≤ (16658305331013/50000000000000 : ℝ)^6245
        have hw : |(4370611843/10000000000 : ℝ)|=(4370611843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899940211/2000000000 : ℝ)|^8293 ≤ (1385185340191/4000000000000 : ℝ)^6245
        have hw : |(899940211/2000000000 : ℝ)|=(899940211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4245264213/10000000000 : ℝ)|^8293 ≤ (32053755817651/100000000000000 : ℝ)^6245
        have hw : |(4245264213/10000000000 : ℝ)|=(4245264213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1100_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2813/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1411/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7017/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1759/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2813/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1759/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2813/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1759/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2813/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1759/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2813/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1759/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2813/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1759/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2813/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2813/25000 : ℝ) ^ (2073/512 : ℝ) ≤ (14407619165324711/100000000000000000000 : ℝ) := by
    have hpowers : (2813/25000 : ℝ)^2073 ≤ (14407619165324711/100000000000000000000 : ℝ)^512 := by
      have hnat : (2813 : ℕ)^2073*100000000000000000000^512 ≤ 14407619165324711^512*25000^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2813 25000 14407619165324711 100000000000000000000 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2813/25000 : ℝ)) (X := (14407619165324711/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1759/12500 : ℝ) ^ (2073/512 : ℝ) ≤ (17815955611110111/50000000000000000000 : ℝ) := by
    have hpowers : (1759/12500 : ℝ)^2073 ≤ (17815955611110111/50000000000000000000 : ℝ)^512 := by
      have hnat : (1759 : ℕ)^2073*50000000000000000000^512 ≤ 17815955611110111^512*12500^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1759 12500 17815955611110111 50000000000000000000 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1759/12500 : ℝ)) (X := (17815955611110111/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014407619165324711/50000000000000000000 : ℝ) ≤ (10000711616096269/10000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (50014407619165324711/50000000000000000000 : ℝ)^512 ≤ (10000711616096269/10000000000000000 : ℝ)^2073 := by
      have hnat : (50014407619165324711 : ℕ)^512*10000000000000000^2073 ≤ 10000711616096269^2073*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014407619165324711 50000000000000000000 10000711616096269 10000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000711616096269/10000000000000000 : ℝ)) (X := (50014407619165324711/50000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050039530387544933/100000000000000000000 : ℝ) ≤ (500061783439581/500000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (100050039530387544933/100000000000000000000 : ℝ)^512 ≤ (500061783439581/500000000000000 : ℝ)^2073 := by
      have hnat : (100050039530387544933 : ℕ)^512*500000000000000^2073 ≤ 500061783439581^2073*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050039530387544933 100000000000000000000 500061783439581 500000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500061783439581/500000000000000 : ℝ)) (X := (100050039530387544933/100000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017815955611110111/25000000000000000000 : ℝ) ≤ (10001759721486971/10000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (25017815955611110111/25000000000000000000 : ℝ)^512 ≤ (10001759721486971/10000000000000000 : ℝ)^2073 := by
      have hnat : (25017815955611110111 : ℕ)^512*10000000000000000^2073 ≤ 10001759721486971^2073*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017815955611110111 25000000000000000000 10001759721486971 10000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001759721486971/10000000000000000 : ℝ)) (X := (25017815955611110111/25000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14407619165324711/100000000000000000000 : ℝ) ≤ ((7047553368883824919/7050000000000000000 : ℝ)+2*(524052695351/282000000000000 : ℝ)*(2813/25000 : ℝ))^(2073/512 : ℝ) := by
    rw [show (7047553368883824919/7050000000000000000 : ℝ)+2*(524052695351/282000000000000 : ℝ)*(2813/25000 : ℝ)=(10000711616096269/10000000000000000 : ℝ) by norm_num, show 1+2*(14407619165324711/100000000000000000000 : ℝ)=(50014407619165324711/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17815955611110111/50000000000000000000 : ℝ)+(14407619165324711/100000000000000000000 : ℝ) ≤ ((7047553368883824919/7050000000000000000 : ℝ)+(524052695351/282000000000000 : ℝ)*((1759/12500 : ℝ)+(2813/25000 : ℝ)))^(2073/512 : ℝ) := by
    rw [show (7047553368883824919/7050000000000000000 : ℝ)+(524052695351/282000000000000 : ℝ)*((1759/12500 : ℝ)+(2813/25000 : ℝ))=(500061783439581/500000000000000 : ℝ) by norm_num, show 1+(17815955611110111/50000000000000000000 : ℝ)+(14407619165324711/100000000000000000000 : ℝ)=(100050039530387544933/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17815955611110111/50000000000000000000 : ℝ) ≤ ((7047553368883824919/7050000000000000000 : ℝ)+2*(524052695351/282000000000000 : ℝ)*(1759/12500 : ℝ))^(2073/512 : ℝ) := by
    rw [show (7047553368883824919/7050000000000000000 : ℝ)+2*(524052695351/282000000000000 : ℝ)*(1759/12500 : ℝ)=(10001759721486971/10000000000000000 : ℝ) by norm_num, show 1+2*(17815955611110111/50000000000000000000 : ℝ)=(25017815955611110111/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7047553368883824919/7050000000000000000 : ℝ)*(X 1 0+X 2 0)+(524052695351/282000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (2813/25000 : ℝ)) (hi := (1759/12500 : ℝ)) (c := (7047553368883824919/7050000000000000000 : ℝ)) (alpha := (524052695351/282000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7047553368883824919/7050000000000000000 : ℝ)*(X 0 1+X 2 1)+(524052695351/282000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (2813/25000 : ℝ)) (hi := (1759/12500 : ℝ)) (c := (7047553368883824919/7050000000000000000 : ℝ)) (alpha := (524052695351/282000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7047553368883824919/7050000000000000000 : ℝ)*(X 0 2+X 1 2)+(524052695351/282000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (2813/25000 : ℝ)) (hi := (1759/12500 : ℝ)) (c := (7047553368883824919/7050000000000000000 : ℝ)) (alpha := (524052695351/282000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1093547161/5000000000 : ℝ)*X 0 0+(1078845573/2000000000 : ℝ)*X 0 1+(1316154769/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069001567/2000000000 : ℝ)*X 1 0+(-450570273/2000000000 : ℝ)*X 1 1+(2632309541/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345007831/10000000000 : ℝ)*X 2 0+(2632309541/5000000000 : ℝ)*X 2 1+(-225285137/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((546325223/1250000000 : ℝ)*X 0 0+(2122308031/5000000000 : ℝ)*X 0 1+(4500346883/10000000000 : ℝ)*X 0 2+(546325223/1250000000 : ℝ)*X 1 0+(2122308031/5000000000 : ℝ)*X 1 1+(4500346883/10000000000 : ℝ)*X 1 2+(546325223/1250000000 : ℝ)*X 2 0+(2122308031/5000000000 : ℝ)*X 2 1+(4500346883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-546774863/2500000000 : ℝ)*X 0 0+(2632473177/5000000000 : ℝ)*X 0 1+(2696949683/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656137509/5000000000 : ℝ)*X 1 0+(-424714211/2000000000 : ℝ)*X 1 1+(337118709/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312275017/10000000000 : ℝ)*X 2 0+(1348474833/2500000000 : ℝ)*X 2 1+(-2123571073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4370611843/10000000000 : ℝ)*X 0 0+(899940211/2000000000 : ℝ)*X 0 1+(4245264213/10000000000 : ℝ)*X 0 2+(4370611843/10000000000 : ℝ)*X 1 0+(899940211/2000000000 : ℝ)*X 1 1+(4245264213/10000000000 : ℝ)*X 1 2+(4370611843/10000000000 : ℝ)*X 2 0+(899940211/2000000000 : ℝ)*X 2 1+(4245264213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (247524812108256713188973943/23500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (416653813/20000000000000 : ℝ)*(base19) + (1936668531/100000000000000 : ℝ)*(base23) + (37635923/50000000000000 : ℝ)*(lower2) + (268204977/100000000000000 : ℝ)*(upper3) + (154346759/100000000000000 : ℝ)*(upper5) + (1162606127667297/20000000000000 : ℝ)*(major0) + (1162606127667297/20000000000000 : ℝ)*(major1) + (1162606127667297/20000000000000 : ℝ)*(major2) + (1928896302295081/25000000000000 : ℝ)*(sp0) + (7715639045623779/100000000000000 : ℝ)*(sp1) + (7715639192224313/100000000000000 : ℝ)*(sp2) + (3910389150295971/100000000000000 : ℝ)*(sp3) + (1397992813/2500000000000 : ℝ)*(sp4) + (7661596281/25000000000000 : ℝ)*(sp7) + (782083959336219/20000000000000 : ℝ)*(f.failure) + (1928910282223211/25000000000000 : ℝ)*(f.sum) + (2320431036429/940000000000000000000000000 : ℝ)*base65 + (381356929568617019/47000000000000000000000000000000 : ℝ)*base68 + (418615069757617019/47000000000000000000000000000000 : ℝ)*base70 + (304172291178382981/47000000000000000000000000000000 : ℝ)*base71 + (935804212969/940000000000000000000000000 : ℝ)*base73 + (556410982655617019/47000000000000000000000000000000 : ℝ)*base76 + (958586819192382981/47000000000000000000000000000000 : ℝ)*base77 + (278495564890617019/47000000000000000000000000000000 : ℝ)*base80 + (1224065096551/940000000000000000000000000 : ℝ)*base82 + (18231/20000000000000000000 : ℝ)*base89 + (18231/20000000000000000000 : ℝ)*base91 + (18231/20000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4848050107608428467281/587500000000000000000000000 : ℝ) := by norm_num
    linear_combination (897093559/50000000000000 : ℝ)*(base19) + (926627447/50000000000000 : ℝ)*(base23) + (85618157/50000000000000 : ℝ)*(upper3) + (16937723/50000000000000 : ℝ)*(lower4) + (201812397/100000000000000 : ℝ)*(upper5) + (365156588032299/6250000000000 : ℝ)*(major0) + (365156588032299/6250000000000 : ℝ)*(major1) + (365156588032299/6250000000000 : ℝ)*(major2) + (49359727751/100000000000000 : ℝ)*(sp1) + (2441689707/5000000000000 : ℝ)*(sp2) + (7754763097370861/100000000000000 : ℝ)*(sp4) + (969338992931999/12500000000000 : ℝ)*(sp5) + (7754712410321827/100000000000000 : ℝ)*(sp6) + (393024744459603/10000000000000 : ℝ)*(sp7) + (393024744459603/10000000000000 : ℝ)*(f.failure) + (7754763097370861/100000000000000 : ℝ)*(f.sum) + (128500796141/587500000000000000000000000 : ℝ)*base65 + (79611869702322073/14687500000000000000000000000000 : ℝ)*base68 + (18066046384822073/14687500000000000000000000000000 : ℝ)*base70 + (41884337801115427/14687500000000000000000000000000 : ℝ)*base71 + (4065582135307/1175000000000000000000000000 : ℝ)*base73 + (23551870462677927/14687500000000000000000000000000 : ℝ)*base75 + (147665630136740427/14687500000000000000000000000000 : ℝ)*base77 + (33438897124197073/14687500000000000000000000000000 : ℝ)*base80 + (6095250998607/1175000000000000000000000000 : ℝ)*base81 + (19953/10000000000000000000 : ℝ)*base90 + (19953/10000000000000000000 : ℝ)*base92 + (19953/10000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1100_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2813/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1100_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1100_s7_0 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1093564611/5000000000 : ℝ)*x 0 + (2696918333/5000000000 : ℝ)*x 1 + (1052997447/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093564611/5000000000 : ℝ)^8293 ≤ (13285910246619/100000000000000 : ℝ)^6245 := by
    have hnat : (1093564611 : ℕ)^8293*100000000000000^6245 ≤ 13285910246619^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093564611 5000000000 13285910246619 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696918333/5000000000 : ℝ)^8293 ≤ (1762120943867/4000000000000 : ℝ)^6245 := by
    have hnat : (2696918333 : ℕ)^8293*4000000000000^6245 ≤ 1762120943867^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696918333 5000000000 1762120943867 4000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052997447/2000000000 : ℝ)^8293 ≤ (21330533073147/50000000000000 : ℝ)^6245 := by
    have hnat : (1052997447 : ℕ)^8293*50000000000000^6245 ≤ 21330533073147^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052997447 2000000000 21330533073147 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1093564611/5000000000 : ℝ), (2696918333/5000000000 : ℝ), (1052997447/2000000000 : ℝ)] ![(13285910246619/100000000000000 : ℝ), (1762120943867/4000000000000 : ℝ), (21330533073147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1093564611/5000000000 : ℝ)|^8293 ≤ (13285910246619/100000000000000 : ℝ)^6245
        have hw : |(-1093564611/5000000000 : ℝ)|=(1093564611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696918333/5000000000 : ℝ)|^8293 ≤ (1762120943867/4000000000000 : ℝ)^6245
        have hw : |(2696918333/5000000000 : ℝ)|=(2696918333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052997447/2000000000 : ℝ)|^8293 ≤ (21330533073147/50000000000000 : ℝ)^6245
        have hw : |(1052997447/2000000000 : ℝ)|=(1052997447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s7_1 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344909449/10000000000 : ℝ)*x 0 + (-563123869/2500000000 : ℝ)*x 1 + (2632493681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344909449/10000000000 : ℝ)^8293 ≤ (4352316509387/10000000000000 : ℝ)^6245 := by
    have hnat : (5344909449 : ℕ)^8293*10000000000000^6245 ≤ 4352316509387^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344909449 10000000000 4352316509387 10000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563123869/2500000000 : ℝ)^8293 ≤ (6907883685451/50000000000000 : ℝ)^6245 := by
    have hnat : (563123869 : ℕ)^8293*50000000000000^6245 ≤ 6907883685451^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563123869 2500000000 6907883685451 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632493681/5000000000 : ℝ)^8293 ≤ (42661067512819/100000000000000 : ℝ)^6245 := by
    have hnat : (2632493681 : ℕ)^8293*100000000000000^6245 ≤ 42661067512819^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632493681 5000000000 42661067512819 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344909449/10000000000 : ℝ), (-563123869/2500000000 : ℝ), (2632493681/5000000000 : ℝ)] ![(4352316509387/10000000000000 : ℝ), (6907883685451/50000000000000 : ℝ), (42661067512819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344909449/10000000000 : ℝ)|^8293 ≤ (4352316509387/10000000000000 : ℝ)^6245
        have hw : |(5344909449/10000000000 : ℝ)|=(5344909449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-563123869/2500000000 : ℝ)|^8293 ≤ (6907883685451/50000000000000 : ℝ)^6245
        have hw : |(-563123869/2500000000 : ℝ)|=(563123869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632493681/5000000000 : ℝ)|^8293 ≤ (42661067512819/100000000000000 : ℝ)^6245
        have hw : |(2632493681/5000000000 : ℝ)|=(2632493681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s7_2 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068981951/2000000000 : ℝ)*x 0 + (5264987153/10000000000 : ℝ)*x 1 + (-2252495347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068981951/2000000000 : ℝ)^8293 ≤ (10880792100687/25000000000000 : ℝ)^6245 := by
    have hnat : (1068981951 : ℕ)^8293*25000000000000^6245 ≤ 10880792100687^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068981951 2000000000 10880792100687 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264987153/10000000000 : ℝ)^8293 ≤ (10665266315993/25000000000000 : ℝ)^6245 := by
    have hnat : (5264987153 : ℕ)^8293*25000000000000^6245 ≤ 10665266315993^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264987153 10000000000 10665266315993 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252495347/10000000000 : ℝ)^8293 ≤ (13815766320199/100000000000000 : ℝ)^6245 := by
    have hnat : (2252495347 : ℕ)^8293*100000000000000^6245 ≤ 13815766320199^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252495347 10000000000 13815766320199 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068981951/2000000000 : ℝ), (5264987153/10000000000 : ℝ), (-2252495347/10000000000 : ℝ)] ![(10880792100687/25000000000000 : ℝ), (10665266315993/25000000000000 : ℝ), (13815766320199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068981951/2000000000 : ℝ)|^8293 ≤ (10880792100687/25000000000000 : ℝ)^6245
        have hw : |(1068981951/2000000000 : ℝ)|=(1068981951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264987153/10000000000 : ℝ)|^8293 ≤ (10665266315993/25000000000000 : ℝ)^6245
        have hw : |(5264987153/10000000000 : ℝ)|=(5264987153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2252495347/10000000000 : ℝ)|^8293 ≤ (13815766320199/100000000000000 : ℝ)^6245
        have hw : |(-2252495347/10000000000 : ℝ)|=(2252495347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s7_3 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2185310649/5000000000 : ℝ)*x 0 + (1061340709/2500000000 : ℝ)*x 1 + (4499594931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185310649/5000000000 : ℝ)^8293 ≤ (4164588296563/12500000000000 : ℝ)^6245 := by
    have hnat : (2185310649 : ℕ)^8293*12500000000000^6245 ≤ 4164588296563^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185310649 5000000000 4164588296563 12500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061340709/2500000000 : ℝ)^8293 ≤ (32054744674181/100000000000000 : ℝ)^6245 := by
    have hnat : (1061340709 : ℕ)^8293*100000000000000^6245 ≤ 32054744674181^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061340709 2500000000 32054744674181 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499594931/10000000000 : ℝ)^8293 ≤ (34628548940269/100000000000000 : ℝ)^6245 := by
    have hnat : (4499594931 : ℕ)^8293*100000000000000^6245 ≤ 34628548940269^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499594931 10000000000 34628548940269 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185310649/5000000000 : ℝ), (1061340709/2500000000 : ℝ), (4499594931/10000000000 : ℝ)] ![(4164588296563/12500000000000 : ℝ), (32054744674181/100000000000000 : ℝ), (34628548940269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185310649/5000000000 : ℝ)|^8293 ≤ (4164588296563/12500000000000 : ℝ)^6245
        have hw : |(2185310649/5000000000 : ℝ)|=(2185310649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061340709/2500000000 : ℝ)|^8293 ≤ (32054744674181/100000000000000 : ℝ)^6245
        have hw : |(1061340709/2500000000 : ℝ)|=(1061340709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499594931/10000000000 : ℝ)|^8293 ≤ (34628548940269/100000000000000 : ℝ)^6245
        have hw : |(4499594931/10000000000 : ℝ)|=(4499594931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s7_4 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-437426869/2000000000 : ℝ)*x 0 + (1053062157/2000000000 : ℝ)*x 1 + (2696755927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437426869/2000000000 : ℝ)^8293 ≤ (13285951572357/100000000000000 : ℝ)^6245 := by
    have hnat : (437426869 : ℕ)^8293*100000000000000^6245 ≤ 13285951572357^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437426869 2000000000 13285951572357 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053062157/2000000000 : ℝ)^8293 ≤ (2666534224379/6250000000000 : ℝ)^6245 := by
    have hnat : (1053062157 : ℕ)^8293*6250000000000^6245 ≤ 2666534224379^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053062157 2000000000 2666534224379 6250000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696755927/5000000000 : ℝ)^8293 ≤ (22024750410737/50000000000000 : ℝ)^6245 := by
    have hnat : (2696755927 : ℕ)^8293*50000000000000^6245 ≤ 22024750410737^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696755927 5000000000 22024750410737 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-437426869/2000000000 : ℝ), (1053062157/2000000000 : ℝ), (2696755927/5000000000 : ℝ)] ![(13285951572357/100000000000000 : ℝ), (2666534224379/6250000000000 : ℝ), (22024750410737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-437426869/2000000000 : ℝ)|^8293 ≤ (13285951572357/100000000000000 : ℝ)^6245
        have hw : |(-437426869/2000000000 : ℝ)|=(437426869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053062157/2000000000 : ℝ)|^8293 ≤ (2666534224379/6250000000000 : ℝ)^6245
        have hw : |(1053062157/2000000000 : ℝ)|=(1053062157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696755927/5000000000 : ℝ)|^8293 ≤ (22024750410737/50000000000000 : ℝ)^6245
        have hw : |(2696755927/5000000000 : ℝ)|=(2696755927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s7_5 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531236841/1000000000 : ℝ)*x 0 + (-212397093/1000000000 : ℝ)*x 1 + (5393511853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531236841/1000000000 : ℝ)^8293 ≤ (21585819975663/50000000000000 : ℝ)^6245 := by
    have hnat : (531236841 : ℕ)^8293*50000000000000^6245 ≤ 21585819975663^6245*1000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531236841 1000000000 21585819975663 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212397093/1000000000 : ℝ)^8293 ≤ (638942961641/5000000000000 : ℝ)^6245 := by
    have hnat : (212397093 : ℕ)^8293*5000000000000^6245 ≤ 638942961641^6245*1000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212397093 1000000000 638942961641 5000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393511853/10000000000 : ℝ)^8293 ≤ (11012375202657/25000000000000 : ℝ)^6245 := by
    have hnat : (5393511853 : ℕ)^8293*25000000000000^6245 ≤ 11012375202657^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393511853 10000000000 11012375202657 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531236841/1000000000 : ℝ), (-212397093/1000000000 : ℝ), (5393511853/10000000000 : ℝ)] ![(21585819975663/50000000000000 : ℝ), (638942961641/5000000000000 : ℝ), (11012375202657/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531236841/1000000000 : ℝ)|^8293 ≤ (21585819975663/50000000000000 : ℝ)^6245
        have hw : |(531236841/1000000000 : ℝ)|=(531236841/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212397093/1000000000 : ℝ)|^8293 ≤ (638942961641/5000000000000 : ℝ)^6245
        have hw : |(-212397093/1000000000 : ℝ)|=(212397093/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393511853/10000000000 : ℝ)|^8293 ≤ (11012375202657/25000000000000 : ℝ)^6245
        have hw : |(5393511853/10000000000 : ℝ)|=(5393511853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s7_6 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312368411/10000000000 : ℝ)*x 0 + (1348377963/2500000000 : ℝ)*x 1 + (-2123970929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312368411/10000000000 : ℝ)^8293 ≤ (21585819981059/50000000000000 : ℝ)^6245 := by
    have hnat : (5312368411 : ℕ)^8293*50000000000000^6245 ≤ 21585819981059^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312368411 10000000000 21585819981059 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348377963/2500000000 : ℝ)^8293 ≤ (44049500799783/100000000000000 : ℝ)^6245 := by
    have hnat : (1348377963 : ℕ)^8293*100000000000000^6245 ≤ 44049500799783^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348377963 2500000000 44049500799783 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123970929/10000000000 : ℝ)^8293 ≤ (1277885922483/10000000000000 : ℝ)^6245 := by
    have hnat : (2123970929 : ℕ)^8293*10000000000000^6245 ≤ 1277885922483^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123970929 10000000000 1277885922483 10000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312368411/10000000000 : ℝ), (1348377963/2500000000 : ℝ), (-2123970929/10000000000 : ℝ)] ![(21585819981059/50000000000000 : ℝ), (44049500799783/100000000000000 : ℝ), (1277885922483/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312368411/10000000000 : ℝ)|^8293 ≤ (21585819981059/50000000000000 : ℝ)^6245
        have hw : |(5312368411/10000000000 : ℝ)|=(5312368411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348377963/2500000000 : ℝ)|^8293 ≤ (44049500799783/100000000000000 : ℝ)^6245
        have hw : |(1348377963/2500000000 : ℝ)|=(1348377963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2123970929/10000000000 : ℝ)|^8293 ≤ (1277885922483/10000000000000 : ℝ)^6245
        have hw : |(-2123970929/10000000000 : ℝ)|=(2123970929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s7_7 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370631061/10000000000 : ℝ)*x 0 + (56236959/125000000 : ℝ)*x 1 + (530750431/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370631061/10000000000 : ℝ)^8293 ≤ (33316805200857/100000000000000 : ℝ)^6245 := by
    have hnat : (4370631061 : ℕ)^8293*100000000000000^6245 ≤ 33316805200857^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370631061 10000000000 33316805200857 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56236959/125000000 : ℝ)^8293 ≤ (34622026737723/100000000000000 : ℝ)^6245 := by
    have hnat : (56236959 : ℕ)^8293*100000000000000^6245 ≤ 34622026737723^6245*125000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56236959 125000000 34622026737723 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530750431/1250000000 : ℝ)^8293 ≤ (16030584019181/50000000000000 : ℝ)^6245 := by
    have hnat : (530750431 : ℕ)^8293*50000000000000^6245 ≤ 16030584019181^6245*1250000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530750431 1250000000 16030584019181 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370631061/10000000000 : ℝ), (56236959/125000000 : ℝ), (530750431/1250000000 : ℝ)] ![(33316805200857/100000000000000 : ℝ), (34622026737723/100000000000000 : ℝ), (16030584019181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370631061/10000000000 : ℝ)|^8293 ≤ (33316805200857/100000000000000 : ℝ)^6245
        have hw : |(4370631061/10000000000 : ℝ)|=(4370631061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56236959/125000000 : ℝ)|^8293 ≤ (34622026737723/100000000000000 : ℝ)^6245
        have hw : |(56236959/125000000 : ℝ)|=(56236959/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(530750431/1250000000 : ℝ)|^8293 ≤ (16030584019181/50000000000000 : ℝ)^6245
        have hw : |(530750431/1250000000 : ℝ)|=(530750431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1100_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (353/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7013/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7017/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1411/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7017/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1411/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7017/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1411/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7017/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1411/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7017/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1411/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7017/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1411/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1411/12500 : ℝ) ^ (2073/512 : ℝ) ≤ (14595166961767181/100000000000000000000 : ℝ) := by
    have hpowers : (1411/12500 : ℝ)^2073 ≤ (14595166961767181/100000000000000000000 : ℝ)^512 := by
      have hnat : (1411 : ℕ)^2073*100000000000000000000^512 ≤ 14595166961767181^512*12500^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1411 12500 14595166961767181 100000000000000000000 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1411/12500 : ℝ)) (X := (14595166961767181/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7017/50000 : ℝ) ^ (2073/512 : ℝ) ≤ (3524393236145551/10000000000000000000 : ℝ) := by
    have hpowers : (7017/50000 : ℝ)^2073 ≤ (3524393236145551/10000000000000000000 : ℝ)^512 := by
      have hnat : (7017 : ℕ)^2073*10000000000000000000^512 ≤ 3524393236145551^512*50000^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7017 50000 3524393236145551 10000000000000000000 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7017/50000 : ℝ)) (X := (3524393236145551/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014595166961767181/50000000000000000000 : ℝ) ≤ (10000720878373723/10000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (50014595166961767181/50000000000000000000 : ℝ)^512 ≤ (10000720878373723/10000000000000000 : ℝ)^2073 := by
      have hnat : (50014595166961767181 : ℕ)^512*10000000000000000^2073 ≤ 10000720878373723^2073*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014595166961767181 50000000000000000000 10000720878373723 10000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000720878373723/10000000000000000 : ℝ)) (X := (50014595166961767181/50000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049839099323222691/100000000000000000000 : ℝ) ≤ (400049228812193/400000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (100049839099323222691/100000000000000000000 : ℝ)^512 ≤ (400049228812193/400000000000000 : ℝ)^2073 := by
      have hnat : (100049839099323222691 : ℕ)^512*400000000000000^2073 ≤ 400049228812193^2073*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049839099323222691 100000000000000000000 400049228812193 400000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400049228812193/400000000000000 : ℝ)) (X := (100049839099323222691/100000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003524393236145551/5000000000000000000 : ℝ) ≤ (10001740562235927/10000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (5003524393236145551/5000000000000000000 : ℝ)^512 ≤ (10001740562235927/10000000000000000 : ℝ)^2073 := by
      have hnat : (5003524393236145551 : ℕ)^512*10000000000000000^2073 ≤ 10001740562235927^2073*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003524393236145551 5000000000000000000 10001740562235927 10000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001740562235927/10000000000000000 : ℝ)) (X := (5003524393236145551/5000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14595166961767181/100000000000000000000 : ℝ) ≤ ((13725234670288842303/13730000000000000000 : ℝ)+2*(254920965551/137300000000000 : ℝ)*(1411/12500 : ℝ))^(2073/512 : ℝ) := by
    rw [show (13725234670288842303/13730000000000000000 : ℝ)+2*(254920965551/137300000000000 : ℝ)*(1411/12500 : ℝ)=(10000720878373723/10000000000000000 : ℝ) by norm_num, show 1+2*(14595166961767181/100000000000000000000 : ℝ)=(50014595166961767181/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3524393236145551/10000000000000000000 : ℝ)+(14595166961767181/100000000000000000000 : ℝ) ≤ ((13725234670288842303/13730000000000000000 : ℝ)+(254920965551/137300000000000 : ℝ)*((7017/50000 : ℝ)+(1411/12500 : ℝ)))^(2073/512 : ℝ) := by
    rw [show (13725234670288842303/13730000000000000000 : ℝ)+(254920965551/137300000000000 : ℝ)*((7017/50000 : ℝ)+(1411/12500 : ℝ))=(400049228812193/400000000000000 : ℝ) by norm_num, show 1+(3524393236145551/10000000000000000000 : ℝ)+(14595166961767181/100000000000000000000 : ℝ)=(100049839099323222691/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3524393236145551/10000000000000000000 : ℝ) ≤ ((13725234670288842303/13730000000000000000 : ℝ)+2*(254920965551/137300000000000 : ℝ)*(7017/50000 : ℝ))^(2073/512 : ℝ) := by
    rw [show (13725234670288842303/13730000000000000000 : ℝ)+2*(254920965551/137300000000000 : ℝ)*(7017/50000 : ℝ)=(10001740562235927/10000000000000000 : ℝ) by norm_num, show 1+2*(3524393236145551/10000000000000000000 : ℝ)=(5003524393236145551/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13725234670288842303/13730000000000000000 : ℝ)*(X 1 0+X 2 0)+(254920965551/137300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (1411/12500 : ℝ)) (hi := (7017/50000 : ℝ)) (c := (13725234670288842303/13730000000000000000 : ℝ)) (alpha := (254920965551/137300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13725234670288842303/13730000000000000000 : ℝ)*(X 0 1+X 2 1)+(254920965551/137300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (1411/12500 : ℝ)) (hi := (7017/50000 : ℝ)) (c := (13725234670288842303/13730000000000000000 : ℝ)) (alpha := (254920965551/137300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13725234670288842303/13730000000000000000 : ℝ)*(X 0 2+X 1 2)+(254920965551/137300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (1411/12500 : ℝ)) (hi := (7017/50000 : ℝ)) (c := (13725234670288842303/13730000000000000000 : ℝ)) (alpha := (254920965551/137300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1093564611/5000000000 : ℝ)*X 0 0+(2696918333/5000000000 : ℝ)*X 0 1+(1052997447/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344909449/10000000000 : ℝ)*X 1 0+(-563123869/2500000000 : ℝ)*X 1 1+(2632493681/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068981951/2000000000 : ℝ)*X 2 0+(5264987153/10000000000 : ℝ)*X 2 1+(-2252495347/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2185310649/5000000000 : ℝ)*X 0 0+(1061340709/2500000000 : ℝ)*X 0 1+(4499594931/10000000000 : ℝ)*X 0 2+(2185310649/5000000000 : ℝ)*X 1 0+(1061340709/2500000000 : ℝ)*X 1 1+(4499594931/10000000000 : ℝ)*X 1 2+(2185310649/5000000000 : ℝ)*X 2 0+(1061340709/2500000000 : ℝ)*X 2 1+(4499594931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-437426869/2000000000 : ℝ)*X 0 0+(1053062157/2000000000 : ℝ)*X 0 1+(2696755927/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531236841/1000000000 : ℝ)*X 1 0+(-212397093/1000000000 : ℝ)*X 1 1+(5393511853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312368411/10000000000 : ℝ)*X 2 0+(1348377963/2500000000 : ℝ)*X 2 1+(-2123970929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4370631061/10000000000 : ℝ)*X 0 0+(56236959/125000000 : ℝ)*X 0 1+(530750431/1250000000 : ℝ)*X 0 2+(4370631061/10000000000 : ℝ)*X 1 0+(56236959/125000000 : ℝ)*X 1 1+(530750431/1250000000 : ℝ)*X 1 2+(4370631061/10000000000 : ℝ)*X 2 0+(56236959/125000000 : ℝ)*X 2 1+(530750431/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (745083837451043940059890479/85812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (909593291/50000000000000 : ℝ)*(base19) + (472266903/25000000000000 : ℝ)*(base23) + (200139223/100000000000000 : ℝ)*(lower2) + (28047993/20000000000000 : ℝ)*(upper3) + (75547857/50000000000000 : ℝ)*(upper5) + (730911186781077/12500000000000 : ℝ)*(major0) + (730911186781077/12500000000000 : ℝ)*(major1) + (730911186781077/12500000000000 : ℝ)*(major2) + (7761049226173073/100000000000000 : ℝ)*(sp0) + (776111118568657/10000000000000 : ℝ)*(sp1) + (7761111115805541/100000000000000 : ℝ)*(sp2) + (3933437550486987/100000000000000 : ℝ)*(sp3) + (797233751/1250000000000 : ℝ)*(sp4) + (879491059/3125000000000 : ℝ)*(sp7) + (31467725553607/800000000000 : ℝ)*(f.failure) + (121267390701143/1562500000000 : ℝ)*(f.sum) + (3048458884037/858125000000000000000000000 : ℝ)*base65 + (1088512792273549669/171625000000000000000000000000000 : ℝ)*base68 + (509728123858299669/171625000000000000000000000000000 : ℝ)*base70 + (564700302663799669/171625000000000000000000000000000 : ℝ)*base72 + (8201816555409/1716250000000000000000000000 : ℝ)*base73 + (4784333108313924669/171625000000000000000000000000000 : ℝ)*base76 + (432300629766924669/171625000000000000000000000000000 : ℝ)*base78 + (3851256073325424669/171625000000000000000000000000000 : ℝ)*base80 + (5541869673197/3432500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (4243/800000000000000000 : ℝ)*base89 + (4243/800000000000000000 : ℝ)*base91 + (4243/800000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3674331308798409681515850219/343250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1966655867/100000000000000 : ℝ)*(base19) + (2142243831/100000000000000 : ℝ)*(base23) + (8548377/4000000000000 : ℝ)*(upper3) + (19778569/25000000000000 : ℝ)*(lower4) + (108910569/50000000000000 : ℝ)*(upper5) + (2938386025588803/50000000000000 : ℝ)*(major0) + (2938386025588803/50000000000000 : ℝ)*(major1) + (2938386025588803/50000000000000 : ℝ)*(major2) + (53798948351/100000000000000 : ℝ)*(sp1) + (289557589/500000000000 : ℝ)*(sp2) + (1560049033056733/20000000000000 : ℝ)*(sp4) + (3900094699839723/50000000000000 : ℝ)*(sp5) + (1560037022304407/20000000000000 : ℝ)*(sp6) + (988324645063433/25000000000000 : ℝ)*(sp7) + (988324645063433/25000000000000 : ℝ)*(f.failure) + (1560049033056733/20000000000000 : ℝ)*(f.sum) + (2536780417551/6865000000000000000000000000 : ℝ)*base65 + (5574454415712333309/686500000000000000000000000000000 : ℝ)*base67 + (6833339730555833309/686500000000000000000000000000000 : ℝ)*base69 + (9577001329633333309/686500000000000000000000000000000 : ℝ)*base71 + (2601475361127/3432500000000000000000000000 : ℝ)*base74 + (15855907223520833309/686500000000000000000000000000000 : ℝ)*base75 + (5210170761434333309/686500000000000000000000000000000 : ℝ)*base77 + (1212670124344833309/686500000000000000000000000000000 : ℝ)*base79 + (27629209464741/6865000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (237283/25000000000000000000 : ℝ)*base90 + (237283/25000000000000000000 : ℝ)*base92 + (237283/25000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1100_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1411/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7013/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1100_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1100_s8_0 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-17497083/80000000 : ℝ)*x 0 + (67421921/125000000 : ℝ)*x 1 + (5265066267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17497083/80000000 : ℝ)^8293 ≤ (13285959881069/100000000000000 : ℝ)^6245 := by
    have hnat : (17497083 : ℕ)^8293*100000000000000^6245 ≤ 13285959881069^6245*80000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17497083 80000000 13285959881069 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67421921/125000000 : ℝ)^8293 ≤ (8810424711717/20000000000000 : ℝ)^6245 := by
    have hnat : (67421921 : ℕ)^8293*20000000000000^6245 ≤ 8810424711717^6245*125000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67421921 125000000 8810424711717 20000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265066267/10000000000 : ℝ)^8293 ≤ (42661916535319/100000000000000 : ℝ)^6245 := by
    have hnat : (5265066267 : ℕ)^8293*100000000000000^6245 ≤ 42661916535319^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265066267 10000000000 42661916535319 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17497083/80000000 : ℝ), (67421921/125000000 : ℝ), (5265066267/10000000000 : ℝ)] ![(13285959881069/100000000000000 : ℝ), (8810424711717/20000000000000 : ℝ), (42661916535319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17497083/80000000 : ℝ)|^8293 ≤ (13285959881069/100000000000000 : ℝ)^6245
        have hw : |(-17497083/80000000 : ℝ)|=(17497083/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67421921/125000000 : ℝ)|^8293 ≤ (8810424711717/20000000000000 : ℝ)^6245
        have hw : |(67421921/125000000 : ℝ)|=(67421921/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265066267/10000000000 : ℝ)|^8293 ≤ (42661916535319/100000000000000 : ℝ)^6245
        have hw : |(5265066267/10000000000 : ℝ)|=(5265066267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s8_1 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334055569/625000000 : ℝ)*x 0 + (-2252418247/10000000000 : ℝ)*x 1 + (1316266567/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334055569/625000000 : ℝ)^8293 ≤ (43522945096867/100000000000000 : ℝ)^6245 := by
    have hnat : (334055569 : ℕ)^8293*100000000000000^6245 ≤ 43522945096867^6245*625000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334055569 625000000 43522945096867 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252418247/10000000000 : ℝ)^8293 ≤ (2763027669073/20000000000000 : ℝ)^6245 := by
    have hnat : (2252418247 : ℕ)^8293*20000000000000^6245 ≤ 2763027669073^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252418247 10000000000 2763027669073 20000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316266567/2500000000 : ℝ)^8293 ≤ (42661916546079/100000000000000 : ℝ)^6245 := by
    have hnat : (1316266567 : ℕ)^8293*100000000000000^6245 ≤ 42661916546079^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316266567 2500000000 42661916546079 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334055569/625000000 : ℝ), (-2252418247/10000000000 : ℝ), (1316266567/2500000000 : ℝ)] ![(43522945096867/100000000000000 : ℝ), (2763027669073/20000000000000 : ℝ), (42661916546079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334055569/625000000 : ℝ)|^8293 ≤ (43522945096867/100000000000000 : ℝ)^6245
        have hw : |(334055569/625000000 : ℝ)|=(334055569/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2252418247/10000000000 : ℝ)|^8293 ≤ (2763027669073/20000000000000 : ℝ)^6245
        have hw : |(-2252418247/10000000000 : ℝ)|=(2252418247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316266567/2500000000 : ℝ)|^8293 ≤ (42661916546079/100000000000000 : ℝ)^6245
        have hw : |(1316266567/2500000000 : ℝ)|=(1316266567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s8_2 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672444551/5000000000 : ℝ)*x 0 + (1316266567/2500000000 : ℝ)*x 1 + (-2252418249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672444551/5000000000 : ℝ)^8293 ≤ (43522945075241/100000000000000 : ℝ)^6245 := by
    have hnat : (2672444551 : ℕ)^8293*100000000000000^6245 ≤ 43522945075241^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672444551 5000000000 43522945075241 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316266567/2500000000 : ℝ)^8293 ≤ (42661916546079/100000000000000 : ℝ)^6245 := by
    have hnat : (1316266567 : ℕ)^8293*100000000000000^6245 ≤ 42661916546079^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316266567 2500000000 42661916546079 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252418249/10000000000 : ℝ)^8293 ≤ (2763027672331/20000000000000 : ℝ)^6245 := by
    have hnat : (2252418249 : ℕ)^8293*20000000000000^6245 ≤ 2763027672331^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252418249 10000000000 2763027672331 20000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672444551/5000000000 : ℝ), (1316266567/2500000000 : ℝ), (-2252418249/10000000000 : ℝ)] ![(43522945075241/100000000000000 : ℝ), (42661916546079/100000000000000 : ℝ), (2763027672331/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672444551/5000000000 : ℝ)|^8293 ≤ (43522945075241/100000000000000 : ℝ)^6245
        have hw : |(2672444551/5000000000 : ℝ)|=(2672444551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316266567/2500000000 : ℝ)|^8293 ≤ (42661916546079/100000000000000 : ℝ)^6245
        have hw : |(1316266567/2500000000 : ℝ)|=(1316266567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2252418249/10000000000 : ℝ)|^8293 ≤ (2763027672331/20000000000000 : ℝ)^6245
        have hw : |(-2252418249/10000000000 : ℝ)|=(2252418249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s8_3 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370625321/10000000000 : ℝ)*x 0 + (849104391/2000000000 : ℝ)*x 1 + (4499434831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370625321/10000000000 : ℝ)^8293 ≤ (4164593387037/12500000000000 : ℝ)^6245 := by
    have hnat : (4370625321 : ℕ)^8293*12500000000000^6245 ≤ 4164593387037^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370625321 10000000000 4164593387037 12500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849104391/2000000000 : ℝ)^8293 ≤ (8014085029431/25000000000000 : ℝ)^6245 := by
    have hnat : (849104391 : ℕ)^8293*25000000000000^6245 ≤ 8014085029431^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849104391 2000000000 8014085029431 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499434831/10000000000 : ℝ)^8293 ≤ (17313456384249/50000000000000 : ℝ)^6245 := by
    have hnat : (4499434831 : ℕ)^8293*50000000000000^6245 ≤ 17313456384249^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499434831 10000000000 17313456384249 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370625321/10000000000 : ℝ), (849104391/2000000000 : ℝ), (4499434831/10000000000 : ℝ)] ![(4164593387037/12500000000000 : ℝ), (8014085029431/25000000000000 : ℝ), (17313456384249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370625321/10000000000 : ℝ)|^8293 ≤ (4164593387037/12500000000000 : ℝ)^6245
        have hw : |(4370625321/10000000000 : ℝ)|=(4370625321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(849104391/2000000000 : ℝ)|^8293 ≤ (8014085029431/25000000000000 : ℝ)^6245
        have hw : |(849104391/2000000000 : ℝ)|=(849104391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499434831/10000000000 : ℝ)|^8293 ≤ (17313456384249/50000000000000 : ℝ)^6245
        have hw : |(4499434831/10000000000 : ℝ)|=(4499434831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s8_4 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1093570191/5000000000 : ℝ)*x 0 + (5265388913/10000000000 : ℝ)*x 1 + (107868597/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093570191/5000000000 : ℝ)^8293 ≤ (2657200054221/20000000000000 : ℝ)^6245 := by
    have hnat : (1093570191 : ℕ)^8293*20000000000000^6245 ≤ 2657200054221^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093570191 5000000000 2657200054221 20000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265388913/10000000000 : ℝ)^8293 ≤ (2666586766807/6250000000000 : ℝ)^6245 := by
    have hnat : (5265388913 : ℕ)^8293*6250000000000^6245 ≤ 2666586766807^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265388913 10000000000 2666586766807 6250000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107868597/200000000 : ℝ)^8293 ≤ (22024305725681/50000000000000 : ℝ)^6245 := by
    have hnat : (107868597 : ℕ)^8293*50000000000000^6245 ≤ 22024305725681^6245*200000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107868597 200000000 22024305725681 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1093570191/5000000000 : ℝ), (5265388913/10000000000 : ℝ), (107868597/200000000 : ℝ)] ![(2657200054221/20000000000000 : ℝ), (2666586766807/6250000000000 : ℝ), (22024305725681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1093570191/5000000000 : ℝ)|^8293 ≤ (2657200054221/20000000000000 : ℝ)^6245
        have hw : |(-1093570191/5000000000 : ℝ)|=(1093570191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265388913/10000000000 : ℝ)|^8293 ≤ (2666586766807/6250000000000 : ℝ)^6245
        have hw : |(5265388913/10000000000 : ℝ)|=(5265388913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107868597/200000000 : ℝ)|^8293 ≤ (22024305725681/50000000000000 : ℝ)^6245
        have hw : |(107868597/200000000 : ℝ)|=(107868597/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s8_5 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312388921/10000000000 : ℝ)*x 0 + (-212405447/1000000000 : ℝ)*x 1 + (53934299/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312388921/10000000000 : ℝ)^8293 ≤ (21585930649941/50000000000000 : ℝ)^6245 := by
    have hnat : (5312388921 : ℕ)^8293*50000000000000^6245 ≤ 21585930649941^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312388921 10000000000 21585930649941 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212405447/1000000000 : ℝ)^8293 ≤ (12779526684779/100000000000000 : ℝ)^6245 := by
    have hnat : (212405447 : ℕ)^8293*100000000000000^6245 ≤ 12779526684779^6245*1000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212405447 1000000000 12779526684779 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53934299/100000000 : ℝ)^8293 ≤ (44048611993633/100000000000000 : ℝ)^6245 := by
    have hnat : (53934299 : ℕ)^8293*100000000000000^6245 ≤ 44048611993633^6245*100000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53934299 100000000 44048611993633 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312388921/10000000000 : ℝ), (-212405447/1000000000 : ℝ), (53934299/100000000 : ℝ)] ![(21585930649941/50000000000000 : ℝ), (12779526684779/100000000000000 : ℝ), (44048611993633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312388921/10000000000 : ℝ)|^8293 ≤ (21585930649941/50000000000000 : ℝ)^6245
        have hw : |(5312388921/10000000000 : ℝ)|=(5312388921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212405447/1000000000 : ℝ)|^8293 ≤ (12779526684779/100000000000000 : ℝ)^6245
        have hw : |(-212405447/1000000000 : ℝ)|=(212405447/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53934299/100000000 : ℝ)|^8293 ≤ (44048611993633/100000000000000 : ℝ)^6245
        have hw : |(53934299/100000000 : ℝ)|=(53934299/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s8_6 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312388621/10000000000 : ℝ)*x 0 + (2696714957/5000000000 : ℝ)*x 1 + (-2124054857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312388621/10000000000 : ℝ)^8293 ≤ (4317185806237/10000000000000 : ℝ)^6245 := by
    have hnat : (5312388621 : ℕ)^8293*10000000000000^6245 ≤ 4317185806237^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312388621 10000000000 4317185806237 10000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696714957/5000000000 : ℝ)^8293 ≤ (44048612145469/100000000000000 : ℝ)^6245 := by
    have hnat : (2696714957 : ℕ)^8293*100000000000000^6245 ≤ 44048612145469^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696714957 5000000000 44048612145469 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124054857/10000000000 : ℝ)^8293 ≤ (6389764888389/50000000000000 : ℝ)^6245 := by
    have hnat : (2124054857 : ℕ)^8293*50000000000000^6245 ≤ 6389764888389^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124054857 10000000000 6389764888389 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312388621/10000000000 : ℝ), (2696714957/5000000000 : ℝ), (-2124054857/10000000000 : ℝ)] ![(4317185806237/10000000000000 : ℝ), (44048612145469/100000000000000 : ℝ), (6389764888389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312388621/10000000000 : ℝ)|^8293 ≤ (4317185806237/10000000000000 : ℝ)^6245
        have hw : |(5312388621/10000000000 : ℝ)|=(5312388621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696714957/5000000000 : ℝ)|^8293 ≤ (44048612145469/100000000000000 : ℝ)^6245
        have hw : |(2696714957/5000000000 : ℝ)|=(2696714957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2124054857/10000000000 : ℝ)|^8293 ≤ (6389764888389/50000000000000 : ℝ)^6245
        have hw : |(-2124054857/10000000000 : ℝ)|=(2124054857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s8_7 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2185317481/5000000000 : ℝ)*x 0 + (899759629/2000000000 : ℝ)*x 1 + (2123080561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185317481/5000000000 : ℝ)^8293 ≤ (16658422344851/50000000000000 : ℝ)^6245 := by
    have hnat : (2185317481 : ℕ)^8293*50000000000000^6245 ≤ 16658422344851^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185317481 5000000000 16658422344851 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899759629/2000000000 : ℝ)^8293 ≤ (34620406226269/100000000000000 : ℝ)^6245 := by
    have hnat : (899759629 : ℕ)^8293*100000000000000^6245 ≤ 34620406226269^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899759629 2000000000 34620406226269 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123080561/5000000000 : ℝ)^8293 ≤ (16031374535709/50000000000000 : ℝ)^6245 := by
    have hnat : (2123080561 : ℕ)^8293*50000000000000^6245 ≤ 16031374535709^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123080561 5000000000 16031374535709 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185317481/5000000000 : ℝ), (899759629/2000000000 : ℝ), (2123080561/5000000000 : ℝ)] ![(16658422344851/50000000000000 : ℝ), (34620406226269/100000000000000 : ℝ), (16031374535709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185317481/5000000000 : ℝ)|^8293 ≤ (16658422344851/50000000000000 : ℝ)^6245
        have hw : |(2185317481/5000000000 : ℝ)|=(2185317481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899759629/2000000000 : ℝ)|^8293 ≤ (34620406226269/100000000000000 : ℝ)^6245
        have hw : |(899759629/2000000000 : ℝ)|=(899759629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2123080561/5000000000 : ℝ)|^8293 ≤ (16031374535709/50000000000000 : ℝ)^6245
        have hw : |(2123080561/5000000000 : ℝ)|=(2123080561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1100_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7013/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (5649/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1753/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7013/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (353/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7013/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (353/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7013/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (353/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7013/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (353/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7013/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (353/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7013/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (353/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (353/3125 : ℝ) ^ (2073/512 : ℝ) ≤ (292741853715083/2000000000000000000 : ℝ) := by
    have hpowers : (353/3125 : ℝ)^2073 ≤ (292741853715083/2000000000000000000 : ℝ)^512 := by
      have hnat : (353 : ℕ)^2073*2000000000000000000^512 ≤ 292741853715083^512*3125^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        353 3125 292741853715083 2000000000000000000 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (353/3125 : ℝ)) (X := (292741853715083/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7013/50000 : ℝ) ^ (2073/512 : ℝ) ≤ (17581329819931001/50000000000000000000 : ℝ) := by
    have hpowers : (7013/50000 : ℝ)^2073 ≤ (17581329819931001/50000000000000000000 : ℝ)^512 := by
      have hnat : (7013 : ℕ)^2073*50000000000000000000^512 ≤ 17581329819931001^512*50000^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7013 50000 17581329819931001 50000000000000000000 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7013/50000 : ℝ)) (X := (17581329819931001/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000292741853715083/1000000000000000000 : ℝ) ≤ (2000144589784667/2000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (1000292741853715083/1000000000000000000 : ℝ)^512 ≤ (2000144589784667/2000000000000000 : ℝ)^2073 := by
      have hnat : (1000292741853715083 : ℕ)^512*2000000000000000^2073 ≤ 2000144589784667^2073*1000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000292741853715083 1000000000000000000 2000144589784667 2000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000144589784667/2000000000000000 : ℝ)) (X := (1000292741853715083/1000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506224969040702019/12500000000000000000 : ℝ) ≤ (5000614874428619/5000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (12506224969040702019/12500000000000000000 : ℝ)^512 ≤ (5000614874428619/5000000000000000 : ℝ)^2073 := by
      have hnat : (12506224969040702019 : ℕ)^512*5000000000000000^2073 ≤ 5000614874428619^2073*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506224969040702019 12500000000000000000 5000614874428619 5000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000614874428619/5000000000000000 : ℝ)) (X := (12506224969040702019/12500000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017581329819931001/25000000000000000000 : ℝ) ≤ (10001736548791141/10000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (25017581329819931001/25000000000000000000 : ℝ)^512 ≤ (10001736548791141/10000000000000000 : ℝ)^2073 := by
      have hnat : (25017581329819931001 : ℕ)^512*10000000000000000^2073 ≤ 10001736548791141^2073*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017581329819931001 25000000000000000000 10001736548791141 10000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001736548791141/10000000000000000 : ℝ)) (X := (25017581329819931001/25000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(292741853715083/2000000000000000000 : ℝ) ≤ ((4548420671075661329/4550000000000000000 : ℝ)+2*(168933311301/91000000000000 : ℝ)*(353/3125 : ℝ))^(2073/512 : ℝ) := by
    rw [show (4548420671075661329/4550000000000000000 : ℝ)+2*(168933311301/91000000000000 : ℝ)*(353/3125 : ℝ)=(2000144589784667/2000000000000000 : ℝ) by norm_num, show 1+2*(292741853715083/2000000000000000000 : ℝ)=(1000292741853715083/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17581329819931001/50000000000000000000 : ℝ)+(292741853715083/2000000000000000000 : ℝ) ≤ ((4548420671075661329/4550000000000000000 : ℝ)+(168933311301/91000000000000 : ℝ)*((7013/50000 : ℝ)+(353/3125 : ℝ)))^(2073/512 : ℝ) := by
    rw [show (4548420671075661329/4550000000000000000 : ℝ)+(168933311301/91000000000000 : ℝ)*((7013/50000 : ℝ)+(353/3125 : ℝ))=(5000614874428619/5000000000000000 : ℝ) by norm_num, show 1+(17581329819931001/50000000000000000000 : ℝ)+(292741853715083/2000000000000000000 : ℝ)=(12506224969040702019/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17581329819931001/50000000000000000000 : ℝ) ≤ ((4548420671075661329/4550000000000000000 : ℝ)+2*(168933311301/91000000000000 : ℝ)*(7013/50000 : ℝ))^(2073/512 : ℝ) := by
    rw [show (4548420671075661329/4550000000000000000 : ℝ)+2*(168933311301/91000000000000 : ℝ)*(7013/50000 : ℝ)=(10001736548791141/10000000000000000 : ℝ) by norm_num, show 1+2*(17581329819931001/50000000000000000000 : ℝ)=(25017581329819931001/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4548420671075661329/4550000000000000000 : ℝ)*(X 1 0+X 2 0)+(168933311301/91000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (353/3125 : ℝ)) (hi := (7013/50000 : ℝ)) (c := (4548420671075661329/4550000000000000000 : ℝ)) (alpha := (168933311301/91000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4548420671075661329/4550000000000000000 : ℝ)*(X 0 1+X 2 1)+(168933311301/91000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (353/3125 : ℝ)) (hi := (7013/50000 : ℝ)) (c := (4548420671075661329/4550000000000000000 : ℝ)) (alpha := (168933311301/91000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4548420671075661329/4550000000000000000 : ℝ)*(X 0 2+X 1 2)+(168933311301/91000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (353/3125 : ℝ)) (hi := (7013/50000 : ℝ)) (c := (4548420671075661329/4550000000000000000 : ℝ)) (alpha := (168933311301/91000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-17497083/80000000 : ℝ)*X 0 0+(67421921/125000000 : ℝ)*X 0 1+(5265066267/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334055569/625000000 : ℝ)*X 1 0+(-2252418247/10000000000 : ℝ)*X 1 1+(1316266567/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672444551/5000000000 : ℝ)*X 2 0+(1316266567/2500000000 : ℝ)*X 2 1+(-2252418249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4370625321/10000000000 : ℝ)*X 0 0+(849104391/2000000000 : ℝ)*X 0 1+(4499434831/10000000000 : ℝ)*X 0 2+(4370625321/10000000000 : ℝ)*X 1 0+(849104391/2000000000 : ℝ)*X 1 1+(4499434831/10000000000 : ℝ)*X 1 2+(4370625321/10000000000 : ℝ)*X 2 0+(849104391/2000000000 : ℝ)*X 2 1+(4499434831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1093570191/5000000000 : ℝ)*X 0 0+(5265388913/10000000000 : ℝ)*X 0 1+(107868597/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312388921/10000000000 : ℝ)*X 1 0+(-212405447/1000000000 : ℝ)*X 1 1+(53934299/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312388621/10000000000 : ℝ)*X 2 0+(2696714957/5000000000 : ℝ)*X 2 1+(-2124054857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2185317481/5000000000 : ℝ)*X 0 0+(899759629/2000000000 : ℝ)*X 0 1+(2123080561/5000000000 : ℝ)*X 0 2+(2185317481/5000000000 : ℝ)*X 1 0+(899759629/2000000000 : ℝ)*X 1 1+(2123080561/5000000000 : ℝ)*X 1 2+(2185317481/5000000000 : ℝ)*X 2 0+(899759629/2000000000 : ℝ)*X 2 1+(2123080561/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6702600455210140487803677/1093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (122684977/10000000000000 : ℝ)*(base19) + (71370999/6250000000000 : ℝ)*(base23) + (43831311/100000000000000 : ℝ)*(lower2) + (78564961/50000000000000 : ℝ)*(upper3) + (92069281/100000000000000 : ℝ)*(upper5) + (731826821502177/12500000000000 : ℝ)*(major0) + (731826821502177/12500000000000 : ℝ)*(major1) + (731826821502177/12500000000000 : ℝ)*(major2) + (7770802598992061/100000000000000 : ℝ)*(sp0) + (7770834446351347/100000000000000 : ℝ)*(sp1) + (7770834531265133/100000000000000 : ℝ)*(sp2) + (492296886842483/12500000000000 : ℝ)*(sp3) + (6614841811/20000000000000 : ℝ)*(sp4) + (3634364823/20000000000000 : ℝ)*(sp7) + (3938393266563979/100000000000000 : ℝ)*(f.failure) + (7770835673201117/100000000000000 : ℝ)*(f.sum) + (474572093367/2275000000000000000000000000 : ℝ)*base66 + (496034135983313233/56875000000000000000000000000000 : ℝ)*base67 + (848298800951438233/56875000000000000000000000000000 : ℝ)*base69 + (185320006575813233/56875000000000000000000000000000 : ℝ)*base71 + (141467593271/1137500000000000000000000000 : ℝ)*base74 + (744964606408313233/56875000000000000000000000000000 : ℝ)*base75 + (725162862514563233/56875000000000000000000000000000 : ℝ)*base77 + (378253593616061767/56875000000000000000000000000000 : ℝ)*base80 + (10238553156567/2275000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (418471/100000000000000000000 : ℝ)*base89 + (418471/100000000000000000000 : ℝ)*base91 + (418471/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20070919187326269908673/2275000000000000000000000000 : ℝ) := by norm_num
    linear_combination (428368227/25000000000000 : ℝ)*(base19) + (287112153/25000000000000 : ℝ)*(base23) + (172631171/50000000000000 : ℝ)*(lower1) + (30856429/100000000000000 : ℝ)*(upper2) + (50551091/50000000000000 : ℝ)*(upper3) + (203553167/100000000000000 : ℝ)*(upper5) + (91939077289987/1562500000000 : ℝ)*(major0) + (91939077289987/1562500000000 : ℝ)*(major1) + (91939077289987/1562500000000 : ℝ)*(major2) + (7439970293/25000000000000 : ℝ)*(sp1) + (1561994575663573/20000000000000 : ℝ)*(sp4) + (976242675620473/12500000000000 : ℝ)*(sp5) + (1952492932467313/25000000000000 : ℝ)*(sp6) + (1979114360360529/50000000000000 : ℝ)*(sp7) + (1979114360360529/50000000000000 : ℝ)*(f.failure) + (1561994575663573/20000000000000 : ℝ)*(f.sum) + (2458764964433/1137500000000000000000000000 : ℝ)*base66 + (5458042812645201/3554687500000000000000000000000 : ℝ)*base68 + (233174997612131473/7109375000000000000000000000000 : ℝ)*base69 + (4431970153649777/7109375000000000000000000000000 : ℝ)*base72 + (198353044567/1137500000000000000000000000 : ℝ)*base73 + (30209611081975223/7109375000000000000000000000000 : ℝ)*base75 + (16489537413537723/7109375000000000000000000000000 : ℝ)*base77 + (128823460316931027/7109375000000000000000000000000 : ℝ)*base80 + (487145103703/17773437500000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (24421/50000000000000000000 : ℝ)*base89 + (24421/50000000000000000000 : ℝ)*base91 + (24421/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1100_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7013/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1100_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1100_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2813/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1100_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1100_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1100_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2813/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1100_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

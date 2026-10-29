-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1502_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:52:25.990951+00:00
-- url     : https://prove2.me/submissions/6a1a4a5f-c02f-4a2d-9891-a1b967370fc9

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
theorem support_rectangle_w1502_s0_0 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1696491531/10000000000 : ℝ)*x 0 + (5920569507/10000000000 : ℝ)*x 1 + (4851016819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1696491531/10000000000 : ℝ)^4501 ≤ (10061192610941/100000000000000 : ℝ)^3477 := by
    have hnat : (1696491531 : ℕ)^4501*100000000000000^3477 ≤ 10061192610941^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1696491531 10000000000 10061192610941 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5920569507/10000000000 : ℝ)^4501 ≤ (6342098817909/12500000000000 : ℝ)^3477 := by
    have hnat : (5920569507 : ℕ)^4501*12500000000000^3477 ≤ 6342098817909^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5920569507 10000000000 6342098817909 12500000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4851016819/10000000000 : ℝ)^4501 ≤ (122506302607/312500000000 : ℝ)^3477 := by
    have hnat : (4851016819 : ℕ)^4501*312500000000^3477 ≤ 122506302607^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4851016819 10000000000 122506302607 312500000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1696491531/10000000000 : ℝ), (5920569507/10000000000 : ℝ), (4851016819/10000000000 : ℝ)] ![(10061192610941/100000000000000 : ℝ), (6342098817909/12500000000000 : ℝ), (122506302607/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1696491531/10000000000 : ℝ)|^4501 ≤ (10061192610941/100000000000000 : ℝ)^3477
        have hw : |(-1696491531/10000000000 : ℝ)|=(1696491531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5920569507/10000000000 : ℝ)|^4501 ≤ (6342098817909/12500000000000 : ℝ)^3477
        have hw : |(5920569507/10000000000 : ℝ)|=(5920569507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4851016819/10000000000 : ℝ)|^4501 ≤ (122506302607/312500000000 : ℝ)^3477
        have hw : |(4851016819/10000000000 : ℝ)|=(4851016819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s0_1 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1370039873/2500000000 : ℝ)*x 0 + (-2296773267/10000000000 : ℝ)*x 1 + (970203359/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1370039873/2500000000 : ℝ)^4501 ≤ (2295281910507/5000000000000 : ℝ)^3477 := by
    have hnat : (1370039873 : ℕ)^4501*5000000000000^3477 ≤ 2295281910507^3477*2500000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370039873 2500000000 2295281910507 5000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2296773267/10000000000 : ℝ)^4501 ≤ (7446172596759/50000000000000 : ℝ)^3477 := by
    have hnat : (2296773267 : ℕ)^4501*50000000000000^3477 ≤ 7446172596759^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296773267 10000000000 7446172596759 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (970203359/2000000000 : ℝ)^4501 ≤ (9800504145793/25000000000000 : ℝ)^3477 := by
    have hnat : (970203359 : ℕ)^4501*25000000000000^3477 ≤ 9800504145793^3477*2000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970203359 2000000000 9800504145793 25000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1370039873/2500000000 : ℝ), (-2296773267/10000000000 : ℝ), (970203359/2000000000 : ℝ)] ![(2295281910507/5000000000000 : ℝ), (7446172596759/50000000000000 : ℝ), (9800504145793/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1370039873/2500000000 : ℝ)|^4501 ≤ (2295281910507/5000000000000 : ℝ)^3477
        have hw : |(1370039873/2500000000 : ℝ)|=(1370039873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2296773267/10000000000 : ℝ)|^4501 ≤ (7446172596759/50000000000000 : ℝ)^3477
        have hw : |(-2296773267/10000000000 : ℝ)|=(2296773267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(970203359/2000000000 : ℝ)|^4501 ≤ (9800504145793/25000000000000 : ℝ)^3477
        have hw : |(970203359/2000000000 : ℝ)|=(970203359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s0_2 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2740079757/5000000000 : ℝ)*x 0 + (1212754199/2500000000 : ℝ)*x 1 + (-2296773237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2740079757/5000000000 : ℝ)^4501 ≤ (45905638448701/100000000000000 : ℝ)^3477 := by
    have hnat : (2740079757 : ℕ)^4501*100000000000000^3477 ≤ 45905638448701^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740079757 5000000000 45905638448701 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1212754199/2500000000 : ℝ)^4501 ≤ (39202016593633/100000000000000 : ℝ)^3477 := by
    have hnat : (1212754199 : ℕ)^4501*100000000000000^3477 ≤ 39202016593633^3477*2500000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1212754199 2500000000 39202016593633 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2296773237/10000000000 : ℝ)^4501 ≤ (14892344941709/100000000000000 : ℝ)^3477 := by
    have hnat : (2296773237 : ℕ)^4501*100000000000000^3477 ≤ 14892344941709^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296773237 10000000000 14892344941709 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2740079757/5000000000 : ℝ), (1212754199/2500000000 : ℝ), (-2296773237/10000000000 : ℝ)] ![(45905638448701/100000000000000 : ℝ), (39202016593633/100000000000000 : ℝ), (14892344941709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2740079757/5000000000 : ℝ)|^4501 ≤ (45905638448701/100000000000000 : ℝ)^3477
        have hw : |(2740079757/5000000000 : ℝ)|=(2740079757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1212754199/2500000000 : ℝ)|^4501 ≤ (39202016593633/100000000000000 : ℝ)^3477
        have hw : |(1212754199/2500000000 : ℝ)|=(1212754199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2296773237/10000000000 : ℝ)|^4501 ≤ (14892344941709/100000000000000 : ℝ)^3477
        have hw : |(-2296773237/10000000000 : ℝ)|=(2296773237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s0_3 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4147851117/10000000000 : ℝ)*x 0 + (1545616577/5000000000 : ℝ)*x 1 + (5499454937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4147851117/10000000000 : ℝ)^4501 ≤ (16004403831683/50000000000000 : ℝ)^3477 := by
    have hnat : (4147851117 : ℕ)^4501*50000000000000^3477 ≤ 16004403831683^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147851117 10000000000 16004403831683 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1545616577/5000000000 : ℝ)^4501 ≤ (10938105931251/50000000000000 : ℝ)^3477 := by
    have hnat : (1545616577 : ℕ)^4501*50000000000000^3477 ≤ 10938105931251^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1545616577 5000000000 10938105931251 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5499454937/10000000000 : ℝ)^4501 ≤ (46114980455753/100000000000000 : ℝ)^3477 := by
    have hnat : (5499454937 : ℕ)^4501*100000000000000^3477 ≤ 46114980455753^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499454937 10000000000 46114980455753 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4147851117/10000000000 : ℝ), (1545616577/5000000000 : ℝ), (5499454937/10000000000 : ℝ)] ![(16004403831683/50000000000000 : ℝ), (10938105931251/50000000000000 : ℝ), (46114980455753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4147851117/10000000000 : ℝ)|^4501 ≤ (16004403831683/50000000000000 : ℝ)^3477
        have hw : |(4147851117/10000000000 : ℝ)|=(4147851117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1545616577/5000000000 : ℝ)|^4501 ≤ (10938105931251/50000000000000 : ℝ)^3477
        have hw : |(1545616577/5000000000 : ℝ)|=(1545616577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5499454937/10000000000 : ℝ)|^4501 ≤ (46114980455753/100000000000000 : ℝ)^3477
        have hw : |(5499454937/10000000000 : ℝ)|=(5499454937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s0_4 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1700098181/10000000000 : ℝ)*x 0 + (4878349243/10000000000 : ℝ)*x 1 + (1473064171/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1700098181/10000000000 : ℝ)^4501 ≤ (10088890199303/100000000000000 : ℝ)^3477 := by
    have hnat : (1700098181 : ℕ)^4501*100000000000000^3477 ≤ 10088890199303^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1700098181 10000000000 10088890199303 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4878349243/10000000000 : ℝ)^4501 ≤ (39488182682061/100000000000000 : ℝ)^3477 := by
    have hnat : (4878349243 : ℕ)^4501*100000000000000^3477 ≤ 39488182682061^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4878349243 10000000000 39488182682061 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1473064171/2500000000 : ℝ)^4501 ≤ (25211463552233/50000000000000 : ℝ)^3477 := by
    have hnat : (1473064171 : ℕ)^4501*50000000000000^3477 ≤ 25211463552233^3477*2500000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1473064171 2500000000 25211463552233 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1700098181/10000000000 : ℝ), (4878349243/10000000000 : ℝ), (1473064171/2500000000 : ℝ)] ![(10088890199303/100000000000000 : ℝ), (39488182682061/100000000000000 : ℝ), (25211463552233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1700098181/10000000000 : ℝ)|^4501 ≤ (10088890199303/100000000000000 : ℝ)^3477
        have hw : |(-1700098181/10000000000 : ℝ)|=(1700098181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4878349243/10000000000 : ℝ)|^4501 ≤ (39488182682061/100000000000000 : ℝ)^3477
        have hw : |(4878349243/10000000000 : ℝ)|=(4878349243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1473064171/2500000000 : ℝ)|^4501 ≤ (25211463552233/50000000000000 : ℝ)^3477
        have hw : |(1473064171/2500000000 : ℝ)|=(1473064171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s0_5 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (648499303/1250000000 : ℝ)*x 0 + (-627766863/5000000000 : ℝ)*x 1 + (294612823/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (648499303/1250000000 : ℝ)^4501 ≤ (42762681189357/100000000000000 : ℝ)^3477 := by
    have hnat : (648499303 : ℕ)^4501*100000000000000^3477 ≤ 42762681189357^3477*1250000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648499303 1250000000 42762681189357 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (627766863/5000000000 : ℝ)^4501 ≤ (851799271439/12500000000000 : ℝ)^3477 := by
    have hnat : (627766863 : ℕ)^4501*12500000000000^3477 ≤ 851799271439^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627766863 5000000000 851799271439 12500000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (294612823/500000000 : ℝ)^4501 ≤ (10084584924611/20000000000000 : ℝ)^3477 := by
    have hnat : (294612823 : ℕ)^4501*20000000000000^3477 ≤ 10084584924611^3477*500000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294612823 500000000 10084584924611 20000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(648499303/1250000000 : ℝ), (-627766863/5000000000 : ℝ), (294612823/500000000 : ℝ)] ![(42762681189357/100000000000000 : ℝ), (851799271439/12500000000000 : ℝ), (10084584924611/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(648499303/1250000000 : ℝ)|^4501 ≤ (42762681189357/100000000000000 : ℝ)^3477
        have hw : |(648499303/1250000000 : ℝ)|=(648499303/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-627766863/5000000000 : ℝ)|^4501 ≤ (851799271439/12500000000000 : ℝ)^3477
        have hw : |(-627766863/5000000000 : ℝ)|=(627766863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(294612823/500000000 : ℝ)|^4501 ≤ (10084584924611/20000000000000 : ℝ)^3477
        have hw : |(294612823/500000000 : ℝ)|=(294612823/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s0_6 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5187994509/10000000000 : ℝ)*x 0 + (5892256461/10000000000 : ℝ)*x 1 + (-251106719/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5187994509/10000000000 : ℝ)^4501 ≤ (42762682096319/100000000000000 : ℝ)^3477 := by
    have hnat : (5187994509 : ℕ)^4501*100000000000000^3477 ≤ 42762682096319^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187994509 10000000000 42762682096319 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5892256461/10000000000 : ℝ)^4501 ≤ (12605731158533/25000000000000 : ℝ)^3477 := by
    have hnat : (5892256461 : ℕ)^4501*25000000000000^3477 ≤ 12605731158533^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5892256461 10000000000 12605731158533 25000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251106719/2000000000 : ℝ)^4501 ≤ (6814393251117/100000000000000 : ℝ)^3477 := by
    have hnat : (251106719 : ℕ)^4501*100000000000000^3477 ≤ 6814393251117^3477*2000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251106719 2000000000 6814393251117 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5187994509/10000000000 : ℝ), (5892256461/10000000000 : ℝ), (-251106719/2000000000 : ℝ)] ![(42762682096319/100000000000000 : ℝ), (12605731158533/25000000000000 : ℝ), (6814393251117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5187994509/10000000000 : ℝ)|^4501 ≤ (42762682096319/100000000000000 : ℝ)^3477
        have hw : |(5187994509/10000000000 : ℝ)|=(5187994509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5892256461/10000000000 : ℝ)|^4501 ≤ (12605731158533/25000000000000 : ℝ)^3477
        have hw : |(5892256461/10000000000 : ℝ)|=(5892256461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-251106719/2000000000 : ℝ)|^4501 ≤ (6814393251117/100000000000000 : ℝ)^3477
        have hw : |(-251106719/2000000000 : ℝ)|=(251106719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s0_7 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4155971967/10000000000 : ℝ)*x 0 + (1087582573/2000000000 : ℝ)*x 1 + (1577491663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4155971967/10000000000 : ℝ)^4501 ≤ (3208995556229/10000000000000 : ℝ)^3477 := by
    have hnat : (4155971967 : ℕ)^4501*10000000000000^3477 ≤ 3208995556229^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155971967 10000000000 3208995556229 10000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087582573/2000000000 : ℝ)^4501 ≤ (4544804980161/10000000000000 : ℝ)^3477 := by
    have hnat : (1087582573 : ℕ)^4501*10000000000000^3477 ≤ 4544804980161^3477*2000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087582573 2000000000 4544804980161 10000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1577491663/5000000000 : ℝ)^4501 ≤ (11230997309073/50000000000000 : ℝ)^3477 := by
    have hnat : (1577491663 : ℕ)^4501*50000000000000^3477 ≤ 11230997309073^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577491663 5000000000 11230997309073 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4155971967/10000000000 : ℝ), (1087582573/2000000000 : ℝ), (1577491663/5000000000 : ℝ)] ![(3208995556229/10000000000000 : ℝ), (4544804980161/10000000000000 : ℝ), (11230997309073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4155971967/10000000000 : ℝ)|^4501 ≤ (3208995556229/10000000000000 : ℝ)^3477
        have hw : |(4155971967/10000000000 : ℝ)|=(4155971967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087582573/2000000000 : ℝ)|^4501 ≤ (4544804980161/10000000000000 : ℝ)^3477
        have hw : |(1087582573/2000000000 : ℝ)|=(1087582573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1577491663/5000000000 : ℝ)|^4501 ≤ (11230997309073/50000000000000 : ℝ)^3477
        have hw : |(1577491663/5000000000 : ℝ)|=(1577491663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1502_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40645197/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1349/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12807/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4499/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4499 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4499*1^1024 ≤ 0^1024*1^4499 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4499 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4499/1024 : ℝ) ≤ (892480660286096051/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4499 ≤ (892480660286096051/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4499*50000000000000000000^1024 ≤ 892480660286096051^1024*5^4499 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 892480660286096051 50000000000000000000 4499 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (892480660286096051/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4499/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4499 := by
      have hnat : (1 : ℕ)^1024*1^4499 ≤ 1^4499*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4499 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50892480660286096051/50000000000000000000 : ℝ) ≤ (10040349672435203/10000000000000000 : ℝ) ^ (4499/1024 : ℝ) := by
    have hpowers : (50892480660286096051/50000000000000000000 : ℝ)^1024 ≤ (10040349672435203/10000000000000000 : ℝ)^4499 := by
      have hnat : (50892480660286096051 : ℕ)^1024*10000000000000000^4499 ≤ 10040349672435203^4499*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50892480660286096051 50000000000000000000 10040349672435203 10000000000000000 1024 4499 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10040349672435203/10000000000000000 : ℝ)) (X := (50892480660286096051/50000000000000000000 : ℝ)) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25892480660286096051/25000000000000000000 : ℝ) ≤ (5040349672435203/5000000000000000 : ℝ) ^ (4499/1024 : ℝ) := by
    have hpowers : (25892480660286096051/25000000000000000000 : ℝ)^1024 ≤ (5040349672435203/5000000000000000 : ℝ)^4499 := by
      have hnat : (25892480660286096051 : ℕ)^1024*5000000000000000^4499 ≤ 5040349672435203^4499*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25892480660286096051 25000000000000000000 5040349672435203 5000000000000000 1024 4499 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5040349672435203/5000000000000000 : ℝ)) (X := (25892480660286096051/25000000000000000000 : ℝ)) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(40349672435203/4000000000000000 : ℝ)*(0 : ℝ))^(4499/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(40349672435203/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(892480660286096051/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(40349672435203/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4499/1024 : ℝ) := by
    rw [show (1 : ℝ)+(40349672435203/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10040349672435203/10000000000000000 : ℝ) by norm_num, show 1+(892480660286096051/50000000000000000000 : ℝ)+(0 : ℝ)=(50892480660286096051/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(892480660286096051/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(40349672435203/4000000000000000 : ℝ)*(2/5 : ℝ))^(4499/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(40349672435203/4000000000000000 : ℝ)*(2/5 : ℝ)=(5040349672435203/5000000000000000 : ℝ) by norm_num, show 1+2*(892480660286096051/50000000000000000000 : ℝ)=(25892480660286096051/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(40349672435203/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4499/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (40349672435203/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(40349672435203/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4499/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (40349672435203/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(40349672435203/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4499/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (40349672435203/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1696491531/10000000000 : ℝ)*X 0 0+(5920569507/10000000000 : ℝ)*X 0 1+(4851016819/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1370039873/2500000000 : ℝ)*X 1 0+(-2296773267/10000000000 : ℝ)*X 1 1+(970203359/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2740079757/5000000000 : ℝ)*X 2 0+(1212754199/2500000000 : ℝ)*X 2 1+(-2296773237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4147851117/10000000000 : ℝ)*X 0 0+(1545616577/5000000000 : ℝ)*X 0 1+(5499454937/10000000000 : ℝ)*X 0 2+(4147851117/10000000000 : ℝ)*X 1 0+(1545616577/5000000000 : ℝ)*X 1 1+(5499454937/10000000000 : ℝ)*X 1 2+(4147851117/10000000000 : ℝ)*X 2 0+(1545616577/5000000000 : ℝ)*X 2 1+(5499454937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1700098181/10000000000 : ℝ)*X 0 0+(4878349243/10000000000 : ℝ)*X 0 1+(1473064171/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((648499303/1250000000 : ℝ)*X 1 0+(-627766863/5000000000 : ℝ)*X 1 1+(294612823/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5187994509/10000000000 : ℝ)*X 2 0+(5892256461/10000000000 : ℝ)*X 2 1+(-251106719/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4155971967/10000000000 : ℝ)*X 0 0+(1087582573/2000000000 : ℝ)*X 0 1+(1577491663/5000000000 : ℝ)*X 0 2+(4155971967/10000000000 : ℝ)*X 1 0+(1087582573/2000000000 : ℝ)*X 1 1+(1577491663/5000000000 : ℝ)*X 1 2+(4155971967/10000000000 : ℝ)*X 2 0+(1087582573/2000000000 : ℝ)*X 2 1+(1577491663/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (291543793097948895172557/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5240567/20000000000000 : ℝ)*(base1) + (661712897/100000000000000 : ℝ)*(base19) + (332733167/50000000000000 : ℝ)*(base23) + (7960459/10000000000000 : ℝ)*(upper3) + (2784161/3125000000000 : ℝ)*(upper5) + (675110558835973/100000000000000 : ℝ)*(major0) + (675110558835973/100000000000000 : ℝ)*(major1) + (675110558835973/100000000000000 : ℝ)*(major2) + (467486236785171/50000000000000 : ℝ)*(sp0) + (233743537428507/25000000000000 : ℝ)*(sp1) + (934974145960591/100000000000000 : ℝ)*(sp2) + (415245150138387/100000000000000 : ℝ)*(sp3) + (1182029709/50000000000000 : ℝ)*(sp4) + (32272579/3125000000000 : ℝ)*(sp7) + (332196967251/80000000000 : ℝ)*(f.failure) + (37398992457077/4000000000000 : ℝ)*(f.sum) + (532393771042481/200000000000000000000000000000 : ℝ)*base66 + (1136453033557519/400000000000000000000000000000 : ℝ)*base67 + (27178754842481/400000000000000000000000000000 : ℝ)*base70 + (410973904442481/400000000000000000000000000000 : ℝ)*base72 + (719855220442481/200000000000000000000000000000 : ℝ)*base74 + (1904873945157519/400000000000000000000000000000 : ℝ)*base75 + (465842496357519/400000000000000000000000000000 : ℝ)*base77 + (1127251246357519/400000000000000000000000000000 : ℝ)*base79 + (1202998388042481/200000000000000000000000000000 : ℝ)*base82 + (16553/2000000000000000000 : ℝ)*base90 + (16553/2000000000000000000 : ℝ)*base92 + (16553/2000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (434269238081654519826441/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (829876107/100000000000000 : ℝ)*(base19) + (429426839/50000000000000 : ℝ)*(base23) + (6260039/10000000000000 : ℝ)*(base32) + (11769917/10000000000000 : ℝ)*(upper3) + (86298663/100000000000000 : ℝ)*(upper5) + (712158418037483/100000000000000 : ℝ)*(major0) + (712158418037483/100000000000000 : ℝ)*(major1) + (712158418037483/100000000000000 : ℝ)*(major2) + (386270167/20000000000000 : ℝ)*(sp1) + (2158967433/100000000000000 : ℝ)*(sp2) + (30821347767497/3125000000000 : ℝ)*(sp4) + (493140183666481/50000000000000 : ℝ)*(sp5) + (986280110738793/100000000000000 : ℝ)*(sp6) + (438033500158257/100000000000000 : ℝ)*(sp7) + (438033562758647/100000000000000 : ℝ)*(f.failure) + (30821347767497/3125000000000 : ℝ)*(f.sum) + (40368636285951/200000000000000000000000000000 : ℝ)*base66 + (1051170848085951/400000000000000000000000000000 : ℝ)*base68 + (331087704485951/400000000000000000000000000000 : ℝ)*base70 + (1425383748085951/400000000000000000000000000000 : ℝ)*base72 + (354773646885951/200000000000000000000000000000 : ℝ)*base74 + (450811708085951/400000000000000000000000000000 : ℝ)*base76 + (1014829944485951/400000000000000000000000000000 : ℝ)*base78 + (522788275685951/400000000000000000000000000000 : ℝ)*base80 + (126435522485951/200000000000000000000000000000 : ℝ)*base82 + (4231541/2500000000000000000000 : ℝ)*base90 + (4231541/2500000000000000000000 : ℝ)*base92 + (4231541/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1502_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40645197/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1349/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12807/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1502_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1502_s1_0 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1852896993/10000000000 : ℝ)*x 0 + (2788623371/5000000000 : ℝ)*x 1 + (2546929301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1852896993/10000000000 : ℝ)^4501 ≤ (5638953760881/50000000000000 : ℝ)^3477 := by
    have hnat : (1852896993 : ℕ)^4501*50000000000000^3477 ≤ 5638953760881^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1852896993 10000000000 5638953760881 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2788623371/5000000000 : ℝ)^4501 ≤ (23480578751811/50000000000000 : ℝ)^3477 := by
    have hnat : (2788623371 : ℕ)^4501*50000000000000^3477 ≤ 23480578751811^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2788623371 5000000000 23480578751811 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2546929301/5000000000 : ℝ)^4501 ≤ (41760934954109/100000000000000 : ℝ)^3477 := by
    have hnat : (2546929301 : ℕ)^4501*100000000000000^3477 ≤ 41760934954109^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2546929301 5000000000 41760934954109 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1852896993/10000000000 : ℝ), (2788623371/5000000000 : ℝ), (2546929301/5000000000 : ℝ)] ![(5638953760881/50000000000000 : ℝ), (23480578751811/50000000000000 : ℝ), (41760934954109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1852896993/10000000000 : ℝ)|^4501 ≤ (5638953760881/50000000000000 : ℝ)^3477
        have hw : |(-1852896993/10000000000 : ℝ)|=(1852896993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2788623371/5000000000 : ℝ)|^4501 ≤ (23480578751811/50000000000000 : ℝ)^3477
        have hw : |(2788623371/5000000000 : ℝ)|=(2788623371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2546929301/5000000000 : ℝ)|^4501 ≤ (41760934954109/100000000000000 : ℝ)^3477
        have hw : |(2546929301/5000000000 : ℝ)|=(2546929301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s1_1 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5388453277/10000000000 : ℝ)*x 0 + (-2107753169/10000000000 : ℝ)*x 1 + (5093859109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5388453277/10000000000 : ℝ)^4501 ≤ (22456832236767/50000000000000 : ℝ)^3477 := by
    have hnat : (5388453277 : ℕ)^4501*50000000000000^3477 ≤ 22456832236767^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388453277 10000000000 22456832236767 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107753169/10000000000 : ℝ)^4501 ≤ (6662697591389/50000000000000 : ℝ)^3477 := by
    have hnat : (2107753169 : ℕ)^4501*50000000000000^3477 ≤ 6662697591389^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107753169 10000000000 6662697591389 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5093859109/10000000000 : ℝ)^4501 ≤ (4176094033477/10000000000000 : ℝ)^3477 := by
    have hnat : (5093859109 : ℕ)^4501*10000000000000^3477 ≤ 4176094033477^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5093859109 10000000000 4176094033477 10000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5388453277/10000000000 : ℝ), (-2107753169/10000000000 : ℝ), (5093859109/10000000000 : ℝ)] ![(22456832236767/50000000000000 : ℝ), (6662697591389/50000000000000 : ℝ), (4176094033477/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5388453277/10000000000 : ℝ)|^4501 ≤ (22456832236767/50000000000000 : ℝ)^3477
        have hw : |(5388453277/10000000000 : ℝ)|=(5388453277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2107753169/10000000000 : ℝ)|^4501 ≤ (6662697591389/50000000000000 : ℝ)^3477
        have hw : |(-2107753169/10000000000 : ℝ)|=(2107753169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5093859109/10000000000 : ℝ)|^4501 ≤ (4176094033477/10000000000000 : ℝ)^3477
        have hw : |(5093859109/10000000000 : ℝ)|=(5093859109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s1_2 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2694226863/5000000000 : ℝ)*x 0 + (5093858843/10000000000 : ℝ)*x 1 + (-1053876461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2694226863/5000000000 : ℝ)^4501 ≤ (22456834659107/50000000000000 : ℝ)^3477 := by
    have hnat : (2694226863 : ℕ)^4501*50000000000000^3477 ≤ 22456834659107^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694226863 5000000000 22456834659107 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5093858843/10000000000 : ℝ)^4501 ≤ (2088046875589/5000000000000 : ℝ)^3477 := by
    have hnat : (5093858843 : ℕ)^4501*5000000000000^3477 ≤ 2088046875589^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5093858843 10000000000 2088046875589 5000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053876461/5000000000 : ℝ)^4501 ≤ (6662696580667/50000000000000 : ℝ)^3477 := by
    have hnat : (1053876461 : ℕ)^4501*50000000000000^3477 ≤ 6662696580667^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053876461 5000000000 6662696580667 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2694226863/5000000000 : ℝ), (5093858843/10000000000 : ℝ), (-1053876461/5000000000 : ℝ)] ![(22456834659107/50000000000000 : ℝ), (2088046875589/5000000000000 : ℝ), (6662696580667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2694226863/5000000000 : ℝ)|^4501 ≤ (22456834659107/50000000000000 : ℝ)^3477
        have hw : |(2694226863/5000000000 : ℝ)|=(2694226863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5093858843/10000000000 : ℝ)|^4501 ≤ (2088046875589/5000000000000 : ℝ)^3477
        have hw : |(5093858843/10000000000 : ℝ)|=(5093858843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1053876461/5000000000 : ℝ)|^4501 ≤ (6662696580667/50000000000000 : ℝ)^3477
        have hw : |(-1053876461/5000000000 : ℝ)|=(1053876461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s1_3 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4253259743/10000000000 : ℝ)*x 0 + (3738695243/10000000000 : ℝ)*x 1 + (603387369/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4253259743/10000000000 : ℝ)^4501 ≤ (3306572102911/10000000000000 : ℝ)^3477 := by
    have hnat : (4253259743 : ℕ)^4501*10000000000000^3477 ≤ 3306572102911^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253259743 10000000000 3306572102911 10000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3738695243/10000000000 : ℝ)^4501 ≤ (27982288945249/100000000000000 : ℝ)^3477 := by
    have hnat : (3738695243 : ℕ)^4501*100000000000000^3477 ≤ 27982288945249^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3738695243 10000000000 27982288945249 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (603387369/1250000000 : ℝ)^4501 ≤ (38951990008619/100000000000000 : ℝ)^3477 := by
    have hnat : (603387369 : ℕ)^4501*100000000000000^3477 ≤ 38951990008619^3477*1250000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603387369 1250000000 38951990008619 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4253259743/10000000000 : ℝ), (3738695243/10000000000 : ℝ), (603387369/1250000000 : ℝ)] ![(3306572102911/10000000000000 : ℝ), (27982288945249/100000000000000 : ℝ), (38951990008619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4253259743/10000000000 : ℝ)|^4501 ≤ (3306572102911/10000000000000 : ℝ)^3477
        have hw : |(4253259743/10000000000 : ℝ)|=(4253259743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3738695243/10000000000 : ℝ)|^4501 ≤ (27982288945249/100000000000000 : ℝ)^3477
        have hw : |(3738695243/10000000000 : ℝ)|=(3738695243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(603387369/1250000000 : ℝ)|^4501 ≤ (38951990008619/100000000000000 : ℝ)^3477
        have hw : |(603387369/1250000000 : ℝ)|=(603387369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s1_4 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1853218191/10000000000 : ℝ)*x 0 + (63741769/125000000 : ℝ)*x 1 + (2785837213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1853218191/10000000000 : ℝ)^4501 ≤ (11280438366439/100000000000000 : ℝ)^3477 := by
    have hnat : (1853218191 : ℕ)^4501*100000000000000^3477 ≤ 11280438366439^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853218191 10000000000 11280438366439 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63741769/125000000 : ℝ)^4501 ≤ (20909566487347/50000000000000 : ℝ)^3477 := by
    have hnat : (63741769 : ℕ)^4501*50000000000000^3477 ≤ 20909566487347^3477*125000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63741769 125000000 20909566487347 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2785837213/5000000000 : ℝ)^4501 ≤ (46900428650563/100000000000000 : ℝ)^3477 := by
    have hnat : (2785837213 : ℕ)^4501*100000000000000^3477 ≤ 46900428650563^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2785837213 5000000000 46900428650563 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1853218191/10000000000 : ℝ), (63741769/125000000 : ℝ), (2785837213/5000000000 : ℝ)] ![(11280438366439/100000000000000 : ℝ), (20909566487347/50000000000000 : ℝ), (46900428650563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1853218191/10000000000 : ℝ)|^4501 ≤ (11280438366439/100000000000000 : ℝ)^3477
        have hw : |(-1853218191/10000000000 : ℝ)|=(1853218191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(63741769/125000000 : ℝ)|^4501 ≤ (20909566487347/50000000000000 : ℝ)^3477
        have hw : |(63741769/125000000 : ℝ)|=(63741769/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2785837213/5000000000 : ℝ)|^4501 ≤ (46900428650563/100000000000000 : ℝ)^3477
        have hw : |(2785837213/5000000000 : ℝ)|=(2785837213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s1_5 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052257433/2000000000 : ℝ)*x 0 + (-814968733/5000000000 : ℝ)*x 1 + (1392918641/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052257433/2000000000 : ℝ)^4501 ≤ (10886586461841/25000000000000 : ℝ)^3477 := by
    have hnat : (1052257433 : ℕ)^4501*25000000000000^3477 ≤ 10886586461841^3477*2000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052257433 2000000000 10886586461841 25000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (814968733/5000000000 : ℝ)^4501 ≤ (597076499331/6250000000000 : ℝ)^3477 := by
    have hnat : (814968733 : ℕ)^4501*6250000000000^3477 ≤ 597076499331^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      814968733 5000000000 597076499331 6250000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1392918641/2500000000 : ℝ)^4501 ≤ (46900430154309/100000000000000 : ℝ)^3477 := by
    have hnat : (1392918641 : ℕ)^4501*100000000000000^3477 ≤ 46900430154309^3477*2500000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1392918641 2500000000 46900430154309 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052257433/2000000000 : ℝ), (-814968733/5000000000 : ℝ), (1392918641/2500000000 : ℝ)] ![(10886586461841/25000000000000 : ℝ), (597076499331/6250000000000 : ℝ), (46900430154309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052257433/2000000000 : ℝ)|^4501 ≤ (10886586461841/25000000000000 : ℝ)^3477
        have hw : |(1052257433/2000000000 : ℝ)|=(1052257433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-814968733/5000000000 : ℝ)|^4501 ≤ (597076499331/6250000000000 : ℝ)^3477
        have hw : |(-814968733/5000000000 : ℝ)|=(814968733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1392918641/2500000000 : ℝ)|^4501 ≤ (46900430154309/100000000000000 : ℝ)^3477
        have hw : |(1392918641/2500000000 : ℝ)|=(1392918641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s1_6 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5261287033/10000000000 : ℝ)*x 0 + (1392918651/2500000000 : ℝ)*x 1 + (-814968797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5261287033/10000000000 : ℝ)^4501 ≤ (1741853777323/4000000000000 : ℝ)^3477 := by
    have hnat : (5261287033 : ℕ)^4501*4000000000000^3477 ≤ 1741853777323^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261287033 10000000000 1741853777323 4000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1392918651/2500000000 : ℝ)^4501 ≤ (46900430590177/100000000000000 : ℝ)^3477 := by
    have hnat : (1392918651 : ℕ)^4501*100000000000000^3477 ≤ 46900430590177^3477*2500000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1392918651 2500000000 46900430590177 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (814968797/5000000000 : ℝ)^4501 ≤ (9553224960461/100000000000000 : ℝ)^3477 := by
    have hnat : (814968797 : ℕ)^4501*100000000000000^3477 ≤ 9553224960461^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      814968797 5000000000 9553224960461 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5261287033/10000000000 : ℝ), (1392918651/2500000000 : ℝ), (-814968797/5000000000 : ℝ)] ![(1741853777323/4000000000000 : ℝ), (46900430590177/100000000000000 : ℝ), (9553224960461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5261287033/10000000000 : ℝ)|^4501 ≤ (1741853777323/4000000000000 : ℝ)^3477
        have hw : |(5261287033/10000000000 : ℝ)|=(5261287033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1392918651/2500000000 : ℝ)|^4501 ≤ (46900430590177/100000000000000 : ℝ)^3477
        have hw : |(1392918651/2500000000 : ℝ)|=(1392918651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-814968797/5000000000 : ℝ)|^4501 ≤ (9553224960461/100000000000000 : ℝ)^3477
        have hw : |(-814968797/5000000000 : ℝ)|=(814968797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s1_7 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4253983389/10000000000 : ℝ)*x 0 + (4814754709/10000000000 : ℝ)*x 1 + (1875620669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4253983389/10000000000 : ℝ)^4501 ≤ (16536501906811/50000000000000 : ℝ)^3477 := by
    have hnat : (4253983389 : ℕ)^4501*50000000000000^3477 ≤ 16536501906811^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253983389 10000000000 16536501906811 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4814754709/10000000000 : ℝ)^4501 ≤ (7764618260237/20000000000000 : ℝ)^3477 := by
    have hnat : (4814754709 : ℕ)^4501*20000000000000^3477 ≤ 7764618260237^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4814754709 10000000000 7764618260237 20000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1875620669/5000000000 : ℝ)^4501 ≤ (7025976217571/25000000000000 : ℝ)^3477 := by
    have hnat : (1875620669 : ℕ)^4501*25000000000000^3477 ≤ 7025976217571^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875620669 5000000000 7025976217571 25000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4253983389/10000000000 : ℝ), (4814754709/10000000000 : ℝ), (1875620669/5000000000 : ℝ)] ![(16536501906811/50000000000000 : ℝ), (7764618260237/20000000000000 : ℝ), (7025976217571/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4253983389/10000000000 : ℝ)|^4501 ≤ (16536501906811/50000000000000 : ℝ)^3477
        have hw : |(4253983389/10000000000 : ℝ)|=(4253983389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4814754709/10000000000 : ℝ)|^4501 ≤ (7764618260237/20000000000000 : ℝ)^3477
        have hw : |(4814754709/10000000000 : ℝ)|=(4814754709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1875620669/5000000000 : ℝ)|^4501 ≤ (7025976217571/25000000000000 : ℝ)^3477
        have hw : |(1875620669/5000000000 : ℝ)|=(1875620669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1502_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40645197/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12807/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1349/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (411/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18443/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12807/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1349/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12807/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1349/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12807/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1349/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12807/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1349/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12807/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1349/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12807/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1349/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1349/50000 : ℝ) ^ (4499/1024 : ℝ) ≤ (1598111208383/12500000000000000000 : ℝ) := by
    have hpowers : (1349/50000 : ℝ)^4499 ≤ (1598111208383/12500000000000000000 : ℝ)^1024 := by
      have hnat : (1349 : ℕ)^4499*12500000000000000000^1024 ≤ 1598111208383^1024*50000^4499 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1349 50000 1598111208383 12500000000000000000 4499 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1349/50000 : ℝ)) (X := (1598111208383/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12807/50000 : ℝ) ^ (4499/1024 : ℝ) ≤ (251833285114089039/100000000000000000000 : ℝ) := by
    have hpowers : (12807/50000 : ℝ)^4499 ≤ (251833285114089039/100000000000000000000 : ℝ)^1024 := by
      have hnat : (12807 : ℕ)^4499*100000000000000000000^1024 ≤ 251833285114089039^1024*50000^4499 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12807 50000 251833285114089039 100000000000000000000 4499 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12807/50000 : ℝ)) (X := (251833285114089039/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250001598111208383/6250000000000000000 : ℝ) ≤ (10000000581983807/10000000000000000 : ℝ) ^ (4499/1024 : ℝ) := by
    have hpowers : (6250001598111208383/6250000000000000000 : ℝ)^1024 ≤ (10000000581983807/10000000000000000 : ℝ)^4499 := by
      have hnat : (6250001598111208383 : ℕ)^1024*10000000000000000^4499 ≤ 10000000581983807^4499*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250001598111208383 6250000000000000000 10000000581983807 10000000000000000 1024 4499 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000581983807/10000000000000000 : ℝ)) (X := (6250001598111208383/6250000000000000000 : ℝ)) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100251846070003756103/100000000000000000000 : ℝ) ≤ (10005726604099643/10000000000000000 : ℝ) ^ (4499/1024 : ℝ) := by
    have hpowers : (100251846070003756103/100000000000000000000 : ℝ)^1024 ≤ (10005726604099643/10000000000000000 : ℝ)^4499 := by
      have hnat : (100251846070003756103 : ℕ)^1024*10000000000000000^4499 ≤ 10005726604099643^4499*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100251846070003756103 100000000000000000000 10005726604099643 10000000000000000 1024 4499 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005726604099643/10000000000000000 : ℝ)) (X := (100251846070003756103/100000000000000000000 : ℝ)) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50251833285114089039/50000000000000000000 : ℝ) ≤ (10011452626215479/10000000000000000 : ℝ) ^ (4499/1024 : ℝ) := by
    have hpowers : (50251833285114089039/50000000000000000000 : ℝ)^1024 ≤ (10011452626215479/10000000000000000 : ℝ)^4499 := by
      have hnat : (50251833285114089039 : ℕ)^1024*10000000000000000^4499 ≤ 10011452626215479^4499*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50251833285114089039 50000000000000000000 10011452626215479 10000000000000000 1024 4499 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011452626215479/10000000000000000 : ℝ)) (X := (50251833285114089039/50000000000000000000 : ℝ)) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1598111208383/12500000000000000000 : ℝ) ≤ ((57282278930350967539/57290000000000000000 : ℝ)+2*(1431505528959/572900000000000 : ℝ)*(1349/50000 : ℝ))^(4499/1024 : ℝ) := by
    rw [show (57282278930350967539/57290000000000000000 : ℝ)+2*(1431505528959/572900000000000 : ℝ)*(1349/50000 : ℝ)=(10000000581983807/10000000000000000 : ℝ) by norm_num, show 1+2*(1598111208383/12500000000000000000 : ℝ)=(6250001598111208383/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(251833285114089039/100000000000000000000 : ℝ)+(1598111208383/12500000000000000000 : ℝ) ≤ ((57282278930350967539/57290000000000000000 : ℝ)+(1431505528959/572900000000000 : ℝ)*((12807/50000 : ℝ)+(1349/50000 : ℝ)))^(4499/1024 : ℝ) := by
    rw [show (57282278930350967539/57290000000000000000 : ℝ)+(1431505528959/572900000000000 : ℝ)*((12807/50000 : ℝ)+(1349/50000 : ℝ))=(10005726604099643/10000000000000000 : ℝ) by norm_num, show 1+(251833285114089039/100000000000000000000 : ℝ)+(1598111208383/12500000000000000000 : ℝ)=(100251846070003756103/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(251833285114089039/100000000000000000000 : ℝ) ≤ ((57282278930350967539/57290000000000000000 : ℝ)+2*(1431505528959/572900000000000 : ℝ)*(12807/50000 : ℝ))^(4499/1024 : ℝ) := by
    rw [show (57282278930350967539/57290000000000000000 : ℝ)+2*(1431505528959/572900000000000 : ℝ)*(12807/50000 : ℝ)=(10011452626215479/10000000000000000 : ℝ) by norm_num, show 1+2*(251833285114089039/100000000000000000000 : ℝ)=(50251833285114089039/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (57282278930350967539/57290000000000000000 : ℝ)*(X 1 0+X 2 0)+(1431505528959/572900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4499/1024 : ℝ)) (lo := (1349/50000 : ℝ)) (hi := (12807/50000 : ℝ)) (c := (57282278930350967539/57290000000000000000 : ℝ)) (alpha := (1431505528959/572900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (57282278930350967539/57290000000000000000 : ℝ)*(X 0 1+X 2 1)+(1431505528959/572900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4499/1024 : ℝ)) (lo := (1349/50000 : ℝ)) (hi := (12807/50000 : ℝ)) (c := (57282278930350967539/57290000000000000000 : ℝ)) (alpha := (1431505528959/572900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (57282278930350967539/57290000000000000000 : ℝ)*(X 0 2+X 1 2)+(1431505528959/572900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4499/1024 : ℝ)) (lo := (1349/50000 : ℝ)) (hi := (12807/50000 : ℝ)) (c := (57282278930350967539/57290000000000000000 : ℝ)) (alpha := (1431505528959/572900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1852896993/10000000000 : ℝ)*X 0 0+(2788623371/5000000000 : ℝ)*X 0 1+(2546929301/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5388453277/10000000000 : ℝ)*X 1 0+(-2107753169/10000000000 : ℝ)*X 1 1+(5093859109/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2694226863/5000000000 : ℝ)*X 2 0+(5093858843/10000000000 : ℝ)*X 2 1+(-1053876461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4253259743/10000000000 : ℝ)*X 0 0+(3738695243/10000000000 : ℝ)*X 0 1+(603387369/1250000000 : ℝ)*X 0 2+(4253259743/10000000000 : ℝ)*X 1 0+(3738695243/10000000000 : ℝ)*X 1 1+(603387369/1250000000 : ℝ)*X 1 2+(4253259743/10000000000 : ℝ)*X 2 0+(3738695243/10000000000 : ℝ)*X 2 1+(603387369/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1853218191/10000000000 : ℝ)*X 0 0+(63741769/125000000 : ℝ)*X 0 1+(2785837213/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1052257433/2000000000 : ℝ)*X 1 0+(-814968733/5000000000 : ℝ)*X 1 1+(1392918641/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5261287033/10000000000 : ℝ)*X 2 0+(1392918651/2500000000 : ℝ)*X 2 1+(-814968797/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4253983389/10000000000 : ℝ)*X 0 0+(4814754709/10000000000 : ℝ)*X 0 1+(1875620669/5000000000 : ℝ)*X 0 2+(4253983389/10000000000 : ℝ)*X 1 0+(4814754709/10000000000 : ℝ)*X 1 1+(1875620669/5000000000 : ℝ)*X 1 2+(4253983389/10000000000 : ℝ)*X 2 0+(4814754709/10000000000 : ℝ)*X 2 1+(1875620669/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16397937153118651756533848979/2864500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (128071751/10000000000000 : ℝ)*(base19) + (179844881/12500000000000 : ℝ)*(base23) + (84690223/100000000000000 : ℝ)*(upper3) + (77271/1000000000000 : ℝ)*(upper4) + (115542519/50000000000000 : ℝ)*(upper5) + (1493771225098987/100000000000000 : ℝ)*(major0) + (1493771225098987/100000000000000 : ℝ)*(major1) + (1493771225098987/100000000000000 : ℝ)*(major2) + (1034370818505817/50000000000000 : ℝ)*(sp0) + (1034376964587443/50000000000000 : ℝ)*(sp1) + (41375075422667/2000000000000 : ℝ)*(sp2) + (918782117796649/100000000000000 : ℝ)*(sp3) + (13572880763/100000000000000 : ℝ)*(sp4) + (4931691011/100000000000000 : ℝ)*(sp7) + (45939352474383/5000000000000 : ℝ)*(f.failure) + (2068755209892397/100000000000000 : ℝ)*(f.sum) + (23586056074169/14322500000000000000000000000 : ℝ)*base65 + (19952816625973917007/5729000000000000000000000000000000 : ℝ)*base68 + (5177895078335917007/5729000000000000000000000000000000 : ℝ)*base70 + (36357631999020082993/5729000000000000000000000000000000 : ℝ)*base71 + (100770907864407/28645000000000000000000000000 : ℝ)*base74 + (17018004751892082993/5729000000000000000000000000000000 : ℝ)*base75 + (24814113125241917007/5729000000000000000000000000000000 : ℝ)*base78 + (76738308637371917007/5729000000000000000000000000000000 : ℝ)*base80 + (23894191882963/28645000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (738451/125000000000000000000 : ℝ)*base89 + (738451/125000000000000000000 : ℝ)*base91 + (738451/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3905995422443099452584950391/358062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (258862571/12500000000000 : ℝ)*(base19) + (541899351/25000000000000 : ℝ)*(base23) + (293678489/100000000000000 : ℝ)*(upper3) + (31975889/50000000000000 : ℝ)*(lower4) + (12178487/6250000000000 : ℝ)*(upper5) + (382178644473123/25000000000000 : ℝ)*(major0) + (382178644473123/25000000000000 : ℝ)*(major1) + (382178644473123/25000000000000 : ℝ)*(major2) + (1707249957/12500000000000 : ℝ)*(sp1) + (296544649/2000000000000 : ℝ)*(sp2) + (529287206576791/25000000000000 : ℝ)*(sp4) + (2117133097406939/100000000000000 : ℝ)*(sp5) + (211713183147731/10000000000000 : ℝ)*(sp6) + (940279965854571/100000000000000 : ℝ)*(sp7) + (940279965854571/100000000000000 : ℝ)*(f.failure) + (529287206576791/25000000000000 : ℝ)*(f.sum) + (108727753403053/28645000000000000000000000000 : ℝ)*base65 + (8707370462111095703/1432250000000000000000000000000000 : ℝ)*base68 + (20338629376522845703/1432250000000000000000000000000000 : ℝ)*base70 + (2890942552026845703/1432250000000000000000000000000000 : ℝ)*base72 + (3753645320817/28645000000000000000000000000 : ℝ)*base74 + (3811285169966154297/1432250000000000000000000000000000 : ℝ)*base75 + (13241268020103595703/1432250000000000000000000000000000 : ℝ)*base78 + (7160026728358595703/1432250000000000000000000000000000 : ℝ)*base80 + (44439089823041/14322500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (11645487/2500000000000000000000 : ℝ)*base89 + (11645487/2500000000000000000000 : ℝ)*base91 + (11645487/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1502_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40645197/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12807/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1349/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (411/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18443/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1502_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1502_s2_0 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-939293019/5000000000 : ℝ)*x 0 + (341324593/625000000 : ℝ)*x 1 + (5193289619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (939293019/5000000000 : ℝ)^4501 ≤ (5740364139623/50000000000000 : ℝ)^3477 := by
    have hnat : (939293019 : ℕ)^4501*50000000000000^3477 ≤ 5740364139623^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939293019 5000000000 5740364139623 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341324593/625000000 : ℝ)^4501 ≤ (45700081608683/100000000000000 : ℝ)^3477 := by
    have hnat : (341324593 : ℕ)^4501*100000000000000^3477 ≤ 45700081608683^3477*625000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341324593 625000000 45700081608683 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5193289619/10000000000 : ℝ)^4501 ≤ (10704797525779/25000000000000 : ℝ)^3477 := by
    have hnat : (5193289619 : ℕ)^4501*25000000000000^3477 ≤ 10704797525779^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193289619 10000000000 10704797525779 25000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-939293019/5000000000 : ℝ), (341324593/625000000 : ℝ), (5193289619/10000000000 : ℝ)] ![(5740364139623/50000000000000 : ℝ), (45700081608683/100000000000000 : ℝ), (10704797525779/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-939293019/5000000000 : ℝ)|^4501 ≤ (5740364139623/50000000000000 : ℝ)^3477
        have hw : |(-939293019/5000000000 : ℝ)|=(939293019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341324593/625000000 : ℝ)|^4501 ≤ (45700081608683/100000000000000 : ℝ)^3477
        have hw : |(341324593/625000000 : ℝ)|=(341324593/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5193289619/10000000000 : ℝ)|^4501 ≤ (10704797525779/25000000000000 : ℝ)^3477
        have hw : |(5193289619/10000000000 : ℝ)|=(5193289619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s2_1 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5359058333/10000000000 : ℝ)*x 0 + (-2016581459/10000000000 : ℝ)*x 1 + (1298322647/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5359058333/10000000000 : ℝ)^4501 ≤ (35677400117/80000000000 : ℝ)^3477 := by
    have hnat : (5359058333 : ℕ)^4501*80000000000^3477 ≤ 35677400117^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359058333 10000000000 35677400117 80000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2016581459/10000000000 : ℝ)^4501 ≤ (2516809878203/20000000000000 : ℝ)^3477 := by
    have hnat : (2016581459 : ℕ)^4501*20000000000000^3477 ≤ 2516809878203^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016581459 10000000000 2516809878203 20000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1298322647/2500000000 : ℝ)^4501 ≤ (2140960022279/5000000000000 : ℝ)^3477 := by
    have hnat : (1298322647 : ℕ)^4501*5000000000000^3477 ≤ 2140960022279^3477*2500000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298322647 2500000000 2140960022279 5000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5359058333/10000000000 : ℝ), (-2016581459/10000000000 : ℝ), (1298322647/2500000000 : ℝ)] ![(35677400117/80000000000 : ℝ), (2516809878203/20000000000000 : ℝ), (2140960022279/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5359058333/10000000000 : ℝ)|^4501 ≤ (35677400117/80000000000 : ℝ)^3477
        have hw : |(5359058333/10000000000 : ℝ)|=(5359058333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2016581459/10000000000 : ℝ)|^4501 ≤ (2516809878203/20000000000000 : ℝ)^3477
        have hw : |(-2016581459/10000000000 : ℝ)|=(2016581459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1298322647/2500000000 : ℝ)|^4501 ≤ (2140960022279/5000000000000 : ℝ)^3477
        have hw : |(1298322647/2500000000 : ℝ)|=(1298322647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s2_2 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679529643/5000000000 : ℝ)*x 0 + (1298322483/2500000000 : ℝ)*x 1 + (-403316211/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679529643/5000000000 : ℝ)^4501 ≤ (44596760412503/100000000000000 : ℝ)^3477 := by
    have hnat : (2679529643 : ℕ)^4501*100000000000000^3477 ≤ 44596760412503^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679529643 5000000000 44596760412503 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1298322483/2500000000 : ℝ)^4501 ≤ (42819193443871/100000000000000 : ℝ)^3477 := by
    have hnat : (1298322483 : ℕ)^4501*100000000000000^3477 ≤ 42819193443871^3477*2500000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298322483 2500000000 42819193443871 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403316211/2000000000 : ℝ)^4501 ≤ (2516809225493/20000000000000 : ℝ)^3477 := by
    have hnat : (403316211 : ℕ)^4501*20000000000000^3477 ≤ 2516809225493^3477*2000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403316211 2000000000 2516809225493 20000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679529643/5000000000 : ℝ), (1298322483/2500000000 : ℝ), (-403316211/2000000000 : ℝ)] ![(44596760412503/100000000000000 : ℝ), (42819193443871/100000000000000 : ℝ), (2516809225493/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679529643/5000000000 : ℝ)|^4501 ≤ (44596760412503/100000000000000 : ℝ)^3477
        have hw : |(2679529643/5000000000 : ℝ)|=(2679529643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1298322483/2500000000 : ℝ)|^4501 ≤ (42819193443871/100000000000000 : ℝ)^3477
        have hw : |(1298322483/2500000000 : ℝ)|=(1298322483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-403316211/2000000000 : ℝ)|^4501 ≤ (2516809225493/20000000000000 : ℝ)^3477
        have hw : |(-403316211/2000000000 : ℝ)|=(403316211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s2_3 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2135833949/5000000000 : ℝ)*x 0 + (3979165849/10000000000 : ℝ)*x 1 + (4582383059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135833949/5000000000 : ℝ)^4501 ≤ (33251094289927/100000000000000 : ℝ)^3477 := by
    have hnat : (2135833949 : ℕ)^4501*100000000000000^3477 ≤ 33251094289927^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135833949 5000000000 33251094289927 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3979165849/10000000000 : ℝ)^4501 ≤ (15166944446903/50000000000000 : ℝ)^3477 := by
    have hnat : (3979165849 : ℕ)^4501*50000000000000^3477 ≤ 15166944446903^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979165849 10000000000 15166944446903 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4582383059/10000000000 : ℝ)^4501 ≤ (910375420099/2500000000000 : ℝ)^3477 := by
    have hnat : (4582383059 : ℕ)^4501*2500000000000^3477 ≤ 910375420099^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4582383059 10000000000 910375420099 2500000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2135833949/5000000000 : ℝ), (3979165849/10000000000 : ℝ), (4582383059/10000000000 : ℝ)] ![(33251094289927/100000000000000 : ℝ), (15166944446903/50000000000000 : ℝ), (910375420099/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2135833949/5000000000 : ℝ)|^4501 ≤ (33251094289927/100000000000000 : ℝ)^3477
        have hw : |(2135833949/5000000000 : ℝ)|=(2135833949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3979165849/10000000000 : ℝ)|^4501 ≤ (15166944446903/50000000000000 : ℝ)^3477
        have hw : |(3979165849/10000000000 : ℝ)|=(3979165849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4582383059/10000000000 : ℝ)|^4501 ≤ (910375420099/2500000000000 : ℝ)^3477
        have hw : |(4582383059/10000000000 : ℝ)|=(4582383059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s2_4 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-234830083/1250000000 : ℝ)*x 0 + (259749127/500000000 : ℝ)*x 1 + (5459485407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (234830083/1250000000 : ℝ)^4501 ≤ (2870290109653/25000000000000 : ℝ)^3477 := by
    have hnat : (234830083 : ℕ)^4501*25000000000000^3477 ≤ 2870290109653^3477*1250000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234830083 1250000000 2870290109653 25000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259749127/500000000 : ℝ)^4501 ≤ (8567452017399/20000000000000 : ℝ)^3477 := by
    have hnat : (259749127 : ℕ)^4501*20000000000000^3477 ≤ 8567452017399^3477*500000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259749127 500000000 8567452017399 20000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5459485407/10000000000 : ℝ)^4501 ≤ (45681579458911/100000000000000 : ℝ)^3477 := by
    have hnat : (5459485407 : ℕ)^4501*100000000000000^3477 ≤ 45681579458911^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459485407 10000000000 45681579458911 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-234830083/1250000000 : ℝ), (259749127/500000000 : ℝ), (5459485407/10000000000 : ℝ)] ![(2870290109653/25000000000000 : ℝ), (8567452017399/20000000000000 : ℝ), (45681579458911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-234830083/1250000000 : ℝ)|^4501 ≤ (2870290109653/25000000000000 : ℝ)^3477
        have hw : |(-234830083/1250000000 : ℝ)|=(234830083/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259749127/500000000 : ℝ)|^4501 ≤ (8567452017399/20000000000000 : ℝ)^3477
        have hw : |(259749127/500000000 : ℝ)|=(259749127/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5459485407/10000000000 : ℝ)|^4501 ≤ (45681579458911/100000000000000 : ℝ)^3477
        have hw : |(5459485407/10000000000 : ℝ)|=(5459485407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s2_5 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528881791/1000000000 : ℝ)*x 0 + (-175038669/1000000000 : ℝ)*x 1 + (5459485197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528881791/1000000000 : ℝ)^4501 ≤ (5480193209053/12500000000000 : ℝ)^3477 := by
    have hnat : (528881791 : ℕ)^4501*12500000000000^3477 ≤ 5480193209053^3477*1000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528881791 1000000000 5480193209053 12500000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (175038669/1000000000 : ℝ)^4501 ≤ (2619219281681/25000000000000 : ℝ)^3477 := by
    have hnat : (175038669 : ℕ)^4501*25000000000000^3477 ≤ 2619219281681^3477*1000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175038669 1000000000 2619219281681 25000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5459485197/10000000000 : ℝ)^4501 ≤ (4568157718427/10000000000000 : ℝ)^3477 := by
    have hnat : (5459485197 : ℕ)^4501*10000000000000^3477 ≤ 4568157718427^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459485197 10000000000 4568157718427 10000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528881791/1000000000 : ℝ), (-175038669/1000000000 : ℝ), (5459485197/10000000000 : ℝ)] ![(5480193209053/12500000000000 : ℝ), (2619219281681/25000000000000 : ℝ), (4568157718427/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528881791/1000000000 : ℝ)|^4501 ≤ (5480193209053/12500000000000 : ℝ)^3477
        have hw : |(528881791/1000000000 : ℝ)|=(528881791/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-175038669/1000000000 : ℝ)|^4501 ≤ (2619219281681/25000000000000 : ℝ)^3477
        have hw : |(-175038669/1000000000 : ℝ)|=(175038669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5459485197/10000000000 : ℝ)|^4501 ≤ (4568157718427/10000000000000 : ℝ)^3477
        have hw : |(5459485197/10000000000 : ℝ)|=(5459485197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s2_6 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644409347/5000000000 : ℝ)*x 0 + (5459484777/10000000000 : ℝ)*x 1 + (-1750386191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644409347/5000000000 : ℝ)^4501 ≤ (43841554085361/100000000000000 : ℝ)^3477 := by
    have hnat : (2644409347 : ℕ)^4501*100000000000000^3477 ≤ 43841554085361^3477*5000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644409347 5000000000 43841554085361 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5459484777/10000000000 : ℝ)^4501 ≤ (22840786317493/50000000000000 : ℝ)^3477 := by
    have hnat : (5459484777 : ℕ)^4501*50000000000000^3477 ≤ 22840786317493^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459484777 10000000000 22840786317493 50000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1750386191/10000000000 : ℝ)^4501 ≤ (261921831509/2500000000000 : ℝ)^3477 := by
    have hnat : (1750386191 : ℕ)^4501*2500000000000^3477 ≤ 261921831509^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1750386191 10000000000 261921831509 2500000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644409347/5000000000 : ℝ), (5459484777/10000000000 : ℝ), (-1750386191/10000000000 : ℝ)] ![(43841554085361/100000000000000 : ℝ), (22840786317493/50000000000000 : ℝ), (261921831509/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644409347/5000000000 : ℝ)|^4501 ≤ (43841554085361/100000000000000 : ℝ)^3477
        have hw : |(2644409347/5000000000 : ℝ)|=(2644409347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5459484777/10000000000 : ℝ)|^4501 ≤ (22840786317493/50000000000000 : ℝ)^3477
        have hw : |(5459484777/10000000000 : ℝ)|=(5459484777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1750386191/10000000000 : ℝ)|^4501 ≤ (261921831509/2500000000000 : ℝ)^3477
        have hw : |(-1750386191/10000000000 : ℝ)|=(1750386191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1502_s2_7 (p : ℝ) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4271791803/10000000000 : ℝ)*x 0 + (915714129/2000000000 : ℝ)*x 1 + (995753131/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4271791803/10000000000 : ℝ)^4501 ≤ (33252342832831/100000000000000 : ℝ)^3477 := by
    have hnat : (4271791803 : ℕ)^4501*100000000000000^3477 ≤ 33252342832831^3477*10000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4271791803 10000000000 33252342832831 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (915714129/2000000000 : ℝ)^4501 ≤ (9093950720447/25000000000000 : ℝ)^3477 := by
    have hnat : (915714129 : ℕ)^4501*25000000000000^3477 ≤ 9093950720447^3477*2000000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915714129 2000000000 9093950720447 25000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (995753131/2500000000 : ℝ)^4501 ≤ (30371854266873/100000000000000 : ℝ)^3477 := by
    have hnat : (995753131 : ℕ)^4501*100000000000000^3477 ≤ 30371854266873^3477*2500000000^4501 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995753131 2500000000 30371854266873 100000000000000 4501 3477 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4501/1024 : ℝ)) 4501 3477 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4271791803/10000000000 : ℝ), (915714129/2000000000 : ℝ), (995753131/2500000000 : ℝ)] ![(33252342832831/100000000000000 : ℝ), (9093950720447/25000000000000 : ℝ), (30371854266873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4271791803/10000000000 : ℝ)|^4501 ≤ (33252342832831/100000000000000 : ℝ)^3477
        have hw : |(4271791803/10000000000 : ℝ)|=(4271791803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(915714129/2000000000 : ℝ)|^4501 ≤ (9093950720447/25000000000000 : ℝ)^3477
        have hw : |(915714129/2000000000 : ℝ)|=(915714129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(995753131/2500000000 : ℝ)|^4501 ≤ (30371854266873/100000000000000 : ℝ)^3477
        have hw : |(995753131/2500000000 : ℝ)|=(995753131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1502_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40645197/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18443/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (411/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (5183/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4009/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18443/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (411/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18443/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (411/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18443/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (411/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18443/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (411/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18443/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (411/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18443/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (411/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (411/5000 : ℝ) ^ (4499/1024 : ℝ) ≤ (1707772387991241/100000000000000000000 : ℝ) := by
    have hpowers : (411/5000 : ℝ)^4499 ≤ (1707772387991241/100000000000000000000 : ℝ)^1024 := by
      have hnat : (411 : ℕ)^4499*100000000000000000000^1024 ≤ 1707772387991241^1024*5000^4499 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        411 5000 1707772387991241 100000000000000000000 4499 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (411/5000 : ℝ)) (X := (1707772387991241/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18443/100000 : ℝ) ^ (4499/1024 : ℝ) ≤ (11896544464930719/20000000000000000000 : ℝ) := by
    have hpowers : (18443/100000 : ℝ)^4499 ≤ (11896544464930719/20000000000000000000 : ℝ)^1024 := by
      have hnat : (18443 : ℕ)^4499*20000000000000000000^1024 ≤ 11896544464930719^1024*100000^4499 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18443 100000 11896544464930719 20000000000000000000 4499 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18443/100000 : ℝ)) (X := (11896544464930719/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001707772387991241/50000000000000000000 : ℝ) ≤ (1000007773886901/1000000000000000 : ℝ) ^ (4499/1024 : ℝ) := by
    have hpowers : (50001707772387991241/50000000000000000000 : ℝ)^1024 ≤ (1000007773886901/1000000000000000 : ℝ)^4499 := by
      have hnat : (50001707772387991241 : ℕ)^1024*1000000000000000^4499 ≤ 1000007773886901^4499*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001707772387991241 50000000000000000000 1000007773886901 1000000000000000 1024 4499 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000007773886901/1000000000000000 : ℝ)) (X := (50001707772387991241/50000000000000000000 : ℝ)) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25015297623678161209/25000000000000000000 : ℝ) ≤ (5000696202096113/5000000000000000 : ℝ) ^ (4499/1024 : ℝ) := by
    have hpowers : (25015297623678161209/25000000000000000000 : ℝ)^1024 ≤ (5000696202096113/5000000000000000 : ℝ)^4499 := by
      have hnat : (25015297623678161209 : ℕ)^1024*5000000000000000^4499 ≤ 5000696202096113^4499*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015297623678161209 25000000000000000000 5000696202096113 5000000000000000 1024 4499 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000696202096113/5000000000000000 : ℝ)) (X := (25015297623678161209/25000000000000000000 : ℝ)) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10011896544464930719/10000000000000000000 : ℝ) ≤ (5001353534757721/5000000000000000 : ℝ) ^ (4499/1024 : ℝ) := by
    have hpowers : (10011896544464930719/10000000000000000000 : ℝ)^1024 ≤ (5001353534757721/5000000000000000 : ℝ)^4499 := by
      have hnat : (10011896544464930719 : ℕ)^1024*5000000000000000^4499 ≤ 5001353534757721^4499*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10011896544464930719 10000000000000000000 5001353534757721 5000000000000000 1024 4499 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001353534757721/5000000000000000 : ℝ)) (X := (10011896544464930719/10000000000000000000 : ℝ)) (by norm_num) 4499 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1707772387991241/100000000000000000000 : ℝ) ≤ ((10220918162654421819/10223000000000000000 : ℝ)+2*(82166582701/63893750000000 : ℝ)*(411/5000 : ℝ))^(4499/1024 : ℝ) := by
    rw [show (10220918162654421819/10223000000000000000 : ℝ)+2*(82166582701/63893750000000 : ℝ)*(411/5000 : ℝ)=(1000007773886901/1000000000000000 : ℝ) by norm_num, show 1+2*(1707772387991241/100000000000000000000 : ℝ)=(50001707772387991241/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11896544464930719/20000000000000000000 : ℝ)+(1707772387991241/100000000000000000000 : ℝ) ≤ ((10220918162654421819/10223000000000000000 : ℝ)+(82166582701/63893750000000 : ℝ)*((18443/100000 : ℝ)+(411/5000 : ℝ)))^(4499/1024 : ℝ) := by
    rw [show (10220918162654421819/10223000000000000000 : ℝ)+(82166582701/63893750000000 : ℝ)*((18443/100000 : ℝ)+(411/5000 : ℝ))=(5000696202096113/5000000000000000 : ℝ) by norm_num, show 1+(11896544464930719/20000000000000000000 : ℝ)+(1707772387991241/100000000000000000000 : ℝ)=(25015297623678161209/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11896544464930719/20000000000000000000 : ℝ) ≤ ((10220918162654421819/10223000000000000000 : ℝ)+2*(82166582701/63893750000000 : ℝ)*(18443/100000 : ℝ))^(4499/1024 : ℝ) := by
    rw [show (10220918162654421819/10223000000000000000 : ℝ)+2*(82166582701/63893750000000 : ℝ)*(18443/100000 : ℝ)=(5001353534757721/5000000000000000 : ℝ) by norm_num, show 1+2*(11896544464930719/20000000000000000000 : ℝ)=(10011896544464930719/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10220918162654421819/10223000000000000000 : ℝ)*(X 1 0+X 2 0)+(82166582701/63893750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4499/1024 : ℝ)) (lo := (411/5000 : ℝ)) (hi := (18443/100000 : ℝ)) (c := (10220918162654421819/10223000000000000000 : ℝ)) (alpha := (82166582701/63893750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10220918162654421819/10223000000000000000 : ℝ)*(X 0 1+X 2 1)+(82166582701/63893750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4499/1024 : ℝ)) (lo := (411/5000 : ℝ)) (hi := (18443/100000 : ℝ)) (c := (10220918162654421819/10223000000000000000 : ℝ)) (alpha := (82166582701/63893750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10220918162654421819/10223000000000000000 : ℝ)*(X 0 2+X 1 2)+(82166582701/63893750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4499/1024 : ℝ)) (lo := (411/5000 : ℝ)) (hi := (18443/100000 : ℝ)) (c := (10220918162654421819/10223000000000000000 : ℝ)) (alpha := (82166582701/63893750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-939293019/5000000000 : ℝ)*X 0 0+(341324593/625000000 : ℝ)*X 0 1+(5193289619/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5359058333/10000000000 : ℝ)*X 1 0+(-2016581459/10000000000 : ℝ)*X 1 1+(1298322647/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2679529643/5000000000 : ℝ)*X 2 0+(1298322483/2500000000 : ℝ)*X 2 1+(-403316211/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2135833949/5000000000 : ℝ)*X 0 0+(3979165849/10000000000 : ℝ)*X 0 1+(4582383059/10000000000 : ℝ)*X 0 2+(2135833949/5000000000 : ℝ)*X 1 0+(3979165849/10000000000 : ℝ)*X 1 1+(4582383059/10000000000 : ℝ)*X 1 2+(2135833949/5000000000 : ℝ)*X 2 0+(3979165849/10000000000 : ℝ)*X 2 1+(4582383059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-234830083/1250000000 : ℝ)*X 0 0+(259749127/500000000 : ℝ)*X 0 1+(5459485407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((528881791/1000000000 : ℝ)*X 1 0+(-175038669/1000000000 : ℝ)*X 1 1+(5459485197/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644409347/5000000000 : ℝ)*X 2 0+(5459484777/10000000000 : ℝ)*X 2 1+(-1750386191/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4271791803/10000000000 : ℝ)*X 0 0+(915714129/2000000000 : ℝ)*X 0 1+(995753131/2500000000 : ℝ)*X 0 2+(4271791803/10000000000 : ℝ)*X 1 0+(915714129/2000000000 : ℝ)*X 1 1+(995753131/2500000000 : ℝ)*X 1 2+(4271791803/10000000000 : ℝ)*X 2 0+(915714129/2000000000 : ℝ)*X 2 1+(995753131/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1502_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1783616645830594954272377517/255575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84337379/6250000000000 : ℝ)*(base19) + (828724591/50000000000000 : ℝ)*(base23) + (56824681/50000000000000 : ℝ)*(upper3) + (190643439/100000000000000 : ℝ)*(upper4) + (74787157/25000000000000 : ℝ)*(upper5) + (1347635840886581/50000000000000 : ℝ)*(major0) + (1347635840886581/50000000000000 : ℝ)*(major1) + (1347635840886581/50000000000000 : ℝ)*(major2) + (186635245404617/5000000000000 : ℝ)*(sp0) + (3732737243278577/100000000000000 : ℝ)*(sp1) + (1866368467613729/50000000000000 : ℝ)*(sp2) + (828895386043477/50000000000000 : ℝ)*(sp3) + (33684584301/100000000000000 : ℝ)*(sp4) + (6883077387/50000000000000 : ℝ)*(sp7) + (25903195910027/1562500000000 : ℝ)*(f.failure) + (3732738592676641/100000000000000 : ℝ)*(f.sum) + (164170095737729/25557500000000000000000000000 : ℝ)*base66 + (972285023885729161/511150000000000000000000000000000 : ℝ)*base68 + (6524184806437679161/511150000000000000000000000000000 : ℝ)*base70 + (2902245691702579161/511150000000000000000000000000000 : ℝ)*base72 + (46828617677303/51115000000000000000000000000 : ℝ)*base74 + (1213295061233029161/511150000000000000000000000000000 : ℝ)*base76 + (673328887053370839/511150000000000000000000000000000 : ℝ)*base77 + (460178912798870839/511150000000000000000000000000000 : ℝ)*base79 + (34619529589411/6389375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (284069/39062500000000000000 : ℝ)*base89 + (284069/39062500000000000000 : ℝ)*base91 + (284069/39062500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1311179127490388431018795317/127787500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (835534549/50000000000000 : ℝ)*(base19) + (591683711/25000000000000 : ℝ)*(base23) + (4117121/20000000000000 : ℝ)*(upper2) + (39683143/20000000000000 : ℝ)*(upper3) + (7340741/2500000000000 : ℝ)*(upper5) + (682472534307327/25000000000000 : ℝ)*(major0) + (682472534307327/25000000000000 : ℝ)*(major1) + (682472534307327/25000000000000 : ℝ)*(major2) + (18067283753/100000000000000 : ℝ)*(sp1) + (2531860759/10000000000000 : ℝ)*(sp2) + (378068231530167/10000000000000 : ℝ)*(sp4) + (189033128847441/5000000000000 : ℝ)*(sp5) + (945163657489809/25000000000000 : ℝ)*(sp6) + (209887202142029/12500000000000 : ℝ)*(sp7) + (209887202142029/12500000000000 : ℝ)*(f.failure) + (378068231530167/10000000000000 : ℝ)*(f.sum) + (6721120238039/6389375000000000000000000000 : ℝ)*base66 + (2752408954401312187/255575000000000000000000000000000 : ℝ)*base68 + (2082277967986662187/255575000000000000000000000000000 : ℝ)*base70 + (1460090083439187187/255575000000000000000000000000000 : ℝ)*base72 + (215669120192967/51115000000000000000000000000 : ℝ)*base74 + (4952156379709712187/255575000000000000000000000000000 : ℝ)*base76 + (1468986284994812187/255575000000000000000000000000000 : ℝ)*base78 + (1728956937821212187/255575000000000000000000000000000 : ℝ)*base80 + (52617168056151/25557500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3184713/312500000000000000000 : ℝ)*base89 + (3184713/312500000000000000000 : ℝ)*base91 + (3184713/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1502_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40645197/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18443/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (411/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5183/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4009/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1502_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1502_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40645197/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5183/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4009/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1502_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1502_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1502_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4499/1024 : ℝ) ≤ p) (hpb : p ≤ (4501/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40645197/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5183/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4009/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1502_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

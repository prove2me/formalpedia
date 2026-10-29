-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1421_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:52:04.401242+00:00
-- url     : https://prove2.me/submissions/0988cade-b668-482f-a1dd-29981175cf77

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
theorem support_rectangle_w1421_s6_0 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-7725147/39062500 : ℝ)*x 0 + (2704317471/5000000000 : ℝ)*x 1 + (2623361497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7725147/39062500 : ℝ)^4381 ≤ (12062778539633/100000000000000 : ℝ)^3357 := by
    have hnat : (7725147 : ℕ)^4381*100000000000000^3357 ≤ 12062778539633^3357*39062500^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7725147 39062500 12062778539633 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704317471/5000000000 : ℝ)^4381 ≤ (44840481270377/100000000000000 : ℝ)^3357 := by
    have hnat : (2704317471 : ℕ)^4381*100000000000000^3357 ≤ 44840481270377^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704317471 5000000000 44840481270377 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623361497/5000000000 : ℝ)^4381 ≤ (21548370086709/50000000000000 : ℝ)^3357 := by
    have hnat : (2623361497 : ℕ)^4381*50000000000000^3357 ≤ 21548370086709^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623361497 5000000000 21548370086709 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7725147/39062500 : ℝ), (2704317471/5000000000 : ℝ), (2623361497/5000000000 : ℝ)] ![(12062778539633/100000000000000 : ℝ), (44840481270377/100000000000000 : ℝ), (21548370086709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7725147/39062500 : ℝ)|^4381 ≤ (12062778539633/100000000000000 : ℝ)^3357
        have hw : |(-7725147/39062500 : ℝ)|=(7725147/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704317471/5000000000 : ℝ)|^4381 ≤ (44840481270377/100000000000000 : ℝ)^3357
        have hw : |(2704317471/5000000000 : ℝ)|=(2704317471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623361497/5000000000 : ℝ)|^4381 ≤ (21548370086709/50000000000000 : ℝ)^3357
        have hw : |(2623361497/5000000000 : ℝ)|=(2623361497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s6_1 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336873877/2500000000 : ℝ)*x 0 + (-2060075331/10000000000 : ℝ)*x 1 + (5246722969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336873877/2500000000 : ℝ)^4381 ≤ (22090065354007/50000000000000 : ℝ)^3357 := by
    have hnat : (1336873877 : ℕ)^4381*50000000000000^3357 ≤ 22090065354007^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336873877 2500000000 22090065354007 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2060075331/10000000000 : ℝ)^4381 ≤ (6361564688279/50000000000000 : ℝ)^3357 := by
    have hnat : (2060075331 : ℕ)^4381*50000000000000^3357 ≤ 6361564688279^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060075331 10000000000 6361564688279 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246722969/10000000000 : ℝ)^4381 ≤ (10774184976357/25000000000000 : ℝ)^3357 := by
    have hnat : (5246722969 : ℕ)^4381*25000000000000^3357 ≤ 10774184976357^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246722969 10000000000 10774184976357 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336873877/2500000000 : ℝ), (-2060075331/10000000000 : ℝ), (5246722969/10000000000 : ℝ)] ![(22090065354007/50000000000000 : ℝ), (6361564688279/50000000000000 : ℝ), (10774184976357/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336873877/2500000000 : ℝ)|^4381 ≤ (22090065354007/50000000000000 : ℝ)^3357
        have hw : |(1336873877/2500000000 : ℝ)|=(1336873877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2060075331/10000000000 : ℝ)|^4381 ≤ (6361564688279/50000000000000 : ℝ)^3357
        have hw : |(-2060075331/10000000000 : ℝ)|=(2060075331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246722969/10000000000 : ℝ)|^4381 ≤ (10774184976357/25000000000000 : ℝ)^3357
        have hw : |(5246722969/10000000000 : ℝ)|=(5246722969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s6_2 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673747833/5000000000 : ℝ)*x 0 + (524672283/1000000000 : ℝ)*x 1 + (-257509413/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673747833/5000000000 : ℝ)^4381 ≤ (44180132411567/100000000000000 : ℝ)^3357 := by
    have hnat : (2673747833 : ℕ)^4381*100000000000000^3357 ≤ 44180132411567^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673747833 5000000000 44180132411567 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524672283/1000000000 : ℝ)^4381 ≤ (8619347683081/20000000000000 : ℝ)^3357 := by
    have hnat : (524672283 : ℕ)^4381*20000000000000^3357 ≤ 8619347683081^3357*1000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524672283 1000000000 8619347683081 20000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257509413/1250000000 : ℝ)^4381 ≤ (12723129158939/100000000000000 : ℝ)^3357 := by
    have hnat : (257509413 : ℕ)^4381*100000000000000^3357 ≤ 12723129158939^3357*1250000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257509413 1250000000 12723129158939 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673747833/5000000000 : ℝ), (524672283/1000000000 : ℝ), (-257509413/1250000000 : ℝ)] ![(44180132411567/100000000000000 : ℝ), (8619347683081/20000000000000 : ℝ), (12723129158939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673747833/5000000000 : ℝ)|^4381 ≤ (44180132411567/100000000000000 : ℝ)^3357
        have hw : |(2673747833/5000000000 : ℝ)|=(2673747833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524672283/1000000000 : ℝ)|^4381 ≤ (8619347683081/20000000000000 : ℝ)^3357
        have hw : |(524672283/1000000000 : ℝ)|=(524672283/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-257509413/1250000000 : ℝ)|^4381 ≤ (12723129158939/100000000000000 : ℝ)^3357
        have hw : |(-257509413/1250000000 : ℝ)|=(257509413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s6_3 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4306377563/10000000000 : ℝ)*x 0 + (2067475739/5000000000 : ℝ)*x 1 + (4484194987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4306377563/10000000000 : ℝ)^4381 ≤ (33304564698521/100000000000000 : ℝ)^3357 := by
    have hnat : (4306377563 : ℕ)^4381*100000000000000^3357 ≤ 33304564698521^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306377563 10000000000 33304564698521 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2067475739/5000000000 : ℝ)^4381 ≤ (15792495465867/50000000000000 : ℝ)^3357 := by
    have hnat : (2067475739 : ℕ)^4381*50000000000000^3357 ≤ 15792495465867^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067475739 5000000000 15792495465867 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4484194987/10000000000 : ℝ)^4381 ≤ (2194402771499/6250000000000 : ℝ)^3357 := by
    have hnat : (4484194987 : ℕ)^4381*6250000000000^3357 ≤ 2194402771499^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484194987 10000000000 2194402771499 6250000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4306377563/10000000000 : ℝ), (2067475739/5000000000 : ℝ), (4484194987/10000000000 : ℝ)] ![(33304564698521/100000000000000 : ℝ), (15792495465867/50000000000000 : ℝ), (2194402771499/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4306377563/10000000000 : ℝ)|^4381 ≤ (33304564698521/100000000000000 : ℝ)^3357
        have hw : |(4306377563/10000000000 : ℝ)|=(4306377563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2067475739/5000000000 : ℝ)|^4381 ≤ (15792495465867/50000000000000 : ℝ)^3357
        have hw : |(2067475739/5000000000 : ℝ)|=(2067475739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4484194987/10000000000 : ℝ)|^4381 ≤ (2194402771499/6250000000000 : ℝ)^3357
        have hw : |(4484194987/10000000000 : ℝ)|=(4484194987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s6_4 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-988824399/5000000000 : ℝ)*x 0 + (5247306707/10000000000 : ℝ)*x 1 + (2704024191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (988824399/5000000000 : ℝ)^4381 ≤ (1206286742301/10000000000000 : ℝ)^3357 := by
    have hnat : (988824399 : ℕ)^4381*10000000000000^3357 ≤ 1206286742301^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988824399 5000000000 1206286742301 10000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247306707/10000000000 : ℝ)^4381 ≤ (43102997443951/100000000000000 : ℝ)^3357 := by
    have hnat : (5247306707 : ℕ)^4381*100000000000000^3357 ≤ 43102997443951^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247306707 10000000000 43102997443951 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704024191/5000000000 : ℝ)^4381 ≤ (11208533782161/25000000000000 : ℝ)^3357 := by
    have hnat : (2704024191 : ℕ)^4381*25000000000000^3357 ≤ 11208533782161^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704024191 5000000000 11208533782161 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-988824399/5000000000 : ℝ), (5247306707/10000000000 : ℝ), (2704024191/5000000000 : ℝ)] ![(1206286742301/10000000000000 : ℝ), (43102997443951/100000000000000 : ℝ), (11208533782161/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-988824399/5000000000 : ℝ)|^4381 ≤ (1206286742301/10000000000000 : ℝ)^3357
        have hw : |(-988824399/5000000000 : ℝ)|=(988824399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247306707/10000000000 : ℝ)|^4381 ≤ (43102997443951/100000000000000 : ℝ)^3357
        have hw : |(5247306707/10000000000 : ℝ)|=(5247306707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704024191/5000000000 : ℝ)|^4381 ≤ (11208533782161/25000000000000 : ℝ)^3357
        have hw : |(2704024191/5000000000 : ℝ)|=(2704024191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s6_5 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326359047/2500000000 : ℝ)*x 0 + (-1898749537/10000000000 : ℝ)*x 1 + (5408048371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326359047/2500000000 : ℝ)^4381 ≤ (43727192989597/100000000000000 : ℝ)^3357 := by
    have hnat : (1326359047 : ℕ)^4381*100000000000000^3357 ≤ 43727192989597^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326359047 2500000000 43727192989597 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1898749537/10000000000 : ℝ)^4381 ≤ (2859667995841/25000000000000 : ℝ)^3357 := by
    have hnat : (1898749537 : ℕ)^4381*25000000000000^3357 ≤ 2859667995841^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898749537 10000000000 2859667995841 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408048371/10000000000 : ℝ)^4381 ≤ (8966827001927/20000000000000 : ℝ)^3357 := by
    have hnat : (5408048371 : ℕ)^4381*20000000000000^3357 ≤ 8966827001927^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408048371 10000000000 8966827001927 20000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326359047/2500000000 : ℝ), (-1898749537/10000000000 : ℝ), (5408048371/10000000000 : ℝ)] ![(43727192989597/100000000000000 : ℝ), (2859667995841/25000000000000 : ℝ), (8966827001927/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326359047/2500000000 : ℝ)|^4381 ≤ (43727192989597/100000000000000 : ℝ)^3357
        have hw : |(1326359047/2500000000 : ℝ)|=(1326359047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1898749537/10000000000 : ℝ)|^4381 ≤ (2859667995841/25000000000000 : ℝ)^3357
        have hw : |(-1898749537/10000000000 : ℝ)|=(1898749537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408048371/10000000000 : ℝ)|^4381 ≤ (8966827001927/20000000000000 : ℝ)^3357
        have hw : |(5408048371/10000000000 : ℝ)|=(5408048371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s6_6 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652718293/5000000000 : ℝ)*x 0 + (5408047741/10000000000 : ℝ)*x 1 + (-94937493/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652718293/5000000000 : ℝ)^4381 ≤ (43727197270501/100000000000000 : ℝ)^3357 := by
    have hnat : (2652718293 : ℕ)^4381*100000000000000^3357 ≤ 43727197270501^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652718293 5000000000 43727197270501 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408047741/10000000000 : ℝ)^4381 ≤ (44834128193617/100000000000000 : ℝ)^3357 := by
    have hnat : (5408047741 : ℕ)^4381*100000000000000^3357 ≤ 44834128193617^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408047741 10000000000 44834128193617 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94937493/500000000 : ℝ)^4381 ≤ (11438674522771/100000000000000 : ℝ)^3357 := by
    have hnat : (94937493 : ℕ)^4381*100000000000000^3357 ≤ 11438674522771^3357*500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94937493 500000000 11438674522771 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652718293/5000000000 : ℝ), (5408047741/10000000000 : ℝ), (-94937493/500000000 : ℝ)] ![(43727197270501/100000000000000 : ℝ), (44834128193617/100000000000000 : ℝ), (11438674522771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652718293/5000000000 : ℝ)|^4381 ≤ (43727197270501/100000000000000 : ℝ)^3357
        have hw : |(2652718293/5000000000 : ℝ)|=(2652718293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408047741/10000000000 : ℝ)|^4381 ≤ (44834128193617/100000000000000 : ℝ)^3357
        have hw : |(5408047741/10000000000 : ℝ)|=(5408047741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94937493/500000000 : ℝ)|^4381 ≤ (11438674522771/100000000000000 : ℝ)^3357
        have hw : |(-94937493/500000000 : ℝ)|=(94937493/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s6_7 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2153200627/5000000000 : ℝ)*x 0 + (4482936893/10000000000 : ℝ)*x 1 + (258513561/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153200627/5000000000 : ℝ)^4381 ≤ (16652401904147/50000000000000 : ℝ)^3357 := by
    have hnat : (2153200627 : ℕ)^4381*50000000000000^3357 ≤ 16652401904147^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153200627 5000000000 16652401904147 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4482936893/10000000000 : ℝ)^4381 ≤ (35097589457239/100000000000000 : ℝ)^3357 := by
    have hnat : (4482936893 : ℕ)^4381*100000000000000^3357 ≤ 35097589457239^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482936893 10000000000 35097589457239 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258513561/625000000 : ℝ)^4381 ≤ (98742520963/312500000000 : ℝ)^3357 := by
    have hnat : (258513561 : ℕ)^4381*312500000000^3357 ≤ 98742520963^3357*625000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258513561 625000000 98742520963 312500000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2153200627/5000000000 : ℝ), (4482936893/10000000000 : ℝ), (258513561/625000000 : ℝ)] ![(16652401904147/50000000000000 : ℝ), (35097589457239/100000000000000 : ℝ), (98742520963/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2153200627/5000000000 : ℝ)|^4381 ≤ (16652401904147/50000000000000 : ℝ)^3357
        have hw : |(2153200627/5000000000 : ℝ)|=(2153200627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4482936893/10000000000 : ℝ)|^4381 ≤ (35097589457239/100000000000000 : ℝ)^3357
        have hw : |(4482936893/10000000000 : ℝ)|=(4482936893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258513561/625000000 : ℝ)|^4381 ≤ (98742520963/312500000000 : ℝ)^3357
        have hw : |(258513561/625000000 : ℝ)|=(258513561/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1421_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (11323/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14753/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14757/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (283/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14757/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (283/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14757/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (283/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14757/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (283/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14757/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (283/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14757/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (283/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (283/2500 : ℝ) ^ (1095/256 : ℝ) ≤ (4486895260100283/50000000000000000000 : ℝ) := by
    have hpowers : (283/2500 : ℝ)^1095 ≤ (4486895260100283/50000000000000000000 : ℝ)^256 := by
      have hnat : (283 : ℕ)^1095*50000000000000000000^256 ≤ 4486895260100283^256*2500^1095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        283 2500 4486895260100283 50000000000000000000 1095 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (283/2500 : ℝ)) (X := (4486895260100283/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14757/100000 : ℝ) ^ (1095/256 : ℝ) ≤ (27894534580198771/100000000000000000000 : ℝ) := by
    have hpowers : (14757/100000 : ℝ)^1095 ≤ (27894534580198771/100000000000000000000 : ℝ)^256 := by
      have hnat : (14757 : ℕ)^1095*100000000000000000000^256 ≤ 27894534580198771^256*100000^1095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14757 100000 27894534580198771 100000000000000000000 1095 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14757/100000 : ℝ)) (X := (27894534580198771/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004486895260100283/25000000000000000000 : ℝ) ≤ (5000209783783797/5000000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (25004486895260100283/25000000000000000000 : ℝ)^256 ≤ (5000209783783797/5000000000000000 : ℝ)^1095 := by
      have hnat : (25004486895260100283 : ℕ)^256*5000000000000000^1095 ≤ 5000209783783797^1095*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004486895260100283 25000000000000000000 5000209783783797 5000000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000209783783797/5000000000000000 : ℝ)) (X := (25004486895260100283/25000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036868325100399337/100000000000000000000 : ℝ) ≤ (1250107727835721/1250000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (100036868325100399337/100000000000000000000 : ℝ)^256 ≤ (1250107727835721/1250000000000000 : ℝ)^1095 := by
      have hnat : (100036868325100399337 : ℕ)^256*1250000000000000^1095 ≤ 1250107727835721^1095*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036868325100399337 100000000000000000000 1250107727835721 1250000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250107727835721/1250000000000000 : ℝ)) (X := (100036868325100399337/100000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027894534580198771/50000000000000000000 : ℝ) ≤ (5000652038901971/5000000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (50027894534580198771/50000000000000000000 : ℝ)^256 ≤ (5000652038901971/5000000000000000 : ℝ)^1095 := by
      have hnat : (50027894534580198771 : ℕ)^256*5000000000000000^1095 ≤ 5000652038901971^1095*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027894534580198771 50000000000000000000 5000652038901971 5000000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000652038901971/5000000000000000 : ℝ)) (X := (50027894534580198771/50000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4486895260100283/50000000000000000000 : ℝ) ≤ ((17180714698927180609/17185000000000000000 : ℝ)+2*(221127559087/171850000000000 : ℝ)*(283/2500 : ℝ))^(1095/256 : ℝ) := by
    rw [show (17180714698927180609/17185000000000000000 : ℝ)+2*(221127559087/171850000000000 : ℝ)*(283/2500 : ℝ)=(5000209783783797/5000000000000000 : ℝ) by norm_num, show 1+2*(4486895260100283/50000000000000000000 : ℝ)=(25004486895260100283/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27894534580198771/100000000000000000000 : ℝ)+(4486895260100283/50000000000000000000 : ℝ) ≤ ((17180714698927180609/17185000000000000000 : ℝ)+(221127559087/171850000000000 : ℝ)*((14757/100000 : ℝ)+(283/2500 : ℝ)))^(1095/256 : ℝ) := by
    rw [show (17180714698927180609/17185000000000000000 : ℝ)+(221127559087/171850000000000 : ℝ)*((14757/100000 : ℝ)+(283/2500 : ℝ))=(1250107727835721/1250000000000000 : ℝ) by norm_num, show 1+(27894534580198771/100000000000000000000 : ℝ)+(4486895260100283/50000000000000000000 : ℝ)=(100036868325100399337/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27894534580198771/100000000000000000000 : ℝ) ≤ ((17180714698927180609/17185000000000000000 : ℝ)+2*(221127559087/171850000000000 : ℝ)*(14757/100000 : ℝ))^(1095/256 : ℝ) := by
    rw [show (17180714698927180609/17185000000000000000 : ℝ)+2*(221127559087/171850000000000 : ℝ)*(14757/100000 : ℝ)=(5000652038901971/5000000000000000 : ℝ) by norm_num, show 1+2*(27894534580198771/100000000000000000000 : ℝ)=(50027894534580198771/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17180714698927180609/17185000000000000000 : ℝ)*(X 1 0+X 2 0)+(221127559087/171850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (283/2500 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (17180714698927180609/17185000000000000000 : ℝ)) (alpha := (221127559087/171850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17180714698927180609/17185000000000000000 : ℝ)*(X 0 1+X 2 1)+(221127559087/171850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (283/2500 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (17180714698927180609/17185000000000000000 : ℝ)) (alpha := (221127559087/171850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17180714698927180609/17185000000000000000 : ℝ)*(X 0 2+X 1 2)+(221127559087/171850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (283/2500 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (17180714698927180609/17185000000000000000 : ℝ)) (alpha := (221127559087/171850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-7725147/39062500 : ℝ)*X 0 0+(2704317471/5000000000 : ℝ)*X 0 1+(2623361497/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336873877/2500000000 : ℝ)*X 1 0+(-2060075331/10000000000 : ℝ)*X 1 1+(5246722969/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673747833/5000000000 : ℝ)*X 2 0+(524672283/1000000000 : ℝ)*X 2 1+(-257509413/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4306377563/10000000000 : ℝ)*X 0 0+(2067475739/5000000000 : ℝ)*X 0 1+(4484194987/10000000000 : ℝ)*X 0 2+(4306377563/10000000000 : ℝ)*X 1 0+(2067475739/5000000000 : ℝ)*X 1 1+(4484194987/10000000000 : ℝ)*X 1 2+(4306377563/10000000000 : ℝ)*X 2 0+(2067475739/5000000000 : ℝ)*X 2 1+(4484194987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-988824399/5000000000 : ℝ)*X 0 0+(5247306707/10000000000 : ℝ)*X 0 1+(2704024191/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326359047/2500000000 : ℝ)*X 1 0+(-1898749537/10000000000 : ℝ)*X 1 1+(5408048371/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652718293/5000000000 : ℝ)*X 2 0+(5408047741/10000000000 : ℝ)*X 2 1+(-94937493/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2153200627/5000000000 : ℝ)*X 0 0+(4482936893/10000000000 : ℝ)*X 0 1+(258513561/625000000 : ℝ)*X 0 2+(2153200627/5000000000 : ℝ)*X 1 0+(4482936893/10000000000 : ℝ)*X 1 1+(258513561/625000000 : ℝ)*X 1 2+(2153200627/5000000000 : ℝ)*X 2 0+(4482936893/10000000000 : ℝ)*X 2 1+(258513561/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (144718416096986699303600919/12275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (474078971/25000000000000 : ℝ)*(base19) + (1823137861/100000000000000 : ℝ)*(base23) + (68358499/50000000000000 : ℝ)*(lower2) + (267297411/100000000000000 : ℝ)*(upper3) + (36453343/25000000000000 : ℝ)*(upper5) + (451982121825793/10000000000000 : ℝ)*(major0) + (451982121825793/10000000000000 : ℝ)*(major1) + (451982121825793/10000000000000 : ℝ)*(major2) + (6176234581857251/100000000000000 : ℝ)*(sp0) + (3088135516237059/50000000000000 : ℝ)*(sp1) + (308813555282607/5000000000000 : ℝ)*(sp2) + (178959284757933/6250000000000 : ℝ)*(sp3) + (153387731/400000000000 : ℝ)*(sp4) + (20558609333/100000000000000 : ℝ)*(sp7) + (2863369114736261/100000000000000 : ℝ)*(f.failure) + (3088136464395001/50000000000000 : ℝ)*(f.sum) + (9226045813773/1718500000000000000000000000 : ℝ)*base65 + (482060921798502063/171850000000000000000000000000000 : ℝ)*base68 + (1033226197250552063/171850000000000000000000000000000 : ℝ)*base70 + (1052249141936752063/171850000000000000000000000000000 : ℝ)*base72 + (6255205558151/3437000000000000000000000000 : ℝ)*base74 + (1456144982654352063/171850000000000000000000000000000 : ℝ)*base76 + (815502274354352063/171850000000000000000000000000000 : ℝ)*base78 + (3233162462548302063/171850000000000000000000000000000 : ℝ)*base80 + (3428337361961/859250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (16337419/5000000000000000000000 : ℝ)*base89 + (16337419/5000000000000000000000 : ℝ)*base91 + (16337419/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (904592148869634966258885693/122750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (220296699/20000000000000 : ℝ)*(base19) + (1540601249/100000000000000 : ℝ)*(base23) + (421203527/100000000000000 : ℝ)*(lower1) + (2820093/50000000000000 : ℝ)*(upper2) + (172744043/100000000000000 : ℝ)*(lower5) + (4552649191765229/100000000000000 : ℝ)*(major0) + (4552649191765229/100000000000000 : ℝ)*(major1) + (4552649191765229/100000000000000 : ℝ)*(major2) + (4819397353/100000000000000 : ℝ)*(sp1) + (10197891/1000000000000 : ℝ)*(sp3) + (6221132048909161/100000000000000 : ℝ)*(sp4) + (6221126128028313/100000000000000 : ℝ)*(sp5) + (6221130508307911/100000000000000 : ℝ)*(sp6) + (144208253459299/5000000000000 : ℝ)*(sp7) + (72104152224377/2500000000000 : ℝ)*(f.failure) + (6221132048909161/100000000000000 : ℝ)*(f.sum) + (7985643995697/2148125000000000000000000000 : ℝ)*base65 + (32301259223312044461/1718500000000000000000000000000000 : ℝ)*base67 + (13227674268884544461/1718500000000000000000000000000000 : ℝ)*base69 + (17594214861123544461/1718500000000000000000000000000000 : ℝ)*base71 + (2043543523443/8592500000000000000000000000 : ℝ)*base73 + (28224333485241544461/1718500000000000000000000000000000 : ℝ)*base75 + (19898292570980544461/1718500000000000000000000000000000 : ℝ)*base77 + (19813029322368044461/1718500000000000000000000000000000 : ℝ)*base79 + (48362516388177/8592500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (674617/125000000000000000000 : ℝ)*base90 + (674617/125000000000000000000 : ℝ)*base92 + (674617/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1421_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1421_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1421_s7_0 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1977642519/10000000000 : ℝ)*x 0 + (5408608327/10000000000 : ℝ)*x 1 + (1311686557/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1977642519/10000000000 : ℝ)^4381 ≤ (12062817441017/100000000000000 : ℝ)^3357 := by
    have hnat : (1977642519 : ℕ)^4381*100000000000000^3357 ≤ 12062817441017^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977642519 10000000000 12062817441017 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408608327/10000000000 : ℝ)^4381 ≤ (2242009665569/5000000000000 : ℝ)^3357 := by
    have hnat : (5408608327 : ℕ)^4381*5000000000000^3357 ≤ 2242009665569^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408608327 10000000000 2242009665569 5000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311686557/2500000000 : ℝ)^4381 ≤ (43096989232553/100000000000000 : ℝ)^3357 := by
    have hnat : (1311686557 : ℕ)^4381*100000000000000^3357 ≤ 43096989232553^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311686557 2500000000 43096989232553 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1977642519/10000000000 : ℝ), (5408608327/10000000000 : ℝ), (1311686557/2500000000 : ℝ)] ![(12062817441017/100000000000000 : ℝ), (2242009665569/5000000000000 : ℝ), (43096989232553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1977642519/10000000000 : ℝ)|^4381 ≤ (12062817441017/100000000000000 : ℝ)^3357
        have hw : |(-1977642519/10000000000 : ℝ)|=(1977642519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408608327/10000000000 : ℝ)|^4381 ≤ (2242009665569/5000000000000 : ℝ)^3357
        have hw : |(5408608327/10000000000 : ℝ)|=(5408608327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311686557/2500000000 : ℝ)|^4381 ≤ (43096989232553/100000000000000 : ℝ)^3357
        have hw : |(1311686557/2500000000 : ℝ)|=(1311686557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s7_1 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106949763/200000000 : ℝ)*x 0 + (-1030027031/5000000000 : ℝ)*x 1 + (5246746361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106949763/200000000 : ℝ)^4381 ≤ (4418005137423/10000000000000 : ℝ)^3357 := by
    have hnat : (106949763 : ℕ)^4381*10000000000000^3357 ≤ 4418005137423^3357*200000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106949763 200000000 4418005137423 10000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030027031/5000000000 : ℝ)^4381 ≤ (12722957949591/100000000000000 : ℝ)^3357 := by
    have hnat : (1030027031 : ℕ)^4381*100000000000000^3357 ≤ 12722957949591^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030027031 5000000000 12722957949591 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246746361/10000000000 : ℝ)^4381 ≤ (2154849532913/5000000000000 : ℝ)^3357 := by
    have hnat : (5246746361 : ℕ)^4381*5000000000000^3357 ≤ 2154849532913^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246746361 10000000000 2154849532913 5000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106949763/200000000 : ℝ), (-1030027031/5000000000 : ℝ), (5246746361/10000000000 : ℝ)] ![(4418005137423/10000000000000 : ℝ), (12722957949591/100000000000000 : ℝ), (2154849532913/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106949763/200000000 : ℝ)|^4381 ≤ (4418005137423/10000000000000 : ℝ)^3357
        have hw : |(106949763/200000000 : ℝ)|=(106949763/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1030027031/5000000000 : ℝ)|^4381 ≤ (12722957949591/100000000000000 : ℝ)^3357
        have hw : |(-1030027031/5000000000 : ℝ)|=(1030027031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246746361/10000000000 : ℝ)|^4381 ≤ (2154849532913/5000000000000 : ℝ)^3357
        have hw : |(5246746361/10000000000 : ℝ)|=(5246746361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s7_2 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347488163/10000000000 : ℝ)*x 0 + (1049349263/2000000000 : ℝ)*x 1 + (-1030027053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347488163/10000000000 : ℝ)^4381 ≤ (8836010302879/20000000000000 : ℝ)^3357 := by
    have hnat : (5347488163 : ℕ)^4381*20000000000000^3357 ≤ 8836010302879^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347488163 10000000000 8836010302879 20000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049349263/2000000000 : ℝ)^4381 ≤ (43096990165159/100000000000000 : ℝ)^3357 := by
    have hnat : (1049349263 : ℕ)^4381*100000000000000^3357 ≤ 43096990165159^3357*2000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049349263 2000000000 43096990165159 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030027053/5000000000 : ℝ)^4381 ≤ (3180739576057/25000000000000 : ℝ)^3357 := by
    have hnat : (1030027053 : ℕ)^4381*25000000000000^3357 ≤ 3180739576057^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030027053 5000000000 3180739576057 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347488163/10000000000 : ℝ), (1049349263/2000000000 : ℝ), (-1030027053/5000000000 : ℝ)] ![(8836010302879/20000000000000 : ℝ), (43096990165159/100000000000000 : ℝ), (3180739576057/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347488163/10000000000 : ℝ)|^4381 ≤ (8836010302879/20000000000000 : ℝ)^3357
        have hw : |(5347488163/10000000000 : ℝ)|=(5347488163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049349263/2000000000 : ℝ)|^4381 ≤ (43096990165159/100000000000000 : ℝ)^3357
        have hw : |(1049349263/2000000000 : ℝ)|=(1049349263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1030027053/5000000000 : ℝ)|^4381 ≤ (3180739576057/25000000000000 : ℝ)^3357
        have hw : |(-1030027053/5000000000 : ℝ)|=(1030027053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s7_3 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2153189679/5000000000 : ℝ)*x 0 + (4135005297/10000000000 : ℝ)*x 1 + (4484140711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153189679/5000000000 : ℝ)^4381 ≤ (16652291407589/50000000000000 : ℝ)^3357 := by
    have hnat : (2153189679 : ℕ)^4381*50000000000000^3357 ≤ 16652291407589^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153189679 5000000000 16652291407589 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4135005297/10000000000 : ℝ)^4381 ≤ (1974095464407/6250000000000 : ℝ)^3357 := by
    have hnat : (4135005297 : ℕ)^4381*6250000000000^3357 ≤ 1974095464407^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135005297 10000000000 1974095464407 6250000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4484140711/10000000000 : ℝ)^4381 ≤ (17554944871407/50000000000000 : ℝ)^3357 := by
    have hnat : (4484140711 : ℕ)^4381*50000000000000^3357 ≤ 17554944871407^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484140711 10000000000 17554944871407 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2153189679/5000000000 : ℝ), (4135005297/10000000000 : ℝ), (4484140711/10000000000 : ℝ)] ![(16652291407589/50000000000000 : ℝ), (1974095464407/6250000000000 : ℝ), (17554944871407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2153189679/5000000000 : ℝ)|^4381 ≤ (16652291407589/50000000000000 : ℝ)^3357
        have hw : |(2153189679/5000000000 : ℝ)|=(2153189679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4135005297/10000000000 : ℝ)|^4381 ≤ (1974095464407/6250000000000 : ℝ)^3357
        have hw : |(4135005297/10000000000 : ℝ)|=(4135005297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4484140711/10000000000 : ℝ)|^4381 ≤ (17554944871407/50000000000000 : ℝ)^3357
        have hw : |(4484140711/10000000000 : ℝ)|=(4484140711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s7_4 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1977653981/10000000000 : ℝ)*x 0 + (1311832393/2500000000 : ℝ)*x 1 + (676002739/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1977653981/10000000000 : ℝ)^4381 ≤ (12062908680679/100000000000000 : ℝ)^3357 := by
    have hnat : (1977653981 : ℕ)^4381*100000000000000^3357 ≤ 12062908680679^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977653981 10000000000 12062908680679 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311832393/2500000000 : ℝ)^4381 ≤ (4310324255587/10000000000000 : ℝ)^3357 := by
    have hnat : (1311832393 : ℕ)^4381*10000000000000^3357 ≤ 4310324255587^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311832393 2500000000 4310324255587 10000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676002739/1250000000 : ℝ)^4381 ≤ (44833848747937/100000000000000 : ℝ)^3357 := by
    have hnat : (676002739 : ℕ)^4381*100000000000000^3357 ≤ 44833848747937^3357*1250000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676002739 1250000000 44833848747937 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1977653981/10000000000 : ℝ), (1311832393/2500000000 : ℝ), (676002739/1250000000 : ℝ)] ![(12062908680679/100000000000000 : ℝ), (4310324255587/10000000000000 : ℝ), (44833848747937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1977653981/10000000000 : ℝ)|^4381 ≤ (12062908680679/100000000000000 : ℝ)^3357
        have hw : |(-1977653981/10000000000 : ℝ)|=(1977653981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311832393/2500000000 : ℝ)|^4381 ≤ (4310324255587/10000000000000 : ℝ)^3357
        have hw : |(1311832393/2500000000 : ℝ)|=(1311832393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676002739/1250000000 : ℝ)|^4381 ≤ (44833848747937/100000000000000 : ℝ)^3357
        have hw : |(676002739/1250000000 : ℝ)|=(676002739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s7_5 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061088339/2000000000 : ℝ)*x 0 + (-1898778063/10000000000 : ℝ)*x 1 + (5408022167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061088339/2000000000 : ℝ)^4381 ≤ (546590652789/1250000000000 : ℝ)^3357 := by
    have hnat : (1061088339 : ℕ)^4381*1250000000000^3357 ≤ 546590652789^3357*2000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061088339 2000000000 546590652789 1250000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1898778063/10000000000 : ℝ)^4381 ≤ (2859724063409/25000000000000 : ℝ)^3357 := by
    have hnat : (1898778063 : ℕ)^4381*25000000000000^3357 ≤ 2859724063409^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898778063 10000000000 2859724063409 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408022167/10000000000 : ℝ)^4381 ≤ (44833851506797/100000000000000 : ℝ)^3357 := by
    have hnat : (5408022167 : ℕ)^4381*100000000000000^3357 ≤ 44833851506797^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408022167 10000000000 44833851506797 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061088339/2000000000 : ℝ), (-1898778063/10000000000 : ℝ), (5408022167/10000000000 : ℝ)] ![(546590652789/1250000000000 : ℝ), (2859724063409/25000000000000 : ℝ), (44833851506797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061088339/2000000000 : ℝ)|^4381 ≤ (546590652789/1250000000000 : ℝ)^3357
        have hw : |(1061088339/2000000000 : ℝ)|=(1061088339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1898778063/10000000000 : ℝ)|^4381 ≤ (2859724063409/25000000000000 : ℝ)^3357
        have hw : |(-1898778063/10000000000 : ℝ)|=(1898778063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408022167/10000000000 : ℝ)|^4381 ≤ (44833851506797/100000000000000 : ℝ)^3357
        have hw : |(5408022167/10000000000 : ℝ)|=(5408022167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s7_6 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265272071/500000000 : ℝ)*x 0 + (1352005557/2500000000 : ℝ)*x 1 + (-474694589/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265272071/500000000 : ℝ)^4381 ≤ (5465906158151/12500000000000 : ℝ)^3357 := by
    have hnat : (265272071 : ℕ)^4381*12500000000000^3357 ≤ 5465906158151^3357*500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265272071 500000000 5465906158151 12500000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352005557/2500000000 : ℝ)^4381 ≤ (1120846304169/2500000000000 : ℝ)^3357 := by
    have hnat : (1352005557 : ℕ)^4381*2500000000000^3357 ≤ 1120846304169^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352005557 2500000000 1120846304169 2500000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (474694589/2500000000 : ℝ)^4381 ≤ (2859724639299/25000000000000 : ℝ)^3357 := by
    have hnat : (474694589 : ℕ)^4381*25000000000000^3357 ≤ 2859724639299^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474694589 2500000000 2859724639299 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265272071/500000000 : ℝ), (1352005557/2500000000 : ℝ), (-474694589/2500000000 : ℝ)] ![(5465906158151/12500000000000 : ℝ), (1120846304169/2500000000000 : ℝ), (2859724639299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265272071/500000000 : ℝ)|^4381 ≤ (5465906158151/12500000000000 : ℝ)^3357
        have hw : |(265272071/500000000 : ℝ)|=(265272071/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352005557/2500000000 : ℝ)|^4381 ≤ (1120846304169/2500000000000 : ℝ)^3357
        have hw : |(1352005557/2500000000 : ℝ)|=(1352005557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-474694589/2500000000 : ℝ)|^4381 ≤ (2859724639299/25000000000000 : ℝ)^3357
        have hw : |(-474694589/2500000000 : ℝ)|=(474694589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s7_7 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4306404189/10000000000 : ℝ)*x 0 + (4482882373/10000000000 : ℝ)*x 1 + (4136269881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4306404189/10000000000 : ℝ)^4381 ≤ (6660966686169/20000000000000 : ℝ)^3357 := by
    have hnat : (4306404189 : ℕ)^4381*20000000000000^3357 ≤ 6660966686169^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306404189 10000000000 6660966686169 20000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4482882373/10000000000 : ℝ)^4381 ≤ (8774258102631/25000000000000 : ℝ)^3357 := by
    have hnat : (4482882373 : ℕ)^4381*25000000000000^3357 ≤ 8774258102631^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482882373 10000000000 8774258102631 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4136269881/10000000000 : ℝ)^4381 ≤ (31598134144871/100000000000000 : ℝ)^3357 := by
    have hnat : (4136269881 : ℕ)^4381*100000000000000^3357 ≤ 31598134144871^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4136269881 10000000000 31598134144871 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4306404189/10000000000 : ℝ), (4482882373/10000000000 : ℝ), (4136269881/10000000000 : ℝ)] ![(6660966686169/20000000000000 : ℝ), (8774258102631/25000000000000 : ℝ), (31598134144871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4306404189/10000000000 : ℝ)|^4381 ≤ (6660966686169/20000000000000 : ℝ)^3357
        have hw : |(4306404189/10000000000 : ℝ)|=(4306404189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4482882373/10000000000 : ℝ)|^4381 ≤ (8774258102631/25000000000000 : ℝ)^3357
        have hw : |(4482882373/10000000000 : ℝ)|=(4482882373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4136269881/10000000000 : ℝ)|^4381 ≤ (31598134144871/100000000000000 : ℝ)^3357
        have hw : |(4136269881/10000000000 : ℝ)|=(4136269881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1421_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2831/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (461/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14753/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11323/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14753/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11323/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14753/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11323/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14753/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11323/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14753/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11323/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14753/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11323/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11323/100000 : ℝ) ^ (1095/256 : ℝ) ≤ (8983967373406863/100000000000000000000 : ℝ) := by
    have hpowers : (11323/100000 : ℝ)^1095 ≤ (8983967373406863/100000000000000000000 : ℝ)^256 := by
      have hnat : (11323 : ℕ)^1095*100000000000000000000^256 ≤ 8983967373406863^256*100000^1095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11323 100000 8983967373406863 100000000000000000000 1095 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11323/100000 : ℝ)) (X := (8983967373406863/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14753/100000 : ℝ) ^ (1095/256 : ℝ) ≤ (27862207812549581/100000000000000000000 : ℝ) := by
    have hpowers : (14753/100000 : ℝ)^1095 ≤ (27862207812549581/100000000000000000000 : ℝ)^256 := by
      have hnat : (14753 : ℕ)^1095*100000000000000000000^256 ≤ 27862207812549581^256*100000^1095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14753 100000 27862207812549581 100000000000000000000 1095 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14753/100000 : ℝ)) (X := (27862207812549581/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008983967373406863/50000000000000000000 : ℝ) ≤ (500021002167567/500000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (50008983967373406863/50000000000000000000 : ℝ)^256 ≤ (500021002167567/500000000000000 : ℝ)^1095 := by
      have hnat : (50008983967373406863 : ℕ)^256*500000000000000^1095 ≤ 500021002167567^1095*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008983967373406863 50000000000000000000 500021002167567 500000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500021002167567/500000000000000 : ℝ)) (X := (50008983967373406863/50000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009211543796489111/25000000000000000000 : ℝ) ≤ (10000861304989213/10000000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (25009211543796489111/25000000000000000000 : ℝ)^256 ≤ (10000861304989213/10000000000000000 : ℝ)^1095 := by
      have hnat : (25009211543796489111 : ℕ)^256*10000000000000000^1095 ≤ 10000861304989213^1095*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009211543796489111 25000000000000000000 10000861304989213 10000000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000861304989213/10000000000000000 : ℝ)) (X := (25009211543796489111/25000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027862207812549581/50000000000000000000 : ℝ) ≤ (5000651283313543/5000000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (50027862207812549581/50000000000000000000 : ℝ)^256 ≤ (5000651283313543/5000000000000000 : ℝ)^1095 := by
      have hnat : (50027862207812549581 : ℕ)^256*5000000000000000^1095 ≤ 5000651283313543^1095*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027862207812549581 50000000000000000000 5000651283313543 5000000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000651283313543/5000000000000000 : ℝ)) (X := (50027862207812549581/50000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8983967373406863/100000000000000000000 : ℝ) ≤ ((2449389138403130303/2450000000000000000 : ℝ)+2*(63037376839/49000000000000 : ℝ)*(11323/100000 : ℝ))^(1095/256 : ℝ) := by
    rw [show (2449389138403130303/2450000000000000000 : ℝ)+2*(63037376839/49000000000000 : ℝ)*(11323/100000 : ℝ)=(500021002167567/500000000000000 : ℝ) by norm_num, show 1+2*(8983967373406863/100000000000000000000 : ℝ)=(50008983967373406863/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27862207812549581/100000000000000000000 : ℝ)+(8983967373406863/100000000000000000000 : ℝ) ≤ ((2449389138403130303/2450000000000000000 : ℝ)+(63037376839/49000000000000 : ℝ)*((14753/100000 : ℝ)+(11323/100000 : ℝ)))^(1095/256 : ℝ) := by
    rw [show (2449389138403130303/2450000000000000000 : ℝ)+(63037376839/49000000000000 : ℝ)*((14753/100000 : ℝ)+(11323/100000 : ℝ))=(10000861304989213/10000000000000000 : ℝ) by norm_num, show 1+(27862207812549581/100000000000000000000 : ℝ)+(8983967373406863/100000000000000000000 : ℝ)=(25009211543796489111/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27862207812549581/100000000000000000000 : ℝ) ≤ ((2449389138403130303/2450000000000000000 : ℝ)+2*(63037376839/49000000000000 : ℝ)*(14753/100000 : ℝ))^(1095/256 : ℝ) := by
    rw [show (2449389138403130303/2450000000000000000 : ℝ)+2*(63037376839/49000000000000 : ℝ)*(14753/100000 : ℝ)=(5000651283313543/5000000000000000 : ℝ) by norm_num, show 1+2*(27862207812549581/100000000000000000000 : ℝ)=(50027862207812549581/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2449389138403130303/2450000000000000000 : ℝ)*(X 1 0+X 2 0)+(63037376839/49000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (11323/100000 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (2449389138403130303/2450000000000000000 : ℝ)) (alpha := (63037376839/49000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2449389138403130303/2450000000000000000 : ℝ)*(X 0 1+X 2 1)+(63037376839/49000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (11323/100000 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (2449389138403130303/2450000000000000000 : ℝ)) (alpha := (63037376839/49000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2449389138403130303/2450000000000000000 : ℝ)*(X 0 2+X 1 2)+(63037376839/49000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (11323/100000 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (2449389138403130303/2450000000000000000 : ℝ)) (alpha := (63037376839/49000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1977642519/10000000000 : ℝ)*X 0 0+(5408608327/10000000000 : ℝ)*X 0 1+(1311686557/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((106949763/200000000 : ℝ)*X 1 0+(-1030027031/5000000000 : ℝ)*X 1 1+(5246746361/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347488163/10000000000 : ℝ)*X 2 0+(1049349263/2000000000 : ℝ)*X 2 1+(-1030027053/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2153189679/5000000000 : ℝ)*X 0 0+(4135005297/10000000000 : ℝ)*X 0 1+(4484140711/10000000000 : ℝ)*X 0 2+(2153189679/5000000000 : ℝ)*X 1 0+(4135005297/10000000000 : ℝ)*X 1 1+(4484140711/10000000000 : ℝ)*X 1 2+(2153189679/5000000000 : ℝ)*X 2 0+(4135005297/10000000000 : ℝ)*X 2 1+(4484140711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1977653981/10000000000 : ℝ)*X 0 0+(1311832393/2500000000 : ℝ)*X 0 1+(676002739/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061088339/2000000000 : ℝ)*X 1 0+(-1898778063/10000000000 : ℝ)*X 1 1+(5408022167/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265272071/500000000 : ℝ)*X 2 0+(1352005557/2500000000 : ℝ)*X 2 1+(-474694589/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4306404189/10000000000 : ℝ)*X 0 0+(4482882373/10000000000 : ℝ)*X 0 1+(4136269881/10000000000 : ℝ)*X 0 2+(4306404189/10000000000 : ℝ)*X 1 0+(4482882373/10000000000 : ℝ)*X 1 1+(4136269881/10000000000 : ℝ)*X 1 2+(4306404189/10000000000 : ℝ)*X 2 0+(4482882373/10000000000 : ℝ)*X 2 1+(4136269881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (392968983453605396175785931/61250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35556681/3125000000000 : ℝ)*(base19) + (215046993/20000000000000 : ℝ)*(base23) + (20747777/50000000000000 : ℝ)*(lower2) + (191131831/100000000000000 : ℝ)*(upper3) + (81401607/100000000000000 : ℝ)*(upper5) + (4521198470620241/100000000000000 : ℝ)*(major0) + (4521198470620241/100000000000000 : ℝ)*(major1) + (4521198470620241/100000000000000 : ℝ)*(major2) + (3089064162966907/50000000000000 : ℝ)*(sp0) + (6178153966452317/100000000000000 : ℝ)*(sp1) + (6178154029031143/100000000000000 : ℝ)*(sp2) + (1432114428907721/50000000000000 : ℝ)*(sp3) + (5355666459/20000000000000 : ℝ)*(sp4) + (6382649127/50000000000000 : ℝ)*(sp7) + (89507550722303/3125000000000 : ℝ)*(f.failure) + (6178155104266109/100000000000000 : ℝ)*(f.sum) + (2308960964749/2450000000000000000000000000 : ℝ)*base65 + (1379482798432213023/245000000000000000000000000000000 : ℝ)*base67 + (1202818508602213023/245000000000000000000000000000000 : ℝ)*base69 + (1347631363222213023/245000000000000000000000000000000 : ℝ)*base71 + (1436924838701/2450000000000000000000000000 : ℝ)*base74 + (987571358622786977/245000000000000000000000000000000 : ℝ)*base76 + (3098568757267213023/245000000000000000000000000000000 : ℝ)*base77 + (2431000472317213023/245000000000000000000000000000000 : ℝ)*base79 + (2814345502901/2450000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (313837/156250000000000000000 : ℝ)*base89 + (313837/156250000000000000000 : ℝ)*base91 + (313837/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (140752237136742854961767241/61250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (840506073/100000000000000 : ℝ)*(base19) + (507172293/100000000000000 : ℝ)*(base23) + (249707111/100000000000000 : ℝ)*(lower1) + (99019857/100000000000000 : ℝ)*(upper3) + (45364101/100000000000000 : ℝ)*(lower4) + (129482917/100000000000000 : ℝ)*(upper5) + (4554055059485349/100000000000000 : ℝ)*(major0) + (4554055059485349/100000000000000 : ℝ)*(major1) + (4554055059485349/100000000000000 : ℝ)*(major2) + (12148097149/100000000000000 : ℝ)*(sp1) + (6223053316794259/100000000000000 : ℝ)*(sp4) + (3111520164095519/50000000000000 : ℝ)*(sp5) + (3111526404810983/50000000000000 : ℝ)*(sp6) + (22539505668567/781250000000 : ℝ)*(sp7) + (22539505668567/781250000000 : ℝ)*(f.failure) + (6223053316794259/100000000000000 : ℝ)*(f.sum) + (9144272941439/2450000000000000000000000000 : ℝ)*base66 + (859214093663019253/245000000000000000000000000000000 : ℝ)*base68 + (910325682676980747/245000000000000000000000000000000 : ℝ)*base69 + (1618289907523019253/245000000000000000000000000000000 : ℝ)*base72 + (9533931797389/2450000000000000000000000000 : ℝ)*base74 + (3459778744438019253/245000000000000000000000000000000 : ℝ)*base76 + (810137307723019253/245000000000000000000000000000000 : ℝ)*base78 + (2063274703163019253/245000000000000000000000000000000 : ℝ)*base80 + (98210509811/2450000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (31317/9765625000000000000 : ℝ)*base89 + (31317/9765625000000000000 : ℝ)*base91 + (31317/9765625000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1421_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (461/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1421_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1421_box_0 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-908201967/5000000000 : ℝ)*x 0 + (5386597529/10000000000 : ℝ)*x 1 + (1077319577/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (908201967/5000000000 : ℝ)^4381 ≤ (10795601603609/100000000000000 : ℝ)^3357 := by
    have hnat : (908201967 : ℕ)^4381*100000000000000^3357 ≤ 10795601603609^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908201967 5000000000 10795601603609 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386597529/10000000000 : ℝ)^4381 ≤ (11150549315663/25000000000000 : ℝ)^3357 := by
    have hnat : (5386597529 : ℕ)^4381*25000000000000^3357 ≤ 11150549315663^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386597529 10000000000 11150549315663 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077319577/2000000000 : ℝ)^4381 ≤ (5575275138697/12500000000000 : ℝ)^3357 := by
    have hnat : (1077319577 : ℕ)^4381*12500000000000^3357 ≤ 5575275138697^3357*2000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077319577 2000000000 5575275138697 12500000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-908201967/5000000000 : ℝ), (5386597529/10000000000 : ℝ), (1077319577/2000000000 : ℝ)] ![(10795601603609/100000000000000 : ℝ), (11150549315663/25000000000000 : ℝ), (5575275138697/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-908201967/5000000000 : ℝ)|^4381 ≤ (10795601603609/100000000000000 : ℝ)^3357
        have hw : |(-908201967/5000000000 : ℝ)|=(908201967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386597529/10000000000 : ℝ)|^4381 ≤ (11150549315663/25000000000000 : ℝ)^3357
        have hw : |(5386597529/10000000000 : ℝ)|=(5386597529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077319577/2000000000 : ℝ)|^4381 ≤ (5575275138697/12500000000000 : ℝ)^3357
        have hw : |(1077319577/2000000000 : ℝ)|=(1077319577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_box_1 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643002689/5000000000 : ℝ)*x 0 + (-390914143/2000000000 : ℝ)*x 1 + (5386597719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643002689/5000000000 : ℝ)^4381 ≤ (1740732450359/4000000000000 : ℝ)^3357 := by
    have hnat : (2643002689 : ℕ)^4381*4000000000000^3357 ≤ 1740732450359^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643002689 5000000000 1740732450359 4000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (390914143/2000000000 : ℝ)^4381 ≤ (11879489401857/100000000000000 : ℝ)^3357 := by
    have hnat : (390914143 : ℕ)^4381*100000000000000^3357 ≤ 11879489401857^3357*2000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390914143 2000000000 11879489401857 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386597719/10000000000 : ℝ)^4381 ≤ (22301099657893/50000000000000 : ℝ)^3357 := by
    have hnat : (5386597719 : ℕ)^4381*50000000000000^3357 ≤ 22301099657893^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386597719 10000000000 22301099657893 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643002689/5000000000 : ℝ), (-390914143/2000000000 : ℝ), (5386597719/10000000000 : ℝ)] ![(1740732450359/4000000000000 : ℝ), (11879489401857/100000000000000 : ℝ), (22301099657893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643002689/5000000000 : ℝ)|^4381 ≤ (1740732450359/4000000000000 : ℝ)^3357
        have hw : |(2643002689/5000000000 : ℝ)|=(2643002689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-390914143/2000000000 : ℝ)|^4381 ≤ (11879489401857/100000000000000 : ℝ)^3357
        have hw : |(-390914143/2000000000 : ℝ)|=(390914143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386597719/10000000000 : ℝ)|^4381 ≤ (22301099657893/50000000000000 : ℝ)^3357
        have hw : |(5386597719/10000000000 : ℝ)|=(5386597719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_box_2 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (660750703/1250000000 : ℝ)*x 0 + (5386597633/10000000000 : ℝ)*x 1 + (-3909141/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660750703/1250000000 : ℝ)^4381 ≤ (43518313902001/100000000000000 : ℝ)^3357 := by
    have hnat : (660750703 : ℕ)^4381*100000000000000^3357 ≤ 43518313902001^3357*1250000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660750703 1250000000 43518313902001 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386597633/10000000000 : ℝ)^4381 ≤ (44602198386473/100000000000000 : ℝ)^3357 := by
    have hnat : (5386597633 : ℕ)^4381*100000000000000^3357 ≤ 44602198386473^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386597633 10000000000 44602198386473 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3909141/20000000 : ℝ)^4381 ≤ (5939743848267/50000000000000 : ℝ)^3357 := by
    have hnat : (3909141 : ℕ)^4381*50000000000000^3357 ≤ 5939743848267^3357*20000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3909141 20000000 5939743848267 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660750703/1250000000 : ℝ), (5386597633/10000000000 : ℝ), (-3909141/20000000 : ℝ)] ![(43518313902001/100000000000000 : ℝ), (44602198386473/100000000000000 : ℝ), (5939743848267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660750703/1250000000 : ℝ)|^4381 ≤ (43518313902001/100000000000000 : ℝ)^3357
        have hw : |(660750703/1250000000 : ℝ)|=(660750703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386597633/10000000000 : ℝ)|^4381 ≤ (44602198386473/100000000000000 : ℝ)^3357
        have hw : |(5386597633/10000000000 : ℝ)|=(5386597633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3909141/20000000 : ℝ)|^4381 ≤ (5939743848267/50000000000000 : ℝ)^3357
        have hw : |(-3909141/20000000 : ℝ)|=(3909141/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_box_3 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4452836227/10000000000 : ℝ)*x 0 + (4236875267/10000000000 : ℝ)*x 1 + (4236875147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4452836227/10000000000 : ℝ)^4381 ≤ (34790357060897/100000000000000 : ℝ)^3357 := by
    have hnat : (4452836227 : ℕ)^4381*100000000000000^3357 ≤ 34790357060897^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4452836227 10000000000 34790357060897 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4236875267/10000000000 : ℝ)^4381 ≤ (2037801378703/6250000000000 : ℝ)^3357 := by
    have hnat : (4236875267 : ℕ)^4381*6250000000000^3357 ≤ 2037801378703^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236875267 10000000000 2037801378703 6250000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4236875147/10000000000 : ℝ)^4381 ≤ (32604820854103/100000000000000 : ℝ)^3357 := by
    have hnat : (4236875147 : ℕ)^4381*100000000000000^3357 ≤ 32604820854103^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236875147 10000000000 32604820854103 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4452836227/10000000000 : ℝ), (4236875267/10000000000 : ℝ), (4236875147/10000000000 : ℝ)] ![(34790357060897/100000000000000 : ℝ), (2037801378703/6250000000000 : ℝ), (32604820854103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4452836227/10000000000 : ℝ)|^4381 ≤ (34790357060897/100000000000000 : ℝ)^3357
        have hw : |(4452836227/10000000000 : ℝ)|=(4452836227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4236875267/10000000000 : ℝ)|^4381 ≤ (2037801378703/6250000000000 : ℝ)^3357
        have hw : |(4236875267/10000000000 : ℝ)|=(4236875267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4236875147/10000000000 : ℝ)|^4381 ≤ (32604820854103/100000000000000 : ℝ)^3357
        have hw : |(4236875147/10000000000 : ℝ)|=(4236875147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_box_4 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2141617949/10000000000 : ℝ)*x 0 + (5266405919/10000000000 : ℝ)*x 1 + (5266406039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141617949/10000000000 : ℝ)^4381 ≤ (6692145659773/50000000000000 : ℝ)^3357 := by
    have hnat : (2141617949 : ℕ)^4381*50000000000000^3357 ≤ 6692145659773^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141617949 10000000000 6692145659773 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266405919/10000000000 : ℝ)^4381 ≤ (5413481711017/12500000000000 : ℝ)^3357 := by
    have hnat : (5266405919 : ℕ)^4381*12500000000000^3357 ≤ 5413481711017^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266405919 10000000000 5413481711017 12500000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266406039/10000000000 : ℝ)^4381 ≤ (43307854975957/100000000000000 : ℝ)^3357 := by
    have hnat : (5266406039 : ℕ)^4381*100000000000000^3357 ≤ 43307854975957^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266406039 10000000000 43307854975957 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2141617949/10000000000 : ℝ), (5266405919/10000000000 : ℝ), (5266406039/10000000000 : ℝ)] ![(6692145659773/50000000000000 : ℝ), (5413481711017/12500000000000 : ℝ), (43307854975957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2141617949/10000000000 : ℝ)|^4381 ≤ (6692145659773/50000000000000 : ℝ)^3357
        have hw : |(-2141617949/10000000000 : ℝ)|=(2141617949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266405919/10000000000 : ℝ)|^4381 ≤ (5413481711017/12500000000000 : ℝ)^3357
        have hw : |(5266405919/10000000000 : ℝ)|=(5266405919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266406039/10000000000 : ℝ)|^4381 ≤ (43307854975957/100000000000000 : ℝ)^3357
        have hw : |(5266406039/10000000000 : ℝ)|=(5266406039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_box_5 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074029891/2000000000 : ℝ)*x 0 + (-250414833/1250000000 : ℝ)*x 1 + (2633202767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074029891/2000000000 : ℝ)^4381 ≤ (11106135687627/25000000000000 : ℝ)^3357 := by
    have hnat : (1074029891 : ℕ)^4381*25000000000000^3357 ≤ 11106135687627^3357*2000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074029891 2000000000 11106135687627 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250414833/1250000000 : ℝ)^4381 ≤ (490704307179/4000000000000 : ℝ)^3357 := by
    have hnat : (250414833 : ℕ)^4381*4000000000000^3357 ≤ 490704307179^3357*1250000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250414833 1250000000 490704307179 4000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633202767/5000000000 : ℝ)^4381 ≤ (21653924778189/50000000000000 : ℝ)^3357 := by
    have hnat : (2633202767 : ℕ)^4381*50000000000000^3357 ≤ 21653924778189^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633202767 5000000000 21653924778189 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074029891/2000000000 : ℝ), (-250414833/1250000000 : ℝ), (2633202767/5000000000 : ℝ)] ![(11106135687627/25000000000000 : ℝ), (490704307179/4000000000000 : ℝ), (21653924778189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074029891/2000000000 : ℝ)|^4381 ≤ (11106135687627/25000000000000 : ℝ)^3357
        have hw : |(1074029891/2000000000 : ℝ)|=(1074029891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-250414833/1250000000 : ℝ)|^4381 ≤ (490704307179/4000000000000 : ℝ)^3357
        have hw : |(-250414833/1250000000 : ℝ)|=(250414833/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633202767/5000000000 : ℝ)|^4381 ≤ (21653924778189/50000000000000 : ℝ)^3357
        have hw : |(2633202767/5000000000 : ℝ)|=(2633202767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_box_6 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2685074427/5000000000 : ℝ)*x 0 + (5266406671/10000000000 : ℝ)*x 1 + (-40066359/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685074427/5000000000 : ℝ)^4381 ≤ (22212268131089/50000000000000 : ℝ)^3357 := by
    have hnat : (2685074427 : ℕ)^4381*50000000000000^3357 ≤ 22212268131089^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685074427 5000000000 22212268131089 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266406671/10000000000 : ℝ)^4381 ≤ (43307861758481/100000000000000 : ℝ)^3357 := by
    have hnat : (5266406671 : ℕ)^4381*100000000000000^3357 ≤ 43307861758481^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266406671 10000000000 43307861758481 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40066359/200000000 : ℝ)^4381 ≤ (12267601973499/100000000000000 : ℝ)^3357 := by
    have hnat : (40066359 : ℕ)^4381*100000000000000^3357 ≤ 12267601973499^3357*200000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40066359 200000000 12267601973499 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685074427/5000000000 : ℝ), (5266406671/10000000000 : ℝ), (-40066359/200000000 : ℝ)] ![(22212268131089/50000000000000 : ℝ), (43307861758481/100000000000000 : ℝ), (12267601973499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685074427/5000000000 : ℝ)|^4381 ≤ (22212268131089/50000000000000 : ℝ)^3357
        have hw : |(2685074427/5000000000 : ℝ)|=(2685074427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266406671/10000000000 : ℝ)|^4381 ≤ (43307861758481/100000000000000 : ℝ)^3357
        have hw : |(5266406671/10000000000 : ℝ)|=(5266406671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-40066359/200000000 : ℝ)|^4381 ≤ (12267601973499/100000000000000 : ℝ)^3357
        have hw : |(-40066359/200000000 : ℝ)|=(40066359/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_box_7 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039721287/2500000000 : ℝ)*x 0 + (4281054/9765625 : ℝ)*x 1 + (2191899977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039721287/2500000000 : ℝ)^4381 ≤ (7955946349567/25000000000000 : ℝ)^3357 := by
    have hnat : (1039721287 : ℕ)^4381*25000000000000^3357 ≤ 7955946349567^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039721287 2500000000 7955946349567 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4281054/9765625 : ℝ)^4381 ≤ (681762079103/2000000000000 : ℝ)^3357 := by
    have hnat : (4281054 : ℕ)^4381*2000000000000^3357 ≤ 681762079103^3357*9765625^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4281054 9765625 681762079103 2000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2191899977/5000000000 : ℝ)^4381 ≤ (8522027658109/25000000000000 : ℝ)^3357 := by
    have hnat : (2191899977 : ℕ)^4381*25000000000000^3357 ≤ 8522027658109^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191899977 5000000000 8522027658109 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039721287/2500000000 : ℝ), (4281054/9765625 : ℝ), (2191899977/5000000000 : ℝ)] ![(7955946349567/25000000000000 : ℝ), (681762079103/2000000000000 : ℝ), (8522027658109/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039721287/2500000000 : ℝ)|^4381 ≤ (7955946349567/25000000000000 : ℝ)^3357
        have hw : |(1039721287/2500000000 : ℝ)|=(1039721287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4281054/9765625 : ℝ)|^4381 ≤ (681762079103/2000000000000 : ℝ)^3357
        have hw : |(4281054/9765625 : ℝ)|=(4281054/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2191899977/5000000000 : ℝ)|^4381 ≤ (8522027658109/25000000000000 : ℝ)^3357
        have hw : |(2191899977/5000000000 : ℝ)|=(2191899977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_box_8 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1036567857/5000000000 : ℝ)*x 0 + (5183305709/10000000000 : ℝ)*x 1 + (1080115299/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036567857/5000000000 : ℝ)^4381 ≤ (12828497144001/100000000000000 : ℝ)^3357 := by
    have hnat : (1036567857 : ℕ)^4381*100000000000000^3357 ≤ 12828497144001^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036567857 5000000000 12828497144001 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183305709/10000000000 : ℝ)^4381 ≤ (21209094790597/50000000000000 : ℝ)^3357 := by
    have hnat : (5183305709 : ℕ)^4381*50000000000000^3357 ≤ 21209094790597^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183305709 10000000000 21209094790597 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080115299/2000000000 : ℝ)^4381 ≤ (22376656630559/50000000000000 : ℝ)^3357 := by
    have hnat : (1080115299 : ℕ)^4381*50000000000000^3357 ≤ 22376656630559^3357*2000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080115299 2000000000 22376656630559 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1036567857/5000000000 : ℝ), (5183305709/10000000000 : ℝ), (1080115299/2000000000 : ℝ)] ![(12828497144001/100000000000000 : ℝ), (21209094790597/50000000000000 : ℝ), (22376656630559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1036567857/5000000000 : ℝ)|^4381 ≤ (12828497144001/100000000000000 : ℝ)^3357
        have hw : |(-1036567857/5000000000 : ℝ)|=(1036567857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183305709/10000000000 : ℝ)|^4381 ≤ (21209094790597/50000000000000 : ℝ)^3357
        have hw : |(5183305709/10000000000 : ℝ)|=(5183305709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080115299/2000000000 : ℝ)|^4381 ≤ (22376656630559/50000000000000 : ℝ)^3357
        have hw : |(1080115299/2000000000 : ℝ)|=(1080115299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_box_9 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329763461/625000000 : ℝ)*x 0 + (-974387063/5000000000 : ℝ)*x 1 + (5400576163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329763461/625000000 : ℝ)^4381 ≤ (21706578558951/50000000000000 : ℝ)^3357 := by
    have hnat : (329763461 : ℕ)^4381*50000000000000^3357 ≤ 21706578558951^3357*625000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329763461 625000000 21706578558951 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (974387063/5000000000 : ℝ)^4381 ≤ (2366706638691/20000000000000 : ℝ)^3357 := by
    have hnat : (974387063 : ℕ)^4381*20000000000000^3357 ≤ 2366706638691^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974387063 5000000000 2366706638691 20000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400576163/10000000000 : ℝ)^4381 ≤ (447533096707/1000000000000 : ℝ)^3357 := by
    have hnat : (5400576163 : ℕ)^4381*1000000000000^3357 ≤ 447533096707^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400576163 10000000000 447533096707 1000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329763461/625000000 : ℝ), (-974387063/5000000000 : ℝ), (5400576163/10000000000 : ℝ)] ![(21706578558951/50000000000000 : ℝ), (2366706638691/20000000000000 : ℝ), (447533096707/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329763461/625000000 : ℝ)|^4381 ≤ (21706578558951/50000000000000 : ℝ)^3357
        have hw : |(329763461/625000000 : ℝ)|=(329763461/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-974387063/5000000000 : ℝ)|^4381 ≤ (2366706638691/20000000000000 : ℝ)^3357
        have hw : |(-974387063/5000000000 : ℝ)|=(974387063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400576163/10000000000 : ℝ)|^4381 ≤ (447533096707/1000000000000 : ℝ)^3357
        have hw : |(5400576163/10000000000 : ℝ)|=(5400576163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_box_10 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638107583/5000000000 : ℝ)*x 0 + (2700288163/5000000000 : ℝ)*x 1 + (-1948774189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638107583/5000000000 : ℝ)^4381 ≤ (8682630972587/20000000000000 : ℝ)^3357 := by
    have hnat : (2638107583 : ℕ)^4381*20000000000000^3357 ≤ 8682630972587^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638107583 5000000000 8682630972587 20000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700288163/5000000000 : ℝ)^4381 ≤ (22376655716733/50000000000000 : ℝ)^3357 := by
    have hnat : (2700288163 : ℕ)^4381*50000000000000^3357 ≤ 22376655716733^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700288163 5000000000 22376655716733 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1948774189/10000000000 : ℝ)^4381 ≤ (5916766846351/50000000000000 : ℝ)^3357 := by
    have hnat : (1948774189 : ℕ)^4381*50000000000000^3357 ≤ 5916766846351^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948774189 10000000000 5916766846351 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638107583/5000000000 : ℝ), (2700288163/5000000000 : ℝ), (-1948774189/10000000000 : ℝ)] ![(8682630972587/20000000000000 : ℝ), (22376655716733/50000000000000 : ℝ), (5916766846351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638107583/5000000000 : ℝ)|^4381 ≤ (8682630972587/20000000000000 : ℝ)^3357
        have hw : |(2638107583/5000000000 : ℝ)|=(2638107583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700288163/5000000000 : ℝ)|^4381 ≤ (22376655716733/50000000000000 : ℝ)^3357
        have hw : |(2700288163/5000000000 : ℝ)|=(2700288163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1948774189/10000000000 : ℝ)|^4381 ≤ (5916766846351/50000000000000 : ℝ)^3357
        have hw : |(-1948774189/10000000000 : ℝ)|=(1948774189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_box_11 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (897293299/2000000000 : ℝ)*x 0 + (2109886413/5000000000 : ℝ)*x 1 + (2109886549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (897293299/2000000000 : ℝ)^4381 ≤ (35133656825313/100000000000000 : ℝ)^3357 := by
    have hnat : (897293299 : ℕ)^4381*100000000000000^3357 ≤ 35133656825313^3357*2000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897293299 2000000000 35133656825313 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109886413/5000000000 : ℝ)^4381 ≤ (810829255473/2500000000000 : ℝ)^3357 := by
    have hnat : (2109886413 : ℕ)^4381*2500000000000^3357 ≤ 810829255473^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109886413 5000000000 810829255473 2500000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2109886549/5000000000 : ℝ)^4381 ≤ (16216586473607/50000000000000 : ℝ)^3357 := by
    have hnat : (2109886549 : ℕ)^4381*50000000000000^3357 ≤ 16216586473607^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109886549 5000000000 16216586473607 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(897293299/2000000000 : ℝ), (2109886413/5000000000 : ℝ), (2109886549/5000000000 : ℝ)] ![(35133656825313/100000000000000 : ℝ), (810829255473/2500000000000 : ℝ), (16216586473607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(897293299/2000000000 : ℝ)|^4381 ≤ (35133656825313/100000000000000 : ℝ)^3357
        have hw : |(897293299/2000000000 : ℝ)|=(897293299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2109886413/5000000000 : ℝ)|^4381 ≤ (810829255473/2500000000000 : ℝ)^3357
        have hw : |(2109886413/5000000000 : ℝ)|=(2109886413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2109886549/5000000000 : ℝ)|^4381 ≤ (16216586473607/50000000000000 : ℝ)^3357
        have hw : |(2109886549/5000000000 : ℝ)|=(2109886549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_box_12 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1885079933/10000000000 : ℝ)*x 0 + (1093531719/2000000000 : ℝ)*x 1 + (5255284187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1885079933/10000000000 : ℝ)^4381 ≤ (11331320549427/100000000000000 : ℝ)^3357 := by
    have hnat : (1885079933 : ℕ)^4381*100000000000000^3357 ≤ 11331320549427^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885079933 10000000000 11331320549427 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093531719/2000000000 : ℝ)^4381 ≤ (45480143951499/100000000000000 : ℝ)^3357 := by
    have hnat : (1093531719 : ℕ)^4381*100000000000000^3357 ≤ 45480143951499^3357*2000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093531719 2000000000 45480143951499 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255284187/10000000000 : ℝ)^4381 ≤ (2699283467967/6250000000000 : ℝ)^3357 := by
    have hnat : (5255284187 : ℕ)^4381*6250000000000^3357 ≤ 2699283467967^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255284187 10000000000 2699283467967 6250000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1885079933/10000000000 : ℝ), (1093531719/2000000000 : ℝ), (5255284187/10000000000 : ℝ)] ![(11331320549427/100000000000000 : ℝ), (45480143951499/100000000000000 : ℝ), (2699283467967/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1885079933/10000000000 : ℝ)|^4381 ≤ (11331320549427/100000000000000 : ℝ)^3357
        have hw : |(-1885079933/10000000000 : ℝ)|=(1885079933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093531719/2000000000 : ℝ)|^4381 ≤ (45480143951499/100000000000000 : ℝ)^3357
        have hw : |(1093531719/2000000000 : ℝ)|=(1093531719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255284187/10000000000 : ℝ)|^4381 ≤ (2699283467967/6250000000000 : ℝ)^3357
        have hw : |(5255284187/10000000000 : ℝ)|=(5255284187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_box_13 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5377933429/10000000000 : ℝ)*x 0 + (-501932351/2500000000 : ℝ)*x 1 + (5255284189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377933429/10000000000 : ℝ)^4381 ≤ (22254298129867/50000000000000 : ℝ)^3357 := by
    have hnat : (5377933429 : ℕ)^4381*50000000000000^3357 ≤ 22254298129867^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377933429 10000000000 22254298129867 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501932351/2500000000 : ℝ)^4381 ≤ (6151434109319/50000000000000 : ℝ)^3357 := by
    have hnat : (501932351 : ℕ)^4381*50000000000000^3357 ≤ 6151434109319^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501932351 2500000000 6151434109319 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255284189/10000000000 : ℝ)^4381 ≤ (21594267754461/50000000000000 : ℝ)^3357 := by
    have hnat : (5255284189 : ℕ)^4381*50000000000000^3357 ≤ 21594267754461^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255284189 10000000000 21594267754461 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377933429/10000000000 : ℝ), (-501932351/2500000000 : ℝ), (5255284189/10000000000 : ℝ)] ![(22254298129867/50000000000000 : ℝ), (6151434109319/50000000000000 : ℝ), (21594267754461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377933429/10000000000 : ℝ)|^4381 ≤ (22254298129867/50000000000000 : ℝ)^3357
        have hw : |(5377933429/10000000000 : ℝ)|=(5377933429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-501932351/2500000000 : ℝ)|^4381 ≤ (6151434109319/50000000000000 : ℝ)^3357
        have hw : |(-501932351/2500000000 : ℝ)|=(501932351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255284189/10000000000 : ℝ)|^4381 ≤ (21594267754461/50000000000000 : ℝ)^3357
        have hw : |(5255284189/10000000000 : ℝ)|=(5255284189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_box_14 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344483353/2500000000 : ℝ)*x 0 + (2627642103/5000000000 : ℝ)*x 1 + (-501932351/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344483353/2500000000 : ℝ)^4381 ≤ (44508596076123/100000000000000 : ℝ)^3357 := by
    have hnat : (1344483353 : ℕ)^4381*100000000000000^3357 ≤ 44508596076123^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344483353 2500000000 44508596076123 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627642103/5000000000 : ℝ)^4381 ≤ (8637707138249/20000000000000 : ℝ)^3357 := by
    have hnat : (2627642103 : ℕ)^4381*20000000000000^3357 ≤ 8637707138249^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627642103 5000000000 8637707138249 20000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501932351/2500000000 : ℝ)^4381 ≤ (6151434109319/50000000000000 : ℝ)^3357 := by
    have hnat : (501932351 : ℕ)^4381*50000000000000^3357 ≤ 6151434109319^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501932351 2500000000 6151434109319 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344483353/2500000000 : ℝ), (2627642103/5000000000 : ℝ), (-501932351/2500000000 : ℝ)] ![(44508596076123/100000000000000 : ℝ), (8637707138249/20000000000000 : ℝ), (6151434109319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344483353/2500000000 : ℝ)|^4381 ≤ (44508596076123/100000000000000 : ℝ)^3357
        have hw : |(1344483353/2500000000 : ℝ)|=(1344483353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627642103/5000000000 : ℝ)|^4381 ≤ (8637707138249/20000000000000 : ℝ)^3357
        have hw : |(2627642103/5000000000 : ℝ)|=(2627642103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-501932351/2500000000 : ℝ)|^4381 ≤ (6151434109319/50000000000000 : ℝ)^3357
        have hw : |(-501932351/2500000000 : ℝ)|=(501932351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_box_15 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4131235073/10000000000 : ℝ)*x 0 + (1099345959/2500000000 : ℝ)*x 1 + (879476871/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4131235073/10000000000 : ℝ)^4381 ≤ (15773974410003/50000000000000 : ℝ)^3357 := by
    have hnat : (4131235073 : ℕ)^4381*50000000000000^3357 ≤ 15773974410003^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131235073 10000000000 15773974410003 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099345959/2500000000 : ℝ)^4381 ≤ (8556505738261/25000000000000 : ℝ)^3357 := by
    have hnat : (1099345959 : ℕ)^4381*25000000000000^3357 ≤ 8556505738261^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099345959 2500000000 8556505738261 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (879476871/2000000000 : ℝ)^4381 ≤ (2139126764047/6250000000000 : ℝ)^3357 := by
    have hnat : (879476871 : ℕ)^4381*6250000000000^3357 ≤ 2139126764047^3357*2000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879476871 2000000000 2139126764047 6250000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4131235073/10000000000 : ℝ), (1099345959/2500000000 : ℝ), (879476871/2000000000 : ℝ)] ![(15773974410003/50000000000000 : ℝ), (8556505738261/25000000000000 : ℝ), (2139126764047/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4131235073/10000000000 : ℝ)|^4381 ≤ (15773974410003/50000000000000 : ℝ)^3357
        have hw : |(4131235073/10000000000 : ℝ)|=(4131235073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1099345959/2500000000 : ℝ)|^4381 ≤ (8556505738261/25000000000000 : ℝ)^3357
        have hw : |(1099345959/2500000000 : ℝ)|=(1099345959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(879476871/2000000000 : ℝ)|^4381 ≤ (2139126764047/6250000000000 : ℝ)^3357
        have hw : |(879476871/2000000000 : ℝ)|=(879476871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1421_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12579/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59097/100000 : ℝ) ∧ (20101/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (16931/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (461/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2831/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (461/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2831/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (461/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2831/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (461/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2831/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (461/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2831/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (461/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2831/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2831/25000 : ℝ) ^ (1095/256 : ℝ) ≤ (8987361622132707/100000000000000000000 : ℝ) := by
    have hpowers : (2831/25000 : ℝ)^1095 ≤ (8987361622132707/100000000000000000000 : ℝ)^256 := by
      have hnat : (2831 : ℕ)^1095*100000000000000000000^256 ≤ 8987361622132707^256*25000^1095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2831 25000 8987361622132707 100000000000000000000 1095 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2831/25000 : ℝ)) (X := (8987361622132707/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hpowhi : (461/3125 : ℝ) ^ (1095/256 : ℝ) ≤ (5570826121531531/20000000000000000000 : ℝ) := by
    have hpowers : (461/3125 : ℝ)^1095 ≤ (5570826121531531/20000000000000000000 : ℝ)^256 := by
      have hnat : (461 : ℕ)^1095*20000000000000000000^256 ≤ 5570826121531531^256*3125^1095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        461 3125 5570826121531531 20000000000000000000 1095 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (461/3125 : ℝ)) (X := (5570826121531531/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008987361622132707/50000000000000000000 : ℝ) ≤ (500021010101887/500000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (50008987361622132707/50000000000000000000 : ℝ)^256 ≤ (500021010101887/500000000000000 : ℝ)^1095 := by
      have hnat : (50008987361622132707 : ℕ)^256*500000000000000^1095 ≤ 500021010101887^1095*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008987361622132707 50000000000000000000 500021010101887 500000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500021010101887/500000000000000 : ℝ)) (X := (50008987361622132707/50000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018420746114895181/50000000000000000000 : ℝ) ≤ (10000861195537299/10000000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (50018420746114895181/50000000000000000000 : ℝ)^256 ≤ (10000861195537299/10000000000000000 : ℝ)^1095 := by
      have hnat : (50018420746114895181 : ℕ)^256*10000000000000000^1095 ≤ 10000861195537299^1095*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018420746114895181 50000000000000000000 10000861195537299 10000000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000861195537299/10000000000000000 : ℝ)) (X := (50018420746114895181/50000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005570826121531531/10000000000000000000 : ℝ) ≤ (5000651094518429/5000000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (10005570826121531531/10000000000000000000 : ℝ)^256 ≤ (5000651094518429/5000000000000000 : ℝ)^1095 := by
      have hnat : (10005570826121531531 : ℕ)^256*5000000000000000^1095 ≤ 5000651094518429^1095*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005570826121531531 10000000000000000000 5000651094518429 5000000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000651094518429/5000000000000000 : ℝ)) (X := (10005570826121531531/10000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8987361622132707/100000000000000000000 : ℝ) ≤ ((4283931603975920061/4285000000000000000 : ℝ)+2*(440993499559/342800000000000 : ℝ)*(2831/25000 : ℝ))^(1095/256 : ℝ) := by
    rw [show (4283931603975920061/4285000000000000000 : ℝ)+2*(440993499559/342800000000000 : ℝ)*(2831/25000 : ℝ)=(500021010101887/500000000000000 : ℝ) by norm_num, show 1+2*(8987361622132707/100000000000000000000 : ℝ)=(50008987361622132707/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5570826121531531/20000000000000000000 : ℝ)+(8987361622132707/100000000000000000000 : ℝ) ≤ ((4283931603975920061/4285000000000000000 : ℝ)+(440993499559/342800000000000 : ℝ)*((461/3125 : ℝ)+(2831/25000 : ℝ)))^(1095/256 : ℝ) := by
    rw [show (4283931603975920061/4285000000000000000 : ℝ)+(440993499559/342800000000000 : ℝ)*((461/3125 : ℝ)+(2831/25000 : ℝ))=(10000861195537299/10000000000000000 : ℝ) by norm_num, show 1+(5570826121531531/20000000000000000000 : ℝ)+(8987361622132707/100000000000000000000 : ℝ)=(50018420746114895181/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5570826121531531/20000000000000000000 : ℝ) ≤ ((4283931603975920061/4285000000000000000 : ℝ)+2*(440993499559/342800000000000 : ℝ)*(461/3125 : ℝ))^(1095/256 : ℝ) := by
    rw [show (4283931603975920061/4285000000000000000 : ℝ)+2*(440993499559/342800000000000 : ℝ)*(461/3125 : ℝ)=(5000651094518429/5000000000000000 : ℝ) by norm_num, show 1+2*(5570826121531531/20000000000000000000 : ℝ)=(10005570826121531531/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4283931603975920061/4285000000000000000 : ℝ)*(X 1 0+X 2 0)+(440993499559/342800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (2831/25000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (4283931603975920061/4285000000000000000 : ℝ)) (alpha := (440993499559/342800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4283931603975920061/4285000000000000000 : ℝ)*(X 0 1+X 2 1)+(440993499559/342800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (2831/25000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (4283931603975920061/4285000000000000000 : ℝ)) (alpha := (440993499559/342800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4283931603975920061/4285000000000000000 : ℝ)*(X 0 2+X 1 2)+(440993499559/342800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (2831/25000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (4283931603975920061/4285000000000000000 : ℝ)) (alpha := (440993499559/342800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-908201967/5000000000 : ℝ)*X 0 0+(5386597529/10000000000 : ℝ)*X 0 1+(1077319577/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2643002689/5000000000 : ℝ)*X 1 0+(-390914143/2000000000 : ℝ)*X 1 1+(5386597719/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((660750703/1250000000 : ℝ)*X 2 0+(5386597633/10000000000 : ℝ)*X 2 1+(-3909141/20000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4452836227/10000000000 : ℝ)*X 0 0+(4236875267/10000000000 : ℝ)*X 0 1+(4236875147/10000000000 : ℝ)*X 0 2+(4452836227/10000000000 : ℝ)*X 1 0+(4236875267/10000000000 : ℝ)*X 1 1+(4236875147/10000000000 : ℝ)*X 1 2+(4452836227/10000000000 : ℝ)*X 2 0+(4236875267/10000000000 : ℝ)*X 2 1+(4236875147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2141617949/10000000000 : ℝ)*X 0 0+(5266405919/10000000000 : ℝ)*X 0 1+(5266406039/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1074029891/2000000000 : ℝ)*X 1 0+(-250414833/1250000000 : ℝ)*X 1 1+(2633202767/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2685074427/5000000000 : ℝ)*X 2 0+(5266406671/10000000000 : ℝ)*X 2 1+(-40066359/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1039721287/2500000000 : ℝ)*X 0 0+(4281054/9765625 : ℝ)*X 0 1+(2191899977/5000000000 : ℝ)*X 0 2+(1039721287/2500000000 : ℝ)*X 1 0+(4281054/9765625 : ℝ)*X 1 1+(2191899977/5000000000 : ℝ)*X 1 2+(1039721287/2500000000 : ℝ)*X 2 0+(4281054/9765625 : ℝ)*X 2 1+(2191899977/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1036567857/5000000000 : ℝ)*X 0 0+(5183305709/10000000000 : ℝ)*X 0 1+(1080115299/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((329763461/625000000 : ℝ)*X 1 0+(-974387063/5000000000 : ℝ)*X 1 1+(5400576163/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2638107583/5000000000 : ℝ)*X 2 0+(2700288163/5000000000 : ℝ)*X 2 1+(-1948774189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((897293299/2000000000 : ℝ)*X 0 0+(2109886413/5000000000 : ℝ)*X 0 1+(2109886549/5000000000 : ℝ)*X 0 2+(897293299/2000000000 : ℝ)*X 1 0+(2109886413/5000000000 : ℝ)*X 1 1+(2109886549/5000000000 : ℝ)*X 1 2+(897293299/2000000000 : ℝ)*X 2 0+(2109886413/5000000000 : ℝ)*X 2 1+(2109886549/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1885079933/10000000000 : ℝ)*X 0 0+(1093531719/2000000000 : ℝ)*X 0 1+(5255284187/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5377933429/10000000000 : ℝ)*X 1 0+(-501932351/2500000000 : ℝ)*X 1 1+(5255284189/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1344483353/2500000000 : ℝ)*X 2 0+(2627642103/5000000000 : ℝ)*X 2 1+(-501932351/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4131235073/10000000000 : ℝ)*X 0 0+(1099345959/2500000000 : ℝ)*X 0 1+(879476871/2000000000 : ℝ)*X 0 2+(4131235073/10000000000 : ℝ)*X 1 0+(1099345959/2500000000 : ℝ)*X 1 1+(879476871/2000000000 : ℝ)*X 1 2+(4131235073/10000000000 : ℝ)*X 2 0+(1099345959/2500000000 : ℝ)*X 2 1+(879476871/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12579/20000 : ℝ) ≤ (-13474624756502990471811107758119/21425000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43913271/50000000000000 : ℝ)*(lower1) + (21262297/25000000000000 : ℝ)*(lower2) + (149871781/100000000000000 : ℝ)*(lower3) + (13274307/100000000000000 : ℝ)*(lower4) + (300810596373207/10000000000000 : ℝ)*(major0) + (300810596373207/10000000000000 : ℝ)*(major1) + (300810596373207/10000000000000 : ℝ)*(major2) + (12196756059/100000000000000 : ℝ)*(sp1) + (10328748273387/250000000000 : ℝ)*(sp4) + (4131487112598741/100000000000000 : ℝ)*(sp5) + (16137578027029/390625000000 : ℝ)*(sp6) + (952821537774159/50000000000000 : ℝ)*(sp7) + (2234675483/800000000000 : ℝ)*(sp14) + (524436931/1562500000000 : ℝ)*(sp15) + (1905676639511903/100000000000000 : ℝ)*(f.failure) + (10328748273387/250000000000 : ℝ)*(f.sum) + (4720883832431/1714000000000000000000000000 : ℝ)*base66 + (270367540202581873/42850000000000000000000000000000 : ℝ)*base68 + (137492928578418127/42850000000000000000000000000000 : ℝ)*base69 + (522437404455431873/42850000000000000000000000000000 : ℝ)*base72 + (5879622298611/1714000000000000000000000000 : ℝ)*base73 + (162387710970668127/42850000000000000000000000000000 : ℝ)*base75 + (276489894211581873/42850000000000000000000000000000 : ℝ)*base78 + (39629012491481873/42850000000000000000000000000000 : ℝ)*base80 + (1079283254073/68560000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (63334737/5000000000000000000000 : ℝ)*base89 + (63334737/5000000000000000000000 : ℝ)*base91 + (63334737/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (59097/100000 : ℝ) ≤ (31655246749798742341468399147299/53562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (451027/25000000000000 : ℝ)*(lower0) + (64769889/100000000000000 : ℝ)*(lower3) + (109372571/100000000000000 : ℝ)*(upper4) + (1539724523381497/50000000000000 : ℝ)*(major0) + (1539724523381497/50000000000000 : ℝ)*(major1) + (1539724523381497/50000000000000 : ℝ)*(major2) + (837664596294199/20000000000000 : ℝ)*(sp0) + (2094161607002721/50000000000000 : ℝ)*(sp1) + (4188322460538687/100000000000000 : ℝ)*(sp2) + (1950871380605973/100000000000000 : ℝ)*(sp3) + (765545841/50000000000000 : ℝ)*(sp5) + (571139609/25000000000000 : ℝ)*(sp6) + (13040823/625000000000 : ℝ)*(sp7) + (110226633/6250000000000 : ℝ)*(sp12) + (487718366784413/25000000000000 : ℝ)*(f.failure) + (1047081186274281/25000000000000 : ℝ)*(f.sum) + (16418676387667/8570000000000000000000000000 : ℝ)*base66 + (1253196796175798817/214250000000000000000000000000000 : ℝ)*base67 + (233651603842798817/214250000000000000000000000000000 : ℝ)*base69 + (1847341117544048817/214250000000000000000000000000000 : ℝ)*base71 + (48761808704187/8570000000000000000000000000 : ℝ)*base74 + (144000759675951183/214250000000000000000000000000000 : ℝ)*base76 + (1514737779388548817/214250000000000000000000000000000 : ℝ)*base77 + (533121204779798817/214250000000000000000000000000000 : ℝ)*base79 + (53158671697247/8570000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (9888973/1250000000000000000000 : ℝ)*base90 + (9888973/1250000000000000000000 : ℝ)*base92 + (9888973/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (20101/25000 : ℝ) ≤ (86135799685248749474792173836771/107125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92412147/100000000000000 : ℝ)*(upper2) + (22099883/20000000000000 : ℝ)*(lower3) + (8363113/10000000000000 : ℝ)*(lower5) + (3387783974661213/100000000000000 : ℝ)*(major0) + (3387783974661213/100000000000000 : ℝ)*(major1) + (3387783974661213/100000000000000 : ℝ)*(major2) + (1467038531/50000000000000 : ℝ)*(sp0) + (4332346413/100000000000000 : ℝ)*(sp2) + (6595110799/20000000000000 : ℝ)*(sp3) + (4602552215446131/100000000000000 : ℝ)*(sp8) + (4602557778985889/100000000000000 : ℝ)*(sp9) + (1150638361659869/25000000000000 : ℝ)*(sp10) + (107308746169539/5000000000000 : ℝ)*(sp11) + (525892539/20000000000000 : ℝ)*(sp12) + (268275987368097/12500000000000 : ℝ)*(f.failure) + (4602557778985889/100000000000000 : ℝ)*(f.sum) + (110532936136747/17140000000000000000000000000 : ℝ)*base65 + (4864321674769131493/428500000000000000000000000000000 : ℝ)*base67 + (1024119141786131493/428500000000000000000000000000000 : ℝ)*base69 + (217937318867868507/428500000000000000000000000000000 : ℝ)*base72 + (105759980167727/17140000000000000000000000000 : ℝ)*base73 + (2955216427016631493/428500000000000000000000000000000 : ℝ)*base75 + (3205396117308131493/428500000000000000000000000000000 : ℝ)*base77 + (2063289847083631493/428500000000000000000000000000000 : ℝ)*base79 + (22627221194327/17140000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2935263/625000000000000000000 : ℝ)*base89 + (2935263/625000000000000000000 : ℝ)*base91 + (2935263/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-16931/20000 : ℝ) ≤ (-181367322728698341545211250433481/214250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (646369/100000000000000 : ℝ)*(lower1) + (238731/10000000000000 : ℝ)*(lower3) + (71212757/100000000000000 : ℝ)*(lower4) + (145403871/100000000000000 : ℝ)*(upper5) + (3425170330094469/100000000000000 : ℝ)*(major0) + (3425170330094469/100000000000000 : ℝ)*(major1) + (3425170330094469/100000000000000 : ℝ)*(major2) + (2412075157/100000000000000 : ℝ)*(sp4) + (40598339889/50000000000000 : ℝ)*(sp6) + (832504761/2000000000000 : ℝ)*(sp7) + (235433148731063/5000000000000 : ℝ)*(sp12) + (4708665386696417/100000000000000 : ℝ)*(sp13) + (4708584190016639/100000000000000 : ℝ)*(sp14) + (1084925522900371/50000000000000 : ℝ)*(sp15) + (271236583879849/12500000000000 : ℝ)*(f.failure) + (4708665386696417/100000000000000 : ℝ)*(f.sum) + (8165940220849/17140000000000000000000000000 : ℝ)*base66 + (1879284513104380109/428500000000000000000000000000000 : ℝ)*base67 + (2653529697301380109/428500000000000000000000000000000 : ℝ)*base69 + (4825939166130380109/428500000000000000000000000000000 : ℝ)*base71 + (83200346418989/17140000000000000000000000000 : ℝ)*base74 + (3568650550306380109/428500000000000000000000000000000 : ℝ)*base75 + (6845505606900880109/428500000000000000000000000000000 : ℝ)*base77 + (2428827754867880109/428500000000000000000000000000000 : ℝ)*base79 + (82696416878389/17140000000000000000000000000 : ℝ)*base82 + (1613271/625000000000000000000 : ℝ)*base89 + (1613271/625000000000000000000 : ℝ)*base91 + (1613271/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1421_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12579/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59097/100000 : ℝ) else (20101/25000 : ℝ) ≤ X j i ∧ X j i ≤ (16931/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1421_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1421_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12579/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59097/100000 : ℝ) else (20101/25000 : ℝ) ≤ X j i ∧ X j i ≤ (16931/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1421_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1421_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1421_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12579/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59097/100000 : ℝ) else (20101/25000 : ℝ) ≤ X j i ∧ X j i ≤ (16931/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1421_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

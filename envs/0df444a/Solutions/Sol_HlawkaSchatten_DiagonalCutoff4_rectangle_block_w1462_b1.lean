-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1462_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:08:34.625732+00:00
-- url     : https://prove2.me/submissions/97326079-f17b-4289-94ee-f6b1adbfdcea

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
theorem support_rectangle_w1462_s3_0 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-971898357/5000000000 : ℝ)*x 0 + (5414077237/10000000000 : ℝ)*x 1 + (1310152881/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (971898357/5000000000 : ℝ)^2211 ≤ (11865420031033/100000000000000 : ℝ)^1699 := by
    have hnat : (971898357 : ℕ)^2211*100000000000000^1699 ≤ 11865420031033^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971898357 5000000000 11865420031033 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414077237/10000000000 : ℝ)^2211 ≤ (45000883805731/100000000000000 : ℝ)^1699 := by
    have hnat : (5414077237 : ℕ)^2211*100000000000000^1699 ≤ 45000883805731^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414077237 10000000000 45000883805731 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310152881/2500000000 : ℝ)^2211 ≤ (43133696145081/100000000000000 : ℝ)^1699 := by
    have hnat : (1310152881 : ℕ)^2211*100000000000000^1699 ≤ 43133696145081^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310152881 2500000000 43133696145081 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-971898357/5000000000 : ℝ), (5414077237/10000000000 : ℝ), (1310152881/2500000000 : ℝ)] ![(11865420031033/100000000000000 : ℝ), (45000883805731/100000000000000 : ℝ), (43133696145081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-971898357/5000000000 : ℝ)|^2211 ≤ (11865420031033/100000000000000 : ℝ)^1699
        have hw : |(-971898357/5000000000 : ℝ)|=(971898357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414077237/10000000000 : ℝ)|^2211 ≤ (45000883805731/100000000000000 : ℝ)^1699
        have hw : |(5414077237/10000000000 : ℝ)|=(5414077237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310152881/2500000000 : ℝ)|^2211 ≤ (43133696145081/100000000000000 : ℝ)^1699
        have hw : |(1310152881/2500000000 : ℝ)|=(1310152881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s3_1 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674285829/5000000000 : ℝ)*x 0 + (-254028671/1250000000 : ℝ)*x 1 + (5240611379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674285829/5000000000 : ℝ)^2211 ≤ (22146814801723/50000000000000 : ℝ)^1699 := by
    have hnat : (2674285829 : ℕ)^2211*50000000000000^1699 ≤ 22146814801723^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674285829 5000000000 22146814801723 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (254028671/1250000000 : ℝ)^2211 ≤ (3143168948809/25000000000000 : ℝ)^1699 := by
    have hnat : (254028671 : ℕ)^2211*25000000000000^1699 ≤ 3143168948809^1699*1250000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254028671 1250000000 3143168948809 25000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240611379/10000000000 : ℝ)^2211 ≤ (21566847295993/50000000000000 : ℝ)^1699 := by
    have hnat : (5240611379 : ℕ)^2211*50000000000000^1699 ≤ 21566847295993^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240611379 10000000000 21566847295993 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674285829/5000000000 : ℝ), (-254028671/1250000000 : ℝ), (5240611379/10000000000 : ℝ)] ![(22146814801723/50000000000000 : ℝ), (3143168948809/25000000000000 : ℝ), (21566847295993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674285829/5000000000 : ℝ)|^2211 ≤ (22146814801723/50000000000000 : ℝ)^1699
        have hw : |(2674285829/5000000000 : ℝ)|=(2674285829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-254028671/1250000000 : ℝ)|^2211 ≤ (3143168948809/25000000000000 : ℝ)^1699
        have hw : |(-254028671/1250000000 : ℝ)|=(254028671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240611379/10000000000 : ℝ)|^2211 ≤ (21566847295993/50000000000000 : ℝ)^1699
        have hw : |(5240611379/10000000000 : ℝ)|=(5240611379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s3_2 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674285919/5000000000 : ℝ)*x 0 + (327538209/625000000 : ℝ)*x 1 + (-1016114587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674285919/5000000000 : ℝ)^2211 ≤ (44293631543311/100000000000000 : ℝ)^1699 := by
    have hnat : (2674285919 : ℕ)^2211*100000000000000^1699 ≤ 44293631543311^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674285919 5000000000 44293631543311 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327538209/625000000 : ℝ)^2211 ≤ (43133694217101/100000000000000 : ℝ)^1699 := by
    have hnat : (327538209 : ℕ)^2211*100000000000000^1699 ≤ 43133694217101^1699*625000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327538209 625000000 43133694217101 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016114587/5000000000 : ℝ)^2211 ≤ (628633711667/5000000000000 : ℝ)^1699 := by
    have hnat : (1016114587 : ℕ)^2211*5000000000000^1699 ≤ 628633711667^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016114587 5000000000 628633711667 5000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674285919/5000000000 : ℝ), (327538209/625000000 : ℝ), (-1016114587/5000000000 : ℝ)] ![(44293631543311/100000000000000 : ℝ), (43133694217101/100000000000000 : ℝ), (628633711667/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674285919/5000000000 : ℝ)|^2211 ≤ (44293631543311/100000000000000 : ℝ)^1699
        have hw : |(2674285919/5000000000 : ℝ)|=(2674285919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327538209/625000000 : ℝ)|^2211 ≤ (43133694217101/100000000000000 : ℝ)^1699
        have hw : |(327538209/625000000 : ℝ)|=(327538209/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1016114587/5000000000 : ℝ)|^2211 ≤ (628633711667/5000000000000 : ℝ)^1699
        have hw : |(-1016114587/5000000000 : ℝ)|=(1016114587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s3_3 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1073914127/2500000000 : ℝ)*x 0 + (513684271/1250000000 : ℝ)*x 1 + (2244640531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073914127/2500000000 : ℝ)^2211 ≤ (6659960061197/20000000000000 : ℝ)^1699 := by
    have hnat : (1073914127 : ℕ)^2211*20000000000000^1699 ≤ 6659960061197^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073914127 2500000000 6659960061197 20000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513684271/1250000000 : ℝ)^2211 ≤ (31433974697939/100000000000000 : ℝ)^1699 := by
    have hnat : (513684271 : ℕ)^2211*100000000000000^1699 ≤ 31433974697939^1699*1250000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513684271 1250000000 31433974697939 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2244640531/5000000000 : ℝ)^2211 ≤ (35266224987863/100000000000000 : ℝ)^1699 := by
    have hnat : (2244640531 : ℕ)^2211*100000000000000^1699 ≤ 35266224987863^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244640531 5000000000 35266224987863 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073914127/2500000000 : ℝ), (513684271/1250000000 : ℝ), (2244640531/5000000000 : ℝ)] ![(6659960061197/20000000000000 : ℝ), (31433974697939/100000000000000 : ℝ), (35266224987863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073914127/2500000000 : ℝ)|^2211 ≤ (6659960061197/20000000000000 : ℝ)^1699
        have hw : |(1073914127/2500000000 : ℝ)|=(1073914127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(513684271/1250000000 : ℝ)|^2211 ≤ (31433974697939/100000000000000 : ℝ)^1699
        have hw : |(513684271/1250000000 : ℝ)|=(513684271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2244640531/5000000000 : ℝ)|^2211 ≤ (35266224987863/100000000000000 : ℝ)^1699
        have hw : |(2244640531/5000000000 : ℝ)|=(2244640531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s3_4 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-485952663/2500000000 : ℝ)*x 0 + (1310324033/2500000000 : ℝ)*x 1 + (1353347263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (485952663/2500000000 : ℝ)^2211 ≤ (11865530751667/100000000000000 : ℝ)^1699 := by
    have hnat : (485952663 : ℕ)^2211*100000000000000^1699 ≤ 11865530751667^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485952663 2500000000 11865530751667 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310324033/2500000000 : ℝ)^2211 ≤ (43141029126571/100000000000000 : ℝ)^1699 := by
    have hnat : (1310324033 : ℕ)^2211*100000000000000^1699 ≤ 43141029126571^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310324033 2500000000 43141029126571 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353347263/2500000000 : ℝ)^2211 ≤ (44993440106033/100000000000000 : ℝ)^1699 := by
    have hnat : (1353347263 : ℕ)^2211*100000000000000^1699 ≤ 44993440106033^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353347263 2500000000 44993440106033 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-485952663/2500000000 : ℝ), (1310324033/2500000000 : ℝ), (1353347263/2500000000 : ℝ)] ![(11865530751667/100000000000000 : ℝ), (43141029126571/100000000000000 : ℝ), (44993440106033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-485952663/2500000000 : ℝ)|^2211 ≤ (11865530751667/100000000000000 : ℝ)^1699
        have hw : |(-485952663/2500000000 : ℝ)|=(485952663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310324033/2500000000 : ℝ)|^2211 ≤ (43141029126571/100000000000000 : ℝ)^1699
        have hw : |(1310324033/2500000000 : ℝ)|=(1310324033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353347263/2500000000 : ℝ)|^2211 ≤ (44993440106033/100000000000000 : ℝ)^1699
        have hw : |(1353347263/2500000000 : ℝ)|=(1353347263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s3_5 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5303334681/10000000000 : ℝ)*x 0 + (-929725907/5000000000 : ℝ)*x 1 + (2706694521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303334681/10000000000 : ℝ)^2211 ≤ (21903366087497/50000000000000 : ℝ)^1699 := by
    have hnat : (5303334681 : ℕ)^2211*50000000000000^1699 ≤ 21903366087497^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303334681 10000000000 21903366087497 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (929725907/5000000000 : ℝ)^2211 ≤ (11199827817723/100000000000000 : ℝ)^1699 := by
    have hnat : (929725907 : ℕ)^2211*100000000000000^1699 ≤ 11199827817723^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929725907 5000000000 11199827817723 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706694521/5000000000 : ℝ)^2211 ≤ (44993439997871/100000000000000 : ℝ)^1699 := by
    have hnat : (2706694521 : ℕ)^2211*100000000000000^1699 ≤ 44993439997871^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706694521 5000000000 44993439997871 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303334681/10000000000 : ℝ), (-929725907/5000000000 : ℝ), (2706694521/5000000000 : ℝ)] ![(21903366087497/50000000000000 : ℝ), (11199827817723/100000000000000 : ℝ), (44993439997871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303334681/10000000000 : ℝ)|^2211 ≤ (21903366087497/50000000000000 : ℝ)^1699
        have hw : |(5303334681/10000000000 : ℝ)|=(5303334681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-929725907/5000000000 : ℝ)|^2211 ≤ (11199827817723/100000000000000 : ℝ)^1699
        have hw : |(-929725907/5000000000 : ℝ)|=(929725907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706694521/5000000000 : ℝ)|^2211 ≤ (44993439997871/100000000000000 : ℝ)^1699
        have hw : |(2706694521/5000000000 : ℝ)|=(2706694521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s3_6 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5303333691/10000000000 : ℝ)*x 0 + (5413389801/10000000000 : ℝ)*x 1 + (-464863031/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303333691/10000000000 : ℝ)^2211 ≤ (5475840191627/12500000000000 : ℝ)^1699 := by
    have hnat : (5303333691 : ℕ)^2211*12500000000000^1699 ≤ 5475840191627^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303333691 10000000000 5475840191627 12500000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413389801/10000000000 : ℝ)^2211 ≤ (22496724103689/50000000000000 : ℝ)^1699 := by
    have hnat : (5413389801 : ℕ)^2211*50000000000000^1699 ≤ 22496724103689^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413389801 10000000000 22496724103689 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (464863031/2500000000 : ℝ)^2211 ≤ (2239966049519/20000000000000 : ℝ)^1699 := by
    have hnat : (464863031 : ℕ)^2211*20000000000000^1699 ≤ 2239966049519^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464863031 2500000000 2239966049519 20000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303333691/10000000000 : ℝ), (5413389801/10000000000 : ℝ), (-464863031/2500000000 : ℝ)] ![(5475840191627/12500000000000 : ℝ), (22496724103689/50000000000000 : ℝ), (2239966049519/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303333691/10000000000 : ℝ)|^2211 ≤ (5475840191627/12500000000000 : ℝ)^1699
        have hw : |(5303333691/10000000000 : ℝ)|=(5303333691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413389801/10000000000 : ℝ)|^2211 ≤ (22496724103689/50000000000000 : ℝ)^1699
        have hw : |(5413389801/10000000000 : ℝ)|=(5413389801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-464863031/2500000000 : ℝ)|^2211 ≤ (2239966049519/20000000000000 : ℝ)^1699
        have hw : |(-464863031/2500000000 : ℝ)|=(464863031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s3_7 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1073921763/2500000000 : ℝ)*x 0 + (4487782607/10000000000 : ℝ)*x 1 + (4110981961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073921763/2500000000 : ℝ)^2211 ≤ (33300108435871/100000000000000 : ℝ)^1699 := by
    have hnat : (1073921763 : ℕ)^2211*100000000000000^1699 ≤ 33300108435871^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073921763 2500000000 33300108435871 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4487782607/10000000000 : ℝ)^2211 ≤ (35250907081797/100000000000000 : ℝ)^1699 := by
    have hnat : (4487782607 : ℕ)^2211*100000000000000^1699 ≤ 35250907081797^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487782607 10000000000 35250907081797 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4110981961/10000000000 : ℝ)^2211 ≤ (31448984471409/100000000000000 : ℝ)^1699 := by
    have hnat : (4110981961 : ℕ)^2211*100000000000000^1699 ≤ 31448984471409^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4110981961 10000000000 31448984471409 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073921763/2500000000 : ℝ), (4487782607/10000000000 : ℝ), (4110981961/10000000000 : ℝ)] ![(33300108435871/100000000000000 : ℝ), (35250907081797/100000000000000 : ℝ), (31448984471409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073921763/2500000000 : ℝ)|^2211 ≤ (33300108435871/100000000000000 : ℝ)^1699
        have hw : |(1073921763/2500000000 : ℝ)|=(1073921763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4487782607/10000000000 : ℝ)|^2211 ≤ (35250907081797/100000000000000 : ℝ)^1699
        have hw : |(4487782607/10000000000 : ℝ)|=(4487782607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4110981961/10000000000 : ℝ)|^2211 ≤ (31448984471409/100000000000000 : ℝ)^1699
        have hw : |(4110981961/10000000000 : ℝ)|=(4110981961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1462_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15703/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10537/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11257/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14931/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15703/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10537/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15703/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10537/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15703/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10537/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15703/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10537/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15703/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10537/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15703/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10537/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10537/100000 : ℝ) ^ (4421/1024 : ℝ) ≤ (603524752646943/10000000000000000000 : ℝ) := by
    have hpowers : (10537/100000 : ℝ)^4421 ≤ (603524752646943/10000000000000000000 : ℝ)^1024 := by
      have hnat : (10537 : ℕ)^4421*10000000000000000000^1024 ≤ 603524752646943^1024*100000^4421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10537 100000 603524752646943 10000000000000000000 4421 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10537/100000 : ℝ)) (X := (603524752646943/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15703/100000 : ℝ) ^ (4421/1024 : ℝ) ≤ (1351478745826777/4000000000000000000 : ℝ) := by
    have hpowers : (15703/100000 : ℝ)^4421 ≤ (1351478745826777/4000000000000000000 : ℝ)^1024 := by
      have hnat : (15703 : ℕ)^4421*4000000000000000000^1024 ≤ 1351478745826777^1024*100000^4421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15703 100000 1351478745826777 4000000000000000000 4421 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15703/100000 : ℝ)) (X := (1351478745826777/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000603524752646943/5000000000000000000 : ℝ) ≤ (5000139783010513/5000000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (5000603524752646943/5000000000000000000 : ℝ)^1024 ≤ (5000139783010513/5000000000000000 : ℝ)^4421 := by
      have hnat : (5000603524752646943 : ℕ)^1024*5000000000000000^4421 ≤ 5000139783010513^4421*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000603524752646943 5000000000000000000 5000139783010513 5000000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000139783010513/5000000000000000 : ℝ)) (X := (5000603524752646943/5000000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007964443234427771/20000000000000000000 : ℝ) ≤ (10000922228276393/10000000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (20007964443234427771/20000000000000000000 : ℝ)^1024 ≤ (10000922228276393/10000000000000000 : ℝ)^4421 := by
      have hnat : (20007964443234427771 : ℕ)^1024*10000000000000000^4421 ≤ 10000922228276393^4421*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007964443234427771 20000000000000000000 10000922228276393 10000000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000922228276393/10000000000000000 : ℝ)) (X := (20007964443234427771/20000000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001351478745826777/2000000000000000000 : ℝ) ≤ (125019561131647/125000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (2001351478745826777/2000000000000000000 : ℝ)^1024 ≤ (125019561131647/125000000000000 : ℝ)^4421 := by
      have hnat : (2001351478745826777 : ℕ)^1024*125000000000000^4421 ≤ 125019561131647^4421*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001351478745826777 2000000000000000000 125019561131647 125000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125019561131647/125000000000000 : ℝ)) (X := (2001351478745826777/2000000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(603524752646943/10000000000000000000 : ℝ) ≤ ((69983605384410591/70000000000000000 : ℝ)+2*(71406917263/57400000000000 : ℝ)*(10537/100000 : ℝ))^(4421/1024 : ℝ) := by
    rw [show (69983605384410591/70000000000000000 : ℝ)+2*(71406917263/57400000000000 : ℝ)*(10537/100000 : ℝ)=(5000139783010513/5000000000000000 : ℝ) by norm_num, show 1+2*(603524752646943/10000000000000000000 : ℝ)=(5000603524752646943/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1351478745826777/4000000000000000000 : ℝ)+(603524752646943/10000000000000000000 : ℝ) ≤ ((69983605384410591/70000000000000000 : ℝ)+(71406917263/57400000000000 : ℝ)*((15703/100000 : ℝ)+(10537/100000 : ℝ)))^(4421/1024 : ℝ) := by
    rw [show (69983605384410591/70000000000000000 : ℝ)+(71406917263/57400000000000 : ℝ)*((15703/100000 : ℝ)+(10537/100000 : ℝ))=(10000922228276393/10000000000000000 : ℝ) by norm_num, show 1+(1351478745826777/4000000000000000000 : ℝ)+(603524752646943/10000000000000000000 : ℝ)=(20007964443234427771/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1351478745826777/4000000000000000000 : ℝ) ≤ ((69983605384410591/70000000000000000 : ℝ)+2*(71406917263/57400000000000 : ℝ)*(15703/100000 : ℝ))^(4421/1024 : ℝ) := by
    rw [show (69983605384410591/70000000000000000 : ℝ)+2*(71406917263/57400000000000 : ℝ)*(15703/100000 : ℝ)=(125019561131647/125000000000000 : ℝ) by norm_num, show 1+2*(1351478745826777/4000000000000000000 : ℝ)=(2001351478745826777/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (69983605384410591/70000000000000000 : ℝ)*(X 1 0+X 2 0)+(71406917263/57400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (10537/100000 : ℝ)) (hi := (15703/100000 : ℝ)) (c := (69983605384410591/70000000000000000 : ℝ)) (alpha := (71406917263/57400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (69983605384410591/70000000000000000 : ℝ)*(X 0 1+X 2 1)+(71406917263/57400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (10537/100000 : ℝ)) (hi := (15703/100000 : ℝ)) (c := (69983605384410591/70000000000000000 : ℝ)) (alpha := (71406917263/57400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (69983605384410591/70000000000000000 : ℝ)*(X 0 2+X 1 2)+(71406917263/57400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (10537/100000 : ℝ)) (hi := (15703/100000 : ℝ)) (c := (69983605384410591/70000000000000000 : ℝ)) (alpha := (71406917263/57400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-971898357/5000000000 : ℝ)*X 0 0+(5414077237/10000000000 : ℝ)*X 0 1+(1310152881/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674285829/5000000000 : ℝ)*X 1 0+(-254028671/1250000000 : ℝ)*X 1 1+(5240611379/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674285919/5000000000 : ℝ)*X 2 0+(327538209/625000000 : ℝ)*X 2 1+(-1016114587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1073914127/2500000000 : ℝ)*X 0 0+(513684271/1250000000 : ℝ)*X 0 1+(2244640531/5000000000 : ℝ)*X 0 2+(1073914127/2500000000 : ℝ)*X 1 0+(513684271/1250000000 : ℝ)*X 1 1+(2244640531/5000000000 : ℝ)*X 1 2+(1073914127/2500000000 : ℝ)*X 2 0+(513684271/1250000000 : ℝ)*X 2 1+(2244640531/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-485952663/2500000000 : ℝ)*X 0 0+(1310324033/2500000000 : ℝ)*X 0 1+(1353347263/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303334681/10000000000 : ℝ)*X 1 0+(-929725907/5000000000 : ℝ)*X 1 1+(2706694521/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303333691/10000000000 : ℝ)*X 2 0+(5413389801/10000000000 : ℝ)*X 2 1+(-464863031/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1073921763/2500000000 : ℝ)*X 0 0+(4487782607/10000000000 : ℝ)*X 0 1+(4110981961/10000000000 : ℝ)*X 0 2+(1073921763/2500000000 : ℝ)*X 1 0+(4487782607/10000000000 : ℝ)*X 1 1+(4110981961/10000000000 : ℝ)*X 1 2+(1073921763/2500000000 : ℝ)*X 2 0+(4487782607/10000000000 : ℝ)*X 2 1+(4110981961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (273439331950740909725203773/71750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14344519/2000000000000 : ℝ)*(base19) + (829254681/100000000000000 : ℝ)*(base23) + (46505523/100000000000000 : ℝ)*(lower2) + (22590679/12500000000000 : ℝ)*(upper5) + (2099445214517187/50000000000000 : ℝ)*(major0) + (2099445214517187/50000000000000 : ℝ)*(major1) + (2099445214517187/50000000000000 : ℝ)*(major2) + (1152966858876879/20000000000000 : ℝ)*(sp0) + (576484849607707/10000000000000 : ℝ)*(sp1) + (5764848971534907/100000000000000 : ℝ)*(sp2) + (329115580532679/12500000000000 : ℝ)*(sp3) + (15506405193/100000000000000 : ℝ)*(sp4) + (73435821/12500000000000 : ℝ)*(sp5) + (6285984347/100000000000000 : ℝ)*(sp7) + (2632930930245779/100000000000000 : ℝ)*(f.failure) + (1441212450197397/25000000000000 : ℝ)*(f.sum) + (569830710609/1435000000000000000000000000 : ℝ)*base66 + (2936928002009521803/143500000000000000000000000000000 : ℝ)*base68 + (2743706539348021803/143500000000000000000000000000000 : ℝ)*base70 + (329066637341521803/143500000000000000000000000000000 : ℝ)*base72 + (4517113829637/717500000000000000000000000 : ℝ)*base74 + (3152889954443021803/143500000000000000000000000000000 : ℝ)*base76 + (1151666352754521803/143500000000000000000000000000000 : ℝ)*base78 + (1146486382599021803/143500000000000000000000000000000 : ℝ)*base80 + (1104302548913/717500000000000000000000000 : ℝ)*base81 + (15690999/2000000000000000000000 : ℝ)*base89 + (15690999/2000000000000000000000 : ℝ)*base91 + (15690999/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3843341859525634164261/2870000000000000000000000000 : ℝ) := by norm_num
    linear_combination (140939973/50000000000000 : ℝ)*(base8) + (840423637/100000000000000 : ℝ)*(base21) + (1952399/2000000000000 : ℝ)*(base29) + (94694869/50000000000000 : ℝ)*(upper2) + (4232368463156873/100000000000000 : ℝ)*(major0) + (529046070097103/12500000000000 : ℝ)*(major1) + (529046070097103/12500000000000 : ℝ)*(major2) + (6227709/10000000000000 : ℝ)*(sp0) + (2753068263/50000000000000 : ℝ)*(sp1) + (710460399/20000000000000 : ℝ)*(sp2) + (5810813206958887/100000000000000 : ℝ)*(sp4) + (5810807947359447/100000000000000 : ℝ)*(sp5) + (5810809060770341/100000000000000 : ℝ)*(sp6) + (1326961762899801/50000000000000 : ℝ)*(sp7) + (1326961762899801/50000000000000 : ℝ)*(f.failure) + (5810813551115923/100000000000000 : ℝ)*(f.sum) + (743627078289/358750000000000000000000000 : ℝ)*base65 + (93293729918717207/35875000000000000000000000000000 : ℝ)*base68 + (5555456620532793/35875000000000000000000000000000 : ℝ)*base69 + (298257887697702809/41000000000000000000000000000000 : ℝ)*base71 + (4175939180191/5740000000000000000000000000 : ℝ)*base73 + (197715813871173457/35875000000000000000000000000000 : ℝ)*base76 + (959491483268297191/41000000000000000000000000000000 : ℝ)*base78 + (93081297116951543/35875000000000000000000000000000 : ℝ)*base79 + (3356938071391/5740000000000000000000000000 : ℝ)*base81 + (7758981/1000000000000000000000 : ℝ)*base89 + (2241019/1000000000000000000000 : ℝ)*base92 + (2241019/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1462_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15703/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10537/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14931/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1462_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1462_s4_0 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-38890909/200000000 : ℝ)*x 0 + (2703798827/5000000000 : ℝ)*x 1 + (2623298733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38890909/200000000 : ℝ)^2211 ≤ (11871368176143/100000000000000 : ℝ)^1699 := by
    have hnat : (38890909 : ℕ)^2211*100000000000000^1699 ≤ 11871368176143^1699*200000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38890909 200000000 11871368176143 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703798827/5000000000 : ℝ)^2211 ≤ (11232702299643/25000000000000 : ℝ)^1699 := by
    have hnat : (2703798827 : ℕ)^2211*25000000000000^1699 ≤ 11232702299643^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703798827 5000000000 11232702299643 25000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623298733/5000000000 : ℝ)^2211 ≤ (43197822609191/100000000000000 : ℝ)^1699 := by
    have hnat : (2623298733 : ℕ)^2211*100000000000000^1699 ≤ 43197822609191^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623298733 5000000000 43197822609191 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38890909/200000000 : ℝ), (2703798827/5000000000 : ℝ), (2623298733/5000000000 : ℝ)] ![(11871368176143/100000000000000 : ℝ), (11232702299643/25000000000000 : ℝ), (43197822609191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38890909/200000000 : ℝ)|^2211 ≤ (11871368176143/100000000000000 : ℝ)^1699
        have hw : |(-38890909/200000000 : ℝ)|=(38890909/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703798827/5000000000 : ℝ)|^2211 ≤ (11232702299643/25000000000000 : ℝ)^1699
        have hw : |(2703798827/5000000000 : ℝ)|=(2703798827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623298733/5000000000 : ℝ)|^2211 ≤ (43197822609191/100000000000000 : ℝ)^1699
        have hw : |(2623298733/5000000000 : ℝ)|=(2623298733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s4_1 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (53468921/100000000 : ℝ)*x 0 + (-1013254933/5000000000 : ℝ)*x 1 + (655824683/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53468921/100000000 : ℝ)^2211 ≤ (44275529824549/100000000000000 : ℝ)^1699 := by
    have hnat : (53468921 : ℕ)^2211*100000000000000^1699 ≤ 44275529824549^1699*100000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53468921 100000000 44275529824549 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1013254933/5000000000 : ℝ)^2211 ≤ (6263323784203/50000000000000 : ℝ)^1699 := by
    have hnat : (1013254933 : ℕ)^2211*50000000000000^1699 ≤ 6263323784203^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013254933 5000000000 6263323784203 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655824683/1250000000 : ℝ)^2211 ≤ (21598911293881/50000000000000 : ℝ)^1699 := by
    have hnat : (655824683 : ℕ)^2211*50000000000000^1699 ≤ 21598911293881^1699*1250000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655824683 1250000000 21598911293881 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53468921/100000000 : ℝ), (-1013254933/5000000000 : ℝ), (655824683/1250000000 : ℝ)] ![(44275529824549/100000000000000 : ℝ), (6263323784203/50000000000000 : ℝ), (21598911293881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53468921/100000000 : ℝ)|^2211 ≤ (44275529824549/100000000000000 : ℝ)^1699
        have hw : |(53468921/100000000 : ℝ)|=(53468921/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1013254933/5000000000 : ℝ)|^2211 ≤ (6263323784203/50000000000000 : ℝ)^1699
        have hw : |(-1013254933/5000000000 : ℝ)|=(1013254933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655824683/1250000000 : ℝ)|^2211 ≤ (21598911293881/50000000000000 : ℝ)^1699
        have hw : |(655824683/1250000000 : ℝ)|=(655824683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s4_2 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5346892103/10000000000 : ℝ)*x 0 + (655824683/1250000000 : ℝ)*x 1 + (-1013254931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346892103/10000000000 : ℝ)^2211 ≤ (44275529856877/100000000000000 : ℝ)^1699 := by
    have hnat : (5346892103 : ℕ)^2211*100000000000000^1699 ≤ 44275529856877^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346892103 10000000000 44275529856877 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655824683/1250000000 : ℝ)^2211 ≤ (21598911293881/50000000000000 : ℝ)^1699 := by
    have hnat : (655824683 : ℕ)^2211*50000000000000^1699 ≤ 21598911293881^1699*1250000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655824683 1250000000 21598911293881 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1013254931/5000000000 : ℝ)^2211 ≤ (12526647536229/100000000000000 : ℝ)^1699 := by
    have hnat : (1013254931 : ℕ)^2211*100000000000000^1699 ≤ 12526647536229^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013254931 5000000000 12526647536229 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346892103/10000000000 : ℝ), (655824683/1250000000 : ℝ), (-1013254931/5000000000 : ℝ)] ![(44275529856877/100000000000000 : ℝ), (21598911293881/50000000000000 : ℝ), (12526647536229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346892103/10000000000 : ℝ)|^2211 ≤ (44275529856877/100000000000000 : ℝ)^1699
        have hw : |(5346892103/10000000000 : ℝ)|=(5346892103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655824683/1250000000 : ℝ)|^2211 ≤ (21598911293881/50000000000000 : ℝ)^1699
        have hw : |(655824683/1250000000 : ℝ)|=(655824683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1013254931/5000000000 : ℝ)|^2211 ≤ (12526647536229/100000000000000 : ℝ)^1699
        have hw : |(-1013254931/5000000000 : ℝ)|=(1013254931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s4_3 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (859223329/2000000000 : ℝ)*x 0 + (257691649/625000000 : ℝ)*x 1 + (4475579179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859223329/2000000000 : ℝ)^2211 ≤ (16652221134159/50000000000000 : ℝ)^1699 := by
    have hnat : (859223329 : ℕ)^2211*50000000000000^1699 ≤ 16652221134159^1699*2000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859223329 2000000000 16652221134159 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257691649/625000000 : ℝ)^2211 ≤ (789233558733/2500000000000 : ℝ)^1699 := by
    have hnat : (257691649 : ℕ)^2211*2500000000000^1699 ≤ 789233558733^1699*625000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257691649 625000000 789233558733 2500000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4475579179/10000000000 : ℝ)^2211 ≤ (3512621536621/10000000000000 : ℝ)^1699 := by
    have hnat : (4475579179 : ℕ)^2211*10000000000000^1699 ≤ 3512621536621^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475579179 10000000000 3512621536621 10000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(859223329/2000000000 : ℝ), (257691649/625000000 : ℝ), (4475579179/10000000000 : ℝ)] ![(16652221134159/50000000000000 : ℝ), (789233558733/2500000000000 : ℝ), (3512621536621/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(859223329/2000000000 : ℝ)|^2211 ≤ (16652221134159/50000000000000 : ℝ)^1699
        have hw : |(859223329/2000000000 : ℝ)|=(859223329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(257691649/625000000 : ℝ)|^2211 ≤ (789233558733/2500000000000 : ℝ)^1699
        have hw : |(257691649/625000000 : ℝ)|=(257691649/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4475579179/10000000000 : ℝ)|^2211 ≤ (3512621536621/10000000000000 : ℝ)^1699
        have hw : |(4475579179/10000000000 : ℝ)|=(4475579179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s4_4 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-194455691/1000000000 : ℝ)*x 0 + (209887497/400000000 : ℝ)*x 1 + (1351751151/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (194455691/1000000000 : ℝ)^2211 ≤ (11871459222599/100000000000000 : ℝ)^1699 := by
    have hnat : (194455691 : ℕ)^2211*100000000000000^1699 ≤ 11871459222599^1699*1000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194455691 1000000000 11871459222599 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209887497/400000000 : ℝ)^2211 ≤ (43204143942119/100000000000000 : ℝ)^1699 := by
    have hnat : (209887497 : ℕ)^2211*100000000000000^1699 ≤ 43204143942119^1699*400000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209887497 400000000 43204143942119 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351751151/2500000000 : ℝ)^2211 ≤ (22462198408433/50000000000000 : ℝ)^1699 := by
    have hnat : (1351751151 : ℕ)^2211*50000000000000^1699 ≤ 22462198408433^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351751151 2500000000 22462198408433 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-194455691/1000000000 : ℝ), (209887497/400000000 : ℝ), (1351751151/2500000000 : ℝ)] ![(11871459222599/100000000000000 : ℝ), (43204143942119/100000000000000 : ℝ), (22462198408433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-194455691/1000000000 : ℝ)|^2211 ≤ (11871459222599/100000000000000 : ℝ)^1699
        have hw : |(-194455691/1000000000 : ℝ)|=(194455691/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209887497/400000000 : ℝ)|^2211 ≤ (43204143942119/100000000000000 : ℝ)^1699
        have hw : |(209887497/400000000 : ℝ)|=(209887497/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351751151/2500000000 : ℝ)|^2211 ≤ (22462198408433/50000000000000 : ℝ)^1699
        have hw : |(1351751151/2500000000 : ℝ)|=(1351751151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s4_5 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5304905193/10000000000 : ℝ)*x 0 + (-1866102781/10000000000 : ℝ)*x 1 + (1081400919/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304905193/10000000000 : ℝ)^2211 ≤ (21911807552539/50000000000000 : ℝ)^1699 := by
    have hnat : (5304905193 : ℕ)^2211*50000000000000^1699 ≤ 21911807552539^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304905193 10000000000 21911807552539 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1866102781/10000000000 : ℝ)^2211 ≤ (1125198815351/10000000000000 : ℝ)^1699 := by
    have hnat : (1866102781 : ℕ)^2211*10000000000000^1699 ≤ 1125198815351^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866102781 10000000000 1125198815351 10000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081400919/2000000000 : ℝ)^2211 ≤ (8984879343911/20000000000000 : ℝ)^1699 := by
    have hnat : (1081400919 : ℕ)^2211*20000000000000^1699 ≤ 8984879343911^1699*2000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081400919 2000000000 8984879343911 20000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304905193/10000000000 : ℝ), (-1866102781/10000000000 : ℝ), (1081400919/2000000000 : ℝ)] ![(21911807552539/50000000000000 : ℝ), (1125198815351/10000000000000 : ℝ), (8984879343911/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304905193/10000000000 : ℝ)|^2211 ≤ (21911807552539/50000000000000 : ℝ)^1699
        have hw : |(5304905193/10000000000 : ℝ)|=(5304905193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1866102781/10000000000 : ℝ)|^2211 ≤ (1125198815351/10000000000000 : ℝ)^1699
        have hw : |(-1866102781/10000000000 : ℝ)|=(1866102781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081400919/2000000000 : ℝ)|^2211 ≤ (8984879343911/20000000000000 : ℝ)^1699
        have hw : |(1081400919/2000000000 : ℝ)|=(1081400919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s4_6 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1060981053/2000000000 : ℝ)*x 0 + (108140091/200000000 : ℝ)*x 1 + (-373220549/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060981053/2000000000 : ℝ)^2211 ≤ (43823615879109/100000000000000 : ℝ)^1699 := by
    have hnat : (1060981053 : ℕ)^2211*100000000000000^1699 ≤ 43823615879109^1699*2000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060981053 2000000000 43823615879109 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108140091/200000000 : ℝ)^2211 ≤ (44924396232999/100000000000000 : ℝ)^1699 := by
    have hnat : (108140091 : ℕ)^2211*100000000000000^1699 ≤ 44924396232999^1699*200000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108140091 200000000 44924396232999 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (373220549/2000000000 : ℝ)^2211 ≤ (2812996967757/25000000000000 : ℝ)^1699 := by
    have hnat : (373220549 : ℕ)^2211*25000000000000^1699 ≤ 2812996967757^1699*2000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373220549 2000000000 2812996967757 25000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060981053/2000000000 : ℝ), (108140091/200000000 : ℝ), (-373220549/2000000000 : ℝ)] ![(43823615879109/100000000000000 : ℝ), (44924396232999/100000000000000 : ℝ), (2812996967757/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060981053/2000000000 : ℝ)|^2211 ≤ (43823615879109/100000000000000 : ℝ)^1699
        have hw : |(1060981053/2000000000 : ℝ)|=(1060981053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108140091/200000000 : ℝ)|^2211 ≤ (44924396232999/100000000000000 : ℝ)^1699
        have hw : |(108140091/200000000 : ℝ)|=(108140091/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-373220549/2000000000 : ℝ)|^2211 ≤ (2812996967757/25000000000000 : ℝ)^1699
        have hw : |(-373220549/2000000000 : ℝ)|=(373220549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s4_7 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4296141783/10000000000 : ℝ)*x 0 + (2237143681/5000000000 : ℝ)*x 1 + (2062182483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4296141783/10000000000 : ℝ)^2211 ≤ (2081543491891/6250000000000 : ℝ)^1699 := by
    have hnat : (4296141783 : ℕ)^2211*6250000000000^1699 ≤ 2081543491891^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296141783 10000000000 2081543491891 6250000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2237143681/5000000000 : ℝ)^2211 ≤ (877825546987/2500000000000 : ℝ)^1699 := by
    have hnat : (2237143681 : ℕ)^2211*2500000000000^1699 ≤ 877825546987^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237143681 5000000000 877825546987 2500000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2062182483/5000000000 : ℝ)^2211 ≤ (31582282238531/100000000000000 : ℝ)^1699 := by
    have hnat : (2062182483 : ℕ)^2211*100000000000000^1699 ≤ 31582282238531^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062182483 5000000000 31582282238531 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4296141783/10000000000 : ℝ), (2237143681/5000000000 : ℝ), (2062182483/5000000000 : ℝ)] ![(2081543491891/6250000000000 : ℝ), (877825546987/2500000000000 : ℝ), (31582282238531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4296141783/10000000000 : ℝ)|^2211 ≤ (2081543491891/6250000000000 : ℝ)^1699
        have hw : |(4296141783/10000000000 : ℝ)|=(4296141783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2237143681/5000000000 : ℝ)|^2211 ≤ (877825546987/2500000000000 : ℝ)^1699
        have hw : |(2237143681/5000000000 : ℝ)|=(2237143681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2062182483/5000000000 : ℝ)|^2211 ≤ (31582282238531/100000000000000 : ℝ)^1699
        have hw : |(2062182483/5000000000 : ℝ)|=(2062182483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1462_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14931/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2277/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3699/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14931/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11257/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14931/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11257/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14931/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11257/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14931/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11257/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14931/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11257/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14931/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11257/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11257/100000 : ℝ) ^ (4421/1024 : ℝ) ≤ (2007097781587789/25000000000000000000 : ℝ) := by
    have hpowers : (11257/100000 : ℝ)^4421 ≤ (2007097781587789/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11257 : ℕ)^4421*25000000000000000000^1024 ≤ 2007097781587789^1024*100000^4421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11257 100000 2007097781587789 25000000000000000000 4421 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11257/100000 : ℝ)) (X := (2007097781587789/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14931/100000 : ℝ) ^ (4421/1024 : ℝ) ≤ (27178506794622903/100000000000000000000 : ℝ) := by
    have hpowers : (14931/100000 : ℝ)^4421 ≤ (27178506794622903/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14931 : ℕ)^4421*100000000000000000000^1024 ≤ 27178506794622903^1024*100000^4421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14931 100000 27178506794622903 100000000000000000000 4421 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14931/100000 : ℝ)) (X := (27178506794622903/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502007097781587789/12500000000000000000 : ℝ) ≤ (2500092971787113/2500000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (12502007097781587789/12500000000000000000 : ℝ)^1024 ≤ (2500092971787113/2500000000000000 : ℝ)^4421 := by
      have hnat : (12502007097781587789 : ℕ)^1024*2500000000000000^4421 ≤ 2500092971787113^4421*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502007097781587789 12500000000000000000 2500092971787113 2500000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500092971787113/2500000000000000 : ℝ)) (X := (12502007097781587789/12500000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035206897920974059/100000000000000000000 : ℝ) ≤ (1250101919780789/1250000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (100035206897920974059/100000000000000000000 : ℝ)^1024 ≤ (1250101919780789/1250000000000000 : ℝ)^4421 := by
      have hnat : (100035206897920974059 : ℕ)^1024*1250000000000000^4421 ≤ 1250101919780789^4421*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035206897920974059 100000000000000000000 1250101919780789 1250000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250101919780789/1250000000000000 : ℝ)) (X := (100035206897920974059/100000000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027178506794622903/50000000000000000000 : ℝ) ≤ (2500314707336043/2500000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (50027178506794622903/50000000000000000000 : ℝ)^1024 ≤ (2500314707336043/2500000000000000 : ℝ)^4421 := by
      have hnat : (50027178506794622903 : ℕ)^1024*2500000000000000^4421 ≤ 2500314707336043^4421*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027178506794622903 50000000000000000000 2500314707336043 2500000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500314707336043/2500000000000000 : ℝ)) (X := (50027178506794622903/50000000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2007097781587789/25000000000000000000 : ℝ) ≤ ((1147855687658943519/1148125000000000000 : ℝ)+2*(22173554893/18370000000000 : ℝ)*(11257/100000 : ℝ))^(4421/1024 : ℝ) := by
    rw [show (1147855687658943519/1148125000000000000 : ℝ)+2*(22173554893/18370000000000 : ℝ)*(11257/100000 : ℝ)=(2500092971787113/2500000000000000 : ℝ) by norm_num, show 1+2*(2007097781587789/25000000000000000000 : ℝ)=(12502007097781587789/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27178506794622903/100000000000000000000 : ℝ)+(2007097781587789/25000000000000000000 : ℝ) ≤ ((1147855687658943519/1148125000000000000 : ℝ)+(22173554893/18370000000000 : ℝ)*((14931/100000 : ℝ)+(11257/100000 : ℝ)))^(4421/1024 : ℝ) := by
    rw [show (1147855687658943519/1148125000000000000 : ℝ)+(22173554893/18370000000000 : ℝ)*((14931/100000 : ℝ)+(11257/100000 : ℝ))=(1250101919780789/1250000000000000 : ℝ) by norm_num, show 1+(27178506794622903/100000000000000000000 : ℝ)+(2007097781587789/25000000000000000000 : ℝ)=(100035206897920974059/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27178506794622903/100000000000000000000 : ℝ) ≤ ((1147855687658943519/1148125000000000000 : ℝ)+2*(22173554893/18370000000000 : ℝ)*(14931/100000 : ℝ))^(4421/1024 : ℝ) := by
    rw [show (1147855687658943519/1148125000000000000 : ℝ)+2*(22173554893/18370000000000 : ℝ)*(14931/100000 : ℝ)=(2500314707336043/2500000000000000 : ℝ) by norm_num, show 1+2*(27178506794622903/100000000000000000000 : ℝ)=(50027178506794622903/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1147855687658943519/1148125000000000000 : ℝ)*(X 1 0+X 2 0)+(22173554893/18370000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (11257/100000 : ℝ)) (hi := (14931/100000 : ℝ)) (c := (1147855687658943519/1148125000000000000 : ℝ)) (alpha := (22173554893/18370000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1147855687658943519/1148125000000000000 : ℝ)*(X 0 1+X 2 1)+(22173554893/18370000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (11257/100000 : ℝ)) (hi := (14931/100000 : ℝ)) (c := (1147855687658943519/1148125000000000000 : ℝ)) (alpha := (22173554893/18370000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1147855687658943519/1148125000000000000 : ℝ)*(X 0 2+X 1 2)+(22173554893/18370000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (11257/100000 : ℝ)) (hi := (14931/100000 : ℝ)) (c := (1147855687658943519/1148125000000000000 : ℝ)) (alpha := (22173554893/18370000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-38890909/200000000 : ℝ)*X 0 0+(2703798827/5000000000 : ℝ)*X 0 1+(2623298733/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((53468921/100000000 : ℝ)*X 1 0+(-1013254933/5000000000 : ℝ)*X 1 1+(655824683/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346892103/10000000000 : ℝ)*X 2 0+(655824683/1250000000 : ℝ)*X 2 1+(-1013254931/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((859223329/2000000000 : ℝ)*X 0 0+(257691649/625000000 : ℝ)*X 0 1+(4475579179/10000000000 : ℝ)*X 0 2+(859223329/2000000000 : ℝ)*X 1 0+(257691649/625000000 : ℝ)*X 1 1+(4475579179/10000000000 : ℝ)*X 1 2+(859223329/2000000000 : ℝ)*X 2 0+(257691649/625000000 : ℝ)*X 2 1+(4475579179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-194455691/1000000000 : ℝ)*X 0 0+(209887497/400000000 : ℝ)*X 0 1+(1351751151/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304905193/10000000000 : ℝ)*X 1 0+(-1866102781/10000000000 : ℝ)*X 1 1+(1081400919/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060981053/2000000000 : ℝ)*X 2 0+(108140091/200000000 : ℝ)*X 2 1+(-373220549/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4296141783/10000000000 : ℝ)*X 0 0+(2237143681/5000000000 : ℝ)*X 0 1+(2062182483/5000000000 : ℝ)*X 0 2+(4296141783/10000000000 : ℝ)*X 1 0+(2237143681/5000000000 : ℝ)*X 1 1+(2062182483/5000000000 : ℝ)*X 1 2+(4296141783/10000000000 : ℝ)*X 2 0+(2237143681/5000000000 : ℝ)*X 2 1+(2062182483/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (65829815763387930669909933/28703125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (402803251/100000000000000 : ℝ)*(base19) + (364066017/100000000000000 : ℝ)*(base23) + (11287869/50000000000000 : ℝ)*(lower2) + (1734127/3125000000000 : ℝ)*(upper3) + (1221073/4000000000000 : ℝ)*(upper5) + (141374596462533/3125000000000 : ℝ)*(major0) + (141374596462533/3125000000000 : ℝ)*(major1) + (141374596462533/3125000000000 : ℝ)*(major2) + (6211181616174973/100000000000000 : ℝ)*(sp0) + (6211189612891801/100000000000000 : ℝ)*(sp1) + (1242237930325807/20000000000000 : ℝ)*(sp2) + (1418389989748299/50000000000000 : ℝ)*(sp3) + (8399520079/100000000000000 : ℝ)*(sp4) + (820392277/20000000000000 : ℝ)*(sp7) + (44324751272781/1562500000000 : ℝ)*(f.failure) + (1552797503923763/25000000000000 : ℝ)*(f.sum) + (3289498894709/1837000000000000000000000000 : ℝ)*base66 + (188490557539092141/28703125000000000000000000000000 : ℝ)*base67 + (67187773286897633/14351562500000000000000000000000 : ℝ)*base69 + (206648230592185891/28703125000000000000000000000000 : ℝ)*base71 + (404566104527/229625000000000000000000000 : ℝ)*base74 + (22770312884986127/3587890625000000000000000000000 : ℝ)*base75 + (111858436907928883/14351562500000000000000000000000 : ℝ)*base77 + (70620409764446117/14351562500000000000000000000000 : ℝ)*base80 + (3856676699241/918500000000000000000000000 : ℝ)*base81 + (368361/31250000000000000000 : ℝ)*base89 + (368361/31250000000000000000 : ℝ)*base91 + (368361/31250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (512658751882198192295222061/57406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5539903/400000000000 : ℝ)*(base19) + (1644574569/100000000000000 : ℝ)*(base23) + (75177823/50000000000000 : ℝ)*(upper3) + (4927023/6250000000000 : ℝ)*(lower4) + (103091037/50000000000000 : ℝ)*(upper5) + (4557463217692591/100000000000000 : ℝ)*(major0) + (4557463217692591/100000000000000 : ℝ)*(major1) + (4557463217692591/100000000000000 : ℝ)*(major2) + (3741507937/12500000000000 : ℝ)*(sp1) + (830655241/2500000000000 : ℝ)*(sp2) + (1251430143067211/20000000000000 : ℝ)*(sp4) + (6257119398296809/100000000000000 : ℝ)*(sp5) + (3128557922275923/50000000000000 : ℝ)*(sp6) + (285777542237029/10000000000000 : ℝ)*(sp7) + (285777542237029/10000000000000 : ℝ)*(f.failure) + (1251430143067211/20000000000000 : ℝ)*(f.sum) + (1364977505107/918500000000000000000000000 : ℝ)*base66 + (1941425696861982271/114812500000000000000000000000000 : ℝ)*base68 + (1193063356061044771/114812500000000000000000000000000 : ℝ)*base70 + (634084973632232271/114812500000000000000000000000000 : ℝ)*base72 + (16077708323229/1837000000000000000000000000 : ℝ)*base74 + (2231567020468732271/114812500000000000000000000000000 : ℝ)*base76 + (1239047119394794771/114812500000000000000000000000000 : ℝ)*base78 + (2761662716658544771/114812500000000000000000000000000 : ℝ)*base80 + (1318513719313/229625000000000000000000000 : ℝ)*base82 + (2857249/200000000000000000000 : ℝ)*base89 + (2857249/200000000000000000000 : ℝ)*base91 + (2857249/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1462_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14931/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3699/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1462_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1462_s5_0 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-77785999/400000000 : ℝ)*x 0 + (5406651851/10000000000 : ℝ)*x 1 + (1311868593/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (77785999/400000000 : ℝ)^2211 ≤ (742012412729/6250000000000 : ℝ)^1699 := by
    have hnat : (77785999 : ℕ)^2211*6250000000000^1699 ≤ 742012412729^1699*400000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77785999 400000000 742012412729 6250000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406651851/10000000000 : ℝ)^2211 ≤ (2246029137929/5000000000000 : ℝ)^1699 := by
    have hnat : (5406651851 : ℕ)^2211*5000000000000^1699 ≤ 2246029137929^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406651851 10000000000 2246029137929 5000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311868593/2500000000 : ℝ)^2211 ≤ (10801804654707/25000000000000 : ℝ)^1699 := by
    have hnat : (1311868593 : ℕ)^2211*25000000000000^1699 ≤ 10801804654707^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311868593 2500000000 10801804654707 25000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-77785999/400000000 : ℝ), (5406651851/10000000000 : ℝ), (1311868593/2500000000 : ℝ)] ![(742012412729/6250000000000 : ℝ), (2246029137929/5000000000000 : ℝ), (10801804654707/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-77785999/400000000 : ℝ)|^2211 ≤ (742012412729/6250000000000 : ℝ)^1699
        have hw : |(-77785999/400000000 : ℝ)|=(77785999/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406651851/10000000000 : ℝ)|^2211 ≤ (2246029137929/5000000000000 : ℝ)^1699
        have hw : |(5406651851/10000000000 : ℝ)|=(5406651851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311868593/2500000000 : ℝ)|^2211 ≤ (10801804654707/25000000000000 : ℝ)^1699
        have hw : |(1311868593/2500000000 : ℝ)|=(1311868593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s5_1 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5346647003/10000000000 : ℝ)*x 0 + (-2025670099/10000000000 : ℝ)*x 1 + (2623737183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346647003/10000000000 : ℝ)^2211 ≤ (22136444338371/50000000000000 : ℝ)^1699 := by
    have hnat : (5346647003 : ℕ)^2211*50000000000000^1699 ≤ 22136444338371^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346647003 10000000000 22136444338371 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2025670099/10000000000 : ℝ)^2211 ≤ (12519892757683/100000000000000 : ℝ)^1699 := by
    have hnat : (2025670099 : ℕ)^2211*100000000000000^1699 ≤ 12519892757683^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025670099 10000000000 12519892757683 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623737183/5000000000 : ℝ)^2211 ≤ (43207218554537/100000000000000 : ℝ)^1699 := by
    have hnat : (2623737183 : ℕ)^2211*100000000000000^1699 ≤ 43207218554537^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623737183 5000000000 43207218554537 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346647003/10000000000 : ℝ), (-2025670099/10000000000 : ℝ), (2623737183/5000000000 : ℝ)] ![(22136444338371/50000000000000 : ℝ), (12519892757683/100000000000000 : ℝ), (43207218554537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346647003/10000000000 : ℝ)|^2211 ≤ (22136444338371/50000000000000 : ℝ)^1699
        have hw : |(5346647003/10000000000 : ℝ)|=(5346647003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2025670099/10000000000 : ℝ)|^2211 ≤ (12519892757683/100000000000000 : ℝ)^1699
        have hw : |(-2025670099/10000000000 : ℝ)|=(2025670099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623737183/5000000000 : ℝ)|^2211 ≤ (43207218554537/100000000000000 : ℝ)^1699
        have hw : |(2623737183/5000000000 : ℝ)|=(2623737183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s5_2 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5346646997/10000000000 : ℝ)*x 0 + (5247474377/10000000000 : ℝ)*x 1 + (-506417523/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346646997/10000000000 : ℝ)^2211 ≤ (44272888612087/100000000000000 : ℝ)^1699 := by
    have hnat : (5346646997 : ℕ)^2211*100000000000000^1699 ≤ 44272888612087^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346646997 10000000000 44272888612087 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247474377/10000000000 : ℝ)^2211 ≤ (10801804668101/25000000000000 : ℝ)^1699 := by
    have hnat : (5247474377 : ℕ)^2211*25000000000000^1699 ≤ 10801804668101^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247474377 10000000000 10801804668101 25000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (506417523/2500000000 : ℝ)^2211 ≤ (12519892701381/100000000000000 : ℝ)^1699 := by
    have hnat : (506417523 : ℕ)^2211*100000000000000^1699 ≤ 12519892701381^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506417523 2500000000 12519892701381 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346646997/10000000000 : ℝ), (5247474377/10000000000 : ℝ), (-506417523/2500000000 : ℝ)] ![(44272888612087/100000000000000 : ℝ), (10801804668101/25000000000000 : ℝ), (12519892701381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346646997/10000000000 : ℝ)|^2211 ≤ (44272888612087/100000000000000 : ℝ)^1699
        have hw : |(5346646997/10000000000 : ℝ)|=(5346646997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247474377/10000000000 : ℝ)|^2211 ≤ (10801804668101/25000000000000 : ℝ)^1699
        have hw : |(5247474377/10000000000 : ℝ)|=(5247474377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-506417523/2500000000 : ℝ)|^2211 ≤ (12519892701381/100000000000000 : ℝ)^1699
        have hw : |(-506417523/2500000000 : ℝ)|=(506417523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s5_3 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4296181069/10000000000 : ℝ)*x 0 + (2062527057/5000000000 : ℝ)*x 1 + (2236788039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4296181069/10000000000 : ℝ)^2211 ≤ (33305092203627/100000000000000 : ℝ)^1699 := by
    have hnat : (4296181069 : ℕ)^2211*100000000000000^1699 ≤ 33305092203627^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296181069 10000000000 33305092203627 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2062527057/5000000000 : ℝ)^2211 ≤ (7897287460529/25000000000000 : ℝ)^1699 := by
    have hnat : (2062527057 : ℕ)^2211*25000000000000^1699 ≤ 7897287460529^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062527057 5000000000 7897287460529 25000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2236788039/5000000000 : ℝ)^2211 ≤ (702115158761/2000000000000 : ℝ)^1699 := by
    have hnat : (2236788039 : ℕ)^2211*2000000000000^1699 ≤ 702115158761^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236788039 5000000000 702115158761 2000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4296181069/10000000000 : ℝ), (2062527057/5000000000 : ℝ), (2236788039/5000000000 : ℝ)] ![(33305092203627/100000000000000 : ℝ), (7897287460529/25000000000000 : ℝ), (702115158761/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4296181069/10000000000 : ℝ)|^2211 ≤ (33305092203627/100000000000000 : ℝ)^1699
        have hw : |(4296181069/10000000000 : ℝ)|=(4296181069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2062527057/5000000000 : ℝ)|^2211 ≤ (7897287460529/25000000000000 : ℝ)^1699
        have hw : |(2062527057/5000000000 : ℝ)|=(2062527057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2236788039/5000000000 : ℝ)|^2211 ≤ (702115158761/2000000000000 : ℝ)^1699
        have hw : |(2236788039/5000000000 : ℝ)|=(2236788039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s5_4 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1944661063/10000000000 : ℝ)*x 0 + (1049610223/2000000000 : ℝ)*x 1 + (5406072113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1944661063/10000000000 : ℝ)^2211 ≤ (11872286696109/100000000000000 : ℝ)^1699 := by
    have hnat : (1944661063 : ℕ)^2211*100000000000000^1699 ≤ 11872286696109^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944661063 10000000000 11872286696109 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049610223/2000000000 : ℝ)^2211 ≤ (8642679730587/20000000000000 : ℝ)^1699 := by
    have hnat : (1049610223 : ℕ)^2211*20000000000000^1699 ≤ 8642679730587^1699*2000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049610223 2000000000 8642679730587 20000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406072113/10000000000 : ℝ)^2211 ≤ (44914314641623/100000000000000 : ℝ)^1699 := by
    have hnat : (5406072113 : ℕ)^2211*100000000000000^1699 ≤ 44914314641623^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406072113 10000000000 44914314641623 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1944661063/10000000000 : ℝ), (1049610223/2000000000 : ℝ), (5406072113/10000000000 : ℝ)] ![(11872286696109/100000000000000 : ℝ), (8642679730587/20000000000000 : ℝ), (44914314641623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1944661063/10000000000 : ℝ)|^2211 ≤ (11872286696109/100000000000000 : ℝ)^1699
        have hw : |(-1944661063/10000000000 : ℝ)|=(1944661063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049610223/2000000000 : ℝ)|^2211 ≤ (8642679730587/20000000000000 : ℝ)^1699
        have hw : |(1049610223/2000000000 : ℝ)|=(1049610223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406072113/10000000000 : ℝ)|^2211 ≤ (44914314641623/100000000000000 : ℝ)^1699
        have hw : |(5406072113/10000000000 : ℝ)|=(5406072113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s5_5 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305135293/10000000000 : ℝ)*x 0 + (-1867072361/10000000000 : ℝ)*x 1 + (5406072091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305135293/10000000000 : ℝ)^2211 ≤ (5478261099471/12500000000000 : ℝ)^1699 := by
    have hnat : (5305135293 : ℕ)^2211*12500000000000^1699 ≤ 5478261099471^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305135293 10000000000 5478261099471 12500000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1867072361/10000000000 : ℝ)^2211 ≤ (11259596787849/100000000000000 : ℝ)^1699 := by
    have hnat : (1867072361 : ℕ)^2211*100000000000000^1699 ≤ 11259596787849^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867072361 10000000000 11259596787849 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406072091/10000000000 : ℝ)^2211 ≤ (44914314403763/100000000000000 : ℝ)^1699 := by
    have hnat : (5406072091 : ℕ)^2211*100000000000000^1699 ≤ 44914314403763^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406072091 10000000000 44914314403763 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305135293/10000000000 : ℝ), (-1867072361/10000000000 : ℝ), (5406072091/10000000000 : ℝ)] ![(5478261099471/12500000000000 : ℝ), (11259596787849/100000000000000 : ℝ), (44914314403763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305135293/10000000000 : ℝ)|^2211 ≤ (5478261099471/12500000000000 : ℝ)^1699
        have hw : |(5305135293/10000000000 : ℝ)|=(5305135293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1867072361/10000000000 : ℝ)|^2211 ≤ (11259596787849/100000000000000 : ℝ)^1699
        have hw : |(-1867072361/10000000000 : ℝ)|=(1867072361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406072091/10000000000 : ℝ)|^2211 ≤ (44914314403763/100000000000000 : ℝ)^1699
        have hw : |(5406072091/10000000000 : ℝ)|=(5406072091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s5_6 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305135263/10000000000 : ℝ)*x 0 + (5406072107/10000000000 : ℝ)*x 1 + (-1867072381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305135263/10000000000 : ℝ)^2211 ≤ (43826088473251/100000000000000 : ℝ)^1699 := by
    have hnat : (5305135263 : ℕ)^2211*100000000000000^1699 ≤ 43826088473251^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305135263 10000000000 43826088473251 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406072107/10000000000 : ℝ)^2211 ≤ (2807144661047/6250000000000 : ℝ)^1699 := by
    have hnat : (5406072107 : ℕ)^2211*6250000000000^1699 ≤ 2807144661047^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406072107 10000000000 2807144661047 6250000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1867072381/10000000000 : ℝ)^2211 ≤ (1407449618101/12500000000000 : ℝ)^1699 := by
    have hnat : (1867072381 : ℕ)^2211*12500000000000^1699 ≤ 1407449618101^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867072381 10000000000 1407449618101 12500000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305135263/10000000000 : ℝ), (5406072107/10000000000 : ℝ), (-1867072381/10000000000 : ℝ)] ![(43826088473251/100000000000000 : ℝ), (2807144661047/6250000000000 : ℝ), (1407449618101/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305135263/10000000000 : ℝ)|^2211 ≤ (43826088473251/100000000000000 : ℝ)^1699
        have hw : |(5305135263/10000000000 : ℝ)|=(5305135263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406072107/10000000000 : ℝ)|^2211 ≤ (2807144661047/6250000000000 : ℝ)^1699
        have hw : |(5406072107/10000000000 : ℝ)|=(5406072107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1867072381/10000000000 : ℝ)|^2211 ≤ (1407449618101/12500000000000 : ℝ)^1699
        have hw : |(-1867072381/10000000000 : ℝ)|=(1867072381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s5_7 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4296205359/10000000000 : ℝ)*x 0 + (4472313279/10000000000 : ℝ)*x 1 + (16118451/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4296205359/10000000000 : ℝ)^2211 ≤ (33305337251711/100000000000000 : ℝ)^1699 := by
    have hnat : (4296205359 : ℕ)^2211*100000000000000^1699 ≤ 33305337251711^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296205359 10000000000 33305337251711 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4472313279/10000000000 : ℝ)^2211 ≤ (35092862543153/100000000000000 : ℝ)^1699 := by
    have hnat : (4472313279 : ℕ)^2211*100000000000000^1699 ≤ 35092862543153^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4472313279 10000000000 35092862543153 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16118451/39062500 : ℝ)^2211 ≤ (3950225023631/12500000000000 : ℝ)^1699 := by
    have hnat : (16118451 : ℕ)^2211*12500000000000^1699 ≤ 3950225023631^1699*39062500^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16118451 39062500 3950225023631 12500000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4296205359/10000000000 : ℝ), (4472313279/10000000000 : ℝ), (16118451/39062500 : ℝ)] ![(33305337251711/100000000000000 : ℝ), (35092862543153/100000000000000 : ℝ), (3950225023631/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4296205359/10000000000 : ℝ)|^2211 ≤ (33305337251711/100000000000000 : ℝ)^1699
        have hw : |(4296205359/10000000000 : ℝ)|=(4296205359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4472313279/10000000000 : ℝ)|^2211 ≤ (35092862543153/100000000000000 : ℝ)^1699
        have hw : |(4472313279/10000000000 : ℝ)|=(4472313279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16118451/39062500 : ℝ)|^2211 ≤ (3950225023631/12500000000000 : ℝ)^1699
        have hw : |(16118451/39062500 : ℝ)|=(16118451/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1462_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3699/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11403/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1847/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3699/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2277/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3699/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2277/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3699/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2277/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3699/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2277/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3699/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2277/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3699/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2277/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2277/20000 : ℝ) ^ (4421/1024 : ℝ) ≤ (2107504317689459/25000000000000000000 : ℝ) := by
    have hpowers : (2277/20000 : ℝ)^4421 ≤ (2107504317689459/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2277 : ℕ)^4421*25000000000000000000^1024 ≤ 2107504317689459^1024*20000^4421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2277 20000 2107504317689459 25000000000000000000 4421 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2277/20000 : ℝ)) (X := (2107504317689459/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3699/25000 : ℝ) ^ (4421/1024 : ℝ) ≤ (5226673331087819/20000000000000000000 : ℝ) := by
    have hpowers : (3699/25000 : ℝ)^4421 ≤ (5226673331087819/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3699 : ℕ)^4421*20000000000000000000^1024 ≤ 5226673331087819^1024*25000^4421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3699 25000 5226673331087819 20000000000000000000 4421 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3699/25000 : ℝ)) (X := (5226673331087819/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502107504317689459/12500000000000000000 : ℝ) ≤ (5000195244935223/5000000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (12502107504317689459/12500000000000000000 : ℝ)^1024 ≤ (5000195244935223/5000000000000000 : ℝ)^4421 := by
      have hnat : (12502107504317689459 : ℕ)^1024*5000000000000000^4421 ≤ 5000195244935223^4421*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502107504317689459 12500000000000000000 5000195244935223 5000000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000195244935223/5000000000000000 : ℝ)) (X := (12502107504317689459/12500000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034563383926196931/100000000000000000000 : ℝ) ≤ (1000080045705311/1000000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (100034563383926196931/100000000000000000000 : ℝ)^1024 ≤ (1000080045705311/1000000000000000 : ℝ)^4421 := by
      have hnat : (100034563383926196931 : ℕ)^1024*1000000000000000^4421 ≤ 1000080045705311^4421*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034563383926196931 100000000000000000000 1000080045705311 1000000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000080045705311/1000000000000000 : ℝ)) (X := (100034563383926196931/100000000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005226673331087819/10000000000000000000 : ℝ) ≤ (5000605212117887/5000000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (10005226673331087819/10000000000000000000 : ℝ)^1024 ≤ (5000605212117887/5000000000000000 : ℝ)^4421 := by
      have hnat : (10005226673331087819 : ℕ)^1024*5000000000000000^4421 ≤ 5000605212117887^4421*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005226673331087819 10000000000000000000 5000605212117887 5000000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000605212117887/5000000000000000 : ℝ)) (X := (10005226673331087819/10000000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2107504317689459/25000000000000000000 : ℝ) ≤ ((1894555389344379557/1895000000000000000 : ℝ)+2*(51245897833/42637500000000 : ℝ)*(2277/20000 : ℝ))^(4421/1024 : ℝ) := by
    rw [show (1894555389344379557/1895000000000000000 : ℝ)+2*(51245897833/42637500000000 : ℝ)*(2277/20000 : ℝ)=(5000195244935223/5000000000000000 : ℝ) by norm_num, show 1+2*(2107504317689459/25000000000000000000 : ℝ)=(12502107504317689459/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5226673331087819/20000000000000000000 : ℝ)+(2107504317689459/25000000000000000000 : ℝ) ≤ ((1894555389344379557/1895000000000000000 : ℝ)+(51245897833/42637500000000 : ℝ)*((3699/25000 : ℝ)+(2277/20000 : ℝ)))^(4421/1024 : ℝ) := by
    rw [show (1894555389344379557/1895000000000000000 : ℝ)+(51245897833/42637500000000 : ℝ)*((3699/25000 : ℝ)+(2277/20000 : ℝ))=(1000080045705311/1000000000000000 : ℝ) by norm_num, show 1+(5226673331087819/20000000000000000000 : ℝ)+(2107504317689459/25000000000000000000 : ℝ)=(100034563383926196931/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5226673331087819/20000000000000000000 : ℝ) ≤ ((1894555389344379557/1895000000000000000 : ℝ)+2*(51245897833/42637500000000 : ℝ)*(3699/25000 : ℝ))^(4421/1024 : ℝ) := by
    rw [show (1894555389344379557/1895000000000000000 : ℝ)+2*(51245897833/42637500000000 : ℝ)*(3699/25000 : ℝ)=(5000605212117887/5000000000000000 : ℝ) by norm_num, show 1+2*(5226673331087819/20000000000000000000 : ℝ)=(10005226673331087819/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1894555389344379557/1895000000000000000 : ℝ)*(X 1 0+X 2 0)+(51245897833/42637500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (2277/20000 : ℝ)) (hi := (3699/25000 : ℝ)) (c := (1894555389344379557/1895000000000000000 : ℝ)) (alpha := (51245897833/42637500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1894555389344379557/1895000000000000000 : ℝ)*(X 0 1+X 2 1)+(51245897833/42637500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (2277/20000 : ℝ)) (hi := (3699/25000 : ℝ)) (c := (1894555389344379557/1895000000000000000 : ℝ)) (alpha := (51245897833/42637500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1894555389344379557/1895000000000000000 : ℝ)*(X 0 2+X 1 2)+(51245897833/42637500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (2277/20000 : ℝ)) (hi := (3699/25000 : ℝ)) (c := (1894555389344379557/1895000000000000000 : ℝ)) (alpha := (51245897833/42637500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-77785999/400000000 : ℝ)*X 0 0+(5406651851/10000000000 : ℝ)*X 0 1+(1311868593/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346647003/10000000000 : ℝ)*X 1 0+(-2025670099/10000000000 : ℝ)*X 1 1+(2623737183/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346646997/10000000000 : ℝ)*X 2 0+(5247474377/10000000000 : ℝ)*X 2 1+(-506417523/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4296181069/10000000000 : ℝ)*X 0 0+(2062527057/5000000000 : ℝ)*X 0 1+(2236788039/5000000000 : ℝ)*X 0 2+(4296181069/10000000000 : ℝ)*X 1 0+(2062527057/5000000000 : ℝ)*X 1 1+(2236788039/5000000000 : ℝ)*X 1 2+(4296181069/10000000000 : ℝ)*X 2 0+(2062527057/5000000000 : ℝ)*X 2 1+(2236788039/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1944661063/10000000000 : ℝ)*X 0 0+(1049610223/2000000000 : ℝ)*X 0 1+(5406072113/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305135293/10000000000 : ℝ)*X 1 0+(-1867072361/10000000000 : ℝ)*X 1 1+(5406072091/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305135263/10000000000 : ℝ)*X 2 0+(5406072107/10000000000 : ℝ)*X 2 1+(-1867072381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4296205359/10000000000 : ℝ)*X 0 0+(4472313279/10000000000 : ℝ)*X 0 1+(16118451/39062500 : ℝ)*X 0 2+(4296205359/10000000000 : ℝ)*X 1 0+(4472313279/10000000000 : ℝ)*X 1 1+(16118451/39062500 : ℝ)*X 1 2+(4296205359/10000000000 : ℝ)*X 2 0+(4472313279/10000000000 : ℝ)*X 2 1+(16118451/39062500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (897683425743370225953939473/94750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (170819949/10000000000000 : ℝ)*(base19) + (1576957553/100000000000000 : ℝ)*(base23) + (4150063/6250000000000 : ℝ)*(lower2) + (232797229/100000000000000 : ℝ)*(upper3) + (75267719/50000000000000 : ℝ)*(upper5) + (4575831760060737/100000000000000 : ℝ)*(major0) + (4575831760060737/100000000000000 : ℝ)*(major1) + (4575831760060737/100000000000000 : ℝ)*(major2) + (6282333442843791/100000000000000 : ℝ)*(sp0) + (3141184003126997/50000000000000 : ℝ)*(sp1) + (6282368137495931/100000000000000 : ℝ)*(sp2) + (1434637815549547/50000000000000 : ℝ)*(sp3) + (18135804847/50000000000000 : ℝ)*(sp4) + (17858761169/100000000000000 : ℝ)*(sp7) + (1434646744930131/50000000000000 : ℝ)*(f.failure) + (1256473942890697/20000000000000 : ℝ)*(f.sum) + (2664205449697/2842500000000000000000000000 : ℝ)*base66 + (7516956531106739473/568500000000000000000000000000000 : ℝ)*base68 + (508166129131260527/568500000000000000000000000000000 : ℝ)*base69 + (3880397232404760527/568500000000000000000000000000000 : ℝ)*base71 + (7764404183671/5685000000000000000000000000 : ℝ)*base73 + (5752902600226260527/568500000000000000000000000000000 : ℝ)*base75 + (7662420642007739473/568500000000000000000000000000000 : ℝ)*base78 + (4928222484427260527/568500000000000000000000000000000 : ℝ)*base79 + (1464685547477/710625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (9401289/1000000000000000000000 : ℝ)*base90 + (9401289/1000000000000000000000 : ℝ)*base92 + (9401289/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (81208404838402637073292369/11843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1153837751/100000000000000 : ℝ)*(base19) + (245309741/20000000000000 : ℝ)*(base23) + (34465261/25000000000000 : ℝ)*(upper3) + (10623071/20000000000000 : ℝ)*(lower4) + (71539873/50000000000000 : ℝ)*(upper5) + (1152316198831011/25000000000000 : ℝ)*(major0) + (1152316198831011/25000000000000 : ℝ)*(major1) + (1152316198831011/25000000000000 : ℝ)*(major2) + (23851634999/100000000000000 : ℝ)*(sp1) + (6230516363/25000000000000 : ℝ)*(sp2) + (3164135777302791/50000000000000 : ℝ)*(sp4) + (197757704660401/3125000000000 : ℝ)*(sp5) + (253129816239657/4000000000000 : ℝ)*(sp6) + (2890257807487623/100000000000000 : ℝ)*(sp7) + (2890257807487623/100000000000000 : ℝ)*(f.failure) + (3164135777302791/50000000000000 : ℝ)*(f.sum) + (16776712387763/5685000000000000000000000000 : ℝ)*base66 + (59649634054151381/142125000000000000000000000000000 : ℝ)*base67 + (770864437596776381/142125000000000000000000000000000 : ℝ)*base69 + (882823833392223619/142125000000000000000000000000000 : ℝ)*base72 + (4860853176317/1421250000000000000000000000 : ℝ)*base74 + (3015928842164276381/142125000000000000000000000000000 : ℝ)*base75 + (740972818170026381/142125000000000000000000000000000 : ℝ)*base77 + (534307062052526381/142125000000000000000000000000000 : ℝ)*base79 + (17177349050543/5685000000000000000000000000 : ℝ)*base82 + (10844763/2000000000000000000000 : ℝ)*base89 + (10844763/2000000000000000000000 : ℝ)*base91 + (10844763/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1462_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3699/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1462_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1462_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15703/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10537/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1462_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1462_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1462_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15703/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10537/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1462_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

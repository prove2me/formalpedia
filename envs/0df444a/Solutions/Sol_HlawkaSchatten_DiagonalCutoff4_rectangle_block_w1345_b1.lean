-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1345_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:05:28.849209+00:00
-- url     : https://prove2.me/submissions/99bbd494-c1ac-45ec-9f81-8581aff7994f

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
theorem support_rectangle_w1345_s3_0 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2039653973/10000000000 : ℝ)*x 0 + (1356696853/2500000000 : ℝ)*x 1 + (5231599939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2039653973/10000000000 : ℝ)^4305 ≤ (1552312347647/12500000000000 : ℝ)^3281 := by
    have hnat : (2039653973 : ℕ)^4305*12500000000000^3281 ≤ 1552312347647^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039653973 10000000000 1552312347647 12500000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356696853/2500000000 : ℝ)^4305 ≤ (22421446744893/50000000000000 : ℝ)^3281 := by
    have hnat : (1356696853 : ℕ)^4305*50000000000000^3281 ≤ 22421446744893^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356696853 2500000000 22421446744893 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5231599939/10000000000 : ℝ)^4305 ≤ (42738607718833/100000000000000 : ℝ)^3281 := by
    have hnat : (5231599939 : ℕ)^4305*100000000000000^3281 ≤ 42738607718833^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231599939 10000000000 42738607718833 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2039653973/10000000000 : ℝ), (1356696853/2500000000 : ℝ), (5231599939/10000000000 : ℝ)] ![(1552312347647/12500000000000 : ℝ), (22421446744893/50000000000000 : ℝ), (42738607718833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2039653973/10000000000 : ℝ)|^4305 ≤ (1552312347647/12500000000000 : ℝ)^3281
        have hw : |(-2039653973/10000000000 : ℝ)|=(2039653973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356696853/2500000000 : ℝ)|^4305 ≤ (22421446744893/50000000000000 : ℝ)^3281
        have hw : |(1356696853/2500000000 : ℝ)|=(1356696853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5231599939/10000000000 : ℝ)|^4305 ≤ (42738607718833/100000000000000 : ℝ)^3281
        have hw : |(5231599939/10000000000 : ℝ)|=(5231599939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s3_1 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676288829/5000000000 : ℝ)*x 0 + (-2139401751/10000000000 : ℝ)*x 1 + (326974993/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676288829/5000000000 : ℝ)^4305 ≤ (22020009130279/50000000000000 : ℝ)^3281 := by
    have hnat : (2676288829 : ℕ)^4305*50000000000000^3281 ≤ 22020009130279^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676288829 5000000000 22020009130279 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2139401751/10000000000 : ℝ)^4305 ≤ (3305343639139/25000000000000 : ℝ)^3281 := by
    have hnat : (2139401751 : ℕ)^4305*25000000000000^3281 ≤ 3305343639139^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139401751 10000000000 3305343639139 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326974993/625000000 : ℝ)^4305 ≤ (21369303586083/50000000000000 : ℝ)^3281 := by
    have hnat : (326974993 : ℕ)^4305*50000000000000^3281 ≤ 21369303586083^3281*625000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326974993 625000000 21369303586083 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676288829/5000000000 : ℝ), (-2139401751/10000000000 : ℝ), (326974993/625000000 : ℝ)] ![(22020009130279/50000000000000 : ℝ), (3305343639139/25000000000000 : ℝ), (21369303586083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676288829/5000000000 : ℝ)|^4305 ≤ (22020009130279/50000000000000 : ℝ)^3281
        have hw : |(2676288829/5000000000 : ℝ)|=(2676288829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2139401751/10000000000 : ℝ)|^4305 ≤ (3305343639139/25000000000000 : ℝ)^3281
        have hw : |(-2139401751/10000000000 : ℝ)|=(2139401751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326974993/625000000 : ℝ)|^4305 ≤ (21369303586083/50000000000000 : ℝ)^3281
        have hw : |(326974993/625000000 : ℝ)|=(326974993/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s3_2 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676288897/5000000000 : ℝ)*x 0 + (5231599699/10000000000 : ℝ)*x 1 + (-106970091/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676288897/5000000000 : ℝ)^4305 ≤ (1761600789151/4000000000000 : ℝ)^3281 := by
    have hnat : (2676288897 : ℕ)^4305*4000000000000^3281 ≤ 1761600789151^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676288897 5000000000 1761600789151 4000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231599699/10000000000 : ℝ)^4305 ≤ (21369302573141/50000000000000 : ℝ)^3281 := by
    have hnat : (5231599699 : ℕ)^4305*50000000000000^3281 ≤ 21369302573141^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231599699 10000000000 21369302573141 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106970091/500000000 : ℝ)^4305 ≤ (1652671889507/12500000000000 : ℝ)^3281 := by
    have hnat : (106970091 : ℕ)^4305*12500000000000^3281 ≤ 1652671889507^3281*500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106970091 500000000 1652671889507 12500000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676288897/5000000000 : ℝ), (5231599699/10000000000 : ℝ), (-106970091/500000000 : ℝ)] ![(1761600789151/4000000000000 : ℝ), (21369302573141/50000000000000 : ℝ), (1652671889507/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676288897/5000000000 : ℝ)|^4305 ≤ (1761600789151/4000000000000 : ℝ)^3281
        have hw : |(2676288897/5000000000 : ℝ)|=(2676288897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231599699/10000000000 : ℝ)|^4305 ≤ (21369302573141/50000000000000 : ℝ)^3281
        have hw : |(5231599699/10000000000 : ℝ)|=(5231599699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-106970091/500000000 : ℝ)|^4305 ≤ (1652671889507/12500000000000 : ℝ)^3281
        have hw : |(-106970091/500000000 : ℝ)|=(106970091/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s3_3 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081197271/2500000000 : ℝ)*x 0 + (4124657561/10000000000 : ℝ)*x 1 + (226697677/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081197271/2500000000 : ℝ)^4305 ≤ (1664637227827/5000000000000 : ℝ)^3281 := by
    have hnat : (1081197271 : ℕ)^4305*5000000000000^3281 ≤ 1664637227827^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081197271 2500000000 1664637227827 5000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4124657561/10000000000 : ℝ)^4305 ≤ (7821507780097/25000000000000 : ℝ)^3281 := by
    have hnat : (4124657561 : ℕ)^4305*25000000000000^3281 ≤ 7821507780097^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124657561 10000000000 7821507780097 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226697677/500000000 : ℝ)^4305 ≤ (17710612153687/50000000000000 : ℝ)^3281 := by
    have hnat : (226697677 : ℕ)^4305*50000000000000^3281 ≤ 17710612153687^3281*500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226697677 500000000 17710612153687 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081197271/2500000000 : ℝ), (4124657561/10000000000 : ℝ), (226697677/500000000 : ℝ)] ![(1664637227827/5000000000000 : ℝ), (7821507780097/25000000000000 : ℝ), (17710612153687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081197271/2500000000 : ℝ)|^4305 ≤ (1664637227827/5000000000000 : ℝ)^3281
        have hw : |(1081197271/2500000000 : ℝ)|=(1081197271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4124657561/10000000000 : ℝ)|^4305 ≤ (7821507780097/25000000000000 : ℝ)^3281
        have hw : |(4124657561/10000000000 : ℝ)|=(4124657561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(226697677/500000000 : ℝ)|^4305 ≤ (17710612153687/50000000000000 : ℝ)^3281
        have hw : |(226697677/500000000 : ℝ)|=(226697677/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s3_4 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-407934627/2000000000 : ℝ)*x 0 + (2616205923/5000000000 : ℝ)*x 1 + (217038823/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (407934627/2000000000 : ℝ)^4305 ≤ (6209325931037/50000000000000 : ℝ)^3281 := by
    have hnat : (407934627 : ℕ)^4305*50000000000000^3281 ≤ 6209325931037^3281*2000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407934627 2000000000 6209325931037 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2616205923/5000000000 : ℝ)^4305 ≤ (10686827682659/25000000000000 : ℝ)^3281 := by
    have hnat : (2616205923 : ℕ)^4305*25000000000000^3281 ≤ 10686827682659^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616205923 5000000000 10686827682659 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217038823/400000000 : ℝ)^4305 ≤ (8966807476193/20000000000000 : ℝ)^3281 := by
    have hnat : (217038823 : ℕ)^4305*20000000000000^3281 ≤ 8966807476193^3281*400000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217038823 400000000 8966807476193 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-407934627/2000000000 : ℝ), (2616205923/5000000000 : ℝ), (217038823/400000000 : ℝ)] ![(6209325931037/50000000000000 : ℝ), (10686827682659/25000000000000 : ℝ), (8966807476193/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-407934627/2000000000 : ℝ)|^4305 ≤ (6209325931037/50000000000000 : ℝ)^3281
        have hw : |(-407934627/2000000000 : ℝ)|=(407934627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2616205923/5000000000 : ℝ)|^4305 ≤ (10686827682659/25000000000000 : ℝ)^3281
        have hw : |(2616205923/5000000000 : ℝ)|=(2616205923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217038823/400000000 : ℝ)|^4305 ≤ (8966807476193/20000000000000 : ℝ)^3281
        have hw : |(217038823/400000000 : ℝ)|=(217038823/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s3_5 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060456667/2000000000 : ℝ)*x 0 + (-389006191/2000000000 : ℝ)*x 1 + (5425970571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060456667/2000000000 : ℝ)^4305 ≤ (43497852911931/100000000000000 : ℝ)^3281 := by
    have hnat : (1060456667 : ℕ)^4305*100000000000000^3281 ≤ 43497852911931^3281*2000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060456667 2000000000 43497852911931 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389006191/2000000000 : ℝ)^4305 ≤ (11668109745133/100000000000000 : ℝ)^3281 := by
    have hnat : (389006191 : ℕ)^4305*100000000000000^3281 ≤ 11668109745133^3281*2000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389006191 2000000000 11668109745133 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425970571/10000000000 : ℝ)^4305 ≤ (22417018668799/50000000000000 : ℝ)^3281 := by
    have hnat : (5425970571 : ℕ)^4305*50000000000000^3281 ≤ 22417018668799^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425970571 10000000000 22417018668799 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060456667/2000000000 : ℝ), (-389006191/2000000000 : ℝ), (5425970571/10000000000 : ℝ)] ![(43497852911931/100000000000000 : ℝ), (11668109745133/100000000000000 : ℝ), (22417018668799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060456667/2000000000 : ℝ)|^4305 ≤ (43497852911931/100000000000000 : ℝ)^3281
        have hw : |(1060456667/2000000000 : ℝ)|=(1060456667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-389006191/2000000000 : ℝ)|^4305 ≤ (11668109745133/100000000000000 : ℝ)^3281
        have hw : |(-389006191/2000000000 : ℝ)|=(389006191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425970571/10000000000 : ℝ)|^4305 ≤ (22417018668799/50000000000000 : ℝ)^3281
        have hw : |(5425970571/10000000000 : ℝ)|=(5425970571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s3_6 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302283099/10000000000 : ℝ)*x 0 + (5425970733/10000000000 : ℝ)*x 1 + (-1945031053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302283099/10000000000 : ℝ)^4305 ≤ (21748925185819/50000000000000 : ℝ)^3281 := by
    have hnat : (5302283099 : ℕ)^4305*50000000000000^3281 ≤ 21748925185819^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302283099 10000000000 21748925185819 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425970733/10000000000 : ℝ)^4305 ≤ (22417019546977/50000000000000 : ℝ)^3281 := by
    have hnat : (5425970733 : ℕ)^4305*50000000000000^3281 ≤ 22417019546977^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425970733 10000000000 22417019546977 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1945031053/10000000000 : ℝ)^4305 ≤ (11668110516511/100000000000000 : ℝ)^3281 := by
    have hnat : (1945031053 : ℕ)^4305*100000000000000^3281 ≤ 11668110516511^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945031053 10000000000 11668110516511 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302283099/10000000000 : ℝ), (5425970733/10000000000 : ℝ), (-1945031053/10000000000 : ℝ)] ![(21748925185819/50000000000000 : ℝ), (22417019546977/50000000000000 : ℝ), (11668110516511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302283099/10000000000 : ℝ)|^4305 ≤ (21748925185819/50000000000000 : ℝ)^3281
        have hw : |(5302283099/10000000000 : ℝ)|=(5302283099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425970733/10000000000 : ℝ)|^4305 ≤ (22417019546977/50000000000000 : ℝ)^3281
        have hw : |(5425970733/10000000000 : ℝ)|=(5425970733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1945031053/10000000000 : ℝ)|^4305 ≤ (11668110516511/100000000000000 : ℝ)^3281
        have hw : |(-1945031053/10000000000 : ℝ)|=(1945031053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s3_7 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2162414481/5000000000 : ℝ)*x 0 + (1133062713/2500000000 : ℝ)*x 1 + (412637059/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162414481/5000000000 : ℝ)^4305 ≤ (6658629470589/20000000000000 : ℝ)^3281 := by
    have hnat : (2162414481 : ℕ)^4305*20000000000000^3281 ≤ 6658629470589^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162414481 5000000000 6658629470589 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133062713/2500000000 : ℝ)^4305 ≤ (4425471448783/12500000000000 : ℝ)^3281 := by
    have hnat : (1133062713 : ℕ)^4305*12500000000000^3281 ≤ 4425471448783^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133062713 2500000000 4425471448783 12500000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (412637059/1000000000 : ℝ)^4305 ≤ (31303081040889/100000000000000 : ℝ)^3281 := by
    have hnat : (412637059 : ℕ)^4305*100000000000000^3281 ≤ 31303081040889^3281*1000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412637059 1000000000 31303081040889 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162414481/5000000000 : ℝ), (1133062713/2500000000 : ℝ), (412637059/1000000000 : ℝ)] ![(6658629470589/20000000000000 : ℝ), (4425471448783/12500000000000 : ℝ), (31303081040889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162414481/5000000000 : ℝ)|^4305 ≤ (6658629470589/20000000000000 : ℝ)^3281
        have hw : |(2162414481/5000000000 : ℝ)|=(2162414481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1133062713/2500000000 : ℝ)|^4305 ≤ (4425471448783/12500000000000 : ℝ)^3281
        have hw : |(1133062713/2500000000 : ℝ)|=(1133062713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(412637059/1000000000 : ℝ)|^4305 ≤ (31303081040889/100000000000000 : ℝ)^3281
        have hw : |(412637059/1000000000 : ℝ)|=(412637059/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1345_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4023/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9871/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2719/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15007/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4023/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9871/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4023/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9871/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4023/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9871/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4023/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9871/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4023/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9871/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4023/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9871/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9871/100000 : ℝ) ^ (269/64 : ℝ) ≤ (5931632234432941/100000000000000000000 : ℝ) := by
    have hpowers : (9871/100000 : ℝ)^269 ≤ (5931632234432941/100000000000000000000 : ℝ)^64 := by
      have hnat : (9871 : ℕ)^269*100000000000000000000^64 ≤ 5931632234432941^64*100000^269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9871 100000 5931632234432941 100000000000000000000 269 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9871/100000 : ℝ)) (X := (5931632234432941/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hpowhi : (4023/25000 : ℝ) ^ (269/64 : ℝ) ≤ (23134108123191771/50000000000000000000 : ℝ) := by
    have hpowers : (4023/25000 : ℝ)^269 ≤ (23134108123191771/50000000000000000000 : ℝ)^64 := by
      have hnat : (4023 : ℕ)^269*50000000000000000000^64 ≤ 23134108123191771^64*25000^269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4023 25000 23134108123191771 50000000000000000000 269 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4023/25000 : ℝ)) (X := (23134108123191771/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005931632234432941/50000000000000000000 : ℝ) ≤ (1000028223591353/1000000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (50005931632234432941/50000000000000000000 : ℝ)^64 ≤ (1000028223591353/1000000000000000 : ℝ)^269 := by
      have hnat : (50005931632234432941 : ℕ)^64*1000000000000000^269 ≤ 1000028223591353^269*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005931632234432941 50000000000000000000 1000028223591353 1000000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000028223591353/1000000000000000 : ℝ)) (X := (50005931632234432941/50000000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052199848480816483/100000000000000000000 : ℝ) ≤ (2500310420633271/2500000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (100052199848480816483/100000000000000000000 : ℝ)^64 ≤ (2500310420633271/2500000000000000 : ℝ)^269 := by
      have hnat : (100052199848480816483 : ℕ)^64*2500000000000000^269 ≤ 2500310420633271^269*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052199848480816483 100000000000000000000 2500310420633271 2500000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500310420633271/2500000000000000 : ℝ)) (X := (100052199848480816483/100000000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (25023134108123191771/25000000000000000000 : ℝ) ≤ (5001100564576319/5000000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (25023134108123191771/25000000000000000000 : ℝ)^64 ≤ (5001100564576319/5000000000000000 : ℝ)^269 := by
      have hnat : (25023134108123191771 : ℕ)^64*5000000000000000^269 ≤ 5001100564576319^269*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25023134108123191771 25000000000000000000 5001100564576319 5000000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001100564576319/5000000000000000 : ℝ)) (X := (25023134108123191771/25000000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5931632234432941/100000000000000000000 : ℝ) ≤ ((31096407197227417531/31105000000000000000 : ℝ)+2*(479723309777/311050000000000 : ℝ)*(9871/100000 : ℝ))^(269/64 : ℝ) := by
    rw [show (31096407197227417531/31105000000000000000 : ℝ)+2*(479723309777/311050000000000 : ℝ)*(9871/100000 : ℝ)=(1000028223591353/1000000000000000 : ℝ) by norm_num, show 1+2*(5931632234432941/100000000000000000000 : ℝ)=(50005931632234432941/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23134108123191771/50000000000000000000 : ℝ)+(5931632234432941/100000000000000000000 : ℝ) ≤ ((31096407197227417531/31105000000000000000 : ℝ)+(479723309777/311050000000000 : ℝ)*((4023/25000 : ℝ)+(9871/100000 : ℝ)))^(269/64 : ℝ) := by
    rw [show (31096407197227417531/31105000000000000000 : ℝ)+(479723309777/311050000000000 : ℝ)*((4023/25000 : ℝ)+(9871/100000 : ℝ))=(2500310420633271/2500000000000000 : ℝ) by norm_num, show 1+(23134108123191771/50000000000000000000 : ℝ)+(5931632234432941/100000000000000000000 : ℝ)=(100052199848480816483/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23134108123191771/50000000000000000000 : ℝ) ≤ ((31096407197227417531/31105000000000000000 : ℝ)+2*(479723309777/311050000000000 : ℝ)*(4023/25000 : ℝ))^(269/64 : ℝ) := by
    rw [show (31096407197227417531/31105000000000000000 : ℝ)+2*(479723309777/311050000000000 : ℝ)*(4023/25000 : ℝ)=(5001100564576319/5000000000000000 : ℝ) by norm_num, show 1+2*(23134108123191771/50000000000000000000 : ℝ)=(25023134108123191771/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (31096407197227417531/31105000000000000000 : ℝ)*(X 1 0+X 2 0)+(479723309777/311050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (9871/100000 : ℝ)) (hi := (4023/25000 : ℝ)) (c := (31096407197227417531/31105000000000000000 : ℝ)) (alpha := (479723309777/311050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (31096407197227417531/31105000000000000000 : ℝ)*(X 0 1+X 2 1)+(479723309777/311050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (9871/100000 : ℝ)) (hi := (4023/25000 : ℝ)) (c := (31096407197227417531/31105000000000000000 : ℝ)) (alpha := (479723309777/311050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (31096407197227417531/31105000000000000000 : ℝ)*(X 0 2+X 1 2)+(479723309777/311050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (9871/100000 : ℝ)) (hi := (4023/25000 : ℝ)) (c := (31096407197227417531/31105000000000000000 : ℝ)) (alpha := (479723309777/311050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2039653973/10000000000 : ℝ)*X 0 0+(1356696853/2500000000 : ℝ)*X 0 1+(5231599939/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676288829/5000000000 : ℝ)*X 1 0+(-2139401751/10000000000 : ℝ)*X 1 1+(326974993/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676288897/5000000000 : ℝ)*X 2 0+(5231599699/10000000000 : ℝ)*X 2 1+(-106970091/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1081197271/2500000000 : ℝ)*X 0 0+(4124657561/10000000000 : ℝ)*X 0 1+(226697677/500000000 : ℝ)*X 0 2+(1081197271/2500000000 : ℝ)*X 1 0+(4124657561/10000000000 : ℝ)*X 1 1+(226697677/500000000 : ℝ)*X 1 2+(1081197271/2500000000 : ℝ)*X 2 0+(4124657561/10000000000 : ℝ)*X 2 1+(226697677/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-407934627/2000000000 : ℝ)*X 0 0+(2616205923/5000000000 : ℝ)*X 0 1+(217038823/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060456667/2000000000 : ℝ)*X 1 0+(-389006191/2000000000 : ℝ)*X 1 1+(5425970571/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302283099/10000000000 : ℝ)*X 2 0+(5425970733/10000000000 : ℝ)*X 2 1+(-1945031053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2162414481/5000000000 : ℝ)*X 0 0+(1133062713/2500000000 : ℝ)*X 0 1+(412637059/1000000000 : ℝ)*X 0 2+(2162414481/5000000000 : ℝ)*X 1 0+(1133062713/2500000000 : ℝ)*X 1 1+(412637059/1000000000 : ℝ)*X 1 2+(2162414481/5000000000 : ℝ)*X 2 0+(1133062713/2500000000 : ℝ)*X 2 1+(412637059/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (67068865467729675101656593/9720312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (287027899/20000000000000 : ℝ)*(base19) + (165549619/12500000000000 : ℝ)*(base23) + (128953009/100000000000000 : ℝ)*(lower2) + (256822611/100000000000000 : ℝ)*(upper3) + (11645589/50000000000000 : ℝ)*(upper5) + (23645524271937/625000000000 : ℝ)*(major0) + (23645524271937/625000000000 : ℝ)*(major1) + (23645524271937/625000000000 : ℝ)*(major2) + (5123304383263113/100000000000000 : ℝ)*(sp0) + (1024664719676177/20000000000000 : ℝ)*(sp1) + (1280830927280857/25000000000000 : ℝ)*(sp2) + (2443228914677713/100000000000000 : ℝ)*(sp3) + (5162564317/25000000000000 : ℝ)*(sp4) + (2717765233/20000000000000 : ℝ)*(sp7) + (1221621251751939/50000000000000 : ℝ)*(f.failure) + (256166251676019/5000000000000 : ℝ)*(f.sum) + (22825710906183/6221000000000000000000000000 : ℝ)*base65 + (40117436450919039/9720312500000000000000000000000 : ℝ)*base68 + (13486493192643461/9720312500000000000000000000000 : ℝ)*base69 + (210392126588802547/19440625000000000000000000000000 : ℝ)*base71 + (6154839345081/3110500000000000000000000000 : ℝ)*base74 + (65704511048621297/19440625000000000000000000000000 : ℝ)*base75 + (290240790298358797/19440625000000000000000000000000 : ℝ)*base77 + (34383724828380961/9720312500000000000000000000000 : ℝ)*base79 + (10992449048737/3110500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (26721423/5000000000000000000000 : ℝ)*base90 + (26721423/5000000000000000000000 : ℝ)*base92 + (26721423/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8226154769727748428111533373/777625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (397084613/20000000000000 : ℝ)*(base19) + (75572619/4000000000000 : ℝ)*(base23) + (5043507/2500000000000 : ℝ)*(upper3) + (249571/312500000000 : ℝ)*(lower4) + (29878799/12500000000000 : ℝ)*(upper5) + (1907542022205487/50000000000000 : ℝ)*(major0) + (1907542022205487/50000000000000 : ℝ)*(major1) + (1907542022205487/50000000000000 : ℝ)*(major2) + (36236509861/100000000000000 : ℝ)*(sp1) + (34467673961/100000000000000 : ℝ)*(sp2) + (5166388707520649/100000000000000 : ℝ)*(sp4) + (5166350485587723/100000000000000 : ℝ)*(sp5) + (5166352350531213/100000000000000 : ℝ)*(sp6) + (1231889514341269/50000000000000 : ℝ)*(sp7) + (1231889514341269/50000000000000 : ℝ)*(f.failure) + (5166388707520649/100000000000000 : ℝ)*(f.sum) + (164871956315791/31105000000000000000000000000 : ℝ)*base65 + (15517466953589407403/1555250000000000000000000000000000 : ℝ)*base68 + (12725840117705657403/1555250000000000000000000000000000 : ℝ)*base70 + (9989512589101657403/1555250000000000000000000000000000 : ℝ)*base72 + (879393003061/486015625000000000000000000 : ℝ)*base74 + (16266354652192157403/1555250000000000000000000000000000 : ℝ)*base76 + (12499234099236157403/1555250000000000000000000000000000 : ℝ)*base78 + (8085734089062907403/1555250000000000000000000000000000 : ℝ)*base80 + (107794167922059/31105000000000000000000000000 : ℝ)*base82 + (29263767/5000000000000000000000 : ℝ)*base89 + (29263767/5000000000000000000000 : ℝ)*base91 + (29263767/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1345_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4023/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9871/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2719/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15007/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1345_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1345_s4_0 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-127568009/625000000 : ℝ)*x 0 + (541506137/1000000000 : ℝ)*x 1 + (5242384341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127568009/625000000 : ℝ)^4305 ≤ (12429957290123/100000000000000 : ℝ)^3281 := by
    have hnat : (127568009 : ℕ)^4305*100000000000000^3281 ≤ 12429957290123^3281*625000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127568009 625000000 12429957290123 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541506137/1000000000 : ℝ)^4305 ≤ (44715800190703/100000000000000 : ℝ)^3281 := by
    have hnat : (541506137 : ℕ)^4305*100000000000000^3281 ≤ 44715800190703^3281*1000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541506137 1000000000 44715800190703 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242384341/10000000000 : ℝ)^4305 ≤ (42854242492227/100000000000000 : ℝ)^3281 := by
    have hnat : (5242384341 : ℕ)^4305*100000000000000^3281 ≤ 42854242492227^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242384341 10000000000 42854242492227 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-127568009/625000000 : ℝ), (541506137/1000000000 : ℝ), (5242384341/10000000000 : ℝ)] ![(12429957290123/100000000000000 : ℝ), (44715800190703/100000000000000 : ℝ), (42854242492227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-127568009/625000000 : ℝ)|^4305 ≤ (12429957290123/100000000000000 : ℝ)^3281
        have hw : |(-127568009/625000000 : ℝ)|=(127568009/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541506137/1000000000 : ℝ)|^4305 ≤ (44715800190703/100000000000000 : ℝ)^3281
        have hw : |(541506137/1000000000 : ℝ)|=(541506137/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242384341/10000000000 : ℝ)|^4305 ≤ (42854242492227/100000000000000 : ℝ)^3281
        have hw : |(5242384341/10000000000 : ℝ)|=(5242384341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s4_1 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668698539/1250000000 : ℝ)*x 0 + (-266139151/1250000000 : ℝ)*x 1 + (1310596039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668698539/1250000000 : ℝ)^4305 ≤ (22003874471987/50000000000000 : ℝ)^3281 := by
    have hnat : (668698539 : ℕ)^4305*50000000000000^3281 ≤ 22003874471987^3281*1250000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668698539 1250000000 22003874471987 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (266139151/1250000000 : ℝ)^4305 ≤ (6569005266981/50000000000000 : ℝ)^3281 := by
    have hnat : (266139151 : ℕ)^4305*50000000000000^3281 ≤ 6569005266981^3281*1250000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266139151 1250000000 6569005266981 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310596039/2500000000 : ℝ)^4305 ≤ (5356780063493/12500000000000 : ℝ)^3281 := by
    have hnat : (1310596039 : ℕ)^4305*12500000000000^3281 ≤ 5356780063493^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310596039 2500000000 5356780063493 12500000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668698539/1250000000 : ℝ), (-266139151/1250000000 : ℝ), (1310596039/2500000000 : ℝ)] ![(22003874471987/50000000000000 : ℝ), (6569005266981/50000000000000 : ℝ), (5356780063493/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668698539/1250000000 : ℝ)|^4305 ≤ (22003874471987/50000000000000 : ℝ)^3281
        have hw : |(668698539/1250000000 : ℝ)|=(668698539/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-266139151/1250000000 : ℝ)|^4305 ≤ (6569005266981/50000000000000 : ℝ)^3281
        have hw : |(-266139151/1250000000 : ℝ)|=(266139151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310596039/2500000000 : ℝ)|^4305 ≤ (5356780063493/12500000000000 : ℝ)^3281
        have hw : |(1310596039/2500000000 : ℝ)|=(1310596039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s4_2 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349588841/10000000000 : ℝ)*x 0 + (1048476777/2000000000 : ℝ)*x 1 + (-1064556431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349588841/10000000000 : ℝ)^4305 ≤ (5500969331739/12500000000000 : ℝ)^3281 := by
    have hnat : (5349588841 : ℕ)^4305*12500000000000^3281 ≤ 5500969331739^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349588841 10000000000 5500969331739 12500000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048476777/2000000000 : ℝ)^4305 ≤ (21427118800619/50000000000000 : ℝ)^3281 := by
    have hnat : (1048476777 : ℕ)^4305*50000000000000^3281 ≤ 21427118800619^3281*2000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048476777 2000000000 21427118800619 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1064556431/5000000000 : ℝ)^4305 ≤ (13138007732571/100000000000000 : ℝ)^3281 := by
    have hnat : (1064556431 : ℕ)^4305*100000000000000^3281 ≤ 13138007732571^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064556431 5000000000 13138007732571 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349588841/10000000000 : ℝ), (1048476777/2000000000 : ℝ), (-1064556431/5000000000 : ℝ)] ![(5500969331739/12500000000000 : ℝ), (21427118800619/50000000000000 : ℝ), (13138007732571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349588841/10000000000 : ℝ)|^4305 ≤ (5500969331739/12500000000000 : ℝ)^3281
        have hw : |(5349588841/10000000000 : ℝ)|=(5349588841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048476777/2000000000 : ℝ)|^4305 ≤ (21427118800619/50000000000000 : ℝ)^3281
        have hw : |(1048476777/2000000000 : ℝ)|=(1048476777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1064556431/5000000000 : ℝ)|^4305 ≤ (13138007732571/100000000000000 : ℝ)^3281
        have hw : |(-1064556431/5000000000 : ℝ)|=(1064556431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s4_3 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (270353893/625000000 : ℝ)*x 0 + (4148150481/10000000000 : ℝ)*x 1 + (451024411/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270353893/625000000 : ℝ)^4305 ≤ (8325391202123/25000000000000 : ℝ)^3281 := by
    have hnat : (270353893 : ℕ)^4305*25000000000000^3281 ≤ 8325391202123^3281*625000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270353893 625000000 8325391202123 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4148150481/10000000000 : ℝ)^4305 ≤ (1970003156623/6250000000000 : ℝ)^3281 := by
    have hnat : (4148150481 : ℕ)^4305*6250000000000^3281 ≤ 1970003156623^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148150481 10000000000 1970003156623 6250000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451024411/1000000000 : ℝ)^4305 ≤ (35178384672263/100000000000000 : ℝ)^3281 := by
    have hnat : (451024411 : ℕ)^4305*100000000000000^3281 ≤ 35178384672263^3281*1000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451024411 1000000000 35178384672263 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270353893/625000000 : ℝ), (4148150481/10000000000 : ℝ), (451024411/1000000000 : ℝ)] ![(8325391202123/25000000000000 : ℝ), (1970003156623/6250000000000 : ℝ), (35178384672263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270353893/625000000 : ℝ)|^4305 ≤ (8325391202123/25000000000000 : ℝ)^3281
        have hw : |(270353893/625000000 : ℝ)|=(270353893/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4148150481/10000000000 : ℝ)|^4305 ≤ (1970003156623/6250000000000 : ℝ)^3281
        have hw : |(4148150481/10000000000 : ℝ)|=(4148150481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(451024411/1000000000 : ℝ)|^4305 ≤ (35178384672263/100000000000000 : ℝ)^3281
        have hw : |(451024411/1000000000 : ℝ)|=(451024411/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s4_4 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2041101743/10000000000 : ℝ)*x 0 + (20480547/39062500 : ℝ)*x 1 + (216576881/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2041101743/10000000000 : ℝ)^4305 ≤ (12430065953257/100000000000000 : ℝ)^3281 := by
    have hnat : (2041101743 : ℕ)^4305*100000000000000^3281 ≤ 12430065953257^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041101743 10000000000 12430065953257 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20480547/39062500 : ℝ)^4305 ≤ (21430530475123/50000000000000 : ℝ)^3281 := by
    have hnat : (20480547 : ℕ)^4305*50000000000000^3281 ≤ 21430530475123^3281*39062500^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20480547 39062500 21430530475123 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216576881/400000000 : ℝ)^4305 ≤ (11177218271227/25000000000000 : ℝ)^3281 := by
    have hnat : (216576881 : ℕ)^4305*25000000000000^3281 ≤ 11177218271227^3281*400000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216576881 400000000 11177218271227 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2041101743/10000000000 : ℝ), (20480547/39062500 : ℝ), (216576881/400000000 : ℝ)] ![(12430065953257/100000000000000 : ℝ), (21430530475123/50000000000000 : ℝ), (11177218271227/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2041101743/10000000000 : ℝ)|^4305 ≤ (12430065953257/100000000000000 : ℝ)^3281
        have hw : |(-2041101743/10000000000 : ℝ)|=(2041101743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20480547/39062500 : ℝ)|^4305 ≤ (21430530475123/50000000000000 : ℝ)^3281
        have hw : |(20480547/39062500 : ℝ)|=(20480547/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216576881/400000000 : ℝ)|^4305 ≤ (11177218271227/25000000000000 : ℝ)^3281
        have hw : |(216576881/400000000 : ℝ)|=(216576881/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s4_5 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305095239/10000000000 : ℝ)*x 0 + (-489268889/2500000000 : ℝ)*x 1 + (5414421803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305095239/10000000000 : ℝ)^4305 ≤ (1360253831889/3125000000000 : ℝ)^3281 := by
    have hnat : (5305095239 : ℕ)^4305*3125000000000^3281 ≤ 1360253831889^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305095239 10000000000 1360253831889 3125000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (489268889/2500000000 : ℝ)^4305 ≤ (5881503342753/50000000000000 : ℝ)^3281 := by
    have hnat : (489268889 : ℕ)^4305*50000000000000^3281 ≤ 5881503342753^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489268889 2500000000 5881503342753 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414421803/10000000000 : ℝ)^4305 ≤ (44708870679651/100000000000000 : ℝ)^3281 := by
    have hnat : (5414421803 : ℕ)^4305*100000000000000^3281 ≤ 44708870679651^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414421803 10000000000 44708870679651 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305095239/10000000000 : ℝ), (-489268889/2500000000 : ℝ), (5414421803/10000000000 : ℝ)] ![(1360253831889/3125000000000 : ℝ), (5881503342753/50000000000000 : ℝ), (44708870679651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305095239/10000000000 : ℝ)|^4305 ≤ (1360253831889/3125000000000 : ℝ)^3281
        have hw : |(5305095239/10000000000 : ℝ)|=(5305095239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-489268889/2500000000 : ℝ)|^4305 ≤ (5881503342753/50000000000000 : ℝ)^3281
        have hw : |(-489268889/2500000000 : ℝ)|=(489268889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414421803/10000000000 : ℝ)|^4305 ≤ (44708870679651/100000000000000 : ℝ)^3281
        have hw : |(5414421803/10000000000 : ℝ)|=(5414421803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s4_6 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305095073/10000000000 : ℝ)*x 0 + (42300171/78125000 : ℝ)*x 1 + (-978537833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305095073/10000000000 : ℝ)^4305 ≤ (5441015104167/12500000000000 : ℝ)^3281 := by
    have hnat : (5305095073 : ℕ)^4305*12500000000000^3281 ≤ 5441015104167^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305095073 10000000000 5441015104167 12500000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42300171/78125000 : ℝ)^4305 ≤ (22354435800291/50000000000000 : ℝ)^3281 := by
    have hnat : (42300171 : ℕ)^4305*50000000000000^3281 ≤ 22354435800291^3281*78125000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42300171 78125000 22354435800291 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (978537833/5000000000 : ℝ)^4305 ≤ (735187972063/6250000000000 : ℝ)^3281 := by
    have hnat : (978537833 : ℕ)^4305*6250000000000^3281 ≤ 735187972063^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978537833 5000000000 735187972063 6250000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305095073/10000000000 : ℝ), (42300171/78125000 : ℝ), (-978537833/5000000000 : ℝ)] ![(5441015104167/12500000000000 : ℝ), (22354435800291/50000000000000 : ℝ), (735187972063/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305095073/10000000000 : ℝ)|^4305 ≤ (5441015104167/12500000000000 : ℝ)^3281
        have hw : |(5305095073/10000000000 : ℝ)|=(5305095073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42300171/78125000 : ℝ)|^4305 ≤ (22354435800291/50000000000000 : ℝ)^3281
        have hw : |(42300171/78125000 : ℝ)|=(42300171/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-978537833/5000000000 : ℝ)|^4305 ≤ (735187972063/6250000000000 : ℝ)^3281
        have hw : |(-978537833/5000000000 : ℝ)|=(978537833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s4_7 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2162844777/5000000000 : ℝ)*x 0 + (4508910469/10000000000 : ℝ)*x 1 + (2074745829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162844777/5000000000 : ℝ)^4305 ≤ (16650920115939/50000000000000 : ℝ)^3281 := by
    have hnat : (2162844777 : ℕ)^4305*50000000000000^3281 ≤ 16650920115939^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162844777 5000000000 16650920115939 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508910469/10000000000 : ℝ)^4305 ≤ (7032947380621/20000000000000 : ℝ)^3281 := by
    have hnat : (4508910469 : ℕ)^4305*20000000000000^3281 ≤ 7032947380621^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508910469 10000000000 7032947380621 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2074745829/5000000000 : ℝ)^4305 ≤ (3941677855453/12500000000000 : ℝ)^3281 := by
    have hnat : (2074745829 : ℕ)^4305*12500000000000^3281 ≤ 3941677855453^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074745829 5000000000 3941677855453 12500000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162844777/5000000000 : ℝ), (4508910469/10000000000 : ℝ), (2074745829/5000000000 : ℝ)] ![(16650920115939/50000000000000 : ℝ), (7032947380621/20000000000000 : ℝ), (3941677855453/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162844777/5000000000 : ℝ)|^4305 ≤ (16650920115939/50000000000000 : ℝ)^3281
        have hw : |(2162844777/5000000000 : ℝ)|=(2162844777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508910469/10000000000 : ℝ)|^4305 ≤ (7032947380621/20000000000000 : ℝ)^3281
        have hw : |(4508910469/10000000000 : ℝ)|=(4508910469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2074745829/5000000000 : ℝ)|^4305 ≤ (3941677855453/12500000000000 : ℝ)^3281
        have hw : |(2074745829/5000000000 : ℝ)|=(2074745829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1345_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2719/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5553/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7381/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15007/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2719/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15007/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2719/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15007/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2719/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15007/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2719/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15007/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2719/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15007/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2719/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2719/25000 : ℝ) ^ (269/64 : ℝ) ≤ (1783157059806551/20000000000000000000 : ℝ) := by
    have hpowers : (2719/25000 : ℝ)^269 ≤ (1783157059806551/20000000000000000000 : ℝ)^64 := by
      have hnat : (2719 : ℕ)^269*20000000000000000000^64 ≤ 1783157059806551^64*25000^269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2719 25000 1783157059806551 20000000000000000000 269 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2719/25000 : ℝ)) (X := (1783157059806551/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hpowhi : (15007/100000 : ℝ) ^ (269/64 : ℝ) ≤ (1380130699449741/4000000000000000000 : ℝ) := by
    have hpowers : (15007/100000 : ℝ)^269 ≤ (1380130699449741/4000000000000000000 : ℝ)^64 := by
      have hnat : (15007 : ℕ)^269*4000000000000000000^64 ≤ 1380130699449741^64*100000^269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15007 100000 1380130699449741 4000000000000000000 269 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15007/100000 : ℝ)) (X := (1380130699449741/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001783157059806551/10000000000000000000 : ℝ) ≤ (10000424216723239/10000000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (10001783157059806551/10000000000000000000 : ℝ)^64 ≤ (10000424216723239/10000000000000000 : ℝ)^269 := by
      have hnat : (10001783157059806551 : ℕ)^64*10000000000000000^269 ≤ 10000424216723239^269*10000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001783157059806551 10000000000000000000 10000424216723239 10000000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000424216723239/10000000000000000 : ℝ)) (X := (10001783157059806551/10000000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501085476319631907/2500000000000000000 : ℝ) ≤ (2500258211873189/2500000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (2501085476319631907/2500000000000000000 : ℝ)^64 ≤ (2500258211873189/2500000000000000 : ℝ)^269 := by
      have hnat : (2501085476319631907 : ℕ)^64*2500000000000000^269 ≤ 2500258211873189^269*2500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501085476319631907 2500000000000000000 2500258211873189 2500000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500258211873189/2500000000000000 : ℝ)) (X := (2501085476319631907/2500000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001380130699449741/2000000000000000000 : ℝ) ≤ (10001641478262273/10000000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (2001380130699449741/2000000000000000000 : ℝ)^64 ≤ (10001641478262273/10000000000000000 : ℝ)^269 := by
      have hnat : (2001380130699449741 : ℕ)^64*10000000000000000^269 ≤ 10001641478262273^269*2000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001380130699449741 2000000000000000000 10001641478262273 10000000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001641478262273/10000000000000000 : ℝ)) (X := (2001380130699449741/2000000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1783157059806551/20000000000000000000 : ℝ) ≤ ((1651940540111406661/1652400000000000000 : ℝ)+2*(608630769517/413100000000000 : ℝ)*(2719/25000 : ℝ))^(269/64 : ℝ) := by
    rw [show (1651940540111406661/1652400000000000000 : ℝ)+2*(608630769517/413100000000000 : ℝ)*(2719/25000 : ℝ)=(10000424216723239/10000000000000000 : ℝ) by norm_num, show 1+2*(1783157059806551/20000000000000000000 : ℝ)=(10001783157059806551/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1380130699449741/4000000000000000000 : ℝ)+(1783157059806551/20000000000000000000 : ℝ) ≤ ((1651940540111406661/1652400000000000000 : ℝ)+(608630769517/413100000000000 : ℝ)*((15007/100000 : ℝ)+(2719/25000 : ℝ)))^(269/64 : ℝ) := by
    rw [show (1651940540111406661/1652400000000000000 : ℝ)+(608630769517/413100000000000 : ℝ)*((15007/100000 : ℝ)+(2719/25000 : ℝ))=(2500258211873189/2500000000000000 : ℝ) by norm_num, show 1+(1380130699449741/4000000000000000000 : ℝ)+(1783157059806551/20000000000000000000 : ℝ)=(2501085476319631907/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1380130699449741/4000000000000000000 : ℝ) ≤ ((1651940540111406661/1652400000000000000 : ℝ)+2*(608630769517/413100000000000 : ℝ)*(15007/100000 : ℝ))^(269/64 : ℝ) := by
    rw [show (1651940540111406661/1652400000000000000 : ℝ)+2*(608630769517/413100000000000 : ℝ)*(15007/100000 : ℝ)=(10001641478262273/10000000000000000 : ℝ) by norm_num, show 1+2*(1380130699449741/4000000000000000000 : ℝ)=(2001380130699449741/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1651940540111406661/1652400000000000000 : ℝ)*(X 1 0+X 2 0)+(608630769517/413100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (2719/25000 : ℝ)) (hi := (15007/100000 : ℝ)) (c := (1651940540111406661/1652400000000000000 : ℝ)) (alpha := (608630769517/413100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1651940540111406661/1652400000000000000 : ℝ)*(X 0 1+X 2 1)+(608630769517/413100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (2719/25000 : ℝ)) (hi := (15007/100000 : ℝ)) (c := (1651940540111406661/1652400000000000000 : ℝ)) (alpha := (608630769517/413100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1651940540111406661/1652400000000000000 : ℝ)*(X 0 2+X 1 2)+(608630769517/413100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (2719/25000 : ℝ)) (hi := (15007/100000 : ℝ)) (c := (1651940540111406661/1652400000000000000 : ℝ)) (alpha := (608630769517/413100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-127568009/625000000 : ℝ)*X 0 0+(541506137/1000000000 : ℝ)*X 0 1+(5242384341/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668698539/1250000000 : ℝ)*X 1 0+(-266139151/1250000000 : ℝ)*X 1 1+(1310596039/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349588841/10000000000 : ℝ)*X 2 0+(1048476777/2000000000 : ℝ)*X 2 1+(-1064556431/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((270353893/625000000 : ℝ)*X 0 0+(4148150481/10000000000 : ℝ)*X 0 1+(451024411/1000000000 : ℝ)*X 0 2+(270353893/625000000 : ℝ)*X 1 0+(4148150481/10000000000 : ℝ)*X 1 1+(451024411/1000000000 : ℝ)*X 1 2+(270353893/625000000 : ℝ)*X 2 0+(4148150481/10000000000 : ℝ)*X 2 1+(451024411/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2041101743/10000000000 : ℝ)*X 0 0+(20480547/39062500 : ℝ)*X 0 1+(216576881/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305095239/10000000000 : ℝ)*X 1 0+(-489268889/2500000000 : ℝ)*X 1 1+(5414421803/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305095073/10000000000 : ℝ)*X 2 0+(42300171/78125000 : ℝ)*X 2 1+(-978537833/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2162844777/5000000000 : ℝ)*X 0 0+(4508910469/10000000000 : ℝ)*X 0 1+(2074745829/5000000000 : ℝ)*X 0 2+(2162844777/5000000000 : ℝ)*X 1 0+(4508910469/10000000000 : ℝ)*X 1 1+(2074745829/5000000000 : ℝ)*X 1 2+(2162844777/5000000000 : ℝ)*X 2 0+(4508910469/10000000000 : ℝ)*X 2 1+(2074745829/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39023782113824853081388073/4590000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (468804231/20000000000000 : ℝ)*(base19) + (210466137/10000000000000 : ℝ)*(base23) + (54300527/12500000000000 : ℝ)*(lower2) + (24257819/12500000000000 : ℝ)*(upper3) + (53403861/50000000000000 : ℝ)*(upper5) + (2138251239849921/50000000000000 : ℝ)*(major0) + (2138251239849921/50000000000000 : ℝ)*(major1) + (2138251239849921/50000000000000 : ℝ)*(major2) + (579119457869331/10000000000000 : ℝ)*(sp0) + (5791239549578513/100000000000000 : ℝ)*(sp1) + (5791239788938299/100000000000000 : ℝ)*(sp2) + (86304260777113/3125000000000 : ℝ)*(sp3) + (47314906359/100000000000000 : ℝ)*(sp4) + (13218767639/50000000000000 : ℝ)*(sp7) + (1380881391201447/50000000000000 : ℝ)*(f.failure) + (1447810473399917/25000000000000 : ℝ)*(f.sum) + (47412893174383/6885000000000000000000000000 : ℝ)*base65 + (102595585998856073/27540000000000000000000000000000 : ℝ)*base68 + (53278018608523927/27540000000000000000000000000000 : ℝ)*base69 + (300911554241743927/27540000000000000000000000000000 : ℝ)*base71 + (1867475614931/860625000000000000000000000 : ℝ)*base73 + (13024884202303927/27540000000000000000000000000000 : ℝ)*base75 + (248674194403123927/27540000000000000000000000000000 : ℝ)*base77 + (87098646978436073/27540000000000000000000000000000 : ℝ)*base80 + (3134747960557/1721250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (55018179/5000000000000000000000 : ℝ)*base90 + (55018179/5000000000000000000000 : ℝ)*base92 + (55018179/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46230595752371786409906469/4590000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (947606721/50000000000000 : ℝ)*(base19) + (936612531/50000000000000 : ℝ)*(base23) + (181225329/100000000000000 : ℝ)*(upper3) + (100023671/100000000000000 : ℝ)*(lower4) + (269385371/100000000000000 : ℝ)*(upper5) + (2154126113847987/50000000000000 : ℝ)*(major0) + (2154126113847987/50000000000000 : ℝ)*(major1) + (2154126113847987/50000000000000 : ℝ)*(major2) + (1014166727/3125000000000 : ℝ)*(sp1) + (7279359617/25000000000000 : ℝ)*(sp2) + (2917118684350257/50000000000000 : ℝ)*(sp4) + (5834203020151809/100000000000000 : ℝ)*(sp5) + (5834206378036983/100000000000000 : ℝ)*(sp6) + (11129067003829/400000000000 : ℝ)*(sp7) + (11129067003829/400000000000 : ℝ)*(f.failure) + (2917118684350257/50000000000000 : ℝ)*(f.sum) + (13866749510239/1721250000000000000000000000 : ℝ)*base65 + (42307432815467531/27540000000000000000000000000000 : ℝ)*base68 + (195515059531547531/27540000000000000000000000000000 : ℝ)*base70 + (7708697303807531/27540000000000000000000000000000 : ℝ)*base72 + (10073748040399/1721250000000000000000000000 : ℝ)*base73 + (794200178377487531/27540000000000000000000000000000 : ℝ)*base76 + (153481583481072469/27540000000000000000000000000000 : ℝ)*base77 + (353159376169092469/27540000000000000000000000000000 : ℝ)*base79 + (9830902261969/1721250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (38153/40000000000000000000 : ℝ)*base90 + (38153/40000000000000000000 : ℝ)*base92 + (38153/40000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1345_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2719/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5553/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1345_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1345_s5_0 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2041335599/10000000000 : ℝ)*x 0 + (1082586771/2000000000 : ℝ)*x 1 + (5244348887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2041335599/10000000000 : ℝ)^4305 ≤ (12431934620559/100000000000000 : ℝ)^3281 := by
    have hnat : (2041335599 : ℕ)^4305*100000000000000^3281 ≤ 12431934620559^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041335599 10000000000 12431934620559 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082586771/2000000000 : ℝ)^4305 ≤ (44692750210847/100000000000000 : ℝ)^3281 := by
    have hnat : (1082586771 : ℕ)^4305*100000000000000^3281 ≤ 44692750210847^3281*2000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082586771 2000000000 44692750210847 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244348887/10000000000 : ℝ)^4305 ≤ (42875315158377/100000000000000 : ℝ)^3281 := by
    have hnat : (5244348887 : ℕ)^4305*100000000000000^3281 ≤ 42875315158377^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244348887 10000000000 42875315158377 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2041335599/10000000000 : ℝ), (1082586771/2000000000 : ℝ), (5244348887/10000000000 : ℝ)] ![(12431934620559/100000000000000 : ℝ), (44692750210847/100000000000000 : ℝ), (42875315158377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2041335599/10000000000 : ℝ)|^4305 ≤ (12431934620559/100000000000000 : ℝ)^3281
        have hw : |(-2041335599/10000000000 : ℝ)|=(2041335599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082586771/2000000000 : ℝ)|^4305 ≤ (44692750210847/100000000000000 : ℝ)^3281
        have hw : |(1082586771/2000000000 : ℝ)|=(1082586771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244348887/10000000000 : ℝ)|^4305 ≤ (42875315158377/100000000000000 : ℝ)^3281
        have hw : |(5244348887/10000000000 : ℝ)|=(5244348887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s5_1 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674522089/5000000000 : ℝ)*x 0 + (-1063617689/5000000000 : ℝ)*x 1 + (5244348917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674522089/5000000000 : ℝ)^4305 ≤ (880037514907/2000000000000 : ℝ)^3281 := by
    have hnat : (2674522089 : ℕ)^4305*2000000000000^3281 ≤ 880037514907^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674522089 5000000000 880037514907 2000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1063617689/5000000000 : ℝ)^4305 ≤ (6561404380173/50000000000000 : ℝ)^3281 := by
    have hnat : (1063617689 : ℕ)^4305*50000000000000^3281 ≤ 6561404380173^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063617689 5000000000 6561404380173 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244348917/10000000000 : ℝ)^4305 ≤ (4287531548019/10000000000000 : ℝ)^3281 := by
    have hnat : (5244348917 : ℕ)^4305*10000000000000^3281 ≤ 4287531548019^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244348917 10000000000 4287531548019 10000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674522089/5000000000 : ℝ), (-1063617689/5000000000 : ℝ), (5244348917/10000000000 : ℝ)] ![(880037514907/2000000000000 : ℝ), (6561404380173/50000000000000 : ℝ), (4287531548019/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674522089/5000000000 : ℝ)|^4305 ≤ (880037514907/2000000000000 : ℝ)^3281
        have hw : |(2674522089/5000000000 : ℝ)|=(2674522089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1063617689/5000000000 : ℝ)|^4305 ≤ (6561404380173/50000000000000 : ℝ)^3281
        have hw : |(-1063617689/5000000000 : ℝ)|=(1063617689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244348917/10000000000 : ℝ)|^4305 ≤ (4287531548019/10000000000000 : ℝ)^3281
        have hw : |(5244348917/10000000000 : ℝ)|=(5244348917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s5_2 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668630527/1250000000 : ℝ)*x 0 + (327771807/625000000 : ℝ)*x 1 + (-1063617667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668630527/1250000000 : ℝ)^4305 ≤ (44001876155503/100000000000000 : ℝ)^3281 := by
    have hnat : (668630527 : ℕ)^4305*100000000000000^3281 ≤ 44001876155503^3281*1250000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668630527 1250000000 44001876155503 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327771807/625000000 : ℝ)^4305 ≤ (8575063085311/20000000000000 : ℝ)^3281 := by
    have hnat : (327771807 : ℕ)^4305*20000000000000^3281 ≤ 8575063085311^3281*625000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327771807 625000000 8575063085311 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063617667/5000000000 : ℝ)^4305 ≤ (13122808404197/100000000000000 : ℝ)^3281 := by
    have hnat : (1063617667 : ℕ)^4305*100000000000000^3281 ≤ 13122808404197^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063617667 5000000000 13122808404197 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668630527/1250000000 : ℝ), (327771807/625000000 : ℝ), (-1063617667/5000000000 : ℝ)] ![(44001876155503/100000000000000 : ℝ), (8575063085311/20000000000000 : ℝ), (13122808404197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668630527/1250000000 : ℝ)|^4305 ≤ (44001876155503/100000000000000 : ℝ)^3281
        have hw : |(668630527/1250000000 : ℝ)|=(668630527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327771807/625000000 : ℝ)|^4305 ≤ (8575063085311/20000000000000 : ℝ)^3281
        have hw : |(327771807/625000000 : ℝ)|=(327771807/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1063617667/5000000000 : ℝ)|^4305 ≤ (13122808404197/100000000000000 : ℝ)^3281
        have hw : |(-1063617667/5000000000 : ℝ)|=(1063617667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s5_3 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4325808953/10000000000 : ℝ)*x 0 + (4152423331/10000000000 : ℝ)*x 1 + (2252967671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325808953/10000000000 : ℝ)^4305 ≤ (33303046329249/100000000000000 : ℝ)^3281 := by
    have hnat : (4325808953 : ℕ)^4305*100000000000000^3281 ≤ 33303046329249^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325808953 10000000000 33303046329249 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4152423331/10000000000 : ℝ)^4305 ≤ (6312531615097/20000000000000 : ℝ)^3281 := by
    have hnat : (4152423331 : ℕ)^4305*20000000000000^3281 ≤ 6312531615097^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152423331 10000000000 6312531615097 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252967671/5000000000 : ℝ)^4305 ≤ (35134295583957/100000000000000 : ℝ)^3281 := by
    have hnat : (2252967671 : ℕ)^4305*100000000000000^3281 ≤ 35134295583957^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252967671 5000000000 35134295583957 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325808953/10000000000 : ℝ), (4152423331/10000000000 : ℝ), (2252967671/5000000000 : ℝ)] ![(33303046329249/100000000000000 : ℝ), (6312531615097/20000000000000 : ℝ), (35134295583957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325808953/10000000000 : ℝ)|^4305 ≤ (33303046329249/100000000000000 : ℝ)^3281
        have hw : |(4325808953/10000000000 : ℝ)|=(4325808953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4152423331/10000000000 : ℝ)|^4305 ≤ (6312531615097/20000000000000 : ℝ)^3281
        have hw : |(4152423331/10000000000 : ℝ)|=(4152423331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2252967671/5000000000 : ℝ)|^4305 ≤ (35134295583957/100000000000000 : ℝ)^3281
        have hw : |(2252967671/5000000000 : ℝ)|=(2252967671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s5_4 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2041347879/10000000000 : ℝ)*x 0 + (655619403/1250000000 : ℝ)*x 1 + (1353081099/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2041347879/10000000000 : ℝ)^4305 ≤ (2486406549579/20000000000000 : ℝ)^3281 := by
    have hnat : (2041347879 : ℕ)^4305*20000000000000^3281 ≤ 2486406549579^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041347879 10000000000 2486406549579 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655619403/1250000000 : ℝ)^4305 ≤ (10720454879633/25000000000000 : ℝ)^3281 := by
    have hnat : (655619403 : ℕ)^4305*25000000000000^3281 ≤ 10720454879633^3281*1250000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655619403 1250000000 10720454879633 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353081099/2500000000 : ℝ)^4305 ≤ (5585768464351/12500000000000 : ℝ)^3281 := by
    have hnat : (1353081099 : ℕ)^4305*12500000000000^3281 ≤ 5585768464351^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353081099 2500000000 5585768464351 12500000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2041347879/10000000000 : ℝ), (655619403/1250000000 : ℝ), (1353081099/2500000000 : ℝ)] ![(2486406549579/20000000000000 : ℝ), (10720454879633/25000000000000 : ℝ), (5585768464351/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2041347879/10000000000 : ℝ)|^4305 ≤ (2486406549579/20000000000000 : ℝ)^3281
        have hw : |(-2041347879/10000000000 : ℝ)|=(2041347879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655619403/1250000000 : ℝ)|^4305 ≤ (10720454879633/25000000000000 : ℝ)^3281
        have hw : |(655619403/1250000000 : ℝ)|=(655619403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353081099/2500000000 : ℝ)|^4305 ≤ (5585768464351/12500000000000 : ℝ)^3281
        have hw : |(1353081099/2500000000 : ℝ)|=(1353081099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s5_5 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652802769/5000000000 : ℝ)*x 0 + (-489814957/2500000000 : ℝ)*x 1 + (676540551/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652802769/5000000000 : ℝ)^4305 ≤ (21766808223303/50000000000000 : ℝ)^3281 := by
    have hnat : (2652802769 : ℕ)^4305*50000000000000^3281 ≤ 21766808223303^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652802769 5000000000 21766808223303 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (489814957/2500000000 : ℝ)^4305 ≤ (1178023568303/10000000000000 : ℝ)^3281 := by
    have hnat : (489814957 : ℕ)^4305*10000000000000^3281 ≤ 1178023568303^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489814957 2500000000 1178023568303 10000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676540551/1250000000 : ℝ)^4305 ≤ (44686147844807/100000000000000 : ℝ)^3281 := by
    have hnat : (676540551 : ℕ)^4305*100000000000000^3281 ≤ 44686147844807^3281*1250000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676540551 1250000000 44686147844807 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652802769/5000000000 : ℝ), (-489814957/2500000000 : ℝ), (676540551/1250000000 : ℝ)] ![(21766808223303/50000000000000 : ℝ), (1178023568303/10000000000000 : ℝ), (44686147844807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652802769/5000000000 : ℝ)|^4305 ≤ (21766808223303/50000000000000 : ℝ)^3281
        have hw : |(2652802769/5000000000 : ℝ)|=(2652802769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-489814957/2500000000 : ℝ)|^4305 ≤ (1178023568303/10000000000000 : ℝ)^3281
        have hw : |(-489814957/2500000000 : ℝ)|=(489814957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676540551/1250000000 : ℝ)|^4305 ≤ (44686147844807/100000000000000 : ℝ)^3281
        have hw : |(676540551/1250000000 : ℝ)|=(676540551/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s5_6 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305605521/10000000000 : ℝ)*x 0 + (5412324421/10000000000 : ℝ)*x 1 + (-391851967/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305605521/10000000000 : ℝ)^4305 ≤ (43533616263583/100000000000000 : ℝ)^3281 := by
    have hnat : (5305605521 : ℕ)^4305*100000000000000^3281 ≤ 43533616263583^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305605521 10000000000 43533616263583 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412324421/10000000000 : ℝ)^4305 ≤ (22343073992819/50000000000000 : ℝ)^3281 := by
    have hnat : (5412324421 : ℕ)^4305*50000000000000^3281 ≤ 22343073992819^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412324421 10000000000 22343073992819 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (391851967/2000000000 : ℝ)^4305 ≤ (5890117869127/50000000000000 : ℝ)^3281 := by
    have hnat : (391851967 : ℕ)^4305*50000000000000^3281 ≤ 5890117869127^3281*2000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391851967 2000000000 5890117869127 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305605521/10000000000 : ℝ), (5412324421/10000000000 : ℝ), (-391851967/2000000000 : ℝ)] ![(43533616263583/100000000000000 : ℝ), (22343073992819/50000000000000 : ℝ), (5890117869127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305605521/10000000000 : ℝ)|^4305 ≤ (43533616263583/100000000000000 : ℝ)^3281
        have hw : |(5305605521/10000000000 : ℝ)|=(5305605521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412324421/10000000000 : ℝ)|^4305 ≤ (22343073992819/50000000000000 : ℝ)^3281
        have hw : |(5412324421/10000000000 : ℝ)|=(5412324421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-391851967/2000000000 : ℝ)|^4305 ≤ (5890117869127/50000000000000 : ℝ)^3281
        have hw : |(-391851967/2000000000 : ℝ)|=(391851967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s5_7 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4325834703/10000000000 : ℝ)*x 0 + (225233199/500000000 : ℝ)*x 1 + (4153701329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325834703/10000000000 : ℝ)^4305 ≤ (32522760197/97656250000 : ℝ)^3281 := by
    have hnat : (4325834703 : ℕ)^4305*97656250000^3281 ≤ 32522760197^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325834703 10000000000 32522760197 97656250000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225233199/500000000 : ℝ)^4305 ≤ (35121288997757/100000000000000 : ℝ)^3281 := by
    have hnat : (225233199 : ℕ)^4305*100000000000000^3281 ≤ 35121288997757^3281*500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225233199 500000000 35121288997757 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4153701329/10000000000 : ℝ)^4305 ≤ (31575404544771/100000000000000 : ℝ)^3281 := by
    have hnat : (4153701329 : ℕ)^4305*100000000000000^3281 ≤ 31575404544771^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153701329 10000000000 31575404544771 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325834703/10000000000 : ℝ), (225233199/500000000 : ℝ), (4153701329/10000000000 : ℝ)] ![(32522760197/97656250000 : ℝ), (35121288997757/100000000000000 : ℝ), (31575404544771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325834703/10000000000 : ℝ)|^4305 ≤ (32522760197/97656250000 : ℝ)^3281
        have hw : |(4325834703/10000000000 : ℝ)|=(4325834703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225233199/500000000 : ℝ)|^4305 ≤ (35121288997757/100000000000000 : ℝ)^3281
        have hw : |(225233199/500000000 : ℝ)|=(225233199/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4153701329/10000000000 : ℝ)|^4305 ≤ (31575404544771/100000000000000 : ℝ)^3281
        have hw : |(4153701329/10000000000 : ℝ)|=(4153701329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1345_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5553/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2787/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14717/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5553/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5553/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5553/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5553/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5553/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5553/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5553/50000 : ℝ) ^ (269/64 : ℝ) ≤ (486776476124717/5000000000000000000 : ℝ) := by
    have hpowers : (5553/50000 : ℝ)^269 ≤ (486776476124717/5000000000000000000 : ℝ)^64 := by
      have hnat : (5553 : ℕ)^269*5000000000000000000^64 ≤ 486776476124717^64*50000^269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5553 50000 486776476124717 5000000000000000000 269 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5553/50000 : ℝ)) (X := (486776476124717/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hpowhi : (7381/50000 : ℝ) ^ (269/64 : ℝ) ≤ (32196852863745283/100000000000000000000 : ℝ) := by
    have hpowers : (7381/50000 : ℝ)^269 ≤ (32196852863745283/100000000000000000000 : ℝ)^64 := by
      have hnat : (7381 : ℕ)^269*100000000000000000000^64 ≤ 32196852863745283^64*50000^269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7381 50000 32196852863745283 100000000000000000000 269 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7381/50000 : ℝ)) (X := (32196852863745283/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500486776476124717/2500000000000000000 : ℝ) ≤ (10000463217596427/10000000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (2500486776476124717/2500000000000000000 : ℝ)^64 ≤ (10000463217596427/10000000000000000 : ℝ)^269 := by
      have hnat : (2500486776476124717 : ℕ)^64*10000000000000000^269 ≤ 10000463217596427^269*2500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500486776476124717 2500000000000000000 10000463217596427 10000000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000463217596427/10000000000000000 : ℝ)) (X := (2500486776476124717/2500000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041932382386239623/100000000000000000000 : ℝ) ≤ (500049874419747/500000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (100041932382386239623/100000000000000000000 : ℝ)^64 ≤ (500049874419747/500000000000000 : ℝ)^269 := by
      have hnat : (100041932382386239623 : ℕ)^64*500000000000000^269 ≤ 500049874419747^269*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041932382386239623 100000000000000000000 500049874419747 500000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500049874419747/500000000000000 : ℝ)) (X := (100041932382386239623/100000000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032196852863745283/50000000000000000000 : ℝ) ≤ (10001531759193453/10000000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (50032196852863745283/50000000000000000000 : ℝ)^64 ≤ (10001531759193453/10000000000000000 : ℝ)^269 := by
      have hnat : (50032196852863745283 : ℕ)^64*10000000000000000^269 ≤ 10001531759193453^269*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032196852863745283 50000000000000000000 10001531759193453 10000000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001531759193453/10000000000000000 : ℝ)) (X := (50032196852863745283/50000000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(486776476124717/5000000000000000000 : ℝ) ≤ ((9137456575138991589/9140000000000000000 : ℝ)+2*(534270798513/365600000000000 : ℝ)*(5553/50000 : ℝ))^(269/64 : ℝ) := by
    rw [show (9137456575138991589/9140000000000000000 : ℝ)+2*(534270798513/365600000000000 : ℝ)*(5553/50000 : ℝ)=(10000463217596427/10000000000000000 : ℝ) by norm_num, show 1+2*(486776476124717/5000000000000000000 : ℝ)=(2500486776476124717/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32196852863745283/100000000000000000000 : ℝ)+(486776476124717/5000000000000000000 : ℝ) ≤ ((9137456575138991589/9140000000000000000 : ℝ)+(534270798513/365600000000000 : ℝ)*((7381/50000 : ℝ)+(5553/50000 : ℝ)))^(269/64 : ℝ) := by
    rw [show (9137456575138991589/9140000000000000000 : ℝ)+(534270798513/365600000000000 : ℝ)*((7381/50000 : ℝ)+(5553/50000 : ℝ))=(500049874419747/500000000000000 : ℝ) by norm_num, show 1+(32196852863745283/100000000000000000000 : ℝ)+(486776476124717/5000000000000000000 : ℝ)=(100041932382386239623/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32196852863745283/100000000000000000000 : ℝ) ≤ ((9137456575138991589/9140000000000000000 : ℝ)+2*(534270798513/365600000000000 : ℝ)*(7381/50000 : ℝ))^(269/64 : ℝ) := by
    rw [show (9137456575138991589/9140000000000000000 : ℝ)+2*(534270798513/365600000000000 : ℝ)*(7381/50000 : ℝ)=(10001531759193453/10000000000000000 : ℝ) by norm_num, show 1+2*(32196852863745283/100000000000000000000 : ℝ)=(50032196852863745283/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9137456575138991589/9140000000000000000 : ℝ)*(X 1 0+X 2 0)+(534270798513/365600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (5553/50000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (9137456575138991589/9140000000000000000 : ℝ)) (alpha := (534270798513/365600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9137456575138991589/9140000000000000000 : ℝ)*(X 0 1+X 2 1)+(534270798513/365600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (5553/50000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (9137456575138991589/9140000000000000000 : ℝ)) (alpha := (534270798513/365600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9137456575138991589/9140000000000000000 : ℝ)*(X 0 2+X 1 2)+(534270798513/365600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (5553/50000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (9137456575138991589/9140000000000000000 : ℝ)) (alpha := (534270798513/365600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2041335599/10000000000 : ℝ)*X 0 0+(1082586771/2000000000 : ℝ)*X 0 1+(5244348887/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674522089/5000000000 : ℝ)*X 1 0+(-1063617689/5000000000 : ℝ)*X 1 1+(5244348917/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668630527/1250000000 : ℝ)*X 2 0+(327771807/625000000 : ℝ)*X 2 1+(-1063617667/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4325808953/10000000000 : ℝ)*X 0 0+(4152423331/10000000000 : ℝ)*X 0 1+(2252967671/5000000000 : ℝ)*X 0 2+(4325808953/10000000000 : ℝ)*X 1 0+(4152423331/10000000000 : ℝ)*X 1 1+(2252967671/5000000000 : ℝ)*X 1 2+(4325808953/10000000000 : ℝ)*X 2 0+(4152423331/10000000000 : ℝ)*X 2 1+(2252967671/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2041347879/10000000000 : ℝ)*X 0 0+(655619403/1250000000 : ℝ)*X 0 1+(1353081099/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652802769/5000000000 : ℝ)*X 1 0+(-489814957/2500000000 : ℝ)*X 1 1+(676540551/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305605521/10000000000 : ℝ)*X 2 0+(5412324421/10000000000 : ℝ)*X 2 1+(-391851967/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4325834703/10000000000 : ℝ)*X 0 0+(225233199/500000000 : ℝ)*X 0 1+(4153701329/10000000000 : ℝ)*X 0 2+(4325834703/10000000000 : ℝ)*X 1 0+(225233199/500000000 : ℝ)*X 1 1+(4153701329/10000000000 : ℝ)*X 1 2+(4325834703/10000000000 : ℝ)*X 2 0+(225233199/500000000 : ℝ)*X 2 1+(4153701329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (856523472631398498722094987/91400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1763694281/100000000000000 : ℝ)*(base19) + (434862947/25000000000000 : ℝ)*(base23) + (17754129/50000000000000 : ℝ)*(lower2) + (26216937/12500000000000 : ℝ)*(upper3) + (55481733/25000000000000 : ℝ)*(upper5) + (876059643440887/20000000000000 : ℝ)*(major0) + (876059643440887/20000000000000 : ℝ)*(major1) + (876059643440887/20000000000000 : ℝ)*(major2) + (5931763607202159/100000000000000 : ℝ)*(sp0) + (2965900174899099/50000000000000 : ℝ)*(sp1) + (1482950093510173/25000000000000 : ℝ)*(sp2) + (11049905919427/390625000000 : ℝ)*(sp3) + (38506290321/100000000000000 : ℝ)*(sp4) + (18093171269/100000000000000 : ℝ)*(sp7) + (1414397004272291/50000000000000 : ℝ)*(f.failure) + (5931802113492479/100000000000000 : ℝ)*(f.sum) + (39267726355823/3656000000000000000000000000 : ℝ)*base65 + (3254238286717325557/182800000000000000000000000000000 : ℝ)*base68 + (1406206077973725557/182800000000000000000000000000000 : ℝ)*base70 + (49441506046125557/182800000000000000000000000000000 : ℝ)*base72 + (8005961321543/3656000000000000000000000000 : ℝ)*base73 + (1279568346601325557/182800000000000000000000000000000 : ℝ)*base76 + (1073934276524525557/182800000000000000000000000000000 : ℝ)*base78 + (1767004404931325557/182800000000000000000000000000000 : ℝ)*base80 + (17710396431519/3656000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (23727313/5000000000000000000000 : ℝ)*base89 + (23727313/5000000000000000000000 : ℝ)*base91 + (23727313/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2245836394194444219773043243/457000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23465897/2500000000000 : ℝ)*(base19) + (46606049/5000000000000 : ℝ)*(base23) + (14901583/12500000000000 : ℝ)*(upper3) + (2434117/50000000000000 : ℝ)*(lower4) + (101155231/100000000000000 : ℝ)*(upper5) + (4412060687824971/100000000000000 : ℝ)*(major0) + (4412060687824971/100000000000000 : ℝ)*(major1) + (4412060687824971/100000000000000 : ℝ)*(major2) + (9482716877/50000000000000 : ℝ)*(sp1) + (9693622871/50000000000000 : ℝ)*(sp2) + (1493703754619389/25000000000000 : ℝ)*(sp4) + (2987397557203961/50000000000000 : ℝ)*(sp5) + (1194958939822167/20000000000000 : ℝ)*(sp6) + (2849306193362283/100000000000000 : ℝ)*(sp7) + (2849306193362283/100000000000000 : ℝ)*(f.failure) + (1493703754619389/25000000000000 : ℝ)*(f.sum) + (58574452115123/18280000000000000000000000000 : ℝ)*base65 + (1041103132599756081/914000000000000000000000000000000 : ℝ)*base68 + (16253411648714243919/914000000000000000000000000000000 : ℝ)*base69 + (7100311365318243919/914000000000000000000000000000000 : ℝ)*base71 + (84264676123237/18280000000000000000000000000 : ℝ)*base74 + (7280629394662243919/914000000000000000000000000000000 : ℝ)*base75 + (6414818623392243919/914000000000000000000000000000000 : ℝ)*base77 + (9378228801829756081/914000000000000000000000000000000 : ℝ)*base80 + (94763170161003/18280000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (22177431/10000000000000000000000 : ℝ)*base90 + (22177431/10000000000000000000000 : ℝ)*base92 + (22177431/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1345_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5553/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1345_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1345_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4023/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9871/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1345_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1345_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1345_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4023/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9871/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1345_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

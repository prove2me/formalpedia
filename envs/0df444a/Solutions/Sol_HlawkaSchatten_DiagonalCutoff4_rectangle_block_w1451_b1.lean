-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1451_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:59:37.572369+00:00
-- url     : https://prove2.me/submissions/9bb6456e-590e-48e7-a0f8-deeca491896c

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
theorem support_rectangle_w1451_s3_0 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1952490897/10000000000 : ℝ)*x 0 + (5415116629/10000000000 : ℝ)*x 1 + (5239957407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1952490897/10000000000 : ℝ)^4411 ≤ (11915466751473/100000000000000 : ℝ)^3387 := by
    have hnat : (1952490897 : ℕ)^4411*100000000000000^3387 ≤ 11915466751473^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952490897 10000000000 11915466751473 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415116629/10000000000 : ℝ)^4411 ≤ (1799404510177/4000000000000 : ℝ)^3387 := by
    have hnat : (5415116629 : ℕ)^4411*4000000000000^3387 ≤ 1799404510177^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415116629 10000000000 1799404510177 4000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239957407/10000000000 : ℝ)^4411 ≤ (21549710238167/50000000000000 : ℝ)^3387 := by
    have hnat : (5239957407 : ℕ)^4411*50000000000000^3387 ≤ 21549710238167^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239957407 10000000000 21549710238167 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1952490897/10000000000 : ℝ), (5415116629/10000000000 : ℝ), (5239957407/10000000000 : ℝ)] ![(11915466751473/100000000000000 : ℝ), (1799404510177/4000000000000 : ℝ), (21549710238167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1952490897/10000000000 : ℝ)|^4411 ≤ (11915466751473/100000000000000 : ℝ)^3387
        have hw : |(-1952490897/10000000000 : ℝ)|=(1952490897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415116629/10000000000 : ℝ)|^4411 ≤ (1799404510177/4000000000000 : ℝ)^3387
        have hw : |(5415116629/10000000000 : ℝ)|=(5415116629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239957407/10000000000 : ℝ)|^4411 ≤ (21549710238167/50000000000000 : ℝ)^3387
        have hw : |(5239957407/10000000000 : ℝ)|=(5239957407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s3_1 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674467357/5000000000 : ℝ)*x 0 + (-2041803491/10000000000 : ℝ)*x 1 + (5239957191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674467357/5000000000 : ℝ)^4411 ≤ (22135212132077/50000000000000 : ℝ)^3387 := by
    have hnat : (2674467357 : ℕ)^4411*50000000000000^3387 ≤ 22135212132077^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674467357 5000000000 22135212132077 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2041803491/10000000000 : ℝ)^4411 ≤ (12630157558119/100000000000000 : ℝ)^3387 := by
    have hnat : (2041803491 : ℕ)^4411*100000000000000^3387 ≤ 12630157558119^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041803491 10000000000 12630157558119 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239957191/10000000000 : ℝ)^4411 ≤ (43099418162569/100000000000000 : ℝ)^3387 := by
    have hnat : (5239957191 : ℕ)^4411*100000000000000^3387 ≤ 43099418162569^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239957191 10000000000 43099418162569 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674467357/5000000000 : ℝ), (-2041803491/10000000000 : ℝ), (5239957191/10000000000 : ℝ)] ![(22135212132077/50000000000000 : ℝ), (12630157558119/100000000000000 : ℝ), (43099418162569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674467357/5000000000 : ℝ)|^4411 ≤ (22135212132077/50000000000000 : ℝ)^3387
        have hw : |(2674467357/5000000000 : ℝ)|=(2674467357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2041803491/10000000000 : ℝ)|^4411 ≤ (12630157558119/100000000000000 : ℝ)^3387
        have hw : |(-2041803491/10000000000 : ℝ)|=(2041803491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239957191/10000000000 : ℝ)|^4411 ≤ (43099418162569/100000000000000 : ℝ)^3387
        have hw : |(5239957191/10000000000 : ℝ)|=(5239957191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s3_2 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348934051/10000000000 : ℝ)*x 0 + (130998943/250000000 : ℝ)*x 1 + (-81672147/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348934051/10000000000 : ℝ)^4411 ≤ (22135208558923/50000000000000 : ℝ)^3387 := by
    have hnat : (5348934051 : ℕ)^4411*50000000000000^3387 ≤ 22135208558923^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348934051 10000000000 22135208558923 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130998943/250000000 : ℝ)^4411 ≤ (43099423829151/100000000000000 : ℝ)^3387 := by
    have hnat : (130998943 : ℕ)^4411*100000000000000^3387 ≤ 43099423829151^3387*250000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130998943 250000000 43099423829151 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81672147/400000000 : ℝ)^4411 ≤ (12630159040413/100000000000000 : ℝ)^3387 := by
    have hnat : (81672147 : ℕ)^4411*100000000000000^3387 ≤ 12630159040413^3387*400000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81672147 400000000 12630159040413 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348934051/10000000000 : ℝ), (130998943/250000000 : ℝ), (-81672147/400000000 : ℝ)] ![(22135208558923/50000000000000 : ℝ), (43099423829151/100000000000000 : ℝ), (12630159040413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348934051/10000000000 : ℝ)|^4411 ≤ (22135208558923/50000000000000 : ℝ)^3387
        have hw : |(5348934051/10000000000 : ℝ)|=(5348934051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130998943/250000000 : ℝ)|^4411 ≤ (43099423829151/100000000000000 : ℝ)^3387
        have hw : |(130998943/250000000 : ℝ)|=(130998943/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-81672147/400000000 : ℝ)|^4411 ≤ (12630159040413/100000000000000 : ℝ)^3387
        have hw : |(-81672147/400000000 : ℝ)|=(81672147/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s3_3 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4298333951/10000000000 : ℝ)*x 0 + (4111121221/10000000000 : ℝ)*x 1 + (1123276389/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298333951/10000000000 : ℝ)^4411 ≤ (166496418779/500000000000 : ℝ)^3387 := by
    have hnat : (4298333951 : ℕ)^4411*500000000000^3387 ≤ 166496418779^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298333951 10000000000 166496418779 500000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4111121221/10000000000 : ℝ)^4411 ≤ (6284604407659/20000000000000 : ℝ)^3387 := by
    have hnat : (4111121221 : ℕ)^4411*20000000000000^3387 ≤ 6284604407659^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4111121221 10000000000 6284604407659 20000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123276389/2500000000 : ℝ)^4411 ≤ (35277694193699/100000000000000 : ℝ)^3387 := by
    have hnat : (1123276389 : ℕ)^4411*100000000000000^3387 ≤ 35277694193699^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123276389 2500000000 35277694193699 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298333951/10000000000 : ℝ), (4111121221/10000000000 : ℝ), (1123276389/2500000000 : ℝ)] ![(166496418779/500000000000 : ℝ), (6284604407659/20000000000000 : ℝ), (35277694193699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298333951/10000000000 : ℝ)|^4411 ≤ (166496418779/500000000000 : ℝ)^3387
        have hw : |(4298333951/10000000000 : ℝ)|=(4298333951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4111121221/10000000000 : ℝ)|^4411 ≤ (6284604407659/20000000000000 : ℝ)^3387
        have hw : |(4111121221/10000000000 : ℝ)|=(4111121221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123276389/2500000000 : ℝ)|^4411 ≤ (35277694193699/100000000000000 : ℝ)^3387
        have hw : |(1123276389/2500000000 : ℝ)|=(1123276389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s3_4 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1952505287/10000000000 : ℝ)*x 0 + (2620325703/5000000000 : ℝ)*x 1 + (338401181/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1952505287/10000000000 : ℝ)^4411 ≤ (2383116223929/20000000000000 : ℝ)^3387 := by
    have hnat : (1952505287 : ℕ)^4411*20000000000000^3387 ≤ 2383116223929^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952505287 10000000000 2383116223929 20000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620325703/5000000000 : ℝ)^4411 ≤ (2694178416023/6250000000000 : ℝ)^3387 := by
    have hnat : (2620325703 : ℕ)^4411*6250000000000^3387 ≤ 2694178416023^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620325703 5000000000 2694178416023 6250000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338401181/625000000 : ℝ)^4411 ≤ (44977564202197/100000000000000 : ℝ)^3387 := by
    have hnat : (338401181 : ℕ)^4411*100000000000000^3387 ≤ 44977564202197^3387*625000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338401181 625000000 44977564202197 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1952505287/10000000000 : ℝ), (2620325703/5000000000 : ℝ), (338401181/625000000 : ℝ)] ![(2383116223929/20000000000000 : ℝ), (2694178416023/6250000000000 : ℝ), (44977564202197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1952505287/10000000000 : ℝ)|^4411 ≤ (2383116223929/20000000000000 : ℝ)^3387
        have hw : |(-1952505287/10000000000 : ℝ)|=(1952505287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620325703/5000000000 : ℝ)|^4411 ≤ (2694178416023/6250000000000 : ℝ)^3387
        have hw : |(2620325703/5000000000 : ℝ)|=(2620325703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338401181/625000000 : ℝ)|^4411 ≤ (44977564202197/100000000000000 : ℝ)^3387
        have hw : |(338401181/625000000 : ℝ)|=(338401181/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s3_5 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (662912789/1250000000 : ℝ)*x 0 + (-1867342491/10000000000 : ℝ)*x 1 + (338401179/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662912789/1250000000 : ℝ)^4411 ≤ (5472399969557/12500000000000 : ℝ)^3387 := by
    have hnat : (662912789 : ℕ)^4411*12500000000000^3387 ≤ 5472399969557^3387*1250000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662912789 1250000000 5472399969557 12500000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1867342491/10000000000 : ℝ)^4411 ≤ (351351137003/3125000000000 : ℝ)^3387 := by
    have hnat : (1867342491 : ℕ)^4411*3125000000000^3387 ≤ 351351137003^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867342491 10000000000 351351137003 3125000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338401179/625000000 : ℝ)^4411 ≤ (22488781928003/50000000000000 : ℝ)^3387 := by
    have hnat : (338401179 : ℕ)^4411*50000000000000^3387 ≤ 22488781928003^3387*625000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338401179 625000000 22488781928003 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662912789/1250000000 : ℝ), (-1867342491/10000000000 : ℝ), (338401179/625000000 : ℝ)] ![(5472399969557/12500000000000 : ℝ), (351351137003/3125000000000 : ℝ), (22488781928003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662912789/1250000000 : ℝ)|^4411 ≤ (5472399969557/12500000000000 : ℝ)^3387
        have hw : |(662912789/1250000000 : ℝ)|=(662912789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1867342491/10000000000 : ℝ)|^4411 ≤ (351351137003/3125000000000 : ℝ)^3387
        have hw : |(-1867342491/10000000000 : ℝ)|=(1867342491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338401179/625000000 : ℝ)|^4411 ≤ (22488781928003/50000000000000 : ℝ)^3387
        have hw : |(338401179/625000000 : ℝ)|=(338401179/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s3_6 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651650587/5000000000 : ℝ)*x 0 + (67680247/125000000 : ℝ)*x 1 + (-1867342813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651650587/5000000000 : ℝ)^4411 ≤ (1751167500879/4000000000000 : ℝ)^3387 := by
    have hnat : (2651650587 : ℕ)^4411*4000000000000^3387 ≤ 1751167500879^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651650587 5000000000 1751167500879 4000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67680247/125000000 : ℝ)^4411 ≤ (22488786774679/50000000000000 : ℝ)^3387 := by
    have hnat : (67680247 : ℕ)^4411*50000000000000^3387 ≤ 22488786774679^3387*125000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67680247 125000000 22488786774679 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1867342813/10000000000 : ℝ)^4411 ≤ (11243238909001/100000000000000 : ℝ)^3387 := by
    have hnat : (1867342813 : ℕ)^4411*100000000000000^3387 ≤ 11243238909001^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867342813 10000000000 11243238909001 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651650587/5000000000 : ℝ), (67680247/125000000 : ℝ), (-1867342813/10000000000 : ℝ)] ![(1751167500879/4000000000000 : ℝ), (22488786774679/50000000000000 : ℝ), (11243238909001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651650587/5000000000 : ℝ)|^4411 ≤ (1751167500879/4000000000000 : ℝ)^3387
        have hw : |(2651650587/5000000000 : ℝ)|=(2651650587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67680247/125000000 : ℝ)|^4411 ≤ (22488786774679/50000000000000 : ℝ)^3387
        have hw : |(67680247/125000000 : ℝ)|=(67680247/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1867342813/10000000000 : ℝ)|^4411 ≤ (11243238909001/100000000000000 : ℝ)^3387
        have hw : |(-1867342813/10000000000 : ℝ)|=(1867342813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s3_7 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4298365011/10000000000 : ℝ)*x 0 + (898318571/2000000000 : ℝ)*x 1 + (205632173/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298365011/10000000000 : ℝ)^4411 ≤ (33299597126599/100000000000000 : ℝ)^3387 := by
    have hnat : (4298365011 : ℕ)^4411*100000000000000^3387 ≤ 33299597126599^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298365011 10000000000 33299597126599 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (898318571/2000000000 : ℝ)^4411 ≤ (17631113590897/50000000000000 : ℝ)^3387 := by
    have hnat : (898318571 : ℕ)^4411*50000000000000^3387 ≤ 17631113590897^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898318571 2000000000 17631113590897 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (205632173/500000000 : ℝ)^4411 ≤ (31438175668289/100000000000000 : ℝ)^3387 := by
    have hnat : (205632173 : ℕ)^4411*100000000000000^3387 ≤ 31438175668289^3387*500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205632173 500000000 31438175668289 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298365011/10000000000 : ℝ), (898318571/2000000000 : ℝ), (205632173/500000000 : ℝ)] ![(33299597126599/100000000000000 : ℝ), (17631113590897/50000000000000 : ℝ), (31438175668289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298365011/10000000000 : ℝ)|^4411 ≤ (33299597126599/100000000000000 : ℝ)^3387
        have hw : |(4298365011/10000000000 : ℝ)|=(4298365011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(898318571/2000000000 : ℝ)|^4411 ≤ (17631113590897/50000000000000 : ℝ)^3387
        have hw : |(898318571/2000000000 : ℝ)|=(898318571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(205632173/500000000 : ℝ)|^4411 ≤ (31438175668289/100000000000000 : ℝ)^3387
        have hw : |(205632173/500000000 : ℝ)|=(205632173/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1451_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7867/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5241/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5613/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1867/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7867/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5241/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7867/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5241/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7867/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5241/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7867/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5241/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7867/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5241/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7867/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5241/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5241/50000 : ℝ) ^ (2205/512 : ℝ) ≤ (6045121095511007/100000000000000000000 : ℝ) := by
    have hpowers : (5241/50000 : ℝ)^2205 ≤ (6045121095511007/100000000000000000000 : ℝ)^512 := by
      have hnat : (5241 : ℕ)^2205*100000000000000000000^512 ≤ 6045121095511007^512*50000^2205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5241 50000 6045121095511007 100000000000000000000 2205 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5241/50000 : ℝ)) (X := (6045121095511007/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7867/50000 : ℝ) ^ (2205/512 : ℝ) ≤ (34759605356257219/100000000000000000000 : ℝ) := by
    have hpowers : (7867/50000 : ℝ)^2205 ≤ (34759605356257219/100000000000000000000 : ℝ)^512 := by
      have hnat : (7867 : ℕ)^2205*100000000000000000000^512 ≤ 34759605356257219^512*50000^2205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7867 50000 34759605356257219 100000000000000000000 2205 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7867/50000 : ℝ)) (X := (34759605356257219/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006045121095511007/50000000000000000000 : ℝ) ≤ (5000140360923067/5000000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (50006045121095511007/50000000000000000000 : ℝ)^512 ≤ (5000140360923067/5000000000000000 : ℝ)^2205 := by
      have hnat : (50006045121095511007 : ℕ)^512*5000000000000000^2205 ≤ 5000140360923067^2205*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006045121095511007 50000000000000000000 5000140360923067 5000000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000140360923067/5000000000000000 : ℝ)) (X := (50006045121095511007/50000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020402363225884113/50000000000000000000 : ℝ) ≤ (2000189467102103/2000000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (50020402363225884113/50000000000000000000 : ℝ)^512 ≤ (2000189467102103/2000000000000000 : ℝ)^2205 := by
      have hnat : (50020402363225884113 : ℕ)^512*2000000000000000^2205 ≤ 2000189467102103^2205*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020402363225884113 50000000000000000000 2000189467102103 2000000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000189467102103/2000000000000000 : ℝ)) (X := (50020402363225884113/50000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034759605356257219/50000000000000000000 : ℝ) ≤ (625100871823431/625000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (50034759605356257219/50000000000000000000 : ℝ)^512 ≤ (625100871823431/625000000000000 : ℝ)^2205 := by
      have hnat : (50034759605356257219 : ℕ)^512*625000000000000^2205 ≤ 625100871823431^2205*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034759605356257219 50000000000000000000 625100871823431 625000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625100871823431/625000000000000 : ℝ)) (X := (50034759605356257219/50000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6045121095511007/100000000000000000000 : ℝ) ≤ ((13126874865568953121/13130000000000000000 : ℝ)+2*(666613664381/525200000000000 : ℝ)*(5241/50000 : ℝ))^(2205/512 : ℝ) := by
    rw [show (13126874865568953121/13130000000000000000 : ℝ)+2*(666613664381/525200000000000 : ℝ)*(5241/50000 : ℝ)=(5000140360923067/5000000000000000 : ℝ) by norm_num, show 1+2*(6045121095511007/100000000000000000000 : ℝ)=(50006045121095511007/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34759605356257219/100000000000000000000 : ℝ)+(6045121095511007/100000000000000000000 : ℝ) ≤ ((13126874865568953121/13130000000000000000 : ℝ)+(666613664381/525200000000000 : ℝ)*((7867/50000 : ℝ)+(5241/50000 : ℝ)))^(2205/512 : ℝ) := by
    rw [show (13126874865568953121/13130000000000000000 : ℝ)+(666613664381/525200000000000 : ℝ)*((7867/50000 : ℝ)+(5241/50000 : ℝ))=(2000189467102103/2000000000000000 : ℝ) by norm_num, show 1+(34759605356257219/100000000000000000000 : ℝ)+(6045121095511007/100000000000000000000 : ℝ)=(50020402363225884113/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34759605356257219/100000000000000000000 : ℝ) ≤ ((13126874865568953121/13130000000000000000 : ℝ)+2*(666613664381/525200000000000 : ℝ)*(7867/50000 : ℝ))^(2205/512 : ℝ) := by
    rw [show (13126874865568953121/13130000000000000000 : ℝ)+2*(666613664381/525200000000000 : ℝ)*(7867/50000 : ℝ)=(625100871823431/625000000000000 : ℝ) by norm_num, show 1+2*(34759605356257219/100000000000000000000 : ℝ)=(50034759605356257219/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13126874865568953121/13130000000000000000 : ℝ)*(X 1 0+X 2 0)+(666613664381/525200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (5241/50000 : ℝ)) (hi := (7867/50000 : ℝ)) (c := (13126874865568953121/13130000000000000000 : ℝ)) (alpha := (666613664381/525200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13126874865568953121/13130000000000000000 : ℝ)*(X 0 1+X 2 1)+(666613664381/525200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (5241/50000 : ℝ)) (hi := (7867/50000 : ℝ)) (c := (13126874865568953121/13130000000000000000 : ℝ)) (alpha := (666613664381/525200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13126874865568953121/13130000000000000000 : ℝ)*(X 0 2+X 1 2)+(666613664381/525200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (5241/50000 : ℝ)) (hi := (7867/50000 : ℝ)) (c := (13126874865568953121/13130000000000000000 : ℝ)) (alpha := (666613664381/525200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1952490897/10000000000 : ℝ)*X 0 0+(5415116629/10000000000 : ℝ)*X 0 1+(5239957407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674467357/5000000000 : ℝ)*X 1 0+(-2041803491/10000000000 : ℝ)*X 1 1+(5239957191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348934051/10000000000 : ℝ)*X 2 0+(130998943/250000000 : ℝ)*X 2 1+(-81672147/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4298333951/10000000000 : ℝ)*X 0 0+(4111121221/10000000000 : ℝ)*X 0 1+(1123276389/2500000000 : ℝ)*X 0 2+(4298333951/10000000000 : ℝ)*X 1 0+(4111121221/10000000000 : ℝ)*X 1 1+(1123276389/2500000000 : ℝ)*X 1 2+(4298333951/10000000000 : ℝ)*X 2 0+(4111121221/10000000000 : ℝ)*X 2 1+(1123276389/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1952505287/10000000000 : ℝ)*X 0 0+(2620325703/5000000000 : ℝ)*X 0 1+(338401181/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((662912789/1250000000 : ℝ)*X 1 0+(-1867342491/10000000000 : ℝ)*X 1 1+(338401179/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651650587/5000000000 : ℝ)*X 2 0+(67680247/125000000 : ℝ)*X 2 1+(-1867342813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4298365011/10000000000 : ℝ)*X 0 0+(898318571/2000000000 : ℝ)*X 0 1+(205632173/500000000 : ℝ)*X 0 2+(4298365011/10000000000 : ℝ)*X 1 0+(898318571/2000000000 : ℝ)*X 1 1+(205632173/500000000 : ℝ)*X 1 2+(4298365011/10000000000 : ℝ)*X 2 0+(898318571/2000000000 : ℝ)*X 2 1+(205632173/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29860313900459679651932037/5050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1125279233/100000000000000 : ℝ)*(base19) + (335005659/50000000000000 : ℝ)*(base23) + (35575257/25000000000000 : ℝ)*(upper3) + (67958017/50000000000000 : ℝ)*(lower4) + (416353170012871/10000000000000 : ℝ)*(major0) + (416353170012871/10000000000000 : ℝ)*(major1) + (416353170012871/10000000000000 : ℝ)*(major2) + (713639987995171/12500000000000 : ℝ)*(sp0) + (570913425598793/10000000000000 : ℝ)*(sp1) + (2854567254797243/50000000000000 : ℝ)*(sp2) + (654479689747729/25000000000000 : ℝ)*(sp3) + (3869326449/25000000000000 : ℝ)*(sp4) + (201661359/100000000000000 : ℝ)*(sp6) + (566431347/6250000000000 : ℝ)*(sp7) + (654481955473117/25000000000000 : ℝ)*(f.failure) + (5709135381267163/100000000000000 : ℝ)*(f.sum) + (1257709678247/202000000000000000000000000 : ℝ)*base65 + (75223661683438107/10100000000000000000000000000000 : ℝ)*base67 + (7202422427038107/10100000000000000000000000000000 : ℝ)*base69 + (24523568927038107/10100000000000000000000000000000 : ℝ)*base71 + (122859850559/40400000000000000000000000 : ℝ)*base73 + (222468462983238107/10100000000000000000000000000000 : ℝ)*base75 + (93603768983838107/10100000000000000000000000000000 : ℝ)*base77 + (72663835752238107/10100000000000000000000000000000 : ℝ)*base79 + (673039937129/202000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1555547/2500000000000000000000 : ℝ)*base90 + (1555547/2500000000000000000000 : ℝ)*base92 + (1555547/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2863015141430083513897230543/328250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (116694061/100000000000000 : ℝ)*(base8) + (7971097/1000000000000 : ℝ)*(base21) + (9466701/6250000000000 : ℝ)*(upper2) + (127696003/100000000000000 : ℝ)*(lower4) + (2098421911636139/50000000000000 : ℝ)*(major0) + (2098421911636139/50000000000000 : ℝ)*(major1) + (2098421911636139/50000000000000 : ℝ)*(major2) + (170004729/20000000000000 : ℝ)*(sp0) + (3416067669/100000000000000 : ℝ)*(sp1) + (1856610149/50000000000000 : ℝ)*(sp2) + (5754812711549447/100000000000000 : ℝ)*(sp4) + (5754810262199483/100000000000000 : ℝ)*(sp5) + (2877404583968577/50000000000000 : ℝ)*(sp6) + (263887367754217/10000000000000 : ℝ)*(sp7) + (263887367754217/10000000000000 : ℝ)*(f.failure) + (359675854891697/6250000000000 : ℝ)*(f.sum) + (14325489814879/13130000000000000000000000000 : ℝ)*base65 + (3118903173416085181/656500000000000000000000000000000 : ℝ)*base68 + (2243648635401085181/656500000000000000000000000000000 : ℝ)*base70 + (3137069346816414819/656500000000000000000000000000000 : ℝ)*base71 + (50113895337619/13130000000000000000000000000 : ℝ)*base73 + (390645543582914819/656500000000000000000000000000000 : ℝ)*base75 + (23937142908408414819/656500000000000000000000000000000 : ℝ)*base77 + (373809168449414819/656500000000000000000000000000000 : ℝ)*base79 + (20262733590719/13130000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1905647/1000000000000000000000 : ℝ)*base90 + (1905647/1000000000000000000000 : ℝ)*base92 + (1905647/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1451_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7867/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5241/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1867/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1451_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1451_s4_0 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1953286601/10000000000 : ℝ)*x 0 + (270412863/500000000 : ℝ)*x 1 + (655786551/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1953286601/10000000000 : ℝ)^4411 ≤ (5960895596599/50000000000000 : ℝ)^3387 := by
    have hnat : (1953286601 : ℕ)^4411*50000000000000^3387 ≤ 5960895596599^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953286601 10000000000 5960895596599 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270412863/500000000 : ℝ)^4411 ≤ (11227729045913/25000000000000 : ℝ)^3387 := by
    have hnat : (270412863 : ℕ)^4411*25000000000000^3387 ≤ 11227729045913^3387*500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270412863 500000000 11227729045913 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655786551/1250000000 : ℝ)^4411 ≤ (5395911577447/12500000000000 : ℝ)^3387 := by
    have hnat : (655786551 : ℕ)^4411*12500000000000^3387 ≤ 5395911577447^3387*1250000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655786551 1250000000 5395911577447 12500000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1953286601/10000000000 : ℝ), (270412863/500000000 : ℝ), (655786551/1250000000 : ℝ)] ![(5960895596599/50000000000000 : ℝ), (11227729045913/25000000000000 : ℝ), (5395911577447/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1953286601/10000000000 : ℝ)|^4411 ≤ (5960895596599/50000000000000 : ℝ)^3387
        have hw : |(-1953286601/10000000000 : ℝ)|=(1953286601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270412863/500000000 : ℝ)|^4411 ≤ (11227729045913/25000000000000 : ℝ)^3387
        have hw : |(270412863/500000000 : ℝ)|=(270412863/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655786551/1250000000 : ℝ)|^4411 ≤ (5395911577447/12500000000000 : ℝ)^3387
        have hw : |(655786551/1250000000 : ℝ)|=(655786551/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s4_1 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347159219/10000000000 : ℝ)*x 0 + (-31808613/156250000 : ℝ)*x 1 + (524629213/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347159219/10000000000 : ℝ)^4411 ≤ (44251287614429/100000000000000 : ℝ)^3387 := by
    have hnat : (5347159219 : ℕ)^4411*100000000000000^3387 ≤ 44251287614429^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347159219 10000000000 44251287614429 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31808613/156250000 : ℝ)^4411 ≤ (6290711366361/50000000000000 : ℝ)^3387 := by
    have hnat : (31808613 : ℕ)^4411*50000000000000^3387 ≤ 6290711366361^3387*156250000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31808613 156250000 6290711366361 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524629213/1000000000 : ℝ)^4411 ≤ (43167289640587/100000000000000 : ℝ)^3387 := by
    have hnat : (524629213 : ℕ)^4411*100000000000000^3387 ≤ 43167289640587^3387*1000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524629213 1000000000 43167289640587 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347159219/10000000000 : ℝ), (-31808613/156250000 : ℝ), (524629213/1000000000 : ℝ)] ![(44251287614429/100000000000000 : ℝ), (6290711366361/50000000000000 : ℝ), (43167289640587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347159219/10000000000 : ℝ)|^4411 ≤ (44251287614429/100000000000000 : ℝ)^3387
        have hw : |(5347159219/10000000000 : ℝ)|=(5347159219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-31808613/156250000 : ℝ)|^4411 ≤ (6290711366361/50000000000000 : ℝ)^3387
        have hw : |(-31808613/156250000 : ℝ)|=(31808613/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524629213/1000000000 : ℝ)|^4411 ≤ (43167289640587/100000000000000 : ℝ)^3387
        have hw : |(524629213/1000000000 : ℝ)|=(524629213/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s4_2 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66839483/125000000 : ℝ)*x 0 + (5246292523/10000000000 : ℝ)*x 1 + (-2035751483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66839483/125000000 : ℝ)^4411 ≤ (44251281374161/100000000000000 : ℝ)^3387 := by
    have hnat : (66839483 : ℕ)^4411*100000000000000^3387 ≤ 44251281374161^3387*125000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66839483 125000000 44251281374161 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246292523/10000000000 : ℝ)^4411 ≤ (10791823462973/25000000000000 : ℝ)^3387 := by
    have hnat : (5246292523 : ℕ)^4411*25000000000000^3387 ≤ 10791823462973^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246292523 10000000000 10791823462973 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2035751483/10000000000 : ℝ)^4411 ≤ (1572678094119/12500000000000 : ℝ)^3387 := by
    have hnat : (2035751483 : ℕ)^4411*12500000000000^3387 ≤ 1572678094119^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035751483 10000000000 1572678094119 12500000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66839483/125000000 : ℝ), (5246292523/10000000000 : ℝ), (-2035751483/10000000000 : ℝ)] ![(44251281374161/100000000000000 : ℝ), (10791823462973/25000000000000 : ℝ), (1572678094119/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66839483/125000000 : ℝ)|^4411 ≤ (44251281374161/100000000000000 : ℝ)^3387
        have hw : |(66839483/125000000 : ℝ)|=(66839483/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246292523/10000000000 : ℝ)|^4411 ≤ (10791823462973/25000000000000 : ℝ)^3387
        have hw : |(5246292523/10000000000 : ℝ)|=(5246292523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2035751483/10000000000 : ℝ)|^4411 ≤ (1572678094119/12500000000000 : ℝ)^3387
        have hw : |(-2035751483/10000000000 : ℝ)|=(2035751483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s4_3 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26867647/62500000 : ℝ)*x 0 + (1031362251/2500000000 : ℝ)*x 1 + (559832511/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26867647/62500000 : ℝ)^4411 ≤ (16652111599447/50000000000000 : ℝ)^3387 := by
    have hnat : (26867647 : ℕ)^4411*50000000000000^3387 ≤ 16652111599447^3387*62500000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26867647 62500000 16652111599447 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031362251/2500000000 : ℝ)^4411 ≤ (15782859886601/50000000000000 : ℝ)^3387 := by
    have hnat : (1031362251 : ℕ)^4411*50000000000000^3387 ≤ 15782859886601^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031362251 2500000000 15782859886601 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559832511/1250000000 : ℝ)^4411 ≤ (35130057004203/100000000000000 : ℝ)^3387 := by
    have hnat : (559832511 : ℕ)^4411*100000000000000^3387 ≤ 35130057004203^3387*1250000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559832511 1250000000 35130057004203 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26867647/62500000 : ℝ), (1031362251/2500000000 : ℝ), (559832511/1250000000 : ℝ)] ![(16652111599447/50000000000000 : ℝ), (15782859886601/50000000000000 : ℝ), (35130057004203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26867647/62500000 : ℝ)|^4411 ≤ (16652111599447/50000000000000 : ℝ)^3387
        have hw : |(26867647/62500000 : ℝ)|=(26867647/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031362251/2500000000 : ℝ)|^4411 ≤ (15782859886601/50000000000000 : ℝ)^3387
        have hw : |(1031362251/2500000000 : ℝ)|=(1031362251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(559832511/1250000000 : ℝ)|^4411 ≤ (35130057004203/100000000000000 : ℝ)^3387
        have hw : |(559832511/1250000000 : ℝ)|=(559832511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s4_4 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2441623/12500000 : ℝ)*x 0 + (1311721433/2500000000 : ℝ)*x 1 + (5407660671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2441623/12500000 : ℝ)^4411 ≤ (5960942490137/50000000000000 : ℝ)^3387 := by
    have hnat : (2441623 : ℕ)^4411*50000000000000^3387 ≤ 5960942490137^3387*12500000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2441623 12500000 5960942490137 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311721433/2500000000 : ℝ)^4411 ≤ (43173650663443/100000000000000 : ℝ)^3387 := by
    have hnat : (1311721433 : ℕ)^4411*100000000000000^3387 ≤ 43173650663443^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311721433 2500000000 43173650663443 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407660671/10000000000 : ℝ)^4411 ≤ (22452232165553/50000000000000 : ℝ)^3387 := by
    have hnat : (5407660671 : ℕ)^4411*50000000000000^3387 ≤ 22452232165553^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407660671 10000000000 22452232165553 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2441623/12500000 : ℝ), (1311721433/2500000000 : ℝ), (5407660671/10000000000 : ℝ)] ![(5960942490137/50000000000000 : ℝ), (43173650663443/100000000000000 : ℝ), (22452232165553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2441623/12500000 : ℝ)|^4411 ≤ (5960942490137/50000000000000 : ℝ)^3387
        have hw : |(-2441623/12500000 : ℝ)|=(2441623/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311721433/2500000000 : ℝ)|^4411 ≤ (43173650663443/100000000000000 : ℝ)^3387
        have hw : |(1311721433/2500000000 : ℝ)|=(1311721433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407660671/10000000000 : ℝ)|^4411 ≤ (22452232165553/50000000000000 : ℝ)^3387
        have hw : |(5407660671/10000000000 : ℝ)|=(5407660671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s4_5 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304963581/10000000000 : ℝ)*x 0 + (-58574471/312500000 : ℝ)*x 1 + (5407660643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304963581/10000000000 : ℝ)^4411 ≤ (43797060676223/100000000000000 : ℝ)^3387 := by
    have hnat : (5304963581 : ℕ)^4411*100000000000000^3387 ≤ 43797060676223^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304963581 10000000000 43797060676223 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (58574471/312500000 : ℝ)^4411 ≤ (5649237638313/50000000000000 : ℝ)^3387 := by
    have hnat : (58574471 : ℕ)^4411*50000000000000^3387 ≤ 5649237638313^3387*312500000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58574471 312500000 5649237638313 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407660643/10000000000 : ℝ)^4411 ≤ (44904464028303/100000000000000 : ℝ)^3387 := by
    have hnat : (5407660643 : ℕ)^4411*100000000000000^3387 ≤ 44904464028303^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407660643 10000000000 44904464028303 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304963581/10000000000 : ℝ), (-58574471/312500000 : ℝ), (5407660643/10000000000 : ℝ)] ![(43797060676223/100000000000000 : ℝ), (5649237638313/50000000000000 : ℝ), (44904464028303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304963581/10000000000 : ℝ)|^4411 ≤ (43797060676223/100000000000000 : ℝ)^3387
        have hw : |(5304963581/10000000000 : ℝ)|=(5304963581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-58574471/312500000 : ℝ)|^4411 ≤ (5649237638313/50000000000000 : ℝ)^3387
        have hw : |(-58574471/312500000 : ℝ)|=(58574471/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407660643/10000000000 : ℝ)|^4411 ≤ (44904464028303/100000000000000 : ℝ)^3387
        have hw : |(5407660643/10000000000 : ℝ)|=(5407660643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s4_6 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326240913/2500000000 : ℝ)*x 0 + (1351915153/2500000000 : ℝ)*x 1 + (-937191509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326240913/2500000000 : ℝ)^4411 ≤ (43797061439607/100000000000000 : ℝ)^3387 := by
    have hnat : (1326240913 : ℕ)^4411*100000000000000^3387 ≤ 43797061439607^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326240913 2500000000 43797061439607 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351915153/2500000000 : ℝ)^4411 ≤ (44904463693057/100000000000000 : ℝ)^3387 := by
    have hnat : (1351915153 : ℕ)^4411*100000000000000^3387 ≤ 44904463693057^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351915153 2500000000 44904463693057 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (937191509/5000000000 : ℝ)^4411 ≤ (1412309356589/12500000000000 : ℝ)^3387 := by
    have hnat : (937191509 : ℕ)^4411*12500000000000^3387 ≤ 1412309356589^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937191509 5000000000 1412309356589 12500000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326240913/2500000000 : ℝ), (1351915153/2500000000 : ℝ), (-937191509/5000000000 : ℝ)] ![(43797061439607/100000000000000 : ℝ), (44904463693057/100000000000000 : ℝ), (1412309356589/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326240913/2500000000 : ℝ)|^4411 ≤ (43797061439607/100000000000000 : ℝ)^3387
        have hw : |(1326240913/2500000000 : ℝ)|=(1326240913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351915153/2500000000 : ℝ)|^4411 ≤ (44904463693057/100000000000000 : ℝ)^3387
        have hw : |(1351915153/2500000000 : ℝ)|=(1351915153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-937191509/5000000000 : ℝ)|^4411 ≤ (1412309356589/12500000000000 : ℝ)^3387
        have hw : |(-937191509/5000000000 : ℝ)|=(937191509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s4_7 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (859769637/2000000000 : ℝ)*x 0 + (895473169/2000000000 : ℝ)*x 1 + (4126750701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859769637/2000000000 : ℝ)^4411 ≤ (33304472057721/100000000000000 : ℝ)^3387 := by
    have hnat : (859769637 : ℕ)^4411*100000000000000^3387 ≤ 33304472057721^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859769637 2000000000 33304472057721 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895473169/2000000000 : ℝ)^4411 ≤ (7023367291197/20000000000000 : ℝ)^3387 := by
    have hnat : (895473169 : ℕ)^4411*20000000000000^3387 ≤ 7023367291197^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895473169 2000000000 7023367291197 20000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4126750701/10000000000 : ℝ)^4411 ≤ (15789345737427/50000000000000 : ℝ)^3387 := by
    have hnat : (4126750701 : ℕ)^4411*50000000000000^3387 ≤ 15789345737427^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4126750701 10000000000 15789345737427 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(859769637/2000000000 : ℝ), (895473169/2000000000 : ℝ), (4126750701/10000000000 : ℝ)] ![(33304472057721/100000000000000 : ℝ), (7023367291197/20000000000000 : ℝ), (15789345737427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(859769637/2000000000 : ℝ)|^4411 ≤ (33304472057721/100000000000000 : ℝ)^3387
        have hw : |(859769637/2000000000 : ℝ)|=(859769637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895473169/2000000000 : ℝ)|^4411 ≤ (7023367291197/20000000000000 : ℝ)^3387
        have hw : |(895473169/2000000000 : ℝ)|=(895473169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4126750701/10000000000 : ℝ)|^4411 ≤ (15789345737427/50000000000000 : ℝ)^3387
        have hw : |(4126750701/10000000000 : ℝ)|=(4126750701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1451_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1867/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11361/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14793/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1867/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5613/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1867/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5613/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1867/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5613/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1867/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5613/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1867/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5613/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1867/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5613/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5613/50000 : ℝ) ^ (2205/512 : ℝ) ≤ (8121954712114577/100000000000000000000 : ℝ) := by
    have hpowers : (5613/50000 : ℝ)^2205 ≤ (8121954712114577/100000000000000000000 : ℝ)^512 := by
      have hnat : (5613 : ℕ)^2205*100000000000000000000^512 ≤ 8121954712114577^512*50000^2205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5613 50000 8121954712114577 100000000000000000000 2205 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5613/50000 : ℝ)) (X := (8121954712114577/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1867/12500 : ℝ) ^ (2205/512 : ℝ) ≤ (27779467139564101/100000000000000000000 : ℝ) := by
    have hpowers : (1867/12500 : ℝ)^2205 ≤ (27779467139564101/100000000000000000000 : ℝ)^512 := by
      have hnat : (1867 : ℕ)^2205*100000000000000000000^512 ≤ 27779467139564101^512*12500^2205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1867 12500 27779467139564101 100000000000000000000 2205 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1867/12500 : ℝ)) (X := (27779467139564101/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008121954712114577/50000000000000000000 : ℝ) ≤ (5000188579660561/5000000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (50008121954712114577/50000000000000000000 : ℝ)^512 ≤ (5000188579660561/5000000000000000 : ℝ)^2205 := by
      have hnat : (50008121954712114577 : ℕ)^512*5000000000000000^2205 ≤ 5000188579660561^2205*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008121954712114577 50000000000000000000 5000188579660561 5000000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000188579660561/5000000000000000 : ℝ)) (X := (50008121954712114577/50000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017950710925839339/50000000000000000000 : ℝ) ≤ (10000833514516011/10000000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (50017950710925839339/50000000000000000000 : ℝ)^512 ≤ (10000833514516011/10000000000000000 : ℝ)^2205 := by
      have hnat : (50017950710925839339 : ℕ)^512*10000000000000000^2205 ≤ 10000833514516011^2205*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017950710925839339 50000000000000000000 10000833514516011 10000000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000833514516011/10000000000000000 : ℝ)) (X := (50017950710925839339/50000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027779467139564101/50000000000000000000 : ℝ) ≤ (100012898697109/100000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (50027779467139564101/50000000000000000000 : ℝ)^512 ≤ (100012898697109/100000000000000 : ℝ)^2205 := by
      have hnat : (50027779467139564101 : ℕ)^512*100000000000000^2205 ≤ 100012898697109^2205*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027779467139564101 50000000000000000000 100012898697109 100000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100012898697109/100000000000000 : ℝ)) (X := (50027779467139564101/50000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8121954712114577/100000000000000000000 : ℝ) ≤ ((4636394146780714349/4637500000000000000 : ℝ)+2*(456355194889/371000000000000 : ℝ)*(5613/50000 : ℝ))^(2205/512 : ℝ) := by
    rw [show (4636394146780714349/4637500000000000000 : ℝ)+2*(456355194889/371000000000000 : ℝ)*(5613/50000 : ℝ)=(5000188579660561/5000000000000000 : ℝ) by norm_num, show 1+2*(8121954712114577/100000000000000000000 : ℝ)=(50008121954712114577/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27779467139564101/100000000000000000000 : ℝ)+(8121954712114577/100000000000000000000 : ℝ) ≤ ((4636394146780714349/4637500000000000000 : ℝ)+(456355194889/371000000000000 : ℝ)*((1867/12500 : ℝ)+(5613/50000 : ℝ)))^(2205/512 : ℝ) := by
    rw [show (4636394146780714349/4637500000000000000 : ℝ)+(456355194889/371000000000000 : ℝ)*((1867/12500 : ℝ)+(5613/50000 : ℝ))=(10000833514516011/10000000000000000 : ℝ) by norm_num, show 1+(27779467139564101/100000000000000000000 : ℝ)+(8121954712114577/100000000000000000000 : ℝ)=(50017950710925839339/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27779467139564101/100000000000000000000 : ℝ) ≤ ((4636394146780714349/4637500000000000000 : ℝ)+2*(456355194889/371000000000000 : ℝ)*(1867/12500 : ℝ))^(2205/512 : ℝ) := by
    rw [show (4636394146780714349/4637500000000000000 : ℝ)+2*(456355194889/371000000000000 : ℝ)*(1867/12500 : ℝ)=(100012898697109/100000000000000 : ℝ) by norm_num, show 1+2*(27779467139564101/100000000000000000000 : ℝ)=(50027779467139564101/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4636394146780714349/4637500000000000000 : ℝ)*(X 1 0+X 2 0)+(456355194889/371000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (1867/12500 : ℝ)) (c := (4636394146780714349/4637500000000000000 : ℝ)) (alpha := (456355194889/371000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4636394146780714349/4637500000000000000 : ℝ)*(X 0 1+X 2 1)+(456355194889/371000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (1867/12500 : ℝ)) (c := (4636394146780714349/4637500000000000000 : ℝ)) (alpha := (456355194889/371000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4636394146780714349/4637500000000000000 : ℝ)*(X 0 2+X 1 2)+(456355194889/371000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (1867/12500 : ℝ)) (c := (4636394146780714349/4637500000000000000 : ℝ)) (alpha := (456355194889/371000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1953286601/10000000000 : ℝ)*X 0 0+(270412863/500000000 : ℝ)*X 0 1+(655786551/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347159219/10000000000 : ℝ)*X 1 0+(-31808613/156250000 : ℝ)*X 1 1+(524629213/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((66839483/125000000 : ℝ)*X 2 0+(5246292523/10000000000 : ℝ)*X 2 1+(-2035751483/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((26867647/62500000 : ℝ)*X 0 0+(1031362251/2500000000 : ℝ)*X 0 1+(559832511/1250000000 : ℝ)*X 0 2+(26867647/62500000 : ℝ)*X 1 0+(1031362251/2500000000 : ℝ)*X 1 1+(559832511/1250000000 : ℝ)*X 1 2+(26867647/62500000 : ℝ)*X 2 0+(1031362251/2500000000 : ℝ)*X 2 1+(559832511/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2441623/12500000 : ℝ)*X 0 0+(1311721433/2500000000 : ℝ)*X 0 1+(5407660671/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304963581/10000000000 : ℝ)*X 1 0+(-58574471/312500000 : ℝ)*X 1 1+(5407660643/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326240913/2500000000 : ℝ)*X 2 0+(1351915153/2500000000 : ℝ)*X 2 1+(-937191509/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((859769637/2000000000 : ℝ)*X 0 0+(895473169/2000000000 : ℝ)*X 0 1+(4126750701/10000000000 : ℝ)*X 0 2+(859769637/2000000000 : ℝ)*X 1 0+(895473169/2000000000 : ℝ)*X 1 1+(4126750701/10000000000 : ℝ)*X 1 2+(859769637/2000000000 : ℝ)*X 2 0+(895473169/2000000000 : ℝ)*X 2 1+(4126750701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (69229551394298169705568437/8281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1703122469/100000000000000 : ℝ)*(base19) + (217135909/20000000000000 : ℝ)*(base23) + (182869727/100000000000000 : ℝ)*(lower2) + (49169523/12500000000000 : ℝ)*(upper3) + (210201043/100000000000000 : ℝ)*(lower4) + (1125678524878153/25000000000000 : ℝ)*(major0) + (1125678524878153/25000000000000 : ℝ)*(major1) + (1125678524878153/25000000000000 : ℝ)*(major2) + (3087107633838363/50000000000000 : ℝ)*(sp0) + (308711436167579/5000000000000 : ℝ)*(sp1) + (771778667599313/12500000000000 : ℝ)*(sp2) + (2831181207619153/100000000000000 : ℝ)*(sp3) + (15158797323/100000000000000 : ℝ)*(sp4) + (4071568047/25000000000000 : ℝ)*(sp7) + (2831197493891341/100000000000000 : ℝ)*(f.failure) + (6174230426474049/100000000000000 : ℝ)*(f.sum) + (1908349674699/579687500000000000000000000 : ℝ)*base65 + (1847819297320103/115937500000000000000000000000000 : ℝ)*base68 + (818480327039507603/115937500000000000000000000000000 : ℝ)*base70 + (872871089848929897/115937500000000000000000000000000 : ℝ)*base71 + (1157110443117/4637500000000000000000000000 : ℝ)*base73 + (25801421307679897/115937500000000000000000000000000 : ℝ)*base75 + (1458019415367679897/115937500000000000000000000000000 : ℝ)*base77 + (1138551991978929897/115937500000000000000000000000000 : ℝ)*base79 + (16972611055233/4637500000000000000000000000 : ℝ)*base82 + (4589269/10000000000000000000000 : ℝ)*base89 + (4589269/10000000000000000000000 : ℝ)*base91 + (4589269/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1413660972563924928542555967/115937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (914841871/50000000000000 : ℝ)*(base19) + (1085125547/50000000000000 : ℝ)*(base23) + (99680389/50000000000000 : ℝ)*(upper3) + (29113643/25000000000000 : ℝ)*(lower4) + (279373281/100000000000000 : ℝ)*(upper5) + (2268001217578361/50000000000000 : ℝ)*(major0) + (2268001217578361/50000000000000 : ℝ)*(major1) + (2268001217578361/50000000000000 : ℝ)*(major2) + (1207400271/3125000000000 : ℝ)*(sp1) + (1059329/2441406250 : ℝ)*(sp2) + (621987607133211/10000000000000 : ℝ)*(sp4) + (388739725302481/6250000000000 : ℝ)*(sp5) + (6219830510965177/100000000000000 : ℝ)*(sp6) + (8912901226681/312500000000 : ℝ)*(sp7) + (8912901226681/312500000000 : ℝ)*(f.failure) + (621987607133211/10000000000000 : ℝ)*(f.sum) + (22075790683071/9275000000000000000000000000 : ℝ)*base66 + (871025004898785511/231875000000000000000000000000000 : ℝ)*base68 + (2339751586467535511/231875000000000000000000000000000 : ℝ)*base70 + (3824123980963785511/231875000000000000000000000000000 : ℝ)*base72 + (22045558835329/9275000000000000000000000000 : ℝ)*base73 + (724200589196214489/231875000000000000000000000000000 : ℝ)*base75 + (3367920459501285511/231875000000000000000000000000000 : ℝ)*base78 + (735887730098714489/231875000000000000000000000000000 : ℝ)*base79 + (9968631142079/9275000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (310329/31250000000000000000 : ℝ)*base89 + (310329/31250000000000000000 : ℝ)*base91 + (310329/31250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1451_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1867/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14793/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1451_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1451_s5_0 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-30521893/156250000 : ℝ)*x 0 + (5407236431/10000000000 : ℝ)*x 1 + (1311809409/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (30521893/156250000 : ℝ)^4411 ≤ (5961350867759/50000000000000 : ℝ)^3387 := by
    have hnat : (30521893 : ℕ)^4411*50000000000000^3387 ≤ 5961350867759^3387*156250000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30521893 156250000 5961350867759 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407236431/10000000000 : ℝ)^4411 ≤ (44899876489529/100000000000000 : ℝ)^3387 := by
    have hnat : (5407236431 : ℕ)^4411*100000000000000^3387 ≤ 44899876489529^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407236431 10000000000 44899876489529 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311809409/2500000000 : ℝ)^4411 ≤ (8635484351969/20000000000000 : ℝ)^3387 := by
    have hnat : (1311809409 : ℕ)^4411*20000000000000^3387 ≤ 8635484351969^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311809409 2500000000 8635484351969 20000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-30521893/156250000 : ℝ), (5407236431/10000000000 : ℝ), (1311809409/2500000000 : ℝ)] ![(5961350867759/50000000000000 : ℝ), (44899876489529/100000000000000 : ℝ), (8635484351969/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-30521893/156250000 : ℝ)|^4411 ≤ (5961350867759/50000000000000 : ℝ)^3387
        have hw : |(-30521893/156250000 : ℝ)|=(30521893/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407236431/10000000000 : ℝ)|^4411 ≤ (44899876489529/100000000000000 : ℝ)^3387
        have hw : |(5407236431/10000000000 : ℝ)|=(5407236431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311809409/2500000000 : ℝ)|^4411 ≤ (8635484351969/20000000000000 : ℝ)^3387
        have hw : |(1311809409/2500000000 : ℝ)|=(1311809409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s5_1 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346894439/10000000000 : ℝ)*x 0 + (-651151/3200000 : ℝ)*x 1 + (1049447527/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346894439/10000000000 : ℝ)^4411 ≤ (44248433925803/100000000000000 : ℝ)^3387 := by
    have hnat : (5346894439 : ℕ)^4411*100000000000000^3387 ≤ 44248433925803^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346894439 10000000000 44248433925803 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651151/3200000 : ℝ)^4411 ≤ (12574144303793/100000000000000 : ℝ)^3387 := by
    have hnat : (651151 : ℕ)^4411*100000000000000^3387 ≤ 12574144303793^3387*3200000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651151 3200000 12574144303793 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049447527/2000000000 : ℝ)^4411 ≤ (43177421749129/100000000000000 : ℝ)^3387 := by
    have hnat : (1049447527 : ℕ)^4411*100000000000000^3387 ≤ 43177421749129^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049447527 2000000000 43177421749129 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346894439/10000000000 : ℝ), (-651151/3200000 : ℝ), (1049447527/2000000000 : ℝ)] ![(44248433925803/100000000000000 : ℝ), (12574144303793/100000000000000 : ℝ), (43177421749129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346894439/10000000000 : ℝ)|^4411 ≤ (44248433925803/100000000000000 : ℝ)^3387
        have hw : |(5346894439/10000000000 : ℝ)|=(5346894439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-651151/3200000 : ℝ)|^4411 ≤ (12574144303793/100000000000000 : ℝ)^3387
        have hw : |(-651151/3200000 : ℝ)|=(651151/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049447527/2000000000 : ℝ)|^4411 ≤ (43177421749129/100000000000000 : ℝ)^3387
        have hw : |(1049447527/2000000000 : ℝ)|=(1049447527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s5_2 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673447219/5000000000 : ℝ)*x 0 + (1311809409/2500000000 : ℝ)*x 1 + (-651151/3200000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673447219/5000000000 : ℝ)^4411 ≤ (22124216957513/50000000000000 : ℝ)^3387 := by
    have hnat : (2673447219 : ℕ)^4411*50000000000000^3387 ≤ 22124216957513^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673447219 5000000000 22124216957513 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311809409/2500000000 : ℝ)^4411 ≤ (8635484351969/20000000000000 : ℝ)^3387 := by
    have hnat : (1311809409 : ℕ)^4411*20000000000000^3387 ≤ 8635484351969^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311809409 2500000000 8635484351969 20000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (651151/3200000 : ℝ)^4411 ≤ (12574144303793/100000000000000 : ℝ)^3387 := by
    have hnat : (651151 : ℕ)^4411*100000000000000^3387 ≤ 12574144303793^3387*3200000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651151 3200000 12574144303793 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673447219/5000000000 : ℝ), (1311809409/2500000000 : ℝ), (-651151/3200000 : ℝ)] ![(22124216957513/50000000000000 : ℝ), (8635484351969/20000000000000 : ℝ), (12574144303793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673447219/5000000000 : ℝ)|^4411 ≤ (22124216957513/50000000000000 : ℝ)^3387
        have hw : |(2673447219/5000000000 : ℝ)|=(2673447219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311809409/2500000000 : ℝ)|^4411 ≤ (8635484351969/20000000000000 : ℝ)^3387
        have hw : |(1311809409/2500000000 : ℝ)|=(1311809409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-651151/3200000 : ℝ)|^4411 ≤ (12574144303793/100000000000000 : ℝ)^3387
        have hw : |(-651151/3200000 : ℝ)|=(651151/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s5_3 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268680777/625000000 : ℝ)*x 0 + (2063792567/5000000000 : ℝ)*x 1 + (559563497/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268680777/625000000 : ℝ)^4411 ≤ (33304918491259/100000000000000 : ℝ)^3387 := by
    have hnat : (268680777 : ℕ)^4411*100000000000000^3387 ≤ 33304918491259^3387*625000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268680777 625000000 33304918491259 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063792567/5000000000 : ℝ)^4411 ≤ (31587007436977/100000000000000 : ℝ)^3387 := by
    have hnat : (2063792567 : ℕ)^4411*100000000000000^3387 ≤ 31587007436977^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063792567 5000000000 31587007436977 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559563497/1250000000 : ℝ)^4411 ≤ (35108074056299/100000000000000 : ℝ)^3387 := by
    have hnat : (559563497 : ℕ)^4411*100000000000000^3387 ≤ 35108074056299^3387*1250000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559563497 1250000000 35108074056299 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268680777/625000000 : ℝ), (2063792567/5000000000 : ℝ), (559563497/1250000000 : ℝ)] ![(33304918491259/100000000000000 : ℝ), (31587007436977/100000000000000 : ℝ), (35108074056299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268680777/625000000 : ℝ)|^4411 ≤ (33304918491259/100000000000000 : ℝ)^3387
        have hw : |(268680777/625000000 : ℝ)|=(268680777/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2063792567/5000000000 : ℝ)|^4411 ≤ (31587007436977/100000000000000 : ℝ)^3387
        have hw : |(2063792567/5000000000 : ℝ)|=(2063792567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(559563497/1250000000 : ℝ)|^4411 ≤ (35108074056299/100000000000000 : ℝ)^3387
        have hw : |(559563497/1250000000 : ℝ)|=(559563497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s5_4 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-7630517/39062500 : ℝ)*x 0 + (5247816893/10000000000 : ℝ)*x 1 + (5406654159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7630517/39062500 : ℝ)^4411 ≤ (11922790762879/100000000000000 : ℝ)^3387 := by
    have hnat : (7630517 : ℕ)^4411*100000000000000^3387 ≤ 11922790762879^3387*39062500^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7630517 39062500 11922790762879 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247816893/10000000000 : ℝ)^4411 ≤ (43183629397687/100000000000000 : ℝ)^3387 := by
    have hnat : (5247816893 : ℕ)^4411*100000000000000^3387 ≤ 43183629397687^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247816893 10000000000 43183629397687 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406654159/10000000000 : ℝ)^4411 ≤ (4489357982603/10000000000000 : ℝ)^3387 := by
    have hnat : (5406654159 : ℕ)^4411*10000000000000^3387 ≤ 4489357982603^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406654159 10000000000 4489357982603 10000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7630517/39062500 : ℝ), (5247816893/10000000000 : ℝ), (5406654159/10000000000 : ℝ)] ![(11922790762879/100000000000000 : ℝ), (43183629397687/100000000000000 : ℝ), (4489357982603/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7630517/39062500 : ℝ)|^4411 ≤ (11922790762879/100000000000000 : ℝ)^3387
        have hw : |(-7630517/39062500 : ℝ)|=(7630517/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247816893/10000000000 : ℝ)|^4411 ≤ (43183629397687/100000000000000 : ℝ)^3387
        have hw : |(5247816893/10000000000 : ℝ)|=(5247816893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406654159/10000000000 : ℝ)|^4411 ≤ (4489357982603/10000000000000 : ℝ)^3387
        have hw : |(5406654159/10000000000 : ℝ)|=(5406654159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s5_5 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305211087/10000000000 : ℝ)*x 0 + (-375086077/2000000000 : ℝ)*x 1 + (5406654221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305211087/10000000000 : ℝ)^4411 ≤ (10949930462467/25000000000000 : ℝ)^3387 := by
    have hnat : (5305211087 : ℕ)^4411*25000000000000^3387 ≤ 10949930462467^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305211087 10000000000 10949930462467 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (375086077/2000000000 : ℝ)^4411 ≤ (2826674409299/25000000000000 : ℝ)^3387 := by
    have hnat : (375086077 : ℕ)^4411*25000000000000^3387 ≤ 2826674409299^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375086077 2000000000 2826674409299 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406654221/10000000000 : ℝ)^4411 ≤ (8978716099297/20000000000000 : ℝ)^3387 := by
    have hnat : (5406654221 : ℕ)^4411*20000000000000^3387 ≤ 8978716099297^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406654221 10000000000 8978716099297 20000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305211087/10000000000 : ℝ), (-375086077/2000000000 : ℝ), (5406654221/10000000000 : ℝ)] ![(10949930462467/25000000000000 : ℝ), (2826674409299/25000000000000 : ℝ), (8978716099297/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305211087/10000000000 : ℝ)|^4411 ≤ (10949930462467/25000000000000 : ℝ)^3387
        have hw : |(5305211087/10000000000 : ℝ)|=(5305211087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-375086077/2000000000 : ℝ)|^4411 ≤ (2826674409299/25000000000000 : ℝ)^3387
        have hw : |(-375086077/2000000000 : ℝ)|=(375086077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406654221/10000000000 : ℝ)|^4411 ≤ (8978716099297/20000000000000 : ℝ)^3387
        have hw : |(5406654221/10000000000 : ℝ)|=(5406654221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s5_6 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305211111/10000000000 : ℝ)*x 0 + (5406654229/10000000000 : ℝ)*x 1 + (-1875430341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305211111/10000000000 : ℝ)^4411 ≤ (43799722107917/100000000000000 : ℝ)^3387 := by
    have hnat : (5305211111 : ℕ)^4411*100000000000000^3387 ≤ 43799722107917^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305211111 10000000000 43799722107917 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406654229/10000000000 : ℝ)^4411 ≤ (8978716116599/20000000000000 : ℝ)^3387 := by
    have hnat : (5406654229 : ℕ)^4411*20000000000000^3387 ≤ 8978716116599^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406654229 10000000000 8978716116599 20000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1875430341/10000000000 : ℝ)^4411 ≤ (11306697291727/100000000000000 : ℝ)^3387 := by
    have hnat : (1875430341 : ℕ)^4411*100000000000000^3387 ≤ 11306697291727^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875430341 10000000000 11306697291727 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305211111/10000000000 : ℝ), (5406654229/10000000000 : ℝ), (-1875430341/10000000000 : ℝ)] ![(43799722107917/100000000000000 : ℝ), (8978716116599/20000000000000 : ℝ), (11306697291727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305211111/10000000000 : ℝ)|^4411 ≤ (43799722107917/100000000000000 : ℝ)^3387
        have hw : |(5305211111/10000000000 : ℝ)|=(5305211111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406654229/10000000000 : ℝ)|^4411 ≤ (8978716116599/20000000000000 : ℝ)^3387
        have hw : |(5406654229/10000000000 : ℝ)|=(5406654229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1875430341/10000000000 : ℝ)|^4411 ≤ (11306697291727/100000000000000 : ℝ)^3387
        have hw : |(-1875430341/10000000000 : ℝ)|=(1875430341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s5_7 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537364603/1250000000 : ℝ)*x 0 + (2237622369/5000000000 : ℝ)*x 1 + (206442747/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537364603/1250000000 : ℝ)^4411 ≤ (8326291149207/25000000000000 : ℝ)^3387 := by
    have hnat : (537364603 : ℕ)^4411*25000000000000^3387 ≤ 8326291149207^3387*1250000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537364603 1250000000 8326291149207 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2237622369/5000000000 : ℝ)^4411 ≤ (35095172082431/100000000000000 : ℝ)^3387 := by
    have hnat : (2237622369 : ℕ)^4411*100000000000000^3387 ≤ 35095172082431^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237622369 5000000000 35095172082431 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206442747/500000000 : ℝ)^4411 ≤ (631993266063/2000000000000 : ℝ)^3387 := by
    have hnat : (206442747 : ℕ)^4411*2000000000000^3387 ≤ 631993266063^3387*500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206442747 500000000 631993266063 2000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537364603/1250000000 : ℝ), (2237622369/5000000000 : ℝ), (206442747/500000000 : ℝ)] ![(8326291149207/25000000000000 : ℝ), (35095172082431/100000000000000 : ℝ), (631993266063/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537364603/1250000000 : ℝ)|^4411 ≤ (8326291149207/25000000000000 : ℝ)^3387
        have hw : |(537364603/1250000000 : ℝ)|=(537364603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2237622369/5000000000 : ℝ)|^4411 ≤ (35095172082431/100000000000000 : ℝ)^3387
        have hw : |(2237622369/5000000000 : ℝ)|=(2237622369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(206442747/500000000 : ℝ)|^4411 ≤ (631993266063/2000000000000 : ℝ)^3387
        have hw : |(206442747/500000000 : ℝ)|=(206442747/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1451_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14793/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11381/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14771/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14793/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11361/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14793/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11361/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14793/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11361/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14793/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11361/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14793/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11361/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14793/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11361/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11361/100000 : ℝ) ^ (2205/512 : ℝ) ≤ (4275516504405871/50000000000000000000 : ℝ) := by
    have hpowers : (11361/100000 : ℝ)^2205 ≤ (4275516504405871/50000000000000000000 : ℝ)^512 := by
      have hnat : (11361 : ℕ)^2205*50000000000000000000^512 ≤ 4275516504405871^512*100000^2205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11361 100000 4275516504405871 50000000000000000000 2205 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11361/100000 : ℝ)) (X := (4275516504405871/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14793/100000 : ℝ) ^ (2205/512 : ℝ) ≤ (26652046420132533/100000000000000000000 : ℝ) := by
    have hpowers : (14793/100000 : ℝ)^2205 ≤ (26652046420132533/100000000000000000000 : ℝ)^512 := by
      have hnat : (14793 : ℕ)^2205*100000000000000000000^512 ≤ 26652046420132533^512*100000^2205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14793 100000 26652046420132533 100000000000000000000 2205 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14793/100000 : ℝ)) (X := (26652046420132533/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004275516504405871/25000000000000000000 : ℝ) ≤ (50001985415639/50000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (25004275516504405871/25000000000000000000 : ℝ)^512 ≤ (50001985415639/50000000000000 : ℝ)^2205 := by
      have hnat : (25004275516504405871 : ℕ)^512*50000000000000^2205 ≤ 50001985415639^2205*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004275516504405871 25000000000000000000 50001985415639 50000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50001985415639/50000000000000 : ℝ)) (X := (25004275516504405871/25000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001408123177157771/4000000000000000000 : ℝ) ≤ (500040865173079/500000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (4001408123177157771/4000000000000000000 : ℝ)^512 ≤ (500040865173079/500000000000000 : ℝ)^2205 := by
      have hnat : (4001408123177157771 : ℕ)^512*500000000000000^2205 ≤ 500040865173079^2205*4000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001408123177157771 4000000000000000000 500040865173079 500000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500040865173079/500000000000000 : ℝ)) (X := (4001408123177157771/4000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026652046420132533/50000000000000000000 : ℝ) ≤ (62507734523721/62500000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (50026652046420132533/50000000000000000000 : ℝ)^512 ≤ (62507734523721/62500000000000 : ℝ)^2205 := by
      have hnat : (50026652046420132533 : ℕ)^512*62500000000000^2205 ≤ 62507734523721^2205*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026652046420132533 50000000000000000000 62507734523721 62500000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62507734523721/62500000000000 : ℝ)) (X := (50026652046420132533/50000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4275516504405871/50000000000000000000 : ℝ) ≤ ((21994752912096449/22000000000000000 : ℝ)+2*(1616232053/1320000000000 : ℝ)*(11361/100000 : ℝ))^(2205/512 : ℝ) := by
    rw [show (21994752912096449/22000000000000000 : ℝ)+2*(1616232053/1320000000000 : ℝ)*(11361/100000 : ℝ)=(50001985415639/50000000000000 : ℝ) by norm_num, show 1+2*(4275516504405871/50000000000000000000 : ℝ)=(25004275516504405871/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26652046420132533/100000000000000000000 : ℝ)+(4275516504405871/50000000000000000000 : ℝ) ≤ ((21994752912096449/22000000000000000 : ℝ)+(1616232053/1320000000000 : ℝ)*((14793/100000 : ℝ)+(11361/100000 : ℝ)))^(2205/512 : ℝ) := by
    rw [show (21994752912096449/22000000000000000 : ℝ)+(1616232053/1320000000000 : ℝ)*((14793/100000 : ℝ)+(11361/100000 : ℝ))=(500040865173079/500000000000000 : ℝ) by norm_num, show 1+(26652046420132533/100000000000000000000 : ℝ)+(4275516504405871/50000000000000000000 : ℝ)=(4001408123177157771/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26652046420132533/100000000000000000000 : ℝ) ≤ ((21994752912096449/22000000000000000 : ℝ)+2*(1616232053/1320000000000 : ℝ)*(14793/100000 : ℝ))^(2205/512 : ℝ) := by
    rw [show (21994752912096449/22000000000000000 : ℝ)+2*(1616232053/1320000000000 : ℝ)*(14793/100000 : ℝ)=(62507734523721/62500000000000 : ℝ) by norm_num, show 1+2*(26652046420132533/100000000000000000000 : ℝ)=(50026652046420132533/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21994752912096449/22000000000000000 : ℝ)*(X 1 0+X 2 0)+(1616232053/1320000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (11361/100000 : ℝ)) (hi := (14793/100000 : ℝ)) (c := (21994752912096449/22000000000000000 : ℝ)) (alpha := (1616232053/1320000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21994752912096449/22000000000000000 : ℝ)*(X 0 1+X 2 1)+(1616232053/1320000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (11361/100000 : ℝ)) (hi := (14793/100000 : ℝ)) (c := (21994752912096449/22000000000000000 : ℝ)) (alpha := (1616232053/1320000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21994752912096449/22000000000000000 : ℝ)*(X 0 2+X 1 2)+(1616232053/1320000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (11361/100000 : ℝ)) (hi := (14793/100000 : ℝ)) (c := (21994752912096449/22000000000000000 : ℝ)) (alpha := (1616232053/1320000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-30521893/156250000 : ℝ)*X 0 0+(5407236431/10000000000 : ℝ)*X 0 1+(1311809409/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346894439/10000000000 : ℝ)*X 1 0+(-651151/3200000 : ℝ)*X 1 1+(1049447527/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673447219/5000000000 : ℝ)*X 2 0+(1311809409/2500000000 : ℝ)*X 2 1+(-651151/3200000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((268680777/625000000 : ℝ)*X 0 0+(2063792567/5000000000 : ℝ)*X 0 1+(559563497/1250000000 : ℝ)*X 0 2+(268680777/625000000 : ℝ)*X 1 0+(2063792567/5000000000 : ℝ)*X 1 1+(559563497/1250000000 : ℝ)*X 1 2+(268680777/625000000 : ℝ)*X 2 0+(2063792567/5000000000 : ℝ)*X 2 1+(559563497/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-7630517/39062500 : ℝ)*X 0 0+(5247816893/10000000000 : ℝ)*X 0 1+(5406654159/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305211087/10000000000 : ℝ)*X 1 0+(-375086077/2000000000 : ℝ)*X 1 1+(5406654221/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305211111/10000000000 : ℝ)*X 2 0+(5406654229/10000000000 : ℝ)*X 2 1+(-1875430341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((537364603/1250000000 : ℝ)*X 0 0+(2237622369/5000000000 : ℝ)*X 0 1+(206442747/500000000 : ℝ)*X 0 2+(537364603/1250000000 : ℝ)*X 1 0+(2237622369/5000000000 : ℝ)*X 1 1+(206442747/500000000 : ℝ)*X 1 2+(537364603/1250000000 : ℝ)*X 2 0+(2237622369/5000000000 : ℝ)*X 2 1+(206442747/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (443885843010780240428073/44000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (455875277/25000000000000 : ℝ)*(base19) + (1698709397/100000000000000 : ℝ)*(base23) + (33049899/50000000000000 : ℝ)*(lower2) + (251139321/100000000000000 : ℝ)*(upper3) + (32255367/20000000000000 : ℝ)*(upper5) + (182322513018141/4000000000000 : ℝ)*(major0) + (182322513018141/4000000000000 : ℝ)*(major1) + (182322513018141/4000000000000 : ℝ)*(major2) + (195315228477697/3125000000000 : ℝ)*(sp0) + (6250124059847951/100000000000000 : ℝ)*(sp1) + (3125062092319831/50000000000000 : ℝ)*(sp2) + (286598028676229/10000000000000 : ℝ)*(sp3) + (7714412551/20000000000000 : ℝ)*(sp4) + (19144518537/100000000000000 : ℝ)*(sp7) + (1432999715640413/50000000000000 : ℝ)*(f.failure) + (6250125883349059/100000000000000 : ℝ)*(f.sum) + (7229569253/880000000000000000000000 : ℝ)*base66 + (989794459591309/88000000000000000000000000000 : ℝ)*base67 + (140404219160691/88000000000000000000000000000 : ℝ)*base70 + (80373080615309/88000000000000000000000000000 : ℝ)*base71 + (83926432627/22000000000000000000000000 : ℝ)*base74 + (2199080137191309/88000000000000000000000000000 : ℝ)*base75 + (42347800480691/88000000000000000000000000000 : ℝ)*base78 + (678322173807309/88000000000000000000000000000 : ℝ)*base79 + (22119360453/4400000000000000000000000 : ℝ)*base82 + (38046683/5000000000000000000000 : ℝ)*base90 + (38046683/5000000000000000000000 : ℝ)*base92 + (38046683/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1608628251384422283554499/275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (799374143/100000000000000 : ℝ)*(base19) + (22675547/2500000000000 : ℝ)*(base23) + (121593841/100000000000000 : ℝ)*(upper3) + (1451769/5000000000000 : ℝ)*(lower4) + (121489631/100000000000000 : ℝ)*(upper5) + (2295668166235183/50000000000000 : ℝ)*(major0) + (2295668166235183/50000000000000 : ℝ)*(major1) + (2295668166235183/50000000000000 : ℝ)*(major2) + (8926925709/50000000000000 : ℝ)*(sp1) + (2096403037/10000000000000 : ℝ)*(sp2) + (12591502927819/200000000000 : ℝ)*(sp4) + (3147866405341969/50000000000000 : ℝ)*(sp5) + (6295729592857249/100000000000000 : ℝ)*(sp6) + (1443460503022989/50000000000000 : ℝ)*(sp7) + (1443460503022989/50000000000000 : ℝ)*(f.failure) + (12591502927819/200000000000 : ℝ)*(f.sum) + (121058454923/33000000000000000000000000 : ℝ)*base65 + (30814174403245501/3300000000000000000000000000000 : ℝ)*base67 + (10845997631554499/3300000000000000000000000000000 : ℝ)*base70 + (37591807740445501/3300000000000000000000000000000 : ℝ)*base71 + (1905387527/33000000000000000000000000 : ℝ)*base73 + (52059565216045501/3300000000000000000000000000000 : ℝ)*base75 + (19504868790145501/3300000000000000000000000000000 : ℝ)*base77 + (66167147527945501/3300000000000000000000000000000 : ℝ)*base79 + (65610893057/16500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (20624299/5000000000000000000000 : ℝ)*base90 + (20624299/5000000000000000000000 : ℝ)*base92 + (20624299/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1451_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14793/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1451_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1451_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7867/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5241/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1451_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1451_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1451_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7867/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5241/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1451_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

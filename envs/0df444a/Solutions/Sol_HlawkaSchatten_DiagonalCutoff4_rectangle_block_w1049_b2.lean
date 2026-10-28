-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1049_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:54:35.228796+00:00
-- url     : https://prove2.me/submissions/d7ea581e-80d7-44c2-9bc8-2298e9542f0b

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
theorem support_rectangle_w1049_s6_0 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1106055887/5000000000 : ℝ)*x 0 + (5395266799/10000000000 : ℝ)*x 1 + (2631778973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1106055887/5000000000 : ℝ)^4121 ≤ (268659620017/2000000000000 : ℝ)^3097 := by
    have hnat : (1106055887 : ℕ)^4121*2000000000000^3097 ≤ 268659620017^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106055887 5000000000 268659620017 2000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395266799/10000000000 : ℝ)^4121 ≤ (10998792345289/25000000000000 : ℝ)^3097 := by
    have hnat : (5395266799 : ℕ)^4121*25000000000000^3097 ≤ 10998792345289^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395266799 10000000000 10998792345289 25000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631778973/5000000000 : ℝ)^4121 ≤ (10642962400927/25000000000000 : ℝ)^3097 := by
    have hnat : (2631778973 : ℕ)^4121*25000000000000^3097 ≤ 10642962400927^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631778973 5000000000 10642962400927 25000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1106055887/5000000000 : ℝ), (5395266799/10000000000 : ℝ), (2631778973/5000000000 : ℝ)] ![(268659620017/2000000000000 : ℝ), (10998792345289/25000000000000 : ℝ), (10642962400927/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1106055887/5000000000 : ℝ)|^4121 ≤ (268659620017/2000000000000 : ℝ)^3097
        have hw : |(-1106055887/5000000000 : ℝ)|=(1106055887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395266799/10000000000 : ℝ)|^4121 ≤ (10998792345289/25000000000000 : ℝ)^3097
        have hw : |(5395266799/10000000000 : ℝ)|=(5395266799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631778973/5000000000 : ℝ)|^4121 ≤ (10642962400927/25000000000000 : ℝ)^3097
        have hw : |(2631778973/5000000000 : ℝ)|=(2631778973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s6_1 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345169149/10000000000 : ℝ)*x 0 + (-1139475079/5000000000 : ℝ)*x 1 + (5263557943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345169149/10000000000 : ℝ)^4121 ≤ (10863104089611/25000000000000 : ℝ)^3097 := by
    have hnat : (5345169149 : ℕ)^4121*25000000000000^3097 ≤ 10863104089611^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345169149 10000000000 10863104089611 25000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1139475079/5000000000 : ℝ)^4121 ≤ (13975734051521/100000000000000 : ℝ)^3097 := by
    have hnat : (1139475079 : ℕ)^4121*100000000000000^3097 ≤ 13975734051521^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139475079 5000000000 13975734051521 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263557943/10000000000 : ℝ)^4121 ≤ (42571849571421/100000000000000 : ℝ)^3097 := by
    have hnat : (5263557943 : ℕ)^4121*100000000000000^3097 ≤ 42571849571421^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263557943 10000000000 42571849571421 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345169149/10000000000 : ℝ), (-1139475079/5000000000 : ℝ), (5263557943/10000000000 : ℝ)] ![(10863104089611/25000000000000 : ℝ), (13975734051521/100000000000000 : ℝ), (42571849571421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345169149/10000000000 : ℝ)|^4121 ≤ (10863104089611/25000000000000 : ℝ)^3097
        have hw : |(5345169149/10000000000 : ℝ)|=(5345169149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1139475079/5000000000 : ℝ)|^4121 ≤ (13975734051521/100000000000000 : ℝ)^3097
        have hw : |(-1139475079/5000000000 : ℝ)|=(1139475079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263557943/10000000000 : ℝ)|^4121 ≤ (42571849571421/100000000000000 : ℝ)^3097
        have hw : |(5263557943/10000000000 : ℝ)|=(5263557943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s6_2 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345168937/10000000000 : ℝ)*x 0 + (5263558081/10000000000 : ℝ)*x 1 + (-142434391/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345168937/10000000000 : ℝ)^4121 ≤ (43452414065203/100000000000000 : ℝ)^3097 := by
    have hnat : (5345168937 : ℕ)^4121*100000000000000^3097 ≤ 43452414065203^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345168937 10000000000 43452414065203 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263558081/10000000000 : ℝ)^4121 ≤ (5321481382077/12500000000000 : ℝ)^3097 := by
    have hnat : (5263558081 : ℕ)^4121*12500000000000^3097 ≤ 5321481382077^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263558081 10000000000 5321481382077 12500000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (142434391/625000000 : ℝ)^4121 ≤ (13975734851221/100000000000000 : ℝ)^3097 := by
    have hnat : (142434391 : ℕ)^4121*100000000000000^3097 ≤ 13975734851221^3097*625000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142434391 625000000 13975734851221 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345168937/10000000000 : ℝ), (5263558081/10000000000 : ℝ), (-142434391/625000000 : ℝ)] ![(43452414065203/100000000000000 : ℝ), (5321481382077/12500000000000 : ℝ), (13975734851221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345168937/10000000000 : ℝ)|^4121 ≤ (43452414065203/100000000000000 : ℝ)^3097
        have hw : |(5345168937/10000000000 : ℝ)|=(5345168937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263558081/10000000000 : ℝ)|^4121 ≤ (5321481382077/12500000000000 : ℝ)^3097
        have hw : |(5263558081/10000000000 : ℝ)|=(5263558081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-142434391/625000000 : ℝ)|^4121 ≤ (13975734851221/100000000000000 : ℝ)^3097
        have hw : |(-142434391/625000000 : ℝ)|=(142434391/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s6_3 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (136809757/312500000 : ℝ)*x 0 + (531400521/1250000000 : ℝ)*x 1 + (4508464531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136809757/312500000 : ℝ)^4121 ≤ (16658069669967/50000000000000 : ℝ)^3097 := by
    have hnat : (136809757 : ℕ)^4121*50000000000000^3097 ≤ 16658069669967^3097*312500000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136809757 312500000 16658069669967 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (531400521/1250000000 : ℝ)^4121 ≤ (32039240190097/100000000000000 : ℝ)^3097 := by
    have hnat : (531400521 : ℕ)^4121*100000000000000^3097 ≤ 32039240190097^3097*1250000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531400521 1250000000 32039240190097 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4508464531/10000000000 : ℝ)^4121 ≤ (4330577557019/12500000000000 : ℝ)^3097 := by
    have hnat : (4508464531 : ℕ)^4121*12500000000000^3097 ≤ 4330577557019^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508464531 10000000000 4330577557019 12500000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136809757/312500000 : ℝ), (531400521/1250000000 : ℝ), (4508464531/10000000000 : ℝ)] ![(16658069669967/50000000000000 : ℝ), (32039240190097/100000000000000 : ℝ), (4330577557019/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136809757/312500000 : ℝ)|^4121 ≤ (16658069669967/50000000000000 : ℝ)^3097
        have hw : |(136809757/312500000 : ℝ)|=(136809757/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(531400521/1250000000 : ℝ)|^4121 ≤ (32039240190097/100000000000000 : ℝ)^3097
        have hw : |(531400521/1250000000 : ℝ)|=(531400521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4508464531/10000000000 : ℝ)|^4121 ≤ (4330577557019/12500000000000 : ℝ)^3097
        have hw : |(4508464531/10000000000 : ℝ)|=(4508464531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s6_4 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-442423411/2000000000 : ℝ)*x 0 + (1315972651/2500000000 : ℝ)*x 1 + (1348733227/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (442423411/2000000000 : ℝ)^4121 ≤ (6716511836429/50000000000000 : ℝ)^3097 := by
    have hnat : (442423411 : ℕ)^4121*50000000000000^3097 ≤ 6716511836429^3097*2000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442423411 2000000000 6716511836429 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315972651/2500000000 : ℝ)^4121 ≤ (42575429801577/100000000000000 : ℝ)^3097 := by
    have hnat : (1315972651 : ℕ)^4121*100000000000000^3097 ≤ 42575429801577^3097*2500000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315972651 2500000000 42575429801577 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348733227/2500000000 : ℝ)^4121 ≤ (43991546502843/100000000000000 : ℝ)^3097 := by
    have hnat : (1348733227 : ℕ)^4121*100000000000000^3097 ≤ 43991546502843^3097*2500000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348733227 2500000000 43991546502843 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-442423411/2000000000 : ℝ), (1315972651/2500000000 : ℝ), (1348733227/2500000000 : ℝ)] ![(6716511836429/50000000000000 : ℝ), (42575429801577/100000000000000 : ℝ), (43991546502843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-442423411/2000000000 : ℝ)|^4121 ≤ (6716511836429/50000000000000 : ℝ)^3097
        have hw : |(-442423411/2000000000 : ℝ)|=(442423411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315972651/2500000000 : ℝ)|^4121 ≤ (42575429801577/100000000000000 : ℝ)^3097
        have hw : |(1315972651/2500000000 : ℝ)|=(1315972651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348733227/2500000000 : ℝ)|^4121 ≤ (43991546502843/100000000000000 : ℝ)^3097
        have hw : |(1348733227/2500000000 : ℝ)|=(1348733227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s6_5 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312039361/10000000000 : ℝ)*x 0 + (-26844691/125000000 : ℝ)*x 1 + (269746649/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312039361/10000000000 : ℝ)^4121 ≤ (5386801667449/12500000000000 : ℝ)^3097 := by
    have hnat : (5312039361 : ℕ)^4121*12500000000000^3097 ≤ 5386801667449^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312039361 10000000000 5386801667449 12500000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26844691/125000000 : ℝ)^4121 ≤ (6457019678637/50000000000000 : ℝ)^3097 := by
    have hnat : (26844691 : ℕ)^4121*50000000000000^3097 ≤ 6457019678637^3097*125000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26844691 125000000 6457019678637 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269746649/500000000 : ℝ)^4121 ≤ (43991547284069/100000000000000 : ℝ)^3097 := by
    have hnat : (269746649 : ℕ)^4121*100000000000000^3097 ≤ 43991547284069^3097*500000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269746649 500000000 43991547284069 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312039361/10000000000 : ℝ), (-26844691/125000000 : ℝ), (269746649/500000000 : ℝ)] ![(5386801667449/12500000000000 : ℝ), (6457019678637/50000000000000 : ℝ), (43991547284069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312039361/10000000000 : ℝ)|^4121 ≤ (5386801667449/12500000000000 : ℝ)^3097
        have hw : |(5312039361/10000000000 : ℝ)|=(5312039361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26844691/125000000 : ℝ)|^4121 ≤ (6457019678637/50000000000000 : ℝ)^3097
        have hw : |(-26844691/125000000 : ℝ)|=(26844691/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269746649/500000000 : ℝ)|^4121 ≤ (43991547284069/100000000000000 : ℝ)^3097
        have hw : |(269746649/500000000 : ℝ)|=(269746649/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s6_6 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16600123/31250000 : ℝ)*x 0 + (5394932969/10000000000 : ℝ)*x 1 + (-4194483/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16600123/31250000 : ℝ)^4121 ≤ (43094413328797/100000000000000 : ℝ)^3097 := by
    have hnat : (16600123 : ℕ)^4121*100000000000000^3097 ≤ 43094413328797^3097*31250000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16600123 31250000 43094413328797 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394932969/10000000000 : ℝ)^4121 ≤ (8798309432943/20000000000000 : ℝ)^3097 := by
    have hnat : (5394932969 : ℕ)^4121*20000000000000^3097 ≤ 8798309432943^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394932969 10000000000 8798309432943 20000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4194483/19531250 : ℝ)^4121 ≤ (12914039485299/100000000000000 : ℝ)^3097 := by
    have hnat : (4194483 : ℕ)^4121*100000000000000^3097 ≤ 12914039485299^3097*19531250^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4194483 19531250 12914039485299 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16600123/31250000 : ℝ), (5394932969/10000000000 : ℝ), (-4194483/19531250 : ℝ)] ![(43094413328797/100000000000000 : ℝ), (8798309432943/20000000000000 : ℝ), (12914039485299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16600123/31250000 : ℝ)|^4121 ≤ (43094413328797/100000000000000 : ℝ)^3097
        have hw : |(16600123/31250000 : ℝ)|=(16600123/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394932969/10000000000 : ℝ)|^4121 ≤ (8798309432943/20000000000000 : ℝ)^3097
        have hw : |(5394932969/10000000000 : ℝ)|=(5394932969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4194483/19531250 : ℝ)|^4121 ≤ (12914039485299/100000000000000 : ℝ)^3097
        have hw : |(-4194483/19531250 : ℝ)|=(4194483/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s6_7 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4377922567/10000000000 : ℝ)*x 0 + (4507814541/10000000000 : ℝ)*x 1 + (4251856433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377922567/10000000000 : ℝ)^4121 ≤ (1041132627371/3125000000000 : ℝ)^3097 := by
    have hnat : (4377922567 : ℕ)^4121*3125000000000^3097 ≤ 1041132627371^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377922567 10000000000 1041132627371 3125000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507814541/10000000000 : ℝ)^4121 ≤ (34637974386581/100000000000000 : ℝ)^3097 := by
    have hnat : (4507814541 : ℕ)^4121*100000000000000^3097 ≤ 34637974386581^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507814541 10000000000 34637974386581 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4251856433/10000000000 : ℝ)^4121 ≤ (500715336413/1562500000000 : ℝ)^3097 := by
    have hnat : (4251856433 : ℕ)^4121*1562500000000^3097 ≤ 500715336413^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251856433 10000000000 500715336413 1562500000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377922567/10000000000 : ℝ), (4507814541/10000000000 : ℝ), (4251856433/10000000000 : ℝ)] ![(1041132627371/3125000000000 : ℝ), (34637974386581/100000000000000 : ℝ), (500715336413/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377922567/10000000000 : ℝ)|^4121 ≤ (1041132627371/3125000000000 : ℝ)^3097
        have hw : |(4377922567/10000000000 : ℝ)|=(4377922567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507814541/10000000000 : ℝ)|^4121 ≤ (34637974386581/100000000000000 : ℝ)^3097
        have hw : |(4507814541/10000000000 : ℝ)|=(4507814541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4251856433/10000000000 : ℝ)|^4121 ≤ (500715336413/1562500000000 : ℝ)^3097
        have hw : |(4251856433/10000000000 : ℝ)|=(4251856433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1049_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147662441/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11171/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2243/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2801/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3513/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11171/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3513/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11171/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3513/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11171/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3513/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11171/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3513/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11171/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3513/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11171/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11171/100000 : ℝ) ^ (8241/2048 : ℝ) ≤ (738861556084443/5000000000000000000 : ℝ) := by
    have hpowers : (11171/100000 : ℝ)^8241 ≤ (738861556084443/5000000000000000000 : ℝ)^2048 := by
      have hnat : (11171 : ℕ)^8241*5000000000000000000^2048 ≤ 738861556084443^2048*100000^8241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11171 100000 738861556084443 5000000000000000000 8241 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11171/100000 : ℝ)) (X := (738861556084443/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3513/25000 : ℝ) ^ (8241/2048 : ℝ) ≤ (37201592707256253/100000000000000000000 : ℝ) := by
    have hpowers : (3513/25000 : ℝ)^8241 ≤ (37201592707256253/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3513 : ℕ)^8241*100000000000000000000^2048 ≤ 37201592707256253^2048*25000^8241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3513 25000 37201592707256253 100000000000000000000 8241 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3513/25000 : ℝ)) (X := (37201592707256253/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500738861556084443/2500000000000000000 : ℝ) ≤ (2000146877365169/2000000000000000 : ℝ) ^ (8241/2048 : ℝ) := by
    have hpowers : (2500738861556084443/2500000000000000000 : ℝ)^2048 ≤ (2000146877365169/2000000000000000 : ℝ)^8241 := by
      have hnat : (2500738861556084443 : ℕ)^2048*2000000000000000^8241 ≤ 2000146877365169^8241*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500738861556084443 2500000000000000000 2000146877365169 2000000000000000 2048 8241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000146877365169/2000000000000000 : ℝ)) (X := (2500738861556084443/2500000000000000000 : ℝ)) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051978823828945113/100000000000000000000 : ℝ) ≤ (10001291491889017/10000000000000000 : ℝ) ^ (8241/2048 : ℝ) := by
    have hpowers : (100051978823828945113/100000000000000000000 : ℝ)^2048 ≤ (10001291491889017/10000000000000000 : ℝ)^8241 := by
      have hnat : (100051978823828945113 : ℕ)^2048*10000000000000000^8241 ≤ 10001291491889017^8241*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051978823828945113 100000000000000000000 10001291491889017 10000000000000000 2048 8241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001291491889017/10000000000000000 : ℝ)) (X := (100051978823828945113/100000000000000000000 : ℝ)) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037201592707256253/50000000000000000000 : ℝ) ≤ (10001848596952189/10000000000000000 : ℝ) ^ (8241/2048 : ℝ) := by
    have hpowers : (50037201592707256253/50000000000000000000 : ℝ)^2048 ≤ (10001848596952189/10000000000000000 : ℝ)^8241 := by
      have hnat : (50037201592707256253 : ℕ)^2048*10000000000000000^8241 ≤ 10001848596952189^8241*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037201592707256253 50000000000000000000 10001848596952189 10000000000000000 2048 8241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001848596952189/10000000000000000 : ℝ)) (X := (50037201592707256253/50000000000000000000 : ℝ)) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(738861556084443/5000000000000000000 : ℝ) ≤ ((28799668927123870621/28810000000000000000 : ℝ)+2*(139276265793/72025000000000 : ℝ)*(11171/100000 : ℝ))^(8241/2048 : ℝ) := by
    rw [show (28799668927123870621/28810000000000000000 : ℝ)+2*(139276265793/72025000000000 : ℝ)*(11171/100000 : ℝ)=(2000146877365169/2000000000000000 : ℝ) by norm_num, show 1+2*(738861556084443/5000000000000000000 : ℝ)=(2500738861556084443/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37201592707256253/100000000000000000000 : ℝ)+(738861556084443/5000000000000000000 : ℝ) ≤ ((28799668927123870621/28810000000000000000 : ℝ)+(139276265793/72025000000000 : ℝ)*((3513/25000 : ℝ)+(11171/100000 : ℝ)))^(8241/2048 : ℝ) := by
    rw [show (28799668927123870621/28810000000000000000 : ℝ)+(139276265793/72025000000000 : ℝ)*((3513/25000 : ℝ)+(11171/100000 : ℝ))=(10001291491889017/10000000000000000 : ℝ) by norm_num, show 1+(37201592707256253/100000000000000000000 : ℝ)+(738861556084443/5000000000000000000 : ℝ)=(100051978823828945113/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37201592707256253/100000000000000000000 : ℝ) ≤ ((28799668927123870621/28810000000000000000 : ℝ)+2*(139276265793/72025000000000 : ℝ)*(3513/25000 : ℝ))^(8241/2048 : ℝ) := by
    rw [show (28799668927123870621/28810000000000000000 : ℝ)+2*(139276265793/72025000000000 : ℝ)*(3513/25000 : ℝ)=(10001848596952189/10000000000000000 : ℝ) by norm_num, show 1+2*(37201592707256253/100000000000000000000 : ℝ)=(50037201592707256253/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28799668927123870621/28810000000000000000 : ℝ)*(X 1 0+X 2 0)+(139276265793/72025000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8241/2048 : ℝ)) (lo := (11171/100000 : ℝ)) (hi := (3513/25000 : ℝ)) (c := (28799668927123870621/28810000000000000000 : ℝ)) (alpha := (139276265793/72025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28799668927123870621/28810000000000000000 : ℝ)*(X 0 1+X 2 1)+(139276265793/72025000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8241/2048 : ℝ)) (lo := (11171/100000 : ℝ)) (hi := (3513/25000 : ℝ)) (c := (28799668927123870621/28810000000000000000 : ℝ)) (alpha := (139276265793/72025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28799668927123870621/28810000000000000000 : ℝ)*(X 0 2+X 1 2)+(139276265793/72025000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8241/2048 : ℝ)) (lo := (11171/100000 : ℝ)) (hi := (3513/25000 : ℝ)) (c := (28799668927123870621/28810000000000000000 : ℝ)) (alpha := (139276265793/72025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1106055887/5000000000 : ℝ)*X 0 0+(5395266799/10000000000 : ℝ)*X 0 1+(2631778973/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345169149/10000000000 : ℝ)*X 1 0+(-1139475079/5000000000 : ℝ)*X 1 1+(5263557943/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345168937/10000000000 : ℝ)*X 2 0+(5263558081/10000000000 : ℝ)*X 2 1+(-142434391/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((136809757/312500000 : ℝ)*X 0 0+(531400521/1250000000 : ℝ)*X 0 1+(4508464531/10000000000 : ℝ)*X 0 2+(136809757/312500000 : ℝ)*X 1 0+(531400521/1250000000 : ℝ)*X 1 1+(4508464531/10000000000 : ℝ)*X 1 2+(136809757/312500000 : ℝ)*X 2 0+(531400521/1250000000 : ℝ)*X 2 1+(4508464531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-442423411/2000000000 : ℝ)*X 0 0+(1315972651/2500000000 : ℝ)*X 0 1+(1348733227/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312039361/10000000000 : ℝ)*X 1 0+(-26844691/125000000 : ℝ)*X 1 1+(269746649/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((16600123/31250000 : ℝ)*X 2 0+(5394932969/10000000000 : ℝ)*X 2 1+(-4194483/19531250 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4377922567/10000000000 : ℝ)*X 0 0+(4507814541/10000000000 : ℝ)*X 0 1+(4251856433/10000000000 : ℝ)*X 0 2+(4377922567/10000000000 : ℝ)*X 1 0+(4507814541/10000000000 : ℝ)*X 1 1+(4251856433/10000000000 : ℝ)*X 1 2+(4377922567/10000000000 : ℝ)*X 2 0+(4507814541/10000000000 : ℝ)*X 2 1+(4251856433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14502707657898036011864311863/1440500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2173196441/100000000000000 : ℝ)*(base19) + (224399041/12500000000000 : ℝ)*(base23) + (10271521/25000000000000 : ℝ)*(lower2) + (2810159/781250000000 : ℝ)*(upper3) + (91835473/100000000000000 : ℝ)*(upper5) + (5739897824398473/100000000000000 : ℝ)*(major0) + (5739897824398473/100000000000000 : ℝ)*(major1) + (2869948912199237/50000000000000 : ℝ)*(major2) + (303702771620129/4000000000000 : ℝ)*(sp0) + (379630895709127/5000000000000 : ℝ)*(sp1) + (7592618292186653/100000000000000 : ℝ)*(sp2) + (3887141745423697/100000000000000 : ℝ)*(sp3) + (12699218939/25000000000000 : ℝ)*(sp4) + (33480399959/100000000000000 : ℝ)*(sp7) + (485896903227957/12500000000000 : ℝ)*(f.failure) + (7592620087378981/100000000000000 : ℝ)*(f.sum) + (69416752607787/14405000000000000000000000000 : ℝ)*base65 + (20904020181879238267/2881000000000000000000000000000000 : ℝ)*base68 + (10967505234925283823/1440500000000000000000000000000000 : ℝ)*base70 + (23155374911333761733/2881000000000000000000000000000000 : ℝ)*base71 + (52133709758033/14405000000000000000000000000 : ℝ)*base74 + (38120585843066283823/1440500000000000000000000000000000 : ℝ)*base76 + (198239157924082831/67000000000000000000000000000000 : ℝ)*base77 + (440529846502082831/67000000000000000000000000000000 : ℝ)*base79 + (48629193668513/7202500000000000000000000000 : ℝ)*base81 + (2436963/1250000000000000000000 : ℝ)*base90 + (2436963/1250000000000000000000 : ℝ)*base92 + (14936963/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6848045759268257171407267539/1440500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (236537511/25000000000000 : ℝ)*(base19) + (956867707/100000000000000 : ℝ)*(base23) + (128337331/100000000000000 : ℝ)*(upper3) + (12624603/100000000000000 : ℝ)*(lower4) + (33611463/20000000000000 : ℝ)*(upper5) + (5769006693567653/100000000000000 : ℝ)*(major0) + (5769006693567653/100000000000000 : ℝ)*(major1) + (5769006693567653/100000000000000 : ℝ)*(major2) + (27578695063/100000000000000 : ℝ)*(sp1) + (3214627783/12500000000000 : ℝ)*(sp2) + (7631124886246781/100000000000000 : ℝ)*(sp4) + (7631096361401673/100000000000000 : ℝ)*(sp5) + (763109821235681/10000000000000 : ℝ)*(sp6) + (976722085605989/25000000000000 : ℝ)*(sp7) + (976722085605989/25000000000000 : ℝ)*(f.failure) + (7631124886246781/100000000000000 : ℝ)*(f.sum) + (86000239053031/14405000000000000000000000000 : ℝ)*base65 + (504900899281529709/67000000000000000000000000000000 : ℝ)*base68 + (952306007073529709/67000000000000000000000000000000 : ℝ)*base70 + (89135340094470291/67000000000000000000000000000000 : ℝ)*base71 + (11052957536253/7202500000000000000000000000 : ℝ)*base73 + (2015965392259470291/67000000000000000000000000000000 : ℝ)*base75 + (729657765981529709/67000000000000000000000000000000 : ℝ)*base78 + (174164682131529709/67000000000000000000000000000000 : ℝ)*base80 + (2068006416231/900312500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (25040851/2500000000000000000000 : ℝ)*base90 + (25040851/2500000000000000000000 : ℝ)*base92 + (25040851/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1049_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147662441/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11171/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2243/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1049_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1049_s7_0 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1106079449/5000000000 : ℝ)*x 0 + (2697381973/5000000000 : ℝ)*x 1 + (5264029529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1106079449/5000000000 : ℝ)^4121 ≤ (3358340444399/25000000000000 : ℝ)^3097 := by
    have hnat : (1106079449 : ℕ)^4121*25000000000000^3097 ≤ 3358340444399^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106079449 5000000000 3358340444399 25000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697381973/5000000000 : ℝ)^4121 ≤ (21994856605969/50000000000000 : ℝ)^3097 := by
    have hnat : (2697381973 : ℕ)^4121*50000000000000^3097 ≤ 21994856605969^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697381973 5000000000 21994856605969 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264029529/10000000000 : ℝ)^4121 ≤ (8515384997979/20000000000000 : ℝ)^3097 := by
    have hnat : (5264029529 : ℕ)^4121*20000000000000^3097 ≤ 8515384997979^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264029529 10000000000 8515384997979 20000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1106079449/5000000000 : ℝ), (2697381973/5000000000 : ℝ), (5264029529/10000000000 : ℝ)] ![(3358340444399/25000000000000 : ℝ), (21994856605969/50000000000000 : ℝ), (8515384997979/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1106079449/5000000000 : ℝ)|^4121 ≤ (3358340444399/25000000000000 : ℝ)^3097
        have hw : |(-1106079449/5000000000 : ℝ)|=(1106079449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697381973/5000000000 : ℝ)|^4121 ≤ (21994856605969/50000000000000 : ℝ)^3097
        have hw : |(2697381973/5000000000 : ℝ)|=(2697381973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264029529/10000000000 : ℝ)|^4121 ≤ (8515384997979/20000000000000 : ℝ)^3097
        have hw : |(5264029529/10000000000 : ℝ)|=(5264029529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s7_1 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345042759/10000000000 : ℝ)*x 0 + (-2278495613/10000000000 : ℝ)*x 1 + (1052805921/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345042759/10000000000 : ℝ)^4121 ≤ (21725524590469/50000000000000 : ℝ)^3097 := by
    have hnat : (5345042759 : ℕ)^4121*50000000000000^3097 ≤ 21725524590469^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345042759 10000000000 21725524590469 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2278495613/10000000000 : ℝ)^4121 ≤ (55888099969/400000000000 : ℝ)^3097 := by
    have hnat : (2278495613 : ℕ)^4121*400000000000^3097 ≤ 55888099969^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278495613 10000000000 55888099969 400000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052805921/2000000000 : ℝ)^4121 ≤ (42576925807853/100000000000000 : ℝ)^3097 := by
    have hnat : (1052805921 : ℕ)^4121*100000000000000^3097 ≤ 42576925807853^3097*2000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052805921 2000000000 42576925807853 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345042759/10000000000 : ℝ), (-2278495613/10000000000 : ℝ), (1052805921/2000000000 : ℝ)] ![(21725524590469/50000000000000 : ℝ), (55888099969/400000000000 : ℝ), (42576925807853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345042759/10000000000 : ℝ)|^4121 ≤ (21725524590469/50000000000000 : ℝ)^3097
        have hw : |(5345042759/10000000000 : ℝ)|=(5345042759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2278495613/10000000000 : ℝ)|^4121 ≤ (55888099969/400000000000 : ℝ)^3097
        have hw : |(-2278495613/10000000000 : ℝ)|=(2278495613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052805921/2000000000 : ℝ)|^4121 ≤ (42576925807853/100000000000000 : ℝ)^3097
        have hw : |(1052805921/2000000000 : ℝ)|=(1052805921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s7_2 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345042803/10000000000 : ℝ)*x 0 + (1052805913/2000000000 : ℝ)*x 1 + (-284811951/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345042803/10000000000 : ℝ)^4121 ≤ (4345104965689/10000000000000 : ℝ)^3097 := by
    have hnat : (5345042803 : ℕ)^4121*10000000000000^3097 ≤ 4345104965689^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345042803 10000000000 4345104965689 10000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052805913/2000000000 : ℝ)^4121 ≤ (42576925377349/100000000000000 : ℝ)^3097 := by
    have hnat : (1052805913 : ℕ)^4121*100000000000000^3097 ≤ 42576925377349^3097*2000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052805913 2000000000 42576925377349 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (284811951/1250000000 : ℝ)^4121 ≤ (13972024951451/100000000000000 : ℝ)^3097 := by
    have hnat : (284811951 : ℕ)^4121*100000000000000^3097 ≤ 13972024951451^3097*1250000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284811951 1250000000 13972024951451 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345042803/10000000000 : ℝ), (1052805913/2000000000 : ℝ), (-284811951/1250000000 : ℝ)] ![(4345104965689/10000000000000 : ℝ), (42576925377349/100000000000000 : ℝ), (13972024951451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345042803/10000000000 : ℝ)|^4121 ≤ (4345104965689/10000000000000 : ℝ)^3097
        have hw : |(5345042803/10000000000 : ℝ)|=(5345042803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052805913/2000000000 : ℝ)|^4121 ≤ (42576925377349/100000000000000 : ℝ)^3097
        have hw : |(1052805913/2000000000 : ℝ)|=(1052805913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-284811951/1250000000 : ℝ)|^4121 ≤ (13972024951451/100000000000000 : ℝ)^3097
        have hw : |(-284811951/1250000000 : ℝ)|=(284811951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s7_3 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (43779373/100000000 : ℝ)*x 0 + (2126076319/5000000000 : ℝ)*x 1 + (140859669/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43779373/100000000 : ℝ)^4121 ≤ (8329098316561/25000000000000 : ℝ)^3097 := by
    have hnat : (43779373 : ℕ)^4121*25000000000000^3097 ≤ 8329098316561^3097*100000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43779373 100000000 8329098316561 25000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126076319/5000000000 : ℝ)^4121 ≤ (8012188044399/25000000000000 : ℝ)^3097 := by
    have hnat : (2126076319 : ℕ)^4121*25000000000000^3097 ≤ 8012188044399^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126076319 5000000000 8012188044399 25000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140859669/312500000 : ℝ)^4121 ≤ (34634854547639/100000000000000 : ℝ)^3097 := by
    have hnat : (140859669 : ℕ)^4121*100000000000000^3097 ≤ 34634854547639^3097*312500000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140859669 312500000 34634854547639 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43779373/100000000 : ℝ), (2126076319/5000000000 : ℝ), (140859669/312500000 : ℝ)] ![(8329098316561/25000000000000 : ℝ), (8012188044399/25000000000000 : ℝ), (34634854547639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43779373/100000000 : ℝ)|^4121 ≤ (8329098316561/25000000000000 : ℝ)^3097
        have hw : |(43779373/100000000 : ℝ)|=(43779373/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2126076319/5000000000 : ℝ)|^4121 ≤ (8012188044399/25000000000000 : ℝ)^3097
        have hw : |(2126076319/5000000000 : ℝ)|=(2126076319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140859669/312500000 : ℝ)|^4121 ≤ (34634854547639/100000000000000 : ℝ)^3097
        have hw : |(140859669/312500000 : ℝ)|=(140859669/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s7_4 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2212163983/10000000000 : ℝ)*x 0 + (5264357371/10000000000 : ℝ)*x 1 + (67430437/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2212163983/10000000000 : ℝ)^4121 ≤ (13433402866157/100000000000000 : ℝ)^3097 := by
    have hnat : (2212163983 : ℕ)^4121*100000000000000^3097 ≤ 13433402866157^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212163983 10000000000 13433402866157 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264357371/10000000000 : ℝ)^4121 ≤ (42580453460037/100000000000000 : ℝ)^3097 := by
    have hnat : (5264357371 : ℕ)^4121*100000000000000^3097 ≤ 42580453460037^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264357371 10000000000 42580453460037 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67430437/125000000 : ℝ)^4121 ≤ (8797228732943/20000000000000 : ℝ)^3097 := by
    have hnat : (67430437 : ℕ)^4121*20000000000000^3097 ≤ 8797228732943^3097*125000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67430437 125000000 8797228732943 20000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2212163983/10000000000 : ℝ), (5264357371/10000000000 : ℝ), (67430437/125000000 : ℝ)] ![(13433402866157/100000000000000 : ℝ), (42580453460037/100000000000000 : ℝ), (8797228732943/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2212163983/10000000000 : ℝ)|^4121 ≤ (13433402866157/100000000000000 : ℝ)^3097
        have hw : |(-2212163983/10000000000 : ℝ)|=(2212163983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264357371/10000000000 : ℝ)|^4121 ≤ (42580453460037/100000000000000 : ℝ)^3097
        have hw : |(5264357371/10000000000 : ℝ)|=(5264357371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67430437/125000000 : ℝ)|^4121 ≤ (8797228732943/20000000000000 : ℝ)^3097
        have hw : |(67430437/125000000 : ℝ)|=(67430437/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s7_5 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312158221/10000000000 : ℝ)*x 0 + (-85923609/400000000 : ℝ)*x 1 + (67430437/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312158221/10000000000 : ℝ)^4121 ≤ (21547848216731/50000000000000 : ℝ)^3097 := by
    have hnat : (5312158221 : ℕ)^4121*50000000000000^3097 ≤ 21547848216731^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312158221 10000000000 21547848216731 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85923609/400000000 : ℝ)^4121 ≤ (2583631977641/20000000000000 : ℝ)^3097 := by
    have hnat : (85923609 : ℕ)^4121*20000000000000^3097 ≤ 2583631977641^3097*400000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85923609 400000000 2583631977641 20000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67430437/125000000 : ℝ)^4121 ≤ (8797228732943/20000000000000 : ℝ)^3097 := by
    have hnat : (67430437 : ℕ)^4121*20000000000000^3097 ≤ 8797228732943^3097*125000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67430437 125000000 8797228732943 20000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312158221/10000000000 : ℝ), (-85923609/400000000 : ℝ), (67430437/125000000 : ℝ)] ![(21547848216731/50000000000000 : ℝ), (2583631977641/20000000000000 : ℝ), (8797228732943/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312158221/10000000000 : ℝ)|^4121 ≤ (21547848216731/50000000000000 : ℝ)^3097
        have hw : |(5312158221/10000000000 : ℝ)|=(5312158221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-85923609/400000000 : ℝ)|^4121 ≤ (2583631977641/20000000000000 : ℝ)^3097
        have hw : |(-85923609/400000000 : ℝ)|=(85923609/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67430437/125000000 : ℝ)|^4121 ≤ (8797228732943/20000000000000 : ℝ)^3097
        have hw : |(67430437/125000000 : ℝ)|=(67430437/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s7_6 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312158221/10000000000 : ℝ)*x 0 + (67430437/125000000 : ℝ)*x 1 + (-85923609/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312158221/10000000000 : ℝ)^4121 ≤ (21547848216731/50000000000000 : ℝ)^3097 := by
    have hnat : (5312158221 : ℕ)^4121*50000000000000^3097 ≤ 21547848216731^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312158221 10000000000 21547848216731 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67430437/125000000 : ℝ)^4121 ≤ (8797228732943/20000000000000 : ℝ)^3097 := by
    have hnat : (67430437 : ℕ)^4121*20000000000000^3097 ≤ 8797228732943^3097*125000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67430437 125000000 8797228732943 20000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85923609/400000000 : ℝ)^4121 ≤ (2583631977641/20000000000000 : ℝ)^3097 := by
    have hnat : (85923609 : ℕ)^4121*20000000000000^3097 ≤ 2583631977641^3097*400000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85923609 400000000 2583631977641 20000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312158221/10000000000 : ℝ), (67430437/125000000 : ℝ), (-85923609/400000000 : ℝ)] ![(21547848216731/50000000000000 : ℝ), (8797228732943/20000000000000 : ℝ), (2583631977641/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312158221/10000000000 : ℝ)|^4121 ≤ (21547848216731/50000000000000 : ℝ)^3097
        have hw : |(5312158221/10000000000 : ℝ)|=(5312158221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67430437/125000000 : ℝ)|^4121 ≤ (8797228732943/20000000000000 : ℝ)^3097
        have hw : |(67430437/125000000 : ℝ)|=(67430437/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85923609/400000000 : ℝ)|^4121 ≤ (2583631977641/20000000000000 : ℝ)^3097
        have hw : |(-85923609/400000000 : ℝ)|=(85923609/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s7_7 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4377947257/10000000000 : ℝ)*x 0 + (4506869161/10000000000 : ℝ)*x 1 + (850559053/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377947257/10000000000 : ℝ)^4121 ≤ (16658247046817/50000000000000 : ℝ)^3097 := by
    have hnat : (4377947257 : ℕ)^4121*50000000000000^3097 ≤ 16658247046817^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377947257 10000000000 16658247046817 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4506869161/10000000000 : ℝ)^4121 ≤ (34628308555357/100000000000000 : ℝ)^3097 := by
    have hnat : (4506869161 : ℕ)^4121*100000000000000^3097 ≤ 34628308555357^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506869161 10000000000 34628308555357 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850559053/2000000000 : ℝ)^4121 ≤ (16027598667343/50000000000000 : ℝ)^3097 := by
    have hnat : (850559053 : ℕ)^4121*50000000000000^3097 ≤ 16027598667343^3097*2000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850559053 2000000000 16027598667343 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377947257/10000000000 : ℝ), (4506869161/10000000000 : ℝ), (850559053/2000000000 : ℝ)] ![(16658247046817/50000000000000 : ℝ), (34628308555357/100000000000000 : ℝ), (16027598667343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377947257/10000000000 : ℝ)|^4121 ≤ (16658247046817/50000000000000 : ℝ)^3097
        have hw : |(4377947257/10000000000 : ℝ)|=(4377947257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4506869161/10000000000 : ℝ)|^4121 ≤ (34628308555357/100000000000000 : ℝ)^3097
        have hw : |(4506869161/10000000000 : ℝ)|=(4506869161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(850559053/2000000000 : ℝ)|^4121 ≤ (16027598667343/50000000000000 : ℝ)^3097
        have hw : |(850559053/2000000000 : ℝ)|=(850559053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1049_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147662441/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2243/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (449/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2799/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2801/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2243/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2801/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2243/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2801/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2243/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2801/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2243/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2801/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2243/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2801/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2243/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2243/20000 : ℝ) ^ (8241/2048 : ℝ) ≤ (3002567729983327/20000000000000000000 : ℝ) := by
    have hpowers : (2243/20000 : ℝ)^8241 ≤ (3002567729983327/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2243 : ℕ)^8241*20000000000000000000^2048 ≤ 3002567729983327^2048*20000^8241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2243 20000 3002567729983327 20000000000000000000 8241 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2243/20000 : ℝ)) (X := (3002567729983327/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2801/20000 : ℝ) ^ (8241/2048 : ℝ) ≤ (18351713200876721/50000000000000000000 : ℝ) := by
    have hpowers : (2801/20000 : ℝ)^8241 ≤ (18351713200876721/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2801 : ℕ)^8241*50000000000000000000^2048 ≤ 18351713200876721^2048*20000^8241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2801 20000 18351713200876721 50000000000000000000 8241 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2801/20000 : ℝ)) (X := (18351713200876721/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10003002567729983327/10000000000000000000 : ℝ) ≤ (10000746094536659/10000000000000000 : ℝ) ^ (8241/2048 : ℝ) := by
    have hpowers : (10003002567729983327/10000000000000000000 : ℝ)^2048 ≤ (10000746094536659/10000000000000000 : ℝ)^8241 := by
      have hnat : (10003002567729983327 : ℕ)^2048*10000000000000000^8241 ≤ 10000746094536659^8241*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003002567729983327 10000000000000000000 10000746094536659 10000000000000000 2048 8241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000746094536659/10000000000000000 : ℝ)) (X := (10003002567729983327/10000000000000000000 : ℝ)) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051716265051670077/100000000000000000000 : ℝ) ≤ (1250160621186163/1250000000000000 : ℝ) ^ (8241/2048 : ℝ) := by
    have hpowers : (100051716265051670077/100000000000000000000 : ℝ)^2048 ≤ (1250160621186163/1250000000000000 : ℝ)^8241 := by
      have hnat : (100051716265051670077 : ℕ)^2048*1250000000000000^8241 ≤ 1250160621186163^8241*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051716265051670077 100000000000000000000 1250160621186163 1250000000000000 2048 8241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250160621186163/1250000000000000 : ℝ)) (X := (100051716265051670077/100000000000000000000 : ℝ)) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018351713200876721/25000000000000000000 : ℝ) ≤ (10001823844441949/10000000000000000 : ℝ) ^ (8241/2048 : ℝ) := by
    have hpowers : (25018351713200876721/25000000000000000000 : ℝ)^2048 ≤ (10001823844441949/10000000000000000 : ℝ)^8241 := by
      have hnat : (25018351713200876721 : ℕ)^2048*10000000000000000^8241 ≤ 10001823844441949^8241*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018351713200876721 25000000000000000000 10001823844441949 10000000000000000 2048 8241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001823844441949/10000000000000000 : ℝ)) (X := (25018351713200876721/25000000000000000000 : ℝ)) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3002567729983327/20000000000000000000 : ℝ) ≤ ((464833243976157521/465000000000000000 : ℝ)+2*(35924996843/18600000000000 : ℝ)*(2243/20000 : ℝ))^(8241/2048 : ℝ) := by
    rw [show (464833243976157521/465000000000000000 : ℝ)+2*(35924996843/18600000000000 : ℝ)*(2243/20000 : ℝ)=(10000746094536659/10000000000000000 : ℝ) by norm_num, show 1+2*(3002567729983327/20000000000000000000 : ℝ)=(10003002567729983327/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18351713200876721/50000000000000000000 : ℝ)+(3002567729983327/20000000000000000000 : ℝ) ≤ ((464833243976157521/465000000000000000 : ℝ)+(35924996843/18600000000000 : ℝ)*((2801/20000 : ℝ)+(2243/20000 : ℝ)))^(8241/2048 : ℝ) := by
    rw [show (464833243976157521/465000000000000000 : ℝ)+(35924996843/18600000000000 : ℝ)*((2801/20000 : ℝ)+(2243/20000 : ℝ))=(1250160621186163/1250000000000000 : ℝ) by norm_num, show 1+(18351713200876721/50000000000000000000 : ℝ)+(3002567729983327/20000000000000000000 : ℝ)=(100051716265051670077/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18351713200876721/50000000000000000000 : ℝ) ≤ ((464833243976157521/465000000000000000 : ℝ)+2*(35924996843/18600000000000 : ℝ)*(2801/20000 : ℝ))^(8241/2048 : ℝ) := by
    rw [show (464833243976157521/465000000000000000 : ℝ)+2*(35924996843/18600000000000 : ℝ)*(2801/20000 : ℝ)=(10001823844441949/10000000000000000 : ℝ) by norm_num, show 1+2*(18351713200876721/50000000000000000000 : ℝ)=(25018351713200876721/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (464833243976157521/465000000000000000 : ℝ)*(X 1 0+X 2 0)+(35924996843/18600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8241/2048 : ℝ)) (lo := (2243/20000 : ℝ)) (hi := (2801/20000 : ℝ)) (c := (464833243976157521/465000000000000000 : ℝ)) (alpha := (35924996843/18600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (464833243976157521/465000000000000000 : ℝ)*(X 0 1+X 2 1)+(35924996843/18600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8241/2048 : ℝ)) (lo := (2243/20000 : ℝ)) (hi := (2801/20000 : ℝ)) (c := (464833243976157521/465000000000000000 : ℝ)) (alpha := (35924996843/18600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (464833243976157521/465000000000000000 : ℝ)*(X 0 2+X 1 2)+(35924996843/18600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8241/2048 : ℝ)) (lo := (2243/20000 : ℝ)) (hi := (2801/20000 : ℝ)) (c := (464833243976157521/465000000000000000 : ℝ)) (alpha := (35924996843/18600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1106079449/5000000000 : ℝ)*X 0 0+(2697381973/5000000000 : ℝ)*X 0 1+(5264029529/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345042759/10000000000 : ℝ)*X 1 0+(-2278495613/10000000000 : ℝ)*X 1 1+(1052805921/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345042803/10000000000 : ℝ)*X 2 0+(1052805913/2000000000 : ℝ)*X 2 1+(-284811951/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((43779373/100000000 : ℝ)*X 0 0+(2126076319/5000000000 : ℝ)*X 0 1+(140859669/312500000 : ℝ)*X 0 2+(43779373/100000000 : ℝ)*X 1 0+(2126076319/5000000000 : ℝ)*X 1 1+(140859669/312500000 : ℝ)*X 1 2+(43779373/100000000 : ℝ)*X 2 0+(2126076319/5000000000 : ℝ)*X 2 1+(140859669/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2212163983/10000000000 : ℝ)*X 0 0+(5264357371/10000000000 : ℝ)*X 0 1+(67430437/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312158221/10000000000 : ℝ)*X 1 0+(-85923609/400000000 : ℝ)*X 1 1+(67430437/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312158221/10000000000 : ℝ)*X 2 0+(67430437/125000000 : ℝ)*X 2 1+(-85923609/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4377947257/10000000000 : ℝ)*X 0 0+(4506869161/10000000000 : ℝ)*X 0 1+(850559053/2000000000 : ℝ)*X 0 2+(4377947257/10000000000 : ℝ)*X 1 0+(4506869161/10000000000 : ℝ)*X 1 1+(850559053/2000000000 : ℝ)*X 1 2+(4377947257/10000000000 : ℝ)*X 2 0+(4506869161/10000000000 : ℝ)*X 2 1+(850559053/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (80352134291792333000387779/7750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1086977259/50000000000000 : ℝ)*(base19) + (2111562117/100000000000000 : ℝ)*(base23) + (1675139/2500000000000 : ℝ)*(lower2) + (279908909/100000000000000 : ℝ)*(upper3) + (41324529/20000000000000 : ℝ)*(upper5) + (57826862758907/1000000000000 : ℝ)*(major0) + (57826862758907/1000000000000 : ℝ)*(major1) + (5782686275890701/100000000000000 : ℝ)*(major2) + (1912289456901183/25000000000000 : ℝ)*(sp0) + (7649217599197841/100000000000000 : ℝ)*(sp1) + (3824608830795121/50000000000000 : ℝ)*(sp2) + (489514964986789/12500000000000 : ℝ)*(sp3) + (15486386907/25000000000000 : ℝ)*(sp4) + (32713134139/100000000000000 : ℝ)*(sp7) + (78323048660569/2000000000000 : ℝ)*(f.failure) + (7649219773152359/100000000000000 : ℝ)*(f.sum) + (1357067723863/1860000000000000000000000000 : ℝ)*base65 + (6490208624149703/465000000000000000000000000000 : ℝ)*base68 + (467318354644112221/46500000000000000000000000000000 : ℝ)*base69 + (2978406538495297/465000000000000000000000000000 : ℝ)*base71 + (4320497160677/1860000000000000000000000000 : ℝ)*base74 + (101843388233612221/46500000000000000000000000000000 : ℝ)*base75 + (10186189638970453/465000000000000000000000000000 : ℝ)*base78 + (6996251111089547/465000000000000000000000000000 : ℝ)*base79 + (22787107219/3720000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1011071/200000000000000000000 : ℝ)*base90 + (1011071/200000000000000000000 : ℝ)*base92 + (3011071/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (76502048034614974598170371/7750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (91996039/5000000000000 : ℝ)*(base19) + (2000385321/100000000000000 : ℝ)*(base23) + (24695097/12500000000000 : ℝ)*(upper3) + (18256791/25000000000000 : ℝ)*(lower4) + (25176561/12500000000000 : ℝ)*(upper5) + (5811790074273617/100000000000000 : ℝ)*(major0) + (5811790074273617/100000000000000 : ℝ)*(major1) + (5811790074273617/100000000000000 : ℝ)*(major2) + (49831289967/100000000000000 : ℝ)*(sp1) + (26772734071/50000000000000 : ℝ)*(sp2) + (960964712989589/12500000000000 : ℝ)*(sp4) + (1537533206541193/20000000000000 : ℝ)*(sp5) + (7687662158063249/100000000000000 : ℝ)*(sp6) + (1967931057794723/50000000000000 : ℝ)*(sp7) + (1967931057794723/50000000000000 : ℝ)*(f.failure) + (960964712989589/12500000000000 : ℝ)*(f.sum) + (8447925934049/930000000000000000000000000 : ℝ)*base66 + (293208440922301543/46500000000000000000000000000000 : ℝ)*base68 + (788064498390301543/46500000000000000000000000000000 : ℝ)*base70 + (550505862435301543/46500000000000000000000000000000 : ℝ)*base72 + (2982038965169/930000000000000000000000000 : ℝ)*base74 + (903522041437801543/46500000000000000000000000000000 : ℝ)*base76 + (489266052355801543/46500000000000000000000000000000 : ℝ)*base78 + (254293479909301543/46500000000000000000000000000000 : ℝ)*base80 + (3739843809839/930000000000000000000000000 : ℝ)*base82 + (25098843/5000000000000000000000 : ℝ)*base89 + (25098843/5000000000000000000000 : ℝ)*base91 + (25098843/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1049_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147662441/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2243/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (449/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1049_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1049_s8_0 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2212166719/10000000000 : ℝ)*x 0 + (1078931257/2000000000 : ℝ)*x 1 + (1052826439/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2212166719/10000000000 : ℝ)^4121 ≤ (13433424973997/100000000000000 : ℝ)^3097 := by
    have hnat : (2212166719 : ℕ)^4121*100000000000000^3097 ≤ 13433424973997^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212166719 10000000000 13433424973997 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078931257/2000000000 : ℝ)^4121 ≤ (4398854506609/10000000000000 : ℝ)^3097 := by
    have hnat : (1078931257 : ℕ)^4121*10000000000000^3097 ≤ 4398854506609^3097*2000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078931257 2000000000 4398854506609 10000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052826439/2000000000 : ℝ)^4121 ≤ (2128901497351/5000000000000 : ℝ)^3097 := by
    have hnat : (1052826439 : ℕ)^4121*5000000000000^3097 ≤ 2128901497351^3097*2000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052826439 2000000000 2128901497351 5000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2212166719/10000000000 : ℝ), (1078931257/2000000000 : ℝ), (1052826439/2000000000 : ℝ)] ![(13433424973997/100000000000000 : ℝ), (4398854506609/10000000000000 : ℝ), (2128901497351/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2212166719/10000000000 : ℝ)|^4121 ≤ (13433424973997/100000000000000 : ℝ)^3097
        have hw : |(-2212166719/10000000000 : ℝ)|=(2212166719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078931257/2000000000 : ℝ)|^4121 ≤ (4398854506609/10000000000000 : ℝ)^3097
        have hw : |(1078931257/2000000000 : ℝ)|=(1078931257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052826439/2000000000 : ℝ)|^4121 ≤ (2128901497351/5000000000000 : ℝ)^3097
        have hw : |(1052826439/2000000000 : ℝ)|=(1052826439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s8_1 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345016277/10000000000 : ℝ)*x 0 + (-1139197593/5000000000 : ℝ)*x 1 + (5264132359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345016277/10000000000 : ℝ)^4121 ≤ (43450762722963/100000000000000 : ℝ)^3097 := by
    have hnat : (5345016277 : ℕ)^4121*100000000000000^3097 ≤ 43450762722963^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345016277 10000000000 43450762722963 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1139197593/5000000000 : ℝ)^4121 ≤ (1746400693387/12500000000000 : ℝ)^3097 := by
    have hnat : (1139197593 : ℕ)^4121*12500000000000^3097 ≤ 1746400693387^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139197593 5000000000 1746400693387 12500000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264132359/10000000000 : ℝ)^4121 ≤ (42578031712099/100000000000000 : ℝ)^3097 := by
    have hnat : (5264132359 : ℕ)^4121*100000000000000^3097 ≤ 42578031712099^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264132359 10000000000 42578031712099 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345016277/10000000000 : ℝ), (-1139197593/5000000000 : ℝ), (5264132359/10000000000 : ℝ)] ![(43450762722963/100000000000000 : ℝ), (1746400693387/12500000000000 : ℝ), (42578031712099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345016277/10000000000 : ℝ)|^4121 ≤ (43450762722963/100000000000000 : ℝ)^3097
        have hw : |(5345016277/10000000000 : ℝ)|=(5345016277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1139197593/5000000000 : ℝ)|^4121 ≤ (1746400693387/12500000000000 : ℝ)^3097
        have hw : |(-1139197593/5000000000 : ℝ)|=(1139197593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264132359/10000000000 : ℝ)|^4121 ≤ (42578031712099/100000000000000 : ℝ)^3097
        have hw : |(5264132359/10000000000 : ℝ)|=(5264132359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s8_2 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672508131/5000000000 : ℝ)*x 0 + (526413229/1000000000 : ℝ)*x 1 + (-2278395297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672508131/5000000000 : ℝ)^4121 ≤ (43450762560707/100000000000000 : ℝ)^3097 := by
    have hnat : (2672508131 : ℕ)^4121*100000000000000^3097 ≤ 43450762560707^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672508131 5000000000 43450762560707 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526413229/1000000000 : ℝ)^4121 ≤ (21289015484737/50000000000000 : ℝ)^3097 := by
    have hnat : (526413229 : ℕ)^4121*50000000000000^3097 ≤ 21289015484737^3097*1000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526413229 1000000000 21289015484737 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2278395297/10000000000 : ℝ)^4121 ≤ (6985603226403/50000000000000 : ℝ)^3097 := by
    have hnat : (2278395297 : ℕ)^4121*50000000000000^3097 ≤ 6985603226403^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278395297 10000000000 6985603226403 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672508131/5000000000 : ℝ), (526413229/1000000000 : ℝ), (-2278395297/10000000000 : ℝ)] ![(43450762560707/100000000000000 : ℝ), (21289015484737/50000000000000 : ℝ), (6985603226403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672508131/5000000000 : ℝ)|^4121 ≤ (43450762560707/100000000000000 : ℝ)^3097
        have hw : |(2672508131/5000000000 : ℝ)|=(2672508131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526413229/1000000000 : ℝ)|^4121 ≤ (21289015484737/50000000000000 : ℝ)^3097
        have hw : |(526413229/1000000000 : ℝ)|=(526413229/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2278395297/10000000000 : ℝ)|^4121 ≤ (6985603226403/50000000000000 : ℝ)^3097
        have hw : |(-2278395297/10000000000 : ℝ)|=(2278395297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s8_3 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4377942603/10000000000 : ℝ)*x 0 + (4252357433/10000000000 : ℝ)*x 1 + (1126825817/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377942603/10000000000 : ℝ)^4121 ≤ (8329111741477/25000000000000 : ℝ)^3097 := by
    have hnat : (4377942603 : ℕ)^4121*25000000000000^3097 ≤ 8329111741477^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377942603 10000000000 8329111741477 25000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4252357433/10000000000 : ℝ)^4121 ≤ (32050806111649/100000000000000 : ℝ)^3097 := by
    have hnat : (4252357433 : ℕ)^4121*100000000000000^3097 ≤ 32050806111649^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252357433 10000000000 32050806111649 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126825817/2500000000 : ℝ)^4121 ≤ (8658186726071/25000000000000 : ℝ)^3097 := by
    have hnat : (1126825817 : ℕ)^4121*25000000000000^3097 ≤ 8658186726071^3097*2500000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126825817 2500000000 8658186726071 25000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377942603/10000000000 : ℝ), (4252357433/10000000000 : ℝ), (1126825817/2500000000 : ℝ)] ![(8329111741477/25000000000000 : ℝ), (32050806111649/100000000000000 : ℝ), (8658186726071/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377942603/10000000000 : ℝ)|^4121 ≤ (8329111741477/25000000000000 : ℝ)^3097
        have hw : |(4377942603/10000000000 : ℝ)|=(4377942603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4252357433/10000000000 : ℝ)|^4121 ≤ (32050806111649/100000000000000 : ℝ)^3097
        have hw : |(4252357433/10000000000 : ℝ)|=(4252357433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126825817/2500000000 : ℝ)|^4121 ≤ (8658186726071/25000000000000 : ℝ)^3097
        have hw : |(1126825817/2500000000 : ℝ)|=(1126825817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s8_4 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-442434369/2000000000 : ℝ)*x 0 + (5264458963/10000000000 : ℝ)*x 1 + (674291041/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (442434369/2000000000 : ℝ)^4121 ≤ (134334663939/1000000000000 : ℝ)^3097 := by
    have hnat : (442434369 : ℕ)^4121*1000000000000^3097 ≤ 134334663939^3097*2000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442434369 2000000000 134334663939 1000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264458963/10000000000 : ℝ)^4121 ≤ (8516309376113/20000000000000 : ℝ)^3097 := by
    have hnat : (5264458963 : ℕ)^4121*20000000000000^3097 ≤ 8516309376113^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264458963 10000000000 8516309376113 20000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674291041/1250000000 : ℝ)^4121 ≤ (21992493353519/50000000000000 : ℝ)^3097 := by
    have hnat : (674291041 : ℕ)^4121*50000000000000^3097 ≤ 21992493353519^3097*1250000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674291041 1250000000 21992493353519 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-442434369/2000000000 : ℝ), (5264458963/10000000000 : ℝ), (674291041/1250000000 : ℝ)] ![(134334663939/1000000000000 : ℝ), (8516309376113/20000000000000 : ℝ), (21992493353519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-442434369/2000000000 : ℝ)|^4121 ≤ (134334663939/1000000000000 : ℝ)^3097
        have hw : |(-442434369/2000000000 : ℝ)|=(442434369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264458963/10000000000 : ℝ)|^4121 ≤ (8516309376113/20000000000000 : ℝ)^3097
        have hw : |(5264458963/10000000000 : ℝ)|=(5264458963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674291041/1250000000 : ℝ)|^4121 ≤ (21992493353519/50000000000000 : ℝ)^3097
        have hw : |(674291041/1250000000 : ℝ)|=(674291041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s8_5 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531218471/1000000000 : ℝ)*x 0 + (-268524893/1250000000 : ℝ)*x 1 + (2697164137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531218471/1000000000 : ℝ)^4121 ≤ (43095982383549/100000000000000 : ℝ)^3097 := by
    have hnat : (531218471 : ℕ)^4121*100000000000000^3097 ≤ 43095982383549^3097*1000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531218471 1000000000 43095982383549 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268524893/1250000000 : ℝ)^4121 ≤ (12919031487423/100000000000000 : ℝ)^3097 := by
    have hnat : (268524893 : ℕ)^4121*100000000000000^3097 ≤ 12919031487423^3097*1250000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268524893 1250000000 12919031487423 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697164137/5000000000 : ℝ)^4121 ≤ (2199249306057/5000000000000 : ℝ)^3097 := by
    have hnat : (2697164137 : ℕ)^4121*5000000000000^3097 ≤ 2199249306057^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697164137 5000000000 2199249306057 5000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531218471/1000000000 : ℝ), (-268524893/1250000000 : ℝ), (2697164137/5000000000 : ℝ)] ![(43095982383549/100000000000000 : ℝ), (12919031487423/100000000000000 : ℝ), (2199249306057/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531218471/1000000000 : ℝ)|^4121 ≤ (43095982383549/100000000000000 : ℝ)^3097
        have hw : |(531218471/1000000000 : ℝ)|=(531218471/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-268524893/1250000000 : ℝ)|^4121 ≤ (12919031487423/100000000000000 : ℝ)^3097
        have hw : |(-268524893/1250000000 : ℝ)|=(268524893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697164137/5000000000 : ℝ)|^4121 ≤ (2199249306057/5000000000000 : ℝ)^3097
        have hw : |(2697164137/5000000000 : ℝ)|=(2697164137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s8_6 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656092347/5000000000 : ℝ)*x 0 + (5394328251/10000000000 : ℝ)*x 1 + (-429639839/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656092347/5000000000 : ℝ)^4121 ≤ (10773995552707/25000000000000 : ℝ)^3097 := by
    have hnat : (2656092347 : ℕ)^4121*25000000000000^3097 ≤ 10773995552707^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656092347 5000000000 10773995552707 25000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394328251/10000000000 : ℝ)^4121 ≤ (43984985871591/100000000000000 : ℝ)^3097 := by
    have hnat : (5394328251 : ℕ)^4121*100000000000000^3097 ≤ 43984985871591^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394328251 10000000000 43984985871591 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429639839/2000000000 : ℝ)^4121 ≤ (6459515947771/50000000000000 : ℝ)^3097 := by
    have hnat : (429639839 : ℕ)^4121*50000000000000^3097 ≤ 6459515947771^3097*2000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429639839 2000000000 6459515947771 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656092347/5000000000 : ℝ), (5394328251/10000000000 : ℝ), (-429639839/2000000000 : ℝ)] ![(10773995552707/25000000000000 : ℝ), (43984985871591/100000000000000 : ℝ), (6459515947771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656092347/5000000000 : ℝ)|^4121 ≤ (10773995552707/25000000000000 : ℝ)^3097
        have hw : |(2656092347/5000000000 : ℝ)|=(2656092347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394328251/10000000000 : ℝ)|^4121 ≤ (43984985871591/100000000000000 : ℝ)^3097
        have hw : |(5394328251/10000000000 : ℝ)|=(5394328251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-429639839/2000000000 : ℝ)|^4121 ≤ (6459515947771/50000000000000 : ℝ)^3097
        have hw : |(-429639839/2000000000 : ℝ)|=(429639839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s8_7 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (175118097/400000000 : ℝ)*x 0 + (1126666287/2500000000 : ℝ)*x 1 + (4252998009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (175118097/400000000 : ℝ)^4121 ≤ (33316546426289/100000000000000 : ℝ)^3097 := by
    have hnat : (175118097 : ℕ)^4121*100000000000000^3097 ≤ 33316546426289^3097*400000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175118097 400000000 33316546426289 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126666287/2500000000 : ℝ)^4121 ≤ (17313111378479/50000000000000 : ℝ)^3097 := by
    have hnat : (1126666287 : ℕ)^4121*50000000000000^3097 ≤ 17313111378479^3097*2500000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126666287 2500000000 17313111378479 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4252998009/10000000000 : ℝ)^4121 ≤ (32057230800247/100000000000000 : ℝ)^3097 := by
    have hnat : (4252998009 : ℕ)^4121*100000000000000^3097 ≤ 32057230800247^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252998009 10000000000 32057230800247 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(175118097/400000000 : ℝ), (1126666287/2500000000 : ℝ), (4252998009/10000000000 : ℝ)] ![(33316546426289/100000000000000 : ℝ), (17313111378479/50000000000000 : ℝ), (32057230800247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(175118097/400000000 : ℝ)|^4121 ≤ (33316546426289/100000000000000 : ℝ)^3097
        have hw : |(175118097/400000000 : ℝ)|=(175118097/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126666287/2500000000 : ℝ)|^4121 ≤ (17313111378479/50000000000000 : ℝ)^3097
        have hw : |(1126666287/2500000000 : ℝ)|=(1126666287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4252998009/10000000000 : ℝ)|^4121 ≤ (32057230800247/100000000000000 : ℝ)^3097
        have hw : |(4252998009/10000000000 : ℝ)|=(4252998009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1049_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147662441/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (449/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (2807/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1749/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2799/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (449/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2799/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (449/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2799/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (449/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2799/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (449/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2799/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (449/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2799/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (449/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (449/4000 : ℝ) ^ (8241/2048 : ℝ) ≤ (15066777161427933/100000000000000000000 : ℝ) := by
    have hpowers : (449/4000 : ℝ)^8241 ≤ (15066777161427933/100000000000000000000 : ℝ)^2048 := by
      have hnat : (449 : ℕ)^8241*100000000000000000000^2048 ≤ 15066777161427933^2048*4000^8241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        449 4000 15066777161427933 100000000000000000000 8241 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (449/4000 : ℝ)) (X := (15066777161427933/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2799/20000 : ℝ) ^ (8241/2048 : ℝ) ≤ (731961673423159/2000000000000000000 : ℝ) := by
    have hpowers : (2799/20000 : ℝ)^8241 ≤ (731961673423159/2000000000000000000 : ℝ)^2048 := by
      have hnat : (2799 : ℕ)^8241*2000000000000000000^2048 ≤ 731961673423159^2048*20000^8241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2799 20000 731961673423159 2000000000000000000 8241 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2799/20000 : ℝ)) (X := (731961673423159/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015066777161427933/50000000000000000000 : ℝ) ≤ (5000374387410399/5000000000000000 : ℝ) ^ (8241/2048 : ℝ) := by
    have hpowers : (50015066777161427933/50000000000000000000 : ℝ)^2048 ≤ (5000374387410399/5000000000000000 : ℝ)^8241 := by
      have hnat : (50015066777161427933 : ℕ)^2048*5000000000000000^8241 ≤ 5000374387410399^8241*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015066777161427933 50000000000000000000 5000374387410399 5000000000000000 2048 8241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000374387410399/5000000000000000 : ℝ)) (X := (50015066777161427933/50000000000000000000 : ℝ)) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051664860832585883/100000000000000000000 : ℝ) ≤ (10001283692520913/10000000000000000 : ℝ) ^ (8241/2048 : ℝ) := by
    have hpowers : (100051664860832585883/100000000000000000000 : ℝ)^2048 ≤ (10001283692520913/10000000000000000 : ℝ)^8241 := by
      have hnat : (100051664860832585883 : ℕ)^2048*10000000000000000^8241 ≤ 10001283692520913^8241*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051664860832585883 100000000000000000000 10001283692520913 10000000000000000 2048 8241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001283692520913/10000000000000000 : ℝ)) (X := (100051664860832585883/100000000000000000000 : ℝ)) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000731961673423159/1000000000000000000 : ℝ) ≤ (2500454652555257/2500000000000000 : ℝ) ^ (8241/2048 : ℝ) := by
    have hpowers : (1000731961673423159/1000000000000000000 : ℝ)^2048 ≤ (2500454652555257/2500000000000000 : ℝ)^8241 := by
      have hnat : (1000731961673423159 : ℕ)^2048*2500000000000000^8241 ≤ 2500454652555257^8241*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000731961673423159 1000000000000000000 2500454652555257 2500000000000000 2048 8241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500454652555257/2500000000000000 : ℝ)) (X := (1000731961673423159/1000000000000000000 : ℝ)) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15066777161427933/100000000000000000000 : ℝ) ≤ ((2769006520388602871/2770000000000000000 : ℝ)+2*(106983540023/55400000000000 : ℝ)*(449/4000 : ℝ))^(8241/2048 : ℝ) := by
    rw [show (2769006520388602871/2770000000000000000 : ℝ)+2*(106983540023/55400000000000 : ℝ)*(449/4000 : ℝ)=(5000374387410399/5000000000000000 : ℝ) by norm_num, show 1+2*(15066777161427933/100000000000000000000 : ℝ)=(50015066777161427933/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(731961673423159/2000000000000000000 : ℝ)+(15066777161427933/100000000000000000000 : ℝ) ≤ ((2769006520388602871/2770000000000000000 : ℝ)+(106983540023/55400000000000 : ℝ)*((2799/20000 : ℝ)+(449/4000 : ℝ)))^(8241/2048 : ℝ) := by
    rw [show (2769006520388602871/2770000000000000000 : ℝ)+(106983540023/55400000000000 : ℝ)*((2799/20000 : ℝ)+(449/4000 : ℝ))=(10001283692520913/10000000000000000 : ℝ) by norm_num, show 1+(731961673423159/2000000000000000000 : ℝ)+(15066777161427933/100000000000000000000 : ℝ)=(100051664860832585883/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(731961673423159/2000000000000000000 : ℝ) ≤ ((2769006520388602871/2770000000000000000 : ℝ)+2*(106983540023/55400000000000 : ℝ)*(2799/20000 : ℝ))^(8241/2048 : ℝ) := by
    rw [show (2769006520388602871/2770000000000000000 : ℝ)+2*(106983540023/55400000000000 : ℝ)*(2799/20000 : ℝ)=(2500454652555257/2500000000000000 : ℝ) by norm_num, show 1+2*(731961673423159/2000000000000000000 : ℝ)=(1000731961673423159/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2769006520388602871/2770000000000000000 : ℝ)*(X 1 0+X 2 0)+(106983540023/55400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8241/2048 : ℝ)) (lo := (449/4000 : ℝ)) (hi := (2799/20000 : ℝ)) (c := (2769006520388602871/2770000000000000000 : ℝ)) (alpha := (106983540023/55400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2769006520388602871/2770000000000000000 : ℝ)*(X 0 1+X 2 1)+(106983540023/55400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8241/2048 : ℝ)) (lo := (449/4000 : ℝ)) (hi := (2799/20000 : ℝ)) (c := (2769006520388602871/2770000000000000000 : ℝ)) (alpha := (106983540023/55400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2769006520388602871/2770000000000000000 : ℝ)*(X 0 2+X 1 2)+(106983540023/55400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8241/2048 : ℝ)) (lo := (449/4000 : ℝ)) (hi := (2799/20000 : ℝ)) (c := (2769006520388602871/2770000000000000000 : ℝ)) (alpha := (106983540023/55400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2212166719/10000000000 : ℝ)*X 0 0+(1078931257/2000000000 : ℝ)*X 0 1+(1052826439/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345016277/10000000000 : ℝ)*X 1 0+(-1139197593/5000000000 : ℝ)*X 1 1+(5264132359/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672508131/5000000000 : ℝ)*X 2 0+(526413229/1000000000 : ℝ)*X 2 1+(-2278395297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4377942603/10000000000 : ℝ)*X 0 0+(4252357433/10000000000 : ℝ)*X 0 1+(1126825817/2500000000 : ℝ)*X 0 2+(4377942603/10000000000 : ℝ)*X 1 0+(4252357433/10000000000 : ℝ)*X 1 1+(1126825817/2500000000 : ℝ)*X 1 2+(4377942603/10000000000 : ℝ)*X 2 0+(4252357433/10000000000 : ℝ)*X 2 1+(1126825817/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-442434369/2000000000 : ℝ)*X 0 0+(5264458963/10000000000 : ℝ)*X 0 1+(674291041/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531218471/1000000000 : ℝ)*X 1 0+(-268524893/1250000000 : ℝ)*X 1 1+(2697164137/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656092347/5000000000 : ℝ)*X 2 0+(5394328251/10000000000 : ℝ)*X 2 1+(-429639839/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((175118097/400000000 : ℝ)*X 0 0+(1126666287/2500000000 : ℝ)*X 0 1+(4252998009/10000000000 : ℝ)*X 0 2+(175118097/400000000 : ℝ)*X 1 0+(1126666287/2500000000 : ℝ)*X 1 1+(4252998009/10000000000 : ℝ)*X 1 2+(175118097/400000000 : ℝ)*X 2 0+(1126666287/2500000000 : ℝ)*X 2 1+(4252998009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7207404709318035085565169/1731250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (357437331/100000000000000 : ℝ)*(base19) + (380981889/100000000000000 : ℝ)*(base23) + (15402167/100000000000000 : ℝ)*(lower2) + (144286929/100000000000000 : ℝ)*(upper3) + (39478949/100000000000000 : ℝ)*(lower4) + (72399167697663/1250000000000 : ℝ)*(major0) + (72399167697663/1250000000000 : ℝ)*(major1) + (72399167697663/1250000000000 : ℝ)*(major2) + (7661440338998153/100000000000000 : ℝ)*(sp0) + (7661451551679581/100000000000000 : ℝ)*(sp1) + (3830725764067511/50000000000000 : ℝ)*(sp2) + (784481400220929/20000000000000 : ℝ)*(sp3) + (5785059379/50000000000000 : ℝ)*(sp4) + (7782633787/100000000000000 : ℝ)*(sp7) + (61287730995913/1562500000000 : ℝ)*(f.failure) + (7661451909116911/100000000000000 : ℝ)*(f.sum) + (1216831812369/277000000000000000000000000 : ℝ)*base66 + (2386597293740473/3462500000000000000000000000000 : ℝ)*base67 + (27333498202684527/3462500000000000000000000000000 : ℝ)*base70 + (55758171562247027/3462500000000000000000000000000 : ℝ)*base72 + (482674319477/277000000000000000000000000 : ℝ)*base73 + (17933673280684527/3462500000000000000000000000000 : ℝ)*base76 + (41867271913234527/3462500000000000000000000000000 : ℝ)*base78 + (45398842826027973/3462500000000000000000000000000 : ℝ)*base79 + (422557169301/277000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (396367/156250000000000000000 : ℝ)*base90 + (396367/156250000000000000000 : ℝ)*base92 + (396367/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56194610982533172934088979/17312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (504570299/100000000000000 : ℝ)*(base19) + (515593437/100000000000000 : ℝ)*(base23) + (26802867/100000000000000 : ℝ)*(upper2) + (19493139/100000000000000 : ℝ)*(upper3) + (18546167/50000000000000 : ℝ)*(upper5) + (727638646955261/12500000000000 : ℝ)*(major0) + (727638646955261/12500000000000 : ℝ)*(major1) + (727638646955261/12500000000000 : ℝ)*(major2) + (6579128611/50000000000000 : ℝ)*(sp1) + (2632643037/25000000000000 : ℝ)*(sp2) + (385002252151863/5000000000000 : ℝ)*(sp4) + (3850015690104869/50000000000000 : ℝ)*(sp5) + (3850016998435837/50000000000000 : ℝ)*(sp6) + (1971086600025151/50000000000000 : ℝ)*(sp7) + (1971086600025151/50000000000000 : ℝ)*(f.failure) + (385002252151863/5000000000000 : ℝ)*(f.sum) + (2019601500619/692500000000000000000000000 : ℝ)*base66 + (433781263748195669/34625000000000000000000000000000 : ℝ)*base68 + (462420083297445669/34625000000000000000000000000000 : ℝ)*base70 + (207996996897695669/34625000000000000000000000000000 : ℝ)*base72 + (52264955997/21640625000000000000000000 : ℝ)*base74 + (231875671236195669/34625000000000000000000000000000 : ℝ)*base76 + (359991053905945669/34625000000000000000000000000000 : ℝ)*base78 + (398857093845445669/34625000000000000000000000000000 : ℝ)*base80 + (587743165363/86562500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (58053591/5000000000000000000000 : ℝ)*base89 + (58053591/5000000000000000000000 : ℝ)*base91 + (58053591/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1049_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147662441/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (449/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2807/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1749/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1049_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1049_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147662441/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11171/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2807/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1749/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1049_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1049_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1049_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147662441/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11171/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2807/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1749/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1049_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

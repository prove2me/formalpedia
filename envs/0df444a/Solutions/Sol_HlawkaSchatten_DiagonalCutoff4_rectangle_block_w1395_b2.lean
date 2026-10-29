-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1395_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:43:59.168392+00:00
-- url     : https://prove2.me/submissions/5ed74edd-3815-4b0a-a998-240c3a0da962

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
theorem support_rectangle_w1395_s6_0 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-249881427/1250000000 : ℝ)*x 0 + (1352494441/2500000000 : ℝ)*x 1 + (2623045701/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (249881427/1250000000 : ℝ)^4355 ≤ (6093357154091/50000000000000 : ℝ)^3331 := by
    have hnat : (249881427 : ℕ)^4355*50000000000000^3331 ≤ 6093357154091^3331*1250000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249881427 1250000000 6093357154091 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352494441/2500000000 : ℝ)^4355 ≤ (22394724393901/50000000000000 : ℝ)^3331 := by
    have hnat : (1352494441 : ℕ)^4355*50000000000000^3331 ≤ 22394724393901^3331*2500000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352494441 2500000000 22394724393901 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623045701/5000000000 : ℝ)^4355 ≤ (8604767376199/20000000000000 : ℝ)^3331 := by
    have hnat : (2623045701 : ℕ)^4355*20000000000000^3331 ≤ 8604767376199^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623045701 5000000000 8604767376199 20000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-249881427/1250000000 : ℝ), (1352494441/2500000000 : ℝ), (2623045701/5000000000 : ℝ)] ![(6093357154091/50000000000000 : ℝ), (22394724393901/50000000000000 : ℝ), (8604767376199/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-249881427/1250000000 : ℝ)|^4355 ≤ (6093357154091/50000000000000 : ℝ)^3331
        have hw : |(-249881427/1250000000 : ℝ)|=(249881427/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352494441/2500000000 : ℝ)|^4355 ≤ (22394724393901/50000000000000 : ℝ)^3331
        have hw : |(1352494441/2500000000 : ℝ)|=(1352494441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623045701/5000000000 : ℝ)|^4355 ≤ (8604767376199/20000000000000 : ℝ)^3331
        have hw : |(2623045701/5000000000 : ℝ)|=(2623045701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s6_1 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674010601/5000000000 : ℝ)*x 0 + (-2082512841/10000000000 : ℝ)*x 1 + (2623045701/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674010601/5000000000 : ℝ)^4355 ≤ (44120005367953/100000000000000 : ℝ)^3331 := by
    have hnat : (2674010601 : ℕ)^4355*100000000000000^3331 ≤ 44120005367953^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674010601 5000000000 44120005367953 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2082512841/10000000000 : ℝ)^4355 ≤ (12856157733729/100000000000000 : ℝ)^3331 := by
    have hnat : (2082512841 : ℕ)^4355*100000000000000^3331 ≤ 12856157733729^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082512841 10000000000 12856157733729 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623045701/5000000000 : ℝ)^4355 ≤ (8604767376199/20000000000000 : ℝ)^3331 := by
    have hnat : (2623045701 : ℕ)^4355*20000000000000^3331 ≤ 8604767376199^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623045701 5000000000 8604767376199 20000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674010601/5000000000 : ℝ), (-2082512841/10000000000 : ℝ), (2623045701/5000000000 : ℝ)] ![(44120005367953/100000000000000 : ℝ), (12856157733729/100000000000000 : ℝ), (8604767376199/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674010601/5000000000 : ℝ)|^4355 ≤ (44120005367953/100000000000000 : ℝ)^3331
        have hw : |(2674010601/5000000000 : ℝ)|=(2674010601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2082512841/10000000000 : ℝ)|^4355 ≤ (12856157733729/100000000000000 : ℝ)^3331
        have hw : |(-2082512841/10000000000 : ℝ)|=(2082512841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623045701/5000000000 : ℝ)|^4355 ≤ (8604767376199/20000000000000 : ℝ)^3331
        have hw : |(2623045701/5000000000 : ℝ)|=(2623045701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s6_2 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674010601/5000000000 : ℝ)*x 0 + (2623045701/5000000000 : ℝ)*x 1 + (-2082512841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674010601/5000000000 : ℝ)^4355 ≤ (44120005367953/100000000000000 : ℝ)^3331 := by
    have hnat : (2674010601 : ℕ)^4355*100000000000000^3331 ≤ 44120005367953^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674010601 5000000000 44120005367953 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623045701/5000000000 : ℝ)^4355 ≤ (8604767376199/20000000000000 : ℝ)^3331 := by
    have hnat : (2623045701 : ℕ)^4355*20000000000000^3331 ≤ 8604767376199^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623045701 5000000000 8604767376199 20000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2082512841/10000000000 : ℝ)^4355 ≤ (12856157733729/100000000000000 : ℝ)^3331 := by
    have hnat : (2082512841 : ℕ)^4355*100000000000000^3331 ≤ 12856157733729^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082512841 10000000000 12856157733729 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674010601/5000000000 : ℝ), (2623045701/5000000000 : ℝ), (-2082512841/10000000000 : ℝ)] ![(44120005367953/100000000000000 : ℝ), (8604767376199/20000000000000 : ℝ), (12856157733729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674010601/5000000000 : ℝ)|^4355 ≤ (44120005367953/100000000000000 : ℝ)^3331
        have hw : |(2674010601/5000000000 : ℝ)|=(2674010601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623045701/5000000000 : ℝ)|^4355 ≤ (8604767376199/20000000000000 : ℝ)^3331
        have hw : |(2623045701/5000000000 : ℝ)|=(2623045701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2082512841/10000000000 : ℝ)|^4355 ≤ (12856157733729/100000000000000 : ℝ)^3331
        have hw : |(-2082512841/10000000000 : ℝ)|=(2082512841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s6_3 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2156474377/5000000000 : ℝ)*x 0 + (414112771/1000000000 : ℝ)*x 1 + (4491256993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156474377/5000000000 : ℝ)^4355 ≤ (33304151164889/100000000000000 : ℝ)^3331 := by
    have hnat : (2156474377 : ℕ)^4355*100000000000000^3331 ≤ 33304151164889^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156474377 5000000000 33304151164889 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (414112771/1000000000 : ℝ)^4355 ≤ (31580214313133/100000000000000 : ℝ)^3331 := by
    have hnat : (414112771 : ℕ)^4355*100000000000000^3331 ≤ 31580214313133^3331*1000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414112771 1000000000 31580214313133 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491256993/10000000000 : ℝ)^4355 ≤ (548681789147/1562500000000 : ℝ)^3331 := by
    have hnat : (4491256993 : ℕ)^4355*1562500000000^3331 ≤ 548681789147^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491256993 10000000000 548681789147 1562500000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2156474377/5000000000 : ℝ), (414112771/1000000000 : ℝ), (4491256993/10000000000 : ℝ)] ![(33304151164889/100000000000000 : ℝ), (31580214313133/100000000000000 : ℝ), (548681789147/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2156474377/5000000000 : ℝ)|^4355 ≤ (33304151164889/100000000000000 : ℝ)^3331
        have hw : |(2156474377/5000000000 : ℝ)|=(2156474377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(414112771/1000000000 : ℝ)|^4355 ≤ (31580214313133/100000000000000 : ℝ)^3331
        have hw : |(414112771/1000000000 : ℝ)|=(414112771/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491256993/10000000000 : ℝ)|^4355 ≤ (548681789147/1562500000000 : ℝ)^3331
        have hw : |(4491256993/10000000000 : ℝ)|=(4491256993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s6_4 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-399812621/2000000000 : ℝ)*x 0 + (5246680723/10000000000 : ℝ)*x 1 + (5409385363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399812621/2000000000 : ℝ)^4355 ≤ (12186807473429/100000000000000 : ℝ)^3331 := by
    have hnat : (399812621 : ℕ)^4355*100000000000000^3331 ≤ 12186807473429^3331*2000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399812621 2000000000 12186807473429 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246680723/10000000000 : ℝ)^4355 ≤ (21515077925019/50000000000000 : ℝ)^3331 := by
    have hnat : (5246680723 : ℕ)^4355*50000000000000^3331 ≤ 21515077925019^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246680723 10000000000 21515077925019 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409385363/10000000000 : ℝ)^4355 ≤ (11195759164751/25000000000000 : ℝ)^3331 := by
    have hnat : (5409385363 : ℕ)^4355*25000000000000^3331 ≤ 11195759164751^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409385363 10000000000 11195759164751 25000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-399812621/2000000000 : ℝ), (5246680723/10000000000 : ℝ), (5409385363/10000000000 : ℝ)] ![(12186807473429/100000000000000 : ℝ), (21515077925019/50000000000000 : ℝ), (11195759164751/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-399812621/2000000000 : ℝ)|^4355 ≤ (12186807473429/100000000000000 : ℝ)^3331
        have hw : |(-399812621/2000000000 : ℝ)|=(399812621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246680723/10000000000 : ℝ)|^4355 ≤ (21515077925019/50000000000000 : ℝ)^3331
        have hw : |(5246680723/10000000000 : ℝ)|=(5246680723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409385363/10000000000 : ℝ)|^4355 ≤ (11195759164751/25000000000000 : ℝ)^3331
        have hw : |(5409385363/10000000000 : ℝ)|=(5409385363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s6_5 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326390339/2500000000 : ℝ)*x 0 + (-191921889/1000000000 : ℝ)*x 1 + (5409385359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326390339/2500000000 : ℝ)^4355 ≤ (43662598067999/100000000000000 : ℝ)^3331 := by
    have hnat : (1326390339 : ℕ)^4355*100000000000000^3331 ≤ 43662598067999^3331*2500000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326390339 2500000000 43662598067999 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (191921889/1000000000 : ℝ)^4355 ≤ (11554365300379/100000000000000 : ℝ)^3331 := by
    have hnat : (191921889 : ℕ)^4355*100000000000000^3331 ≤ 11554365300379^3331*1000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191921889 1000000000 11554365300379 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409385359/10000000000 : ℝ)^4355 ≤ (44783036615709/100000000000000 : ℝ)^3331 := by
    have hnat : (5409385359 : ℕ)^4355*100000000000000^3331 ≤ 44783036615709^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409385359 10000000000 44783036615709 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326390339/2500000000 : ℝ), (-191921889/1000000000 : ℝ), (5409385359/10000000000 : ℝ)] ![(43662598067999/100000000000000 : ℝ), (11554365300379/100000000000000 : ℝ), (44783036615709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326390339/2500000000 : ℝ)|^4355 ≤ (43662598067999/100000000000000 : ℝ)^3331
        have hw : |(1326390339/2500000000 : ℝ)|=(1326390339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-191921889/1000000000 : ℝ)|^4355 ≤ (11554365300379/100000000000000 : ℝ)^3331
        have hw : |(-191921889/1000000000 : ℝ)|=(191921889/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409385359/10000000000 : ℝ)|^4355 ≤ (44783036615709/100000000000000 : ℝ)^3331
        have hw : |(5409385359/10000000000 : ℝ)|=(5409385359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s6_6 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305561369/10000000000 : ℝ)*x 0 + (1081877069/2000000000 : ℝ)*x 1 + (-1919218891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305561369/10000000000 : ℝ)^4355 ≤ (341114048499/781250000000 : ℝ)^3331 := by
    have hnat : (5305561369 : ℕ)^4355*781250000000^3331 ≤ 341114048499^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305561369 10000000000 341114048499 781250000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081877069/2000000000 : ℝ)^4355 ≤ (2798939779011/6250000000000 : ℝ)^3331 := by
    have hnat : (1081877069 : ℕ)^4355*6250000000000^3331 ≤ 2798939779011^3331*2000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081877069 2000000000 2798939779011 6250000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1919218891/10000000000 : ℝ)^4355 ≤ (46217461233/400000000000 : ℝ)^3331 := by
    have hnat : (1919218891 : ℕ)^4355*400000000000^3331 ≤ 46217461233^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919218891 10000000000 46217461233 400000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305561369/10000000000 : ℝ), (1081877069/2000000000 : ℝ), (-1919218891/10000000000 : ℝ)] ![(341114048499/781250000000 : ℝ), (2798939779011/6250000000000 : ℝ), (46217461233/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305561369/10000000000 : ℝ)|^4355 ≤ (341114048499/781250000000 : ℝ)^3331
        have hw : |(5305561369/10000000000 : ℝ)|=(5305561369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081877069/2000000000 : ℝ)|^4355 ≤ (2798939779011/6250000000000 : ℝ)^3331
        have hw : |(1081877069/2000000000 : ℝ)|=(1081877069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1919218891/10000000000 : ℝ)|^4355 ≤ (46217461233/400000000000 : ℝ)^3331
        have hw : |(-1919218891/10000000000 : ℝ)|=(1919218891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s6_7 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4312973629/10000000000 : ℝ)*x 0 + (2244998959/5000000000 : ℝ)*x 1 + (4142393293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312973629/10000000000 : ℝ)^4355 ≤ (13009532147/39062500000 : ℝ)^3331 := by
    have hnat : (4312973629 : ℕ)^4355*39062500000^3331 ≤ 13009532147^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312973629 10000000000 13009532147 39062500000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244998959/5000000000 : ℝ)^4355 ≤ (17551382245611/50000000000000 : ℝ)^3331 := by
    have hnat : (2244998959 : ℕ)^4355*50000000000000^3331 ≤ 17551382245611^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244998959 5000000000 17551382245611 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4142393293/10000000000 : ℝ)^4355 ≤ (123409504683/390625000000 : ℝ)^3331 := by
    have hnat : (4142393293 : ℕ)^4355*390625000000^3331 ≤ 123409504683^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4142393293 10000000000 123409504683 390625000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312973629/10000000000 : ℝ), (2244998959/5000000000 : ℝ), (4142393293/10000000000 : ℝ)] ![(13009532147/39062500000 : ℝ), (17551382245611/50000000000000 : ℝ), (123409504683/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312973629/10000000000 : ℝ)|^4355 ≤ (13009532147/39062500000 : ℝ)^3331
        have hw : |(4312973629/10000000000 : ℝ)|=(4312973629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244998959/5000000000 : ℝ)|^4355 ≤ (17551382245611/50000000000000 : ℝ)^3331
        have hw : |(2244998959/5000000000 : ℝ)|=(2244998959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4142393293/10000000000 : ℝ)|^4355 ≤ (123409504683/390625000000 : ℝ)^3331
        have hw : |(4142393293/10000000000 : ℝ)|=(4142393293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1395_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (627283/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1843/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (2817/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14739/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1843/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (352/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1843/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (352/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1843/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (352/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1843/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (352/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1843/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (352/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1843/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (352/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (352/3125 : ℝ) ^ (2177/512 : ℝ) ≤ (4643137759695809/50000000000000000000 : ℝ) := by
    have hpowers : (352/3125 : ℝ)^2177 ≤ (4643137759695809/50000000000000000000 : ℝ)^512 := by
      have hnat : (352 : ℕ)^2177*50000000000000000000^512 ≤ 4643137759695809^512*3125^2177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        352 3125 4643137759695809 50000000000000000000 2177 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (352/3125 : ℝ)) (X := (4643137759695809/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1843/12500 : ℝ) ^ (2177/512 : ℝ) ≤ (29173687136556203/100000000000000000000 : ℝ) := by
    have hpowers : (1843/12500 : ℝ)^2177 ≤ (29173687136556203/100000000000000000000 : ℝ)^512 := by
      have hnat : (1843 : ℕ)^2177*100000000000000000000^512 ≤ 29173687136556203^512*12500^2177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1843 12500 29173687136556203 100000000000000000000 2177 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1843/12500 : ℝ)) (X := (29173687136556203/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004643137759695809/25000000000000000000 : ℝ) ≤ (625027298090377/625000000000000 : ℝ) ^ (2177/512 : ℝ) := by
    have hpowers : (25004643137759695809/25000000000000000000 : ℝ)^512 ≤ (625027298090377/625000000000000 : ℝ)^2177 := by
      have hnat : (25004643137759695809 : ℕ)^512*625000000000000^2177 ≤ 625027298090377^2177*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004643137759695809 25000000000000000000 625027298090377 625000000000000 512 2177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625027298090377/625000000000000 : ℝ)) (X := (25004643137759695809/25000000000000000000 : ℝ)) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038459962655947821/100000000000000000000 : ℝ) ≤ (5000452195806967/5000000000000000 : ℝ) ^ (2177/512 : ℝ) := by
    have hpowers : (100038459962655947821/100000000000000000000 : ℝ)^512 ≤ (5000452195806967/5000000000000000 : ℝ)^2177 := by
      have hnat : (100038459962655947821 : ℕ)^512*5000000000000000^2177 ≤ 5000452195806967^2177*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038459962655947821 100000000000000000000 5000452195806967 5000000000000000 512 2177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000452195806967/5000000000000000 : ℝ)) (X := (100038459962655947821/100000000000000000000 : ℝ)) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029173687136556203/50000000000000000000 : ℝ) ≤ (2500343003445459/2500000000000000 : ℝ) ^ (2177/512 : ℝ) := by
    have hpowers : (50029173687136556203/50000000000000000000 : ℝ)^512 ≤ (2500343003445459/2500000000000000 : ℝ)^2177 := by
      have hnat : (50029173687136556203 : ℕ)^512*2500000000000000^2177 ≤ 2500343003445459^2177*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029173687136556203 50000000000000000000 2500343003445459 2500000000000000 512 2177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500343003445459/2500000000000000 : ℝ)) (X := (50029173687136556203/50000000000000000000 : ℝ)) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4643137759695809/50000000000000000000 : ℝ) ≤ ((271804573167763243/271875000000000000 : ℝ)+2*(233811083951/174000000000000 : ℝ)*(352/3125 : ℝ))^(2177/512 : ℝ) := by
    rw [show (271804573167763243/271875000000000000 : ℝ)+2*(233811083951/174000000000000 : ℝ)*(352/3125 : ℝ)=(625027298090377/625000000000000 : ℝ) by norm_num, show 1+2*(4643137759695809/50000000000000000000 : ℝ)=(25004643137759695809/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29173687136556203/100000000000000000000 : ℝ)+(4643137759695809/50000000000000000000 : ℝ) ≤ ((271804573167763243/271875000000000000 : ℝ)+(233811083951/174000000000000 : ℝ)*((1843/12500 : ℝ)+(352/3125 : ℝ)))^(2177/512 : ℝ) := by
    rw [show (271804573167763243/271875000000000000 : ℝ)+(233811083951/174000000000000 : ℝ)*((1843/12500 : ℝ)+(352/3125 : ℝ))=(5000452195806967/5000000000000000 : ℝ) by norm_num, show 1+(29173687136556203/100000000000000000000 : ℝ)+(4643137759695809/50000000000000000000 : ℝ)=(100038459962655947821/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29173687136556203/100000000000000000000 : ℝ) ≤ ((271804573167763243/271875000000000000 : ℝ)+2*(233811083951/174000000000000 : ℝ)*(1843/12500 : ℝ))^(2177/512 : ℝ) := by
    rw [show (271804573167763243/271875000000000000 : ℝ)+2*(233811083951/174000000000000 : ℝ)*(1843/12500 : ℝ)=(2500343003445459/2500000000000000 : ℝ) by norm_num, show 1+2*(29173687136556203/100000000000000000000 : ℝ)=(50029173687136556203/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (271804573167763243/271875000000000000 : ℝ)*(X 1 0+X 2 0)+(233811083951/174000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2177/512 : ℝ)) (lo := (352/3125 : ℝ)) (hi := (1843/12500 : ℝ)) (c := (271804573167763243/271875000000000000 : ℝ)) (alpha := (233811083951/174000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (271804573167763243/271875000000000000 : ℝ)*(X 0 1+X 2 1)+(233811083951/174000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2177/512 : ℝ)) (lo := (352/3125 : ℝ)) (hi := (1843/12500 : ℝ)) (c := (271804573167763243/271875000000000000 : ℝ)) (alpha := (233811083951/174000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (271804573167763243/271875000000000000 : ℝ)*(X 0 2+X 1 2)+(233811083951/174000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2177/512 : ℝ)) (lo := (352/3125 : ℝ)) (hi := (1843/12500 : ℝ)) (c := (271804573167763243/271875000000000000 : ℝ)) (alpha := (233811083951/174000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-249881427/1250000000 : ℝ)*X 0 0+(1352494441/2500000000 : ℝ)*X 0 1+(2623045701/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674010601/5000000000 : ℝ)*X 1 0+(-2082512841/10000000000 : ℝ)*X 1 1+(2623045701/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674010601/5000000000 : ℝ)*X 2 0+(2623045701/5000000000 : ℝ)*X 2 1+(-2082512841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2156474377/5000000000 : ℝ)*X 0 0+(414112771/1000000000 : ℝ)*X 0 1+(4491256993/10000000000 : ℝ)*X 0 2+(2156474377/5000000000 : ℝ)*X 1 0+(414112771/1000000000 : ℝ)*X 1 1+(4491256993/10000000000 : ℝ)*X 1 2+(2156474377/5000000000 : ℝ)*X 2 0+(414112771/1000000000 : ℝ)*X 2 1+(4491256993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-399812621/2000000000 : ℝ)*X 0 0+(5246680723/10000000000 : ℝ)*X 0 1+(5409385363/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326390339/2500000000 : ℝ)*X 1 0+(-191921889/1000000000 : ℝ)*X 1 1+(5409385359/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305561369/10000000000 : ℝ)*X 2 0+(1081877069/2000000000 : ℝ)*X 2 1+(-1919218891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4312973629/10000000000 : ℝ)*X 0 0+(2244998959/5000000000 : ℝ)*X 0 1+(4142393293/10000000000 : ℝ)*X 0 2+(4312973629/10000000000 : ℝ)*X 1 0+(2244998959/5000000000 : ℝ)*X 1 1+(4142393293/10000000000 : ℝ)*X 1 2+(4312973629/10000000000 : ℝ)*X 2 0+(2244998959/5000000000 : ℝ)*X 2 1+(4142393293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45054563824074343583240397/4531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (458117631/25000000000000 : ℝ)*(base19) + (853814667/50000000000000 : ℝ)*(base23) + (66765333/100000000000000 : ℝ)*(lower2) + (62228063/25000000000000 : ℝ)*(upper3) + (31525377/20000000000000 : ℝ)*(upper5) + (4478995851357743/100000000000000 : ℝ)*(major0) + (4478995851357743/100000000000000 : ℝ)*(major1) + (4478995851357743/100000000000000 : ℝ)*(major2) + (1525457193303543/25000000000000 : ℝ)*(sp0) + (6101865045489319/100000000000000 : ℝ)*(sp1) + (610186517033051/10000000000000 : ℝ)*(sp2) + (1428052591206049/50000000000000 : ℝ)*(sp3) + (4763093209/12500000000000 : ℝ)*(sp4) + (19310907659/100000000000000 : ℝ)*(sp7) + (1428062246659879/50000000000000 : ℝ)*(f.failure) + (1525466719489961/25000000000000 : ℝ)*(f.sum) + (13744620650893/8700000000000000000000000000 : ℝ)*base65 + (291864689785155259/18125000000000000000000000000000 : ℝ)*base68 + (183820453269530259/18125000000000000000000000000000 : ℝ)*base70 + (167560721669530259/18125000000000000000000000000000 : ℝ)*base72 + (40469341794493/8700000000000000000000000000 : ℝ)*base73 + (196518595508280259/18125000000000000000000000000000 : ℝ)*base76 + (282671356593280259/18125000000000000000000000000000 : ℝ)*base78 + (338618539737655259/18125000000000000000000000000000 : ℝ)*base80 + (9813071510893/8700000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (278757/20000000000000000000 : ℝ)*base89 + (278757/20000000000000000000 : ℝ)*base91 + (278757/20000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21180620661744457591647/2900000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1337723181/100000000000000 : ℝ)*(base19) + (1399422517/100000000000000 : ℝ)*(base23) + (448529121/100000000000000 : ℝ)*(lower1) + (8155481/5000000000000 : ℝ)*(upper3) + (10556631/50000000000000 : ℝ)*(lower4) + (163852551/100000000000000 : ℝ)*(upper5) + (4511448636526503/100000000000000 : ℝ)*(major0) + (4511448636526503/100000000000000 : ℝ)*(major1) + (4511448636526503/100000000000000 : ℝ)*(major2) + (427672379/50000000000000 : ℝ)*(sp2) + (768259793188729/12500000000000 : ℝ)*(sp4) + (6146077007786651/100000000000000 : ℝ)*(sp5) + (6146076090742557/100000000000000 : ℝ)*(sp6) + (1438409342043863/50000000000000 : ℝ)*(sp7) + (1438409342043863/50000000000000 : ℝ)*(f.failure) + (768259793188729/12500000000000 : ℝ)*(f.sum) + (18768231531851/2900000000000000000000000000 : ℝ)*base65 + (866079080667771139/18125000000000000000000000000000 : ℝ)*base68 + (72550045774021139/18125000000000000000000000000000 : ℝ)*base70 + (3544782136151521139/18125000000000000000000000000000 : ℝ)*base72 + (3729736958251/2900000000000000000000000000 : ℝ)*base73 + (1795744981040353861/18125000000000000000000000000000 : ℝ)*base75 + (23871210162853861/18125000000000000000000000000000 : ℝ)*base77 + (48656512454103861/18125000000000000000000000000000 : ℝ)*base79 + (3800469379249/2900000000000000000000000000 : ℝ)*base82 + (85771/20000000000000000000 : ℝ)*base90 + (85771/20000000000000000000 : ℝ)*base92 + (85771/20000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1395_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (627283/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1843/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2817/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14739/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1395_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1395_s7_0 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1999057327/10000000000 : ℝ)*x 0 + (1352485641/2500000000 : ℝ)*x 1 + (327882659/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1999057327/10000000000 : ℝ)^4355 ≤ (3046690355203/25000000000000 : ℝ)^3331 := by
    have hnat : (1999057327 : ℕ)^4355*25000000000000^3331 ≤ 3046690355203^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999057327 10000000000 3046690355203 25000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352485641/2500000000 : ℝ)^4355 ≤ (44789067778137/100000000000000 : ℝ)^3331 := by
    have hnat : (1352485641 : ℕ)^4355*100000000000000^3331 ≤ 44789067778137^3331*2500000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352485641 2500000000 44789067778137 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327882659/625000000 : ℝ)^4355 ≤ (2689010674643/6250000000000 : ℝ)^3331 := by
    have hnat : (327882659 : ℕ)^4355*6250000000000^3331 ≤ 2689010674643^3331*625000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327882659 625000000 2689010674643 6250000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1999057327/10000000000 : ℝ), (1352485641/2500000000 : ℝ), (327882659/625000000 : ℝ)] ![(3046690355203/25000000000000 : ℝ), (44789067778137/100000000000000 : ℝ), (2689010674643/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1999057327/10000000000 : ℝ)|^4355 ≤ (3046690355203/25000000000000 : ℝ)^3331
        have hw : |(-1999057327/10000000000 : ℝ)|=(1999057327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352485641/2500000000 : ℝ)|^4355 ≤ (44789067778137/100000000000000 : ℝ)^3331
        have hw : |(1352485641/2500000000 : ℝ)|=(1352485641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327882659/625000000 : ℝ)|^4355 ≤ (2689010674643/6250000000000 : ℝ)^3331
        have hw : |(327882659/625000000 : ℝ)|=(327882659/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s7_1 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337002931/2500000000 : ℝ)*x 0 + (-2082483979/10000000000 : ℝ)*x 1 + (5246122661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337002931/2500000000 : ℝ)^4355 ≤ (44119903139321/100000000000000 : ℝ)^3331 := by
    have hnat : (1337002931 : ℕ)^4355*100000000000000^3331 ≤ 44119903139321^3331*2500000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337002931 2500000000 44119903139321 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2082483979/10000000000 : ℝ)^4355 ≤ (12855924783829/100000000000000 : ℝ)^3331 := by
    have hnat : (2082483979 : ℕ)^4355*100000000000000^3331 ≤ 12855924783829^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082483979 10000000000 12855924783829 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246122661/10000000000 : ℝ)^4355 ≤ (10756043012199/25000000000000 : ℝ)^3331 := by
    have hnat : (5246122661 : ℕ)^4355*25000000000000^3331 ≤ 10756043012199^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246122661 10000000000 10756043012199 25000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337002931/2500000000 : ℝ), (-2082483979/10000000000 : ℝ), (5246122661/10000000000 : ℝ)] ![(44119903139321/100000000000000 : ℝ), (12855924783829/100000000000000 : ℝ), (10756043012199/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337002931/2500000000 : ℝ)|^4355 ≤ (44119903139321/100000000000000 : ℝ)^3331
        have hw : |(1337002931/2500000000 : ℝ)|=(1337002931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2082483979/10000000000 : ℝ)|^4355 ≤ (12855924783829/100000000000000 : ℝ)^3331
        have hw : |(-2082483979/10000000000 : ℝ)|=(2082483979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246122661/10000000000 : ℝ)|^4355 ≤ (10756043012199/25000000000000 : ℝ)^3331
        have hw : |(5246122661/10000000000 : ℝ)|=(5246122661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s7_2 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674005653/5000000000 : ℝ)*x 0 + (1311530829/2500000000 : ℝ)*x 1 + (-208248367/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674005653/5000000000 : ℝ)^4355 ≤ (22059949315411/50000000000000 : ℝ)^3331 := by
    have hnat : (2674005653 : ℕ)^4355*50000000000000^3331 ≤ 22059949315411^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674005653 5000000000 22059949315411 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311530829/2500000000 : ℝ)^4355 ≤ (43024179071897/100000000000000 : ℝ)^3331 := by
    have hnat : (1311530829 : ℕ)^4355*100000000000000^3331 ≤ 43024179071897^3331*2500000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311530829 2500000000 43024179071897 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208248367/1000000000 : ℝ)^4355 ≤ (2571184457969/20000000000000 : ℝ)^3331 := by
    have hnat : (208248367 : ℕ)^4355*20000000000000^3331 ≤ 2571184457969^3331*1000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208248367 1000000000 2571184457969 20000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674005653/5000000000 : ℝ), (1311530829/2500000000 : ℝ), (-208248367/1000000000 : ℝ)] ![(22059949315411/50000000000000 : ℝ), (43024179071897/100000000000000 : ℝ), (2571184457969/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674005653/5000000000 : ℝ)|^4355 ≤ (22059949315411/50000000000000 : ℝ)^3331
        have hw : |(2674005653/5000000000 : ℝ)|=(2674005653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311530829/2500000000 : ℝ)|^4355 ≤ (43024179071897/100000000000000 : ℝ)^3331
        have hw : |(1311530829/2500000000 : ℝ)|=(1311530829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-208248367/1000000000 : ℝ)|^4355 ≤ (2571184457969/20000000000000 : ℝ)^3331
        have hw : |(-208248367/1000000000 : ℝ)|=(208248367/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s7_3 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4312950969/10000000000 : ℝ)*x 0 + (4141199121/10000000000 : ℝ)*x 1 + (2245592577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312950969/10000000000 : ℝ)^4355 ≤ (16652086763463/50000000000000 : ℝ)^3331 := by
    have hnat : (4312950969 : ℕ)^4355*50000000000000^3331 ≤ 16652086763463^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312950969 10000000000 16652086763463 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4141199121/10000000000 : ℝ)^4355 ≤ (31580926306981/100000000000000 : ℝ)^3331 := by
    have hnat : (4141199121 : ℕ)^4355*100000000000000^3331 ≤ 31580926306981^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4141199121 10000000000 31580926306981 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245592577/5000000000 : ℝ)^4355 ≤ (87787250379/250000000000 : ℝ)^3331 := by
    have hnat : (2245592577 : ℕ)^4355*250000000000^3331 ≤ 87787250379^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245592577 5000000000 87787250379 250000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312950969/10000000000 : ℝ), (4141199121/10000000000 : ℝ), (2245592577/5000000000 : ℝ)] ![(16652086763463/50000000000000 : ℝ), (31580926306981/100000000000000 : ℝ), (87787250379/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312950969/10000000000 : ℝ)|^4355 ≤ (16652086763463/50000000000000 : ℝ)^3331
        have hw : |(4312950969/10000000000 : ℝ)|=(4312950969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4141199121/10000000000 : ℝ)|^4355 ≤ (31580926306981/100000000000000 : ℝ)^3331
        have hw : |(4141199121/10000000000 : ℝ)|=(4141199121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2245592577/5000000000 : ℝ)|^4355 ≤ (87787250379/250000000000 : ℝ)^3331
        have hw : |(2245592577/5000000000 : ℝ)|=(2245592577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s7_4 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1999068777/10000000000 : ℝ)*x 0 + (5246711929/10000000000 : ℝ)*x 1 + (42260549/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1999068777/10000000000 : ℝ)^4355 ≤ (1218685268123/10000000000000 : ℝ)^3331 := by
    have hnat : (1999068777 : ℕ)^4355*10000000000000^3331 ≤ 1218685268123^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999068777 10000000000 1218685268123 10000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246711929/10000000000 : ℝ)^4355 ≤ (5378811307639/12500000000000 : ℝ)^3331 := by
    have hnat : (5246711929 : ℕ)^4355*12500000000000^3331 ≤ 5378811307639^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246711929 10000000000 5378811307639 12500000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42260549/78125000 : ℝ)^4355 ≤ (8956531368391/20000000000000 : ℝ)^3331 := by
    have hnat : (42260549 : ℕ)^4355*20000000000000^3331 ≤ 8956531368391^3331*78125000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42260549 78125000 8956531368391 20000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1999068777/10000000000 : ℝ), (5246711929/10000000000 : ℝ), (42260549/78125000 : ℝ)] ![(1218685268123/10000000000000 : ℝ), (5378811307639/12500000000000 : ℝ), (8956531368391/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1999068777/10000000000 : ℝ)|^4355 ≤ (1218685268123/10000000000000 : ℝ)^3331
        have hw : |(-1999068777/10000000000 : ℝ)|=(1999068777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246711929/10000000000 : ℝ)|^4355 ≤ (5378811307639/12500000000000 : ℝ)^3331
        have hw : |(5246711929/10000000000 : ℝ)|=(5246711929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42260549/78125000 : ℝ)|^4355 ≤ (8956531368391/20000000000000 : ℝ)^3331
        have hw : |(42260549/78125000 : ℝ)|=(42260549/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s7_5 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305569071/10000000000 : ℝ)*x 0 + (-959628221/5000000000 : ℝ)*x 1 + (2704675191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305569071/10000000000 : ℝ)^4355 ≤ (43662681077497/100000000000000 : ℝ)^3331 := by
    have hnat : (5305569071 : ℕ)^4355*100000000000000^3331 ≤ 43662681077497^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305569071 10000000000 43662681077497 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (959628221/5000000000 : ℝ)^4355 ≤ (5777330438299/50000000000000 : ℝ)^3331 := by
    have hnat : (959628221 : ℕ)^4355*50000000000000^3331 ≤ 5777330438299^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959628221 5000000000 5777330438299 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704675191/5000000000 : ℝ)^4355 ≤ (44782658032569/100000000000000 : ℝ)^3331 := by
    have hnat : (2704675191 : ℕ)^4355*100000000000000^3331 ≤ 44782658032569^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704675191 5000000000 44782658032569 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305569071/10000000000 : ℝ), (-959628221/5000000000 : ℝ), (2704675191/5000000000 : ℝ)] ![(43662681077497/100000000000000 : ℝ), (5777330438299/50000000000000 : ℝ), (44782658032569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305569071/10000000000 : ℝ)|^4355 ≤ (43662681077497/100000000000000 : ℝ)^3331
        have hw : |(5305569071/10000000000 : ℝ)|=(5305569071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-959628221/5000000000 : ℝ)|^4355 ≤ (5777330438299/50000000000000 : ℝ)^3331
        have hw : |(-959628221/5000000000 : ℝ)|=(959628221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704675191/5000000000 : ℝ)|^4355 ≤ (44782658032569/100000000000000 : ℝ)^3331
        have hw : |(2704675191/5000000000 : ℝ)|=(2704675191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s7_6 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305569223/10000000000 : ℝ)*x 0 + (540935047/1000000000 : ℝ)*x 1 + (-1919256113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305569223/10000000000 : ℝ)^4355 ≤ (2183134135647/5000000000000 : ℝ)^3331 := by
    have hnat : (5305569223 : ℕ)^4355*5000000000000^3331 ≤ 2183134135647^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305569223 10000000000 2183134135647 5000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540935047/1000000000 : ℝ)^4355 ≤ (2239132949253/5000000000000 : ℝ)^3331 := by
    have hnat : (540935047 : ℕ)^4355*5000000000000^3331 ≤ 2239132949253^3331*1000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540935047 1000000000 2239132949253 5000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1919256113/10000000000 : ℝ)^4355 ≤ (722166142937/6250000000000 : ℝ)^3331 := by
    have hnat : (1919256113 : ℕ)^4355*6250000000000^3331 ≤ 722166142937^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919256113 10000000000 722166142937 6250000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305569223/10000000000 : ℝ), (540935047/1000000000 : ℝ), (-1919256113/10000000000 : ℝ)] ![(2183134135647/5000000000000 : ℝ), (2239132949253/5000000000000 : ℝ), (722166142937/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305569223/10000000000 : ℝ)|^4355 ≤ (2183134135647/5000000000000 : ℝ)^3331
        have hw : |(5305569223/10000000000 : ℝ)|=(5305569223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540935047/1000000000 : ℝ)|^4355 ≤ (2239132949253/5000000000000 : ℝ)^3331
        have hw : |(540935047/1000000000 : ℝ)|=(540935047/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1919256113/10000000000 : ℝ)|^4355 ≤ (722166142937/6250000000000 : ℝ)^3331
        have hw : |(-1919256113/10000000000 : ℝ)|=(1919256113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_s7_7 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107824399/250000000 : ℝ)*x 0 + (4489927131/10000000000 : ℝ)*x 1 + (828492699/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107824399/250000000 : ℝ)^4355 ≤ (260190826793/781250000000 : ℝ)^3331 := by
    have hnat : (107824399 : ℕ)^4355*781250000000^3331 ≤ 260190826793^3331*250000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107824399 250000000 260190826793 781250000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4489927131/10000000000 : ℝ)^4355 ≤ (35102040953527/100000000000000 : ℝ)^3331 := by
    have hnat : (4489927131 : ℕ)^4355*100000000000000^3331 ≤ 35102040953527^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489927131 10000000000 35102040953527 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (828492699/2000000000 : ℝ)^4355 ≤ (31593533204243/100000000000000 : ℝ)^3331 := by
    have hnat : (828492699 : ℕ)^4355*100000000000000^3331 ≤ 31593533204243^3331*2000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828492699 2000000000 31593533204243 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107824399/250000000 : ℝ), (4489927131/10000000000 : ℝ), (828492699/2000000000 : ℝ)] ![(260190826793/781250000000 : ℝ), (35102040953527/100000000000000 : ℝ), (31593533204243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107824399/250000000 : ℝ)|^4355 ≤ (260190826793/781250000000 : ℝ)^3331
        have hw : |(107824399/250000000 : ℝ)|=(107824399/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4489927131/10000000000 : ℝ)|^4355 ≤ (35102040953527/100000000000000 : ℝ)^3331
        have hw : |(4489927131/10000000000 : ℝ)|=(4489927131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(828492699/2000000000 : ℝ)|^4355 ≤ (31593533204243/100000000000000 : ℝ)^3331
        have hw : |(828492699/2000000000 : ℝ)|=(828492699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1395_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (627283/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14739/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2817/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11269/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7369/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14739/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2817/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14739/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2817/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14739/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2817/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14739/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2817/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14739/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2817/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14739/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2817/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2817/25000 : ℝ) ^ (2177/512 : ℝ) ≤ (930030521153483/10000000000000000000 : ℝ) := by
    have hpowers : (2817/25000 : ℝ)^2177 ≤ (930030521153483/10000000000000000000 : ℝ)^512 := by
      have hnat : (2817 : ℕ)^2177*10000000000000000000^512 ≤ 930030521153483^512*25000^2177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2817 25000 930030521153483 10000000000000000000 2177 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2817/25000 : ℝ)) (X := (930030521153483/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14739/100000 : ℝ) ^ (2177/512 : ℝ) ≤ (29131644010960919/100000000000000000000 : ℝ) := by
    have hpowers : (14739/100000 : ℝ)^2177 ≤ (29131644010960919/100000000000000000000 : ℝ)^512 := by
      have hnat : (14739 : ℕ)^2177*100000000000000000000^512 ≤ 29131644010960919^512*100000^2177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14739 100000 29131644010960919 100000000000000000000 2177 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14739/100000 : ℝ)) (X := (29131644010960919/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000930030521153483/5000000000000000000 : ℝ) ≤ (5000218714634887/5000000000000000 : ℝ) ^ (2177/512 : ℝ) := by
    have hpowers : (5000930030521153483/5000000000000000000 : ℝ)^512 ≤ (5000218714634887/5000000000000000 : ℝ)^2177 := by
      have hnat : (5000930030521153483 : ℕ)^512*5000000000000000^2177 ≤ 5000218714634887^2177*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000930030521153483 5000000000000000000 5000218714634887 5000000000000000 512 2177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000218714634887/5000000000000000 : ℝ)) (X := (5000930030521153483/5000000000000000000 : ℝ)) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038431949222495749/100000000000000000000 : ℝ) ≤ (2500225933242689/2500000000000000 : ℝ) ^ (2177/512 : ℝ) := by
    have hpowers : (100038431949222495749/100000000000000000000 : ℝ)^512 ≤ (2500225933242689/2500000000000000 : ℝ)^2177 := by
      have hnat : (100038431949222495749 : ℕ)^512*2500000000000000^2177 ≤ 2500225933242689^2177*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038431949222495749 100000000000000000000 2500225933242689 2500000000000000 512 2177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500225933242689/2500000000000000 : ℝ)) (X := (100038431949222495749/100000000000000000000 : ℝ)) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029131644010960919/50000000000000000000 : ℝ) ≤ (5000685018335869/5000000000000000 : ℝ) ^ (2177/512 : ℝ) := by
    have hpowers : (50029131644010960919/50000000000000000000 : ℝ)^512 ≤ (5000685018335869/5000000000000000 : ℝ)^2177 := by
      have hnat : (50029131644010960919 : ℕ)^512*5000000000000000^2177 ≤ 5000685018335869^2177*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029131644010960919 50000000000000000000 5000685018335869 5000000000000000 512 2177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000685018335869/5000000000000000 : ℝ)) (X := (50029131644010960919/50000000000000000000 : ℝ)) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(930030521153483/10000000000000000000 : ℝ) ≤ ((5783501616131675867/5785000000000000000 : ℝ)+2*(77717283497/57850000000000 : ℝ)*(2817/25000 : ℝ))^(2177/512 : ℝ) := by
    rw [show (5783501616131675867/5785000000000000000 : ℝ)+2*(77717283497/57850000000000 : ℝ)*(2817/25000 : ℝ)=(5000218714634887/5000000000000000 : ℝ) by norm_num, show 1+2*(930030521153483/10000000000000000000 : ℝ)=(5000930030521153483/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29131644010960919/100000000000000000000 : ℝ)+(930030521153483/10000000000000000000 : ℝ) ≤ ((5783501616131675867/5785000000000000000 : ℝ)+(77717283497/57850000000000 : ℝ)*((14739/100000 : ℝ)+(2817/25000 : ℝ)))^(2177/512 : ℝ) := by
    rw [show (5783501616131675867/5785000000000000000 : ℝ)+(77717283497/57850000000000 : ℝ)*((14739/100000 : ℝ)+(2817/25000 : ℝ))=(2500225933242689/2500000000000000 : ℝ) by norm_num, show 1+(29131644010960919/100000000000000000000 : ℝ)+(930030521153483/10000000000000000000 : ℝ)=(100038431949222495749/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29131644010960919/100000000000000000000 : ℝ) ≤ ((5783501616131675867/5785000000000000000 : ℝ)+2*(77717283497/57850000000000 : ℝ)*(14739/100000 : ℝ))^(2177/512 : ℝ) := by
    rw [show (5783501616131675867/5785000000000000000 : ℝ)+2*(77717283497/57850000000000 : ℝ)*(14739/100000 : ℝ)=(5000685018335869/5000000000000000 : ℝ) by norm_num, show 1+2*(29131644010960919/100000000000000000000 : ℝ)=(50029131644010960919/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5783501616131675867/5785000000000000000 : ℝ)*(X 1 0+X 2 0)+(77717283497/57850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2177/512 : ℝ)) (lo := (2817/25000 : ℝ)) (hi := (14739/100000 : ℝ)) (c := (5783501616131675867/5785000000000000000 : ℝ)) (alpha := (77717283497/57850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5783501616131675867/5785000000000000000 : ℝ)*(X 0 1+X 2 1)+(77717283497/57850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2177/512 : ℝ)) (lo := (2817/25000 : ℝ)) (hi := (14739/100000 : ℝ)) (c := (5783501616131675867/5785000000000000000 : ℝ)) (alpha := (77717283497/57850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5783501616131675867/5785000000000000000 : ℝ)*(X 0 2+X 1 2)+(77717283497/57850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2177/512 : ℝ)) (lo := (2817/25000 : ℝ)) (hi := (14739/100000 : ℝ)) (c := (5783501616131675867/5785000000000000000 : ℝ)) (alpha := (77717283497/57850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1999057327/10000000000 : ℝ)*X 0 0+(1352485641/2500000000 : ℝ)*X 0 1+(327882659/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337002931/2500000000 : ℝ)*X 1 0+(-2082483979/10000000000 : ℝ)*X 1 1+(5246122661/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674005653/5000000000 : ℝ)*X 2 0+(1311530829/2500000000 : ℝ)*X 2 1+(-208248367/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4312950969/10000000000 : ℝ)*X 0 0+(4141199121/10000000000 : ℝ)*X 0 1+(2245592577/5000000000 : ℝ)*X 0 2+(4312950969/10000000000 : ℝ)*X 1 0+(4141199121/10000000000 : ℝ)*X 1 1+(2245592577/5000000000 : ℝ)*X 1 2+(4312950969/10000000000 : ℝ)*X 2 0+(4141199121/10000000000 : ℝ)*X 2 1+(2245592577/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1999068777/10000000000 : ℝ)*X 0 0+(5246711929/10000000000 : ℝ)*X 0 1+(42260549/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305569071/10000000000 : ℝ)*X 1 0+(-959628221/5000000000 : ℝ)*X 1 1+(2704675191/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305569223/10000000000 : ℝ)*X 2 0+(540935047/1000000000 : ℝ)*X 2 1+(-1919256113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((107824399/250000000 : ℝ)*X 0 0+(4489927131/10000000000 : ℝ)*X 0 1+(828492699/2000000000 : ℝ)*X 0 2+(107824399/250000000 : ℝ)*X 1 0+(4489927131/10000000000 : ℝ)*X 1 1+(828492699/2000000000 : ℝ)*X 1 2+(107824399/250000000 : ℝ)*X 2 0+(4489927131/10000000000 : ℝ)*X 2 1+(828492699/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (234475634307492889770658809/36156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1603265139/100000000000000 : ℝ)*(base19) + (455648483/50000000000000 : ℝ)*(base23) + (94574981/100000000000000 : ℝ)*(upper3) + (114903803/100000000000000 : ℝ)*(upper4) + (249792493/100000000000000 : ℝ)*(upper5) + (560101859585841/12500000000000 : ℝ)*(major0) + (560101859585841/12500000000000 : ℝ)*(major1) + (560101859585841/12500000000000 : ℝ)*(major2) + (6104299829399931/100000000000000 : ℝ)*(sp0) + (6104343501435019/100000000000000 : ℝ)*(sp1) + (6104344193403193/100000000000000 : ℝ)*(sp2) + (285727219256821/10000000000000 : ℝ)*(sp3) + (45275300227/100000000000000 : ℝ)*(sp4) + (12239936243/100000000000000 : ℝ)*(sp7) + (1428642216252227/50000000000000 : ℝ)*(f.failure) + (3052172552350079/50000000000000 : ℝ)*(f.sum) + (5047195088371/2892500000000000000000000000 : ℝ)*base65 + (74549915400825853/72312500000000000000000000000000 : ℝ)*base68 + (158098442548486647/72312500000000000000000000000000 : ℝ)*base69 + (478745322935924147/72312500000000000000000000000000 : ℝ)*base71 + (22896423003331/2892500000000000000000000000 : ℝ)*base73 + (926085441354299147/72312500000000000000000000000000 : ℝ)*base75 + (164595431785049147/72312500000000000000000000000000 : ℝ)*base77 + (1436431259981888353/72312500000000000000000000000000 : ℝ)*base80 + (68051991643/5785000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (109241/20000000000000000000 : ℝ)*base89 + (109241/20000000000000000000 : ℝ)*base91 + (109241/20000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32290050693026853121848021/7231250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (769262579/100000000000000 : ℝ)*(base19) + (1143822249/100000000000000 : ℝ)*(base23) + (122676049/50000000000000 : ℝ)*(lower1) + (21927989/12500000000000 : ℝ)*(upper3) + (22773077/100000000000000 : ℝ)*(lower4) + (14909223/100000000000000 : ℝ)*(upper5) + (225664692853421/5000000000000 : ℝ)*(major0) + (225664692853421/5000000000000 : ℝ)*(major1) + (225664692853421/5000000000000 : ℝ)*(major2) + (4859184241/25000000000000 : ℝ)*(sp2) + (3074296119049629/50000000000000 : ℝ)*(sp4) + (3074295734418339/50000000000000 : ℝ)*(sp5) + (1229714331508009/20000000000000 : ℝ)*(sp6) + (143899766359631/5000000000000 : ℝ)*(sp7) + (143899766359631/5000000000000 : ℝ)*(f.failure) + (3074296119049629/50000000000000 : ℝ)*(f.sum) + (720078391171/578500000000000000000000000 : ℝ)*base66 + (1450696995277558993/28925000000000000000000000000000 : ℝ)*base68 + (312607673585508993/28925000000000000000000000000000 : ℝ)*base70 + (296830614536141007/28925000000000000000000000000000 : ℝ)*base71 + (63157365383/18078125000000000000000000 : ℝ)*base74 + (463295724404008993/28925000000000000000000000000000 : ℝ)*base76 + (418049715721783993/28925000000000000000000000000000 : ℝ)*base78 + (583796669813658993/28925000000000000000000000000000 : ℝ)*base80 + (8041763433101/1157000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (12573/2000000000000000000 : ℝ)*base89 + (12573/2000000000000000000 : ℝ)*base91 + (12573/2000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1395_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (627283/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14739/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2817/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1395_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1395_box_0 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1835895159/10000000000 : ℝ)*x 0 + (8418291/15625000 : ℝ)*x 1 + (5387706231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1835895159/10000000000 : ℝ)^4355 ≤ (10902937720707/100000000000000 : ℝ)^3331 := by
    have hnat : (1835895159 : ℕ)^4355*100000000000000^3331 ≤ 10902937720707^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1835895159 10000000000 10902937720707 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8418291/15625000 : ℝ)^4355 ≤ (445485311809/1000000000000 : ℝ)^3331 := by
    have hnat : (8418291 : ℕ)^4355*1000000000000^3331 ≤ 445485311809^3331*15625000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8418291 15625000 445485311809 1000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387706231/10000000000 : ℝ)^4355 ≤ (22274265541803/50000000000000 : ℝ)^3331 := by
    have hnat : (5387706231 : ℕ)^4355*50000000000000^3331 ≤ 22274265541803^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387706231 10000000000 22274265541803 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1835895159/10000000000 : ℝ), (8418291/15625000 : ℝ), (5387706231/10000000000 : ℝ)] ![(10902937720707/100000000000000 : ℝ), (445485311809/1000000000000 : ℝ), (22274265541803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1835895159/10000000000 : ℝ)|^4355 ≤ (10902937720707/100000000000000 : ℝ)^3331
        have hw : |(-1835895159/10000000000 : ℝ)|=(1835895159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8418291/15625000 : ℝ)|^4355 ≤ (445485311809/1000000000000 : ℝ)^3331
        have hw : |(8418291/15625000 : ℝ)|=(8418291/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387706231/10000000000 : ℝ)|^4355 ≤ (22274265541803/50000000000000 : ℝ)^3331
        have hw : |(5387706231/10000000000 : ℝ)|=(5387706231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_box_1 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642890493/5000000000 : ℝ)*x 0 + (-1975781053/10000000000 : ℝ)*x 1 + (538770631/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642890493/5000000000 : ℝ)^4355 ≤ (43449893406061/100000000000000 : ℝ)^3331 := by
    have hnat : (2642890493 : ℕ)^4355*100000000000000^3331 ≤ 43449893406061^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642890493 5000000000 43449893406061 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1975781053/10000000000 : ℝ)^4355 ≤ (12001574638601/100000000000000 : ℝ)^3331 := by
    have hnat : (1975781053 : ℕ)^4355*100000000000000^3331 ≤ 12001574638601^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975781053 10000000000 12001574638601 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538770631/1000000000 : ℝ)^4355 ≤ (4454853193763/10000000000000 : ℝ)^3331 := by
    have hnat : (538770631 : ℕ)^4355*10000000000000^3331 ≤ 4454853193763^3331*1000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538770631 1000000000 4454853193763 10000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642890493/5000000000 : ℝ), (-1975781053/10000000000 : ℝ), (538770631/1000000000 : ℝ)] ![(43449893406061/100000000000000 : ℝ), (12001574638601/100000000000000 : ℝ), (4454853193763/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642890493/5000000000 : ℝ)|^4355 ≤ (43449893406061/100000000000000 : ℝ)^3331
        have hw : |(2642890493/5000000000 : ℝ)|=(2642890493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1975781053/10000000000 : ℝ)|^4355 ≤ (12001574638601/100000000000000 : ℝ)^3331
        have hw : |(-1975781053/10000000000 : ℝ)|=(1975781053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538770631/1000000000 : ℝ)|^4355 ≤ (4454853193763/10000000000000 : ℝ)^3331
        have hw : |(538770631/1000000000 : ℝ)|=(538770631/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_box_2 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642890597/5000000000 : ℝ)*x 0 + (5387706141/10000000000 : ℝ)*x 1 + (-1975781003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642890597/5000000000 : ℝ)^4355 ≤ (43449895641467/100000000000000 : ℝ)^3331 := by
    have hnat : (2642890597 : ℕ)^4355*100000000000000^3331 ≤ 43449895641467^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642890597 5000000000 43449895641467 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387706141/10000000000 : ℝ)^4355 ≤ (44548530110667/100000000000000 : ℝ)^3331 := by
    have hnat : (5387706141 : ℕ)^4355*100000000000000^3331 ≤ 44548530110667^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387706141 10000000000 44548530110667 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1975781003/10000000000 : ℝ)^4355 ≤ (12001574241517/100000000000000 : ℝ)^3331 := by
    have hnat : (1975781003 : ℕ)^4355*100000000000000^3331 ≤ 12001574241517^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975781003 10000000000 12001574241517 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642890597/5000000000 : ℝ), (5387706141/10000000000 : ℝ), (-1975781003/10000000000 : ℝ)] ![(43449895641467/100000000000000 : ℝ), (44548530110667/100000000000000 : ℝ), (12001574241517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642890597/5000000000 : ℝ)|^4355 ≤ (43449895641467/100000000000000 : ℝ)^3331
        have hw : |(2642890597/5000000000 : ℝ)|=(2642890597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387706141/10000000000 : ℝ)|^4355 ≤ (44548530110667/100000000000000 : ℝ)^3331
        have hw : |(5387706141/10000000000 : ℝ)|=(5387706141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1975781003/10000000000 : ℝ)|^4355 ≤ (12001574241517/100000000000000 : ℝ)^3331
        have hw : |(-1975781003/10000000000 : ℝ)|=(1975781003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_box_3 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4459950519/10000000000 : ℝ)*x 0 + (4243227867/10000000000 : ℝ)*x 1 + (1060806893/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4459950519/10000000000 : ℝ)^4355 ≤ (17397977799171/50000000000000 : ℝ)^3331 := by
    have hnat : (4459950519 : ℕ)^4355*50000000000000^3331 ≤ 17397977799171^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4459950519 10000000000 17397977799171 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4243227867/10000000000 : ℝ)^4355 ≤ (8150505918693/25000000000000 : ℝ)^3331 := by
    have hnat : (4243227867 : ℕ)^4355*25000000000000^3331 ≤ 8150505918693^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243227867 10000000000 8150505918693 25000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060806893/2500000000 : ℝ)^4355 ≤ (4075252588927/12500000000000 : ℝ)^3331 := by
    have hnat : (1060806893 : ℕ)^4355*12500000000000^3331 ≤ 4075252588927^3331*2500000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060806893 2500000000 4075252588927 12500000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4459950519/10000000000 : ℝ), (4243227867/10000000000 : ℝ), (1060806893/2500000000 : ℝ)] ![(17397977799171/50000000000000 : ℝ), (8150505918693/25000000000000 : ℝ), (4075252588927/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4459950519/10000000000 : ℝ)|^4355 ≤ (17397977799171/50000000000000 : ℝ)^3331
        have hw : |(4459950519/10000000000 : ℝ)|=(4459950519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4243227867/10000000000 : ℝ)|^4355 ≤ (8150505918693/25000000000000 : ℝ)^3331
        have hw : |(4243227867/10000000000 : ℝ)|=(4243227867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060806893/2500000000 : ℝ)|^4355 ≤ (4075252588927/12500000000000 : ℝ)^3331
        have hw : |(1060806893/2500000000 : ℝ)|=(1060806893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_box_4 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-216496053/1000000000 : ℝ)*x 0 + (2632988963/5000000000 : ℝ)*x 1 + (2632988943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216496053/1000000000 : ℝ)^4355 ≤ (13525620966413/100000000000000 : ℝ)^3331 := by
    have hnat : (216496053 : ℕ)^4355*100000000000000^3331 ≤ 13525620966413^3331*1000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216496053 1000000000 13525620966413 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632988963/5000000000 : ℝ)^4355 ≤ (21618594864331/50000000000000 : ℝ)^3331 := by
    have hnat : (2632988963 : ℕ)^4355*50000000000000^3331 ≤ 21618594864331^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632988963 5000000000 21618594864331 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632988943/5000000000 : ℝ)^4355 ≤ (5404648662409/12500000000000 : ℝ)^3331 := by
    have hnat : (2632988943 : ℕ)^4355*12500000000000^3331 ≤ 5404648662409^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632988943 5000000000 5404648662409 12500000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-216496053/1000000000 : ℝ), (2632988963/5000000000 : ℝ), (2632988943/5000000000 : ℝ)] ![(13525620966413/100000000000000 : ℝ), (21618594864331/50000000000000 : ℝ), (5404648662409/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-216496053/1000000000 : ℝ)|^4355 ≤ (13525620966413/100000000000000 : ℝ)^3331
        have hw : |(-216496053/1000000000 : ℝ)|=(216496053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632988963/5000000000 : ℝ)|^4355 ≤ (21618594864331/50000000000000 : ℝ)^3331
        have hw : |(2632988963/5000000000 : ℝ)|=(2632988963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632988943/5000000000 : ℝ)|^4355 ≤ (5404648662409/12500000000000 : ℝ)^3331
        have hw : |(2632988943/5000000000 : ℝ)|=(2632988943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_box_5 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5371091161/10000000000 : ℝ)*x 0 + (-2024982783/10000000000 : ℝ)*x 1 + (5265978239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371091161/10000000000 : ℝ)^4355 ≤ (2773062513633/6250000000000 : ℝ)^3331 := by
    have hnat : (5371091161 : ℕ)^4355*6250000000000^3331 ≤ 2773062513633^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371091161 10000000000 2773062513633 6250000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2024982783/10000000000 : ℝ)^4355 ≤ (3098451669109/25000000000000 : ℝ)^3331 := by
    have hnat : (2024982783 : ℕ)^4355*25000000000000^3331 ≤ 3098451669109^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024982783 10000000000 3098451669109 25000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265978239/10000000000 : ℝ)^4355 ≤ (43237193088639/100000000000000 : ℝ)^3331 := by
    have hnat : (5265978239 : ℕ)^4355*100000000000000^3331 ≤ 43237193088639^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265978239 10000000000 43237193088639 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371091161/10000000000 : ℝ), (-2024982783/10000000000 : ℝ), (5265978239/10000000000 : ℝ)] ![(2773062513633/6250000000000 : ℝ), (3098451669109/25000000000000 : ℝ), (43237193088639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371091161/10000000000 : ℝ)|^4355 ≤ (2773062513633/6250000000000 : ℝ)^3331
        have hw : |(5371091161/10000000000 : ℝ)|=(5371091161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2024982783/10000000000 : ℝ)|^4355 ≤ (3098451669109/25000000000000 : ℝ)^3331
        have hw : |(-2024982783/10000000000 : ℝ)|=(2024982783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265978239/10000000000 : ℝ)|^4355 ≤ (43237193088639/100000000000000 : ℝ)^3331
        have hw : |(5265978239/10000000000 : ℝ)|=(5265978239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_box_6 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5371091519/10000000000 : ℝ)*x 0 + (5265977709/10000000000 : ℝ)*x 1 + (-2024983011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371091519/10000000000 : ℝ)^4355 ≤ (44369004084589/100000000000000 : ℝ)^3331 := by
    have hnat : (5371091519 : ℕ)^4355*100000000000000^3331 ≤ 44369004084589^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371091519 10000000000 44369004084589 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265977709/10000000000 : ℝ)^4355 ≤ (43237187399221/100000000000000 : ℝ)^3331 := by
    have hnat : (5265977709 : ℕ)^4355*100000000000000^3331 ≤ 43237187399221^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265977709 10000000000 43237187399221 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2024983011/10000000000 : ℝ)^4355 ≤ (2478761700177/20000000000000 : ℝ)^3331 := by
    have hnat : (2024983011 : ℕ)^4355*20000000000000^3331 ≤ 2478761700177^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024983011 10000000000 2478761700177 20000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371091519/10000000000 : ℝ), (5265977709/10000000000 : ℝ), (-2024983011/10000000000 : ℝ)] ![(44369004084589/100000000000000 : ℝ), (43237187399221/100000000000000 : ℝ), (2478761700177/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371091519/10000000000 : ℝ)|^4355 ≤ (44369004084589/100000000000000 : ℝ)^3331
        have hw : |(5371091519/10000000000 : ℝ)|=(5371091519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265977709/10000000000 : ℝ)|^4355 ≤ (43237187399221/100000000000000 : ℝ)^3331
        have hw : |(5265977709/10000000000 : ℝ)|=(5265977709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2024983011/10000000000 : ℝ)|^4355 ≤ (2478761700177/20000000000000 : ℝ)^3331
        have hw : |(-2024983011/10000000000 : ℝ)|=(2024983011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_box_7 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2082474929/5000000000 : ℝ)*x 0 + (4390676159/10000000000 : ℝ)*x 1 + (274417259/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2082474929/5000000000 : ℝ)^4355 ≤ (31817938967943/100000000000000 : ℝ)^3331 := by
    have hnat : (2082474929 : ℕ)^4355*100000000000000^3331 ≤ 31817938967943^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082474929 5000000000 31817938967943 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4390676159/10000000000 : ℝ)^4355 ≤ (3409103058663/10000000000000 : ℝ)^3331 := by
    have hnat : (4390676159 : ℕ)^4355*10000000000000^3331 ≤ 3409103058663^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4390676159 10000000000 3409103058663 10000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274417259/625000000 : ℝ)^4355 ≤ (34091030434361/100000000000000 : ℝ)^3331 := by
    have hnat : (274417259 : ℕ)^4355*100000000000000^3331 ≤ 34091030434361^3331*625000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274417259 625000000 34091030434361 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2082474929/5000000000 : ℝ), (4390676159/10000000000 : ℝ), (274417259/625000000 : ℝ)] ![(31817938967943/100000000000000 : ℝ), (3409103058663/10000000000000 : ℝ), (34091030434361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2082474929/5000000000 : ℝ)|^4355 ≤ (31817938967943/100000000000000 : ℝ)^3331
        have hw : |(2082474929/5000000000 : ℝ)|=(2082474929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4390676159/10000000000 : ℝ)|^4355 ≤ (3409103058663/10000000000000 : ℝ)^3331
        have hw : |(4390676159/10000000000 : ℝ)|=(4390676159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(274417259/625000000 : ℝ)|^4355 ≤ (34091030434361/100000000000000 : ℝ)^3331
        have hw : |(274417259/625000000 : ℝ)|=(274417259/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_box_8 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2095726439/10000000000 : ℝ)*x 0 + (1036386479/2000000000 : ℝ)*x 1 + (2700850717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095726439/10000000000 : ℝ)^4355 ≤ (3240727730501/25000000000000 : ℝ)^3331 := by
    have hnat : (2095726439 : ℕ)^4355*25000000000000^3331 ≤ 3240727730501^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095726439 10000000000 3240727730501 25000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036386479/2000000000 : ℝ)^4355 ≤ (8467440685487/20000000000000 : ℝ)^3331 := by
    have hnat : (1036386479 : ℕ)^4355*20000000000000^3331 ≤ 8467440685487^3331*2000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036386479 2000000000 8467440685487 20000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700850717/5000000000 : ℝ)^4355 ≤ (44699885631039/100000000000000 : ℝ)^3331 := by
    have hnat : (2700850717 : ℕ)^4355*100000000000000^3331 ≤ 44699885631039^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700850717 5000000000 44699885631039 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2095726439/10000000000 : ℝ), (1036386479/2000000000 : ℝ), (2700850717/5000000000 : ℝ)] ![(3240727730501/25000000000000 : ℝ), (8467440685487/20000000000000 : ℝ), (44699885631039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2095726439/10000000000 : ℝ)|^4355 ≤ (3240727730501/25000000000000 : ℝ)^3331
        have hw : |(-2095726439/10000000000 : ℝ)|=(2095726439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036386479/2000000000 : ℝ)|^4355 ≤ (8467440685487/20000000000000 : ℝ)^3331
        have hw : |(1036386479/2000000000 : ℝ)|=(1036386479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700850717/5000000000 : ℝ)|^4355 ≤ (44699885631039/100000000000000 : ℝ)^3331
        have hw : |(2700850717/5000000000 : ℝ)|=(2700850717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_box_9 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275968223/10000000000 : ℝ)*x 0 + (-984998809/5000000000 : ℝ)*x 1 + (1350425011/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275968223/10000000000 : ℝ)^4355 ≤ (43344464332377/100000000000000 : ℝ)^3331 := by
    have hnat : (5275968223 : ℕ)^4355*100000000000000^3331 ≤ 43344464332377^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275968223 10000000000 43344464332377 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (984998809/5000000000 : ℝ)^4355 ≤ (11955665068889/100000000000000 : ℝ)^3331 := by
    have hnat : (984998809 : ℕ)^4355*100000000000000^3331 ≤ 11955665068889^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984998809 5000000000 11955665068889 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350425011/2500000000 : ℝ)^4355 ≤ (5587483824069/12500000000000 : ℝ)^3331 := by
    have hnat : (1350425011 : ℕ)^4355*12500000000000^3331 ≤ 5587483824069^3331*2500000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350425011 2500000000 5587483824069 12500000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275968223/10000000000 : ℝ), (-984998809/5000000000 : ℝ), (1350425011/2500000000 : ℝ)] ![(43344464332377/100000000000000 : ℝ), (11955665068889/100000000000000 : ℝ), (5587483824069/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275968223/10000000000 : ℝ)|^4355 ≤ (43344464332377/100000000000000 : ℝ)^3331
        have hw : |(5275968223/10000000000 : ℝ)|=(5275968223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-984998809/5000000000 : ℝ)|^4355 ≤ (11955665068889/100000000000000 : ℝ)^3331
        have hw : |(-984998809/5000000000 : ℝ)|=(984998809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350425011/2500000000 : ℝ)|^4355 ≤ (5587483824069/12500000000000 : ℝ)^3331
        have hw : |(1350425011/2500000000 : ℝ)|=(1350425011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_box_10 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275970219/10000000000 : ℝ)*x 0 + (5401699099/10000000000 : ℝ)*x 1 + (-492499051/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275970219/10000000000 : ℝ)^4355 ≤ (10836121442857/25000000000000 : ℝ)^3331 := by
    have hnat : (5275970219 : ℕ)^4355*25000000000000^3331 ≤ 10836121442857^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275970219 10000000000 10836121442857 25000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401699099/10000000000 : ℝ)^4355 ≤ (8939972073709/20000000000000 : ℝ)^3331 := by
    have hnat : (5401699099 : ℕ)^4355*20000000000000^3331 ≤ 8939972073709^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401699099 10000000000 8939972073709 20000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (492499051/2500000000 : ℝ)^4355 ≤ (747228365591/6250000000000 : ℝ)^3331 := by
    have hnat : (492499051 : ℕ)^4355*6250000000000^3331 ≤ 747228365591^3331*2500000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492499051 2500000000 747228365591 6250000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275970219/10000000000 : ℝ), (5401699099/10000000000 : ℝ), (-492499051/2500000000 : ℝ)] ![(10836121442857/25000000000000 : ℝ), (8939972073709/20000000000000 : ℝ), (747228365591/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275970219/10000000000 : ℝ)|^4355 ≤ (10836121442857/25000000000000 : ℝ)^3331
        have hw : |(5275970219/10000000000 : ℝ)|=(5275970219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401699099/10000000000 : ℝ)|^4355 ≤ (8939972073709/20000000000000 : ℝ)^3331
        have hw : |(5401699099/10000000000 : ℝ)|=(5401699099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-492499051/2500000000 : ℝ)|^4355 ≤ (747228365591/6250000000000 : ℝ)^3331
        have hw : |(-492499051/2500000000 : ℝ)|=(492499051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_box_11 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4493305313/10000000000 : ℝ)*x 0 + (169050523/400000000 : ℝ)*x 1 + (4226263127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4493305313/10000000000 : ℝ)^4355 ≤ (7027314878987/20000000000000 : ℝ)^3331 := by
    have hnat : (4493305313 : ℕ)^4355*20000000000000^3331 ≤ 7027314878987^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493305313 10000000000 7027314878987 20000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169050523/400000000 : ℝ)^4355 ≤ (16215856268333/50000000000000 : ℝ)^3331 := by
    have hnat : (169050523 : ℕ)^4355*50000000000000^3331 ≤ 16215856268333^3331*400000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169050523 400000000 16215856268333 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4226263127/10000000000 : ℝ)^4355 ≤ (32431713058377/100000000000000 : ℝ)^3331 := by
    have hnat : (4226263127 : ℕ)^4355*100000000000000^3331 ≤ 32431713058377^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226263127 10000000000 32431713058377 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4493305313/10000000000 : ℝ), (169050523/400000000 : ℝ), (4226263127/10000000000 : ℝ)] ![(7027314878987/20000000000000 : ℝ), (16215856268333/50000000000000 : ℝ), (32431713058377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4493305313/10000000000 : ℝ)|^4355 ≤ (7027314878987/20000000000000 : ℝ)^3331
        have hw : |(4493305313/10000000000 : ℝ)|=(4493305313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169050523/400000000 : ℝ)|^4355 ≤ (16215856268333/50000000000000 : ℝ)^3331
        have hw : |(169050523/400000000 : ℝ)|=(169050523/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4226263127/10000000000 : ℝ)|^4355 ≤ (32431713058377/100000000000000 : ℝ)^3331
        have hw : |(4226263127/10000000000 : ℝ)|=(4226263127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_box_12 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-952684059/5000000000 : ℝ)*x 0 + (2734829429/5000000000 : ℝ)*x 1 + (5254870767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (952684059/5000000000 : ℝ)^4355 ≤ (572273285329/5000000000000 : ℝ)^3331 := by
    have hnat : (952684059 : ℕ)^4355*5000000000000^3331 ≤ 572273285329^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952684059 5000000000 572273285329 5000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734829429/5000000000 : ℝ)^4355 ≤ (9087307690891/20000000000000 : ℝ)^3331 := by
    have hnat : (2734829429 : ℕ)^4355*20000000000000^3331 ≤ 9087307690891^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734829429 5000000000 9087307690891 20000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254870767/10000000000 : ℝ)^4355 ≤ (5389749477967/12500000000000 : ℝ)^3331 := by
    have hnat : (5254870767 : ℕ)^4355*12500000000000^3331 ≤ 5389749477967^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254870767 10000000000 5389749477967 12500000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-952684059/5000000000 : ℝ), (2734829429/5000000000 : ℝ), (5254870767/10000000000 : ℝ)] ![(572273285329/5000000000000 : ℝ), (9087307690891/20000000000000 : ℝ), (5389749477967/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-952684059/5000000000 : ℝ)|^4355 ≤ (572273285329/5000000000000 : ℝ)^3331
        have hw : |(-952684059/5000000000 : ℝ)|=(952684059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734829429/5000000000 : ℝ)|^4355 ≤ (9087307690891/20000000000000 : ℝ)^3331
        have hw : |(2734829429/5000000000 : ℝ)|=(2734829429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254870767/10000000000 : ℝ)|^4355 ≤ (5389749477967/12500000000000 : ℝ)^3331
        have hw : |(5254870767/10000000000 : ℝ)|=(5254870767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_box_13 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537887381/1000000000 : ℝ)*x 0 + (-507342807/2500000000 : ℝ)*x 1 + (5254870461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537887381/1000000000 : ℝ)^4355 ≤ (44453072875169/100000000000000 : ℝ)^3331 := by
    have hnat : (537887381 : ℕ)^4355*100000000000000^3331 ≤ 44453072875169^3331*1000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537887381 1000000000 44453072875169 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (507342807/2500000000 : ℝ)^4355 ≤ (12428934572519/100000000000000 : ℝ)^3331 := by
    have hnat : (507342807 : ℕ)^4355*100000000000000^3331 ≤ 12428934572519^3331*2500000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507342807 2500000000 12428934572519 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254870461/10000000000 : ℝ)^4355 ≤ (21558996270517/50000000000000 : ℝ)^3331 := by
    have hnat : (5254870461 : ℕ)^4355*50000000000000^3331 ≤ 21558996270517^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254870461 10000000000 21558996270517 50000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537887381/1000000000 : ℝ), (-507342807/2500000000 : ℝ), (5254870461/10000000000 : ℝ)] ![(44453072875169/100000000000000 : ℝ), (12428934572519/100000000000000 : ℝ), (21558996270517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537887381/1000000000 : ℝ)|^4355 ≤ (44453072875169/100000000000000 : ℝ)^3331
        have hw : |(537887381/1000000000 : ℝ)|=(537887381/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-507342807/2500000000 : ℝ)|^4355 ≤ (12428934572519/100000000000000 : ℝ)^3331
        have hw : |(-507342807/2500000000 : ℝ)|=(507342807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254870461/10000000000 : ℝ)|^4355 ≤ (21558996270517/50000000000000 : ℝ)^3331
        have hw : |(5254870461/10000000000 : ℝ)|=(5254870461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_box_14 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344718277/2500000000 : ℝ)*x 0 + (5254870921/10000000000 : ℝ)*x 1 + (-2029371559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344718277/2500000000 : ℝ)^4355 ≤ (44453065290073/100000000000000 : ℝ)^3331 := by
    have hnat : (1344718277 : ℕ)^4355*100000000000000^3331 ≤ 44453065290073^3331*2500000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344718277 2500000000 44453065290073 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254870921/10000000000 : ℝ)^4355 ≤ (8623599495163/20000000000000 : ℝ)^3331 := by
    have hnat : (5254870921 : ℕ)^4355*20000000000000^3331 ≤ 8623599495163^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254870921 10000000000 8623599495163 20000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2029371559/10000000000 : ℝ)^4355 ≤ (2485787444587/20000000000000 : ℝ)^3331 := by
    have hnat : (2029371559 : ℕ)^4355*20000000000000^3331 ≤ 2485787444587^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029371559 10000000000 2485787444587 20000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344718277/2500000000 : ℝ), (5254870921/10000000000 : ℝ), (-2029371559/10000000000 : ℝ)] ![(44453065290073/100000000000000 : ℝ), (8623599495163/20000000000000 : ℝ), (2485787444587/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344718277/2500000000 : ℝ)|^4355 ≤ (44453065290073/100000000000000 : ℝ)^3331
        have hw : |(1344718277/2500000000 : ℝ)|=(1344718277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254870921/10000000000 : ℝ)|^4355 ≤ (8623599495163/20000000000000 : ℝ)^3331
        have hw : |(5254870921/10000000000 : ℝ)|=(5254870921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2029371559/10000000000 : ℝ)|^4355 ≤ (2485787444587/20000000000000 : ℝ)^3331
        have hw : |(-2029371559/10000000000 : ℝ)|=(2029371559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1395_box_15 (p : ℝ) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4137583033/10000000000 : ℝ)*x 0 + (4404119127/10000000000 : ℝ)*x 1 + (2202059837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4137583033/10000000000 : ℝ)^4355 ≤ (6308975465693/20000000000000 : ℝ)^3331 := by
    have hnat : (4137583033 : ℕ)^4355*20000000000000^3331 ≤ 6308975465693^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137583033 10000000000 6308975465693 20000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4404119127/10000000000 : ℝ)^4355 ≤ (34227558548077/100000000000000 : ℝ)^3331 := by
    have hnat : (4404119127 : ℕ)^4355*100000000000000^3331 ≤ 34227558548077^3331*10000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4404119127 10000000000 34227558548077 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2202059837/5000000000 : ℝ)^4355 ≤ (34227564106067/100000000000000 : ℝ)^3331 := by
    have hnat : (2202059837 : ℕ)^4355*100000000000000^3331 ≤ 34227564106067^3331*5000000000^4355 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202059837 5000000000 34227564106067 100000000000000 4355 3331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4355/1024 : ℝ)) 4355 3331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4137583033/10000000000 : ℝ), (4404119127/10000000000 : ℝ), (2202059837/5000000000 : ℝ)] ![(6308975465693/20000000000000 : ℝ), (34227558548077/100000000000000 : ℝ), (34227564106067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4137583033/10000000000 : ℝ)|^4355 ≤ (6308975465693/20000000000000 : ℝ)^3331
        have hw : |(4137583033/10000000000 : ℝ)|=(4137583033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4404119127/10000000000 : ℝ)|^4355 ≤ (34227558548077/100000000000000 : ℝ)^3331
        have hw : |(4404119127/10000000000 : ℝ)|=(4404119127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2202059837/5000000000 : ℝ)|^4355 ≤ (34227564106067/100000000000000 : ℝ)^3331
        have hw : |(2202059837/5000000000 : ℝ)|=(2202059837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1395_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (627283/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(393/625 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11809/20000 : ℝ) ∧ (80259/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21139/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7369/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7369/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7369/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7369/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7369/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7369/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11269/100000 : ℝ) ^ (2177/512 : ℝ) ≤ (372152606645519/4000000000000000000 : ℝ) := by
    have hpowers : (11269/100000 : ℝ)^2177 ≤ (372152606645519/4000000000000000000 : ℝ)^512 := by
      have hnat : (11269 : ℕ)^2177*4000000000000000000^512 ≤ 372152606645519^512*100000^2177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11269 100000 372152606645519 4000000000000000000 2177 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11269/100000 : ℝ)) (X := (372152606645519/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7369/50000 : ℝ) ^ (2177/512 : ℝ) ≤ (5824648189928169/20000000000000000000 : ℝ) := by
    have hpowers : (7369/50000 : ℝ)^2177 ≤ (5824648189928169/20000000000000000000 : ℝ)^512 := by
      have hnat : (7369 : ℕ)^2177*20000000000000000000^512 ≤ 5824648189928169^512*50000^2177 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7369 50000 5824648189928169 20000000000000000000 2177 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7369/50000 : ℝ)) (X := (5824648189928169/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000372152606645519/2000000000000000000 : ℝ) ≤ (2500109398586187/2500000000000000 : ℝ) ^ (2177/512 : ℝ) := by
    have hpowers : (2000372152606645519/2000000000000000000 : ℝ)^512 ≤ (2500109398586187/2500000000000000 : ℝ)^2177 := by
      have hnat : (2000372152606645519 : ℕ)^512*2500000000000000^2177 ≤ 2500109398586187^2177*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000372152606645519 2000000000000000000 2500109398586187 2500000000000000 512 2177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500109398586187/2500000000000000 : ℝ)) (X := (2000372152606645519/2000000000000000000 : ℝ)) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (5001921352805788941/5000000000000000000 : ℝ) ≤ (10000903617925531/10000000000000000 : ℝ) ^ (2177/512 : ℝ) := by
    have hpowers : (5001921352805788941/5000000000000000000 : ℝ)^512 ≤ (10000903617925531/10000000000000000 : ℝ)^2177 := by
      have hnat : (5001921352805788941 : ℕ)^512*10000000000000000^2177 ≤ 10000903617925531^2177*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001921352805788941 5000000000000000000 10000903617925531 10000000000000000 512 2177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000903617925531/10000000000000000 : ℝ)) (X := (5001921352805788941/5000000000000000000 : ℝ)) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005824648189928169/10000000000000000000 : ℝ) ≤ (5000684820753157/5000000000000000 : ℝ) ^ (2177/512 : ℝ) := by
    have hpowers : (10005824648189928169/10000000000000000000 : ℝ)^512 ≤ (5000684820753157/5000000000000000 : ℝ)^2177 := by
      have hnat : (10005824648189928169 : ℕ)^512*5000000000000000^2177 ≤ 5000684820753157^2177*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005824648189928169 10000000000000000000 5000684820753157 5000000000000000 512 2177 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000684820753157/5000000000000000 : ℝ)) (X := (10005824648189928169/10000000000000000000 : ℝ)) (by norm_num) 2177 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(372152606645519/4000000000000000000 : ℝ) ≤ ((17340507387659121779/17345000000000000000 : ℝ)+2*(466023580783/346900000000000 : ℝ)*(11269/100000 : ℝ))^(2177/512 : ℝ) := by
    rw [show (17340507387659121779/17345000000000000000 : ℝ)+2*(466023580783/346900000000000 : ℝ)*(11269/100000 : ℝ)=(2500109398586187/2500000000000000 : ℝ) by norm_num, show 1+2*(372152606645519/4000000000000000000 : ℝ)=(2000372152606645519/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5824648189928169/20000000000000000000 : ℝ)+(372152606645519/4000000000000000000 : ℝ) ≤ ((17340507387659121779/17345000000000000000 : ℝ)+(466023580783/346900000000000 : ℝ)*((7369/50000 : ℝ)+(11269/100000 : ℝ)))^(2177/512 : ℝ) := by
    rw [show (17340507387659121779/17345000000000000000 : ℝ)+(466023580783/346900000000000 : ℝ)*((7369/50000 : ℝ)+(11269/100000 : ℝ))=(10000903617925531/10000000000000000 : ℝ) by norm_num, show 1+(5824648189928169/20000000000000000000 : ℝ)+(372152606645519/4000000000000000000 : ℝ)=(5001921352805788941/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5824648189928169/20000000000000000000 : ℝ) ≤ ((17340507387659121779/17345000000000000000 : ℝ)+2*(466023580783/346900000000000 : ℝ)*(7369/50000 : ℝ))^(2177/512 : ℝ) := by
    rw [show (17340507387659121779/17345000000000000000 : ℝ)+2*(466023580783/346900000000000 : ℝ)*(7369/50000 : ℝ)=(5000684820753157/5000000000000000 : ℝ) by norm_num, show 1+2*(5824648189928169/20000000000000000000 : ℝ)=(10005824648189928169/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17340507387659121779/17345000000000000000 : ℝ)*(X 1 0+X 2 0)+(466023580783/346900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2177/512 : ℝ)) (lo := (11269/100000 : ℝ)) (hi := (7369/50000 : ℝ)) (c := (17340507387659121779/17345000000000000000 : ℝ)) (alpha := (466023580783/346900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17340507387659121779/17345000000000000000 : ℝ)*(X 0 1+X 2 1)+(466023580783/346900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2177/512 : ℝ)) (lo := (11269/100000 : ℝ)) (hi := (7369/50000 : ℝ)) (c := (17340507387659121779/17345000000000000000 : ℝ)) (alpha := (466023580783/346900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17340507387659121779/17345000000000000000 : ℝ)*(X 0 2+X 1 2)+(466023580783/346900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2177/512 : ℝ)) (lo := (11269/100000 : ℝ)) (hi := (7369/50000 : ℝ)) (c := (17340507387659121779/17345000000000000000 : ℝ)) (alpha := (466023580783/346900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1835895159/10000000000 : ℝ)*X 0 0+(8418291/15625000 : ℝ)*X 0 1+(5387706231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642890493/5000000000 : ℝ)*X 1 0+(-1975781053/10000000000 : ℝ)*X 1 1+(538770631/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642890597/5000000000 : ℝ)*X 2 0+(5387706141/10000000000 : ℝ)*X 2 1+(-1975781003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4459950519/10000000000 : ℝ)*X 0 0+(4243227867/10000000000 : ℝ)*X 0 1+(1060806893/2500000000 : ℝ)*X 0 2+(4459950519/10000000000 : ℝ)*X 1 0+(4243227867/10000000000 : ℝ)*X 1 1+(1060806893/2500000000 : ℝ)*X 1 2+(4459950519/10000000000 : ℝ)*X 2 0+(4243227867/10000000000 : ℝ)*X 2 1+(1060806893/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-216496053/1000000000 : ℝ)*X 0 0+(2632988963/5000000000 : ℝ)*X 0 1+(2632988943/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5371091161/10000000000 : ℝ)*X 1 0+(-2024982783/10000000000 : ℝ)*X 1 1+(5265978239/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5371091519/10000000000 : ℝ)*X 2 0+(5265977709/10000000000 : ℝ)*X 2 1+(-2024983011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2082474929/5000000000 : ℝ)*X 0 0+(4390676159/10000000000 : ℝ)*X 0 1+(274417259/625000000 : ℝ)*X 0 2+(2082474929/5000000000 : ℝ)*X 1 0+(4390676159/10000000000 : ℝ)*X 1 1+(274417259/625000000 : ℝ)*X 1 2+(2082474929/5000000000 : ℝ)*X 2 0+(4390676159/10000000000 : ℝ)*X 2 1+(274417259/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2095726439/10000000000 : ℝ)*X 0 0+(1036386479/2000000000 : ℝ)*X 0 1+(2700850717/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275968223/10000000000 : ℝ)*X 1 0+(-984998809/5000000000 : ℝ)*X 1 1+(1350425011/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275970219/10000000000 : ℝ)*X 2 0+(5401699099/10000000000 : ℝ)*X 2 1+(-492499051/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4493305313/10000000000 : ℝ)*X 0 0+(169050523/400000000 : ℝ)*X 0 1+(4226263127/10000000000 : ℝ)*X 0 2+(4493305313/10000000000 : ℝ)*X 1 0+(169050523/400000000 : ℝ)*X 1 1+(4226263127/10000000000 : ℝ)*X 1 2+(4493305313/10000000000 : ℝ)*X 2 0+(169050523/400000000 : ℝ)*X 2 1+(4226263127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-952684059/5000000000 : ℝ)*X 0 0+(2734829429/5000000000 : ℝ)*X 0 1+(5254870767/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((537887381/1000000000 : ℝ)*X 1 0+(-507342807/2500000000 : ℝ)*X 1 1+(5254870461/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1344718277/2500000000 : ℝ)*X 2 0+(5254870921/10000000000 : ℝ)*X 2 1+(-2029371559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4137583033/10000000000 : ℝ)*X 0 0+(4404119127/10000000000 : ℝ)*X 0 1+(2202059837/5000000000 : ℝ)*X 0 2+(4137583033/10000000000 : ℝ)*X 1 0+(4404119127/10000000000 : ℝ)*X 1 1+(2202059837/5000000000 : ℝ)*X 1 2+(4137583033/10000000000 : ℝ)*X 2 0+(4404119127/10000000000 : ℝ)*X 2 1+(2202059837/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1395_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-393/625 : ℝ) ≤ (-272652020713208990288672229644763/433625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (83647/1562500000000 : ℝ)*(upper0) + (199249/12500000000000 : ℝ)*(upper2) + (95650321/100000000000000 : ℝ)*(upper3) + (79146901/100000000000000 : ℝ)*(upper5) + (1489785580892701/50000000000000 : ℝ)*(major0) + (1489785580892701/50000000000000 : ℝ)*(major1) + (1489785580892701/50000000000000 : ℝ)*(major2) + (416737097/3125000000000 : ℝ)*(sp2) + (1557085387/25000000000000 : ℝ)*(sp3) + (2040058085754077/50000000000000 : ℝ)*(sp4) + (1020018154610251/25000000000000 : ℝ)*(sp5) + (81602056718421/2000000000000 : ℝ)*(sp6) + (1899979048980109/100000000000000 : ℝ)*(sp7) + (43553067149/100000000000000 : ℝ)*(sp13) + (1899985277321657/100000000000000 : ℝ)*(f.failure) + (2040058085754077/50000000000000 : ℝ)*(f.sum) + (2029162884141/4336250000000000000000000000 : ℝ)*base66 + (8446618761494364921/867250000000000000000000000000000 : ℝ)*base68 + (4847371292895614921/867250000000000000000000000000000 : ℝ)*base70 + (1356870146437614921/867250000000000000000000000000000 : ℝ)*base72 + (178651879660431/17345000000000000000000000000 : ℝ)*base73 + (1946478574037135079/867250000000000000000000000000000 : ℝ)*base75 + (10349267270049614921/867250000000000000000000000000000 : ℝ)*base78 + (18653147221458135079/867250000000000000000000000000000 : ℝ)*base79 + (2671959807571/4336250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (167931/40000000000000000000 : ℝ)*base89 + (167931/40000000000000000000 : ℝ)*base91 + (167931/40000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (11809/20000 : ℝ) ≤ (32005741918147030274583842142237/54203125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (689249/50000000000000 : ℝ)*(lower1) + (5248291/6250000000000 : ℝ)*(upper4) + (36896757/100000000000000 : ℝ)*(lower5) + (190626840525049/6250000000000 : ℝ)*(major0) + (190626840525049/6250000000000 : ℝ)*(major1) + (190626840525049/6250000000000 : ℝ)*(major2) + (827092072999649/20000000000000 : ℝ)*(sp0) + (206772971953519/5000000000000 : ℝ)*(sp1) + (1033864919695447/25000000000000 : ℝ)*(sp2) + (194491278959653/10000000000000 : ℝ)*(sp3) + (600256401/25000000000000 : ℝ)*(sp5) + (432262839/20000000000000 : ℝ)*(sp6) + (66953119/4000000000000 : ℝ)*(sp7) + (737548869/50000000000000 : ℝ)*(sp8) + (388982892684901/20000000000000 : ℝ)*(f.failure) + (258466365005999/6250000000000 : ℝ)*(f.sum) + (69495641637763/17345000000000000000000000000 : ℝ)*base66 + (33605024531010921/108406250000000000000000000000000 : ℝ)*base67 + (463061413739198421/108406250000000000000000000000000 : ℝ)*base69 + (255908685119957829/108406250000000000000000000000000 : ℝ)*base72 + (6640621268137/17345000000000000000000000000 : ℝ)*base73 + (108507036077917171/108406250000000000000000000000000 : ℝ)*base75 + (190867770268614079/108406250000000000000000000000000 : ℝ)*base78 + (780213172160479671/108406250000000000000000000000000 : ℝ)*base79 + (12792293305723/17345000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (33983/8000000000000000000 : ℝ)*base89 + (33983/8000000000000000000 : ℝ)*base91 + (33983/8000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80259/100000 : ℝ) ≤ (348033468132721513426642339585443/433625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26734821/6250000000000 : ℝ)*(upper0) + (20343571/12500000000000 : ℝ)*(lower3) + (1016752617/100000000000000 : ℝ)*(upper4) + (3359731003807939/100000000000000 : ℝ)*(major0) + (3359731003807939/100000000000000 : ℝ)*(major1) + (3359731003807939/100000000000000 : ℝ)*(major2) + (123609919787/50000000000000 : ℝ)*(sp1) + (178933532099/50000000000000 : ℝ)*(sp2) + (206251966319/100000000000000 : ℝ)*(sp3) + (30049938397/50000000000000 : ℝ)*(sp4) + (142195188554021/3125000000000 : ℝ)*(sp8) + (1137514728441473/25000000000000 : ℝ)*(sp9) + (1137487066635317/25000000000000 : ℝ)*(sp10) + (1071097912083531/50000000000000 : ℝ)*(sp11) + (2142402076133381/100000000000000 : ℝ)*(f.failure) + (2275153066802733/50000000000000 : ℝ)*(f.sum) + (11240184162359/8672500000000000000000000000 : ℝ)*base66 + (23299045036351646519/1734500000000000000000000000000000 : ℝ)*base68 + (20090111746313146519/1734500000000000000000000000000000 : ℝ)*base70 + (13493455055281646519/1734500000000000000000000000000000 : ℝ)*base72 + (27827397083303/4336250000000000000000000000 : ℝ)*base73 + (7275136714445146519/1734500000000000000000000000000000 : ℝ)*base76 + (10386619043809646519/1734500000000000000000000000000000 : ℝ)*base78 + (46415750294021353481/1734500000000000000000000000000000 : ℝ)*base79 + (48713344166983/17345000000000000000000000000 : ℝ)*base82 + (33823/40000000000000000000 : ℝ)*base89 + (33823/40000000000000000000 : ℝ)*base91 + (33823/40000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-21139/25000 : ℝ) ≤ (-366646403977032400628147238851787/433625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (384250009/100000000000000 : ℝ)*(upper3) + (144227089/50000000000000 : ℝ)*(lower4) + (326997553/100000000000000 : ℝ)*(upper5) + (1698411507641383/50000000000000 : ℝ)*(major0) + (1698411507641383/50000000000000 : ℝ)*(major1) + (1698411507641383/50000000000000 : ℝ)*(major2) + (3592265909/25000000000000 : ℝ)*(sp4) + (122138884737/25000000000000 : ℝ)*(sp5) + (439298870019/100000000000000 : ℝ)*(sp6) + (31954426193/10000000000000 : ℝ)*(sp7) + (931152338994361/20000000000000 : ℝ)*(sp12) + (4655287508496493/100000000000000 : ℝ)*(sp13) + (2327668382582711/50000000000000 : ℝ)*(sp14) + (433147004280317/20000000000000 : ℝ)*(sp15) + (433210913132703/20000000000000 : ℝ)*(f.failure) + (4655776064035441/100000000000000 : ℝ)*(f.sum) + (59297717165403/17345000000000000000000000000 : ℝ)*base65 + (550200402393319643/867250000000000000000000000000000 : ℝ)*base68 + (12107536716430819643/867250000000000000000000000000000 : ℝ)*base70 + (5132454027450319643/867250000000000000000000000000000 : ℝ)*base72 + (200824343497213/17345000000000000000000000000 : ℝ)*base73 + (13830127564847319643/867250000000000000000000000000000 : ℝ)*base76 + (9497282932113069643/867250000000000000000000000000000 : ℝ)*base78 + (8373751551589069643/867250000000000000000000000000000 : ℝ)*base80 + (1288158445757/17345000000000000000000000000 : ℝ)*base82 + (55949/8000000000000000000 : ℝ)*base89 + (55949/8000000000000000000 : ℝ)*base91 + (55949/8000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1395_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (627283/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(393/625 : ℝ) ≤ X j i ∧ X j i ≤ -(11809/20000 : ℝ) else (80259/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21139/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1395_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1395_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (627283/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1843/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(393/625 : ℝ) ≤ X j i ∧ X j i ≤ -(11809/20000 : ℝ) else (80259/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21139/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1395_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1395_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1395_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2177/512 : ℝ) ≤ p) (hpb : p ≤ (4355/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (627283/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1843/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(393/625 : ℝ) ≤ X j i ∧ X j i ≤ -(11809/20000 : ℝ) else (80259/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21139/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1395_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

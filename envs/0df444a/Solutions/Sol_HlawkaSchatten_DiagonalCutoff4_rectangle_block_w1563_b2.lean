-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1563_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:25:16.507889+00:00
-- url     : https://prove2.me/submissions/c65bc27d-c33b-47fb-9e55-eaa4796361e5

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
theorem support_rectangle_w1563_s6_0 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-897610633/5000000000 : ℝ)*x 0 + (5426675239/10000000000 : ℝ)*x 1 + (5219823323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (897610633/5000000000 : ℝ)^4623 ≤ (43018679289/390625000000 : ℝ)^3599 := by
    have hnat : (897610633 : ℕ)^4623*390625000000^3599 ≤ 43018679289^3599*5000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897610633 5000000000 43018679289 390625000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426675239/10000000000 : ℝ)^4623 ≤ (45603951405827/100000000000000 : ℝ)^3599 := by
    have hnat : (5426675239 : ℕ)^4623*100000000000000^3599 ≤ 45603951405827^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426675239 10000000000 45603951405827 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219823323/10000000000 : ℝ)^4623 ≤ (21691633344427/50000000000000 : ℝ)^3599 := by
    have hnat : (5219823323 : ℕ)^4623*50000000000000^3599 ≤ 21691633344427^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219823323 10000000000 21691633344427 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-897610633/5000000000 : ℝ), (5426675239/10000000000 : ℝ), (5219823323/10000000000 : ℝ)] ![(43018679289/390625000000 : ℝ), (45603951405827/100000000000000 : ℝ), (21691633344427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-897610633/5000000000 : ℝ)|^4623 ≤ (43018679289/390625000000 : ℝ)^3599
        have hw : |(-897610633/5000000000 : ℝ)|=(897610633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426675239/10000000000 : ℝ)|^4623 ≤ (45603951405827/100000000000000 : ℝ)^3599
        have hw : |(5426675239/10000000000 : ℝ)|=(5426675239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219823323/10000000000 : ℝ)|^4623 ≤ (21691633344427/50000000000000 : ℝ)^3599
        have hw : |(5219823323/10000000000 : ℝ)|=(5219823323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s6_1 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348615841/10000000000 : ℝ)*x 0 + (-1901057577/10000000000 : ℝ)*x 1 + (5219825083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348615841/10000000000 : ℝ)^4623 ≤ (2238152683361/5000000000000 : ℝ)^3599 := by
    have hnat : (5348615841 : ℕ)^4623*5000000000000^3599 ≤ 2238152683361^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348615841 10000000000 2238152683361 5000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1901057577/10000000000 : ℝ)^4623 ≤ (11853660831621/100000000000000 : ℝ)^3599 := by
    have hnat : (1901057577 : ℕ)^4623*100000000000000^3599 ≤ 11853660831621^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901057577 10000000000 11853660831621 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219825083/10000000000 : ℝ)^4623 ≤ (10845821369653/25000000000000 : ℝ)^3599 := by
    have hnat : (5219825083 : ℕ)^4623*25000000000000^3599 ≤ 10845821369653^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219825083 10000000000 10845821369653 25000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348615841/10000000000 : ℝ), (-1901057577/10000000000 : ℝ), (5219825083/10000000000 : ℝ)] ![(2238152683361/5000000000000 : ℝ), (11853660831621/100000000000000 : ℝ), (10845821369653/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348615841/10000000000 : ℝ)|^4623 ≤ (2238152683361/5000000000000 : ℝ)^3599
        have hw : |(5348615841/10000000000 : ℝ)|=(5348615841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1901057577/10000000000 : ℝ)|^4623 ≤ (11853660831621/100000000000000 : ℝ)^3599
        have hw : |(-1901057577/10000000000 : ℝ)|=(1901057577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219825083/10000000000 : ℝ)|^4623 ≤ (10845821369653/25000000000000 : ℝ)^3599
        have hw : |(5219825083/10000000000 : ℝ)|=(5219825083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s6_2 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334288527/625000000 : ℝ)*x 0 + (1043964929/2000000000 : ℝ)*x 1 + (-237632171/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334288527/625000000 : ℝ)^4623 ≤ (11190765005161/25000000000000 : ℝ)^3599 := by
    have hnat : (334288527 : ℕ)^4623*25000000000000^3599 ≤ 11190765005161^3599*625000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334288527 625000000 11190765005161 25000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043964929/2000000000 : ℝ)^4623 ≤ (10845820200631/25000000000000 : ℝ)^3599 := by
    have hnat : (1043964929 : ℕ)^4623*25000000000000^3599 ≤ 10845820200631^3599*2000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043964929 2000000000 10845820200631 25000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (237632171/1250000000 : ℝ)^4623 ≤ (11853659157659/100000000000000 : ℝ)^3599 := by
    have hnat : (237632171 : ℕ)^4623*100000000000000^3599 ≤ 11853659157659^3599*1250000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237632171 1250000000 11853659157659 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334288527/625000000 : ℝ), (1043964929/2000000000 : ℝ), (-237632171/1250000000 : ℝ)] ![(11190765005161/25000000000000 : ℝ), (10845820200631/25000000000000 : ℝ), (11853659157659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334288527/625000000 : ℝ)|^4623 ≤ (11190765005161/25000000000000 : ℝ)^3599
        have hw : |(334288527/625000000 : ℝ)|=(334288527/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043964929/2000000000 : ℝ)|^4623 ≤ (10845820200631/25000000000000 : ℝ)^3599
        have hw : |(1043964929/2000000000 : ℝ)|=(1043964929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-237632171/1250000000 : ℝ)|^4623 ≤ (11853659157659/100000000000000 : ℝ)^3599
        have hw : |(-237632171/1250000000 : ℝ)|=(237632171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s6_3 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061649867/2500000000 : ℝ)*x 0 + (160371311/400000000 : ℝ)*x 1 + (4495237423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061649867/2500000000 : ℝ)^4623 ≤ (33282069106199/100000000000000 : ℝ)^3599 := by
    have hnat : (1061649867 : ℕ)^4623*100000000000000^3599 ≤ 33282069106199^3599*2500000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061649867 2500000000 33282069106199 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160371311/400000000 : ℝ)^4623 ≤ (30912194792079/100000000000000 : ℝ)^3599 := by
    have hnat : (160371311 : ℕ)^4623*100000000000000^3599 ≤ 30912194792079^3599*400000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160371311 400000000 30912194792079 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4495237423/10000000000 : ℝ)^4623 ≤ (8951434020579/25000000000000 : ℝ)^3599 := by
    have hnat : (4495237423 : ℕ)^4623*25000000000000^3599 ≤ 8951434020579^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495237423 10000000000 8951434020579 25000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061649867/2500000000 : ℝ), (160371311/400000000 : ℝ), (4495237423/10000000000 : ℝ)] ![(33282069106199/100000000000000 : ℝ), (30912194792079/100000000000000 : ℝ), (8951434020579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061649867/2500000000 : ℝ)|^4623 ≤ (33282069106199/100000000000000 : ℝ)^3599
        have hw : |(1061649867/2500000000 : ℝ)|=(1061649867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160371311/400000000 : ℝ)|^4623 ≤ (30912194792079/100000000000000 : ℝ)^3599
        have hw : |(160371311/400000000 : ℝ)|=(160371311/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4495237423/10000000000 : ℝ)|^4623 ≤ (8951434020579/25000000000000 : ℝ)^3599
        have hw : |(4495237423/10000000000 : ℝ)|=(4495237423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s6_4 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-22440629/125000000 : ℝ)*x 0 + (1305224851/2500000000 : ℝ)*x 1 + (5425589719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22440629/125000000 : ℝ)^4623 ≤ (11013010841333/100000000000000 : ℝ)^3599 := by
    have hnat : (22440629 : ℕ)^4623*100000000000000^3599 ≤ 11013010841333^3599*125000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22440629 125000000 11013010841333 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305224851/2500000000 : ℝ)^4623 ≤ (43394755264631/100000000000000 : ℝ)^3599 := by
    have hnat : (1305224851 : ℕ)^4623*100000000000000^3599 ≤ 43394755264631^3599*2500000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305224851 2500000000 43394755264631 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425589719/10000000000 : ℝ)^4623 ≤ (356189327137/781250000000 : ℝ)^3599 := by
    have hnat : (5425589719 : ℕ)^4623*781250000000^3599 ≤ 356189327137^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425589719 10000000000 356189327137 781250000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22440629/125000000 : ℝ), (1305224851/2500000000 : ℝ), (5425589719/10000000000 : ℝ)] ![(11013010841333/100000000000000 : ℝ), (43394755264631/100000000000000 : ℝ), (356189327137/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22440629/125000000 : ℝ)|^4623 ≤ (11013010841333/100000000000000 : ℝ)^3599
        have hw : |(-22440629/125000000 : ℝ)|=(22440629/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305224851/2500000000 : ℝ)|^4623 ≤ (43394755264631/100000000000000 : ℝ)^3599
        have hw : |(1305224851/2500000000 : ℝ)|=(1305224851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425589719/10000000000 : ℝ)|^4623 ≤ (356189327137/781250000000 : ℝ)^3599
        have hw : |(5425589719/10000000000 : ℝ)|=(5425589719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s6_5 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1674305543/2000000000 : ℝ)*x 0 + (-685919197/10000000000 : ℝ)*x 1 + (2541661183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1674305543/2000000000 : ℝ)^4623 ≤ (15917352907611/20000000000000 : ℝ)^3599 := by
    have hnat : (1674305543 : ℕ)^4623*20000000000000^3599 ≤ 15917352907611^3599*2000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674305543 2000000000 15917352907611 20000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (685919197/10000000000 : ℝ)^4623 ≤ (400014104089/12500000000000 : ℝ)^3599 := by
    have hnat : (685919197 : ℕ)^4623*12500000000000^3599 ≤ 400014104089^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685919197 10000000000 400014104089 12500000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2541661183/10000000000 : ℝ)^4623 ≤ (215164032707/1250000000000 : ℝ)^3599 := by
    have hnat : (2541661183 : ℕ)^4623*1250000000000^3599 ≤ 215164032707^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541661183 10000000000 215164032707 1250000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1674305543/2000000000 : ℝ), (-685919197/10000000000 : ℝ), (2541661183/10000000000 : ℝ)] ![(15917352907611/20000000000000 : ℝ), (400014104089/12500000000000 : ℝ), (215164032707/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1674305543/2000000000 : ℝ)|^4623 ≤ (15917352907611/20000000000000 : ℝ)^3599
        have hw : |(1674305543/2000000000 : ℝ)|=(1674305543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-685919197/10000000000 : ℝ)|^4623 ≤ (400014104089/12500000000000 : ℝ)^3599
        have hw : |(-685919197/10000000000 : ℝ)|=(685919197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2541661183/10000000000 : ℝ)|^4623 ≤ (215164032707/1250000000000 : ℝ)^3599
        have hw : |(2541661183/10000000000 : ℝ)|=(2541661183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s6_6 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1674096987/2000000000 : ℝ)*x 0 + (1272702389/5000000000 : ℝ)*x 1 + (-136521279/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1674096987/2000000000 : ℝ)^4623 ≤ (79574030587071/100000000000000 : ℝ)^3599 := by
    have hnat : (1674096987 : ℕ)^4623*100000000000000^3599 ≤ 79574030587071^3599*2000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674096987 2000000000 79574030587071 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1272702389/5000000000 : ℝ)^4623 ≤ (3449139214983/20000000000000 : ℝ)^3599 := by
    have hnat : (1272702389 : ℕ)^4623*20000000000000^3599 ≤ 3449139214983^3599*5000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1272702389 5000000000 3449139214983 20000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136521279/2000000000 : ℝ)^4623 ≤ (1590136659669/50000000000000 : ℝ)^3599 := by
    have hnat : (136521279 : ℕ)^4623*50000000000000^3599 ≤ 1590136659669^3599*2000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136521279 2000000000 1590136659669 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1674096987/2000000000 : ℝ), (1272702389/5000000000 : ℝ), (-136521279/2000000000 : ℝ)] ![(79574030587071/100000000000000 : ℝ), (3449139214983/20000000000000 : ℝ), (1590136659669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1674096987/2000000000 : ℝ)|^4623 ≤ (79574030587071/100000000000000 : ℝ)^3599
        have hw : |(1674096987/2000000000 : ℝ)|=(1674096987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1272702389/5000000000 : ℝ)|^4623 ≤ (3449139214983/20000000000000 : ℝ)^3599
        have hw : |(1272702389/5000000000 : ℝ)|=(1272702389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-136521279/2000000000 : ℝ)|^4623 ≤ (1590136659669/50000000000000 : ℝ)^3599
        have hw : |(-136521279/2000000000 : ℝ)|=(136521279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s6_7 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (174982729/250000000 : ℝ)*x 0 + (167125393/625000000 : ℝ)*x 1 + (668997463/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174982729/250000000 : ℝ)^4623 ≤ (63236778393911/100000000000000 : ℝ)^3599 := by
    have hnat : (174982729 : ℕ)^4623*100000000000000^3599 ≤ 63236778393911^3599*250000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174982729 250000000 63236778393911 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (167125393/625000000 : ℝ)^4623 ≤ (36745713113/200000000000 : ℝ)^3599 := by
    have hnat : (167125393 : ℕ)^4623*200000000000^3599 ≤ 36745713113^3599*625000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167125393 625000000 36745713113 200000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (668997463/2500000000 : ℝ)^4623 ≤ (18390365032481/100000000000000 : ℝ)^3599 := by
    have hnat : (668997463 : ℕ)^4623*100000000000000^3599 ≤ 18390365032481^3599*2500000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668997463 2500000000 18390365032481 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174982729/250000000 : ℝ), (167125393/625000000 : ℝ), (668997463/2500000000 : ℝ)] ![(63236778393911/100000000000000 : ℝ), (36745713113/200000000000 : ℝ), (18390365032481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174982729/250000000 : ℝ)|^4623 ≤ (63236778393911/100000000000000 : ℝ)^3599
        have hw : |(174982729/250000000 : ℝ)|=(174982729/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(167125393/625000000 : ℝ)|^4623 ≤ (36745713113/200000000000 : ℝ)^3599
        have hw : |(167125393/625000000 : ℝ)|=(167125393/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(668997463/2500000000 : ℝ)|^4623 ≤ (18390365032481/100000000000000 : ℝ)^3599
        have hw : |(668997463/2500000000 : ℝ)|=(668997463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1563_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6698619/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5549/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11099/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5549/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5549/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5549/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5549/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5549/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5549/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5549/50000 : ℝ) ^ (4621/1024 : ℝ) ≤ (2457255579462299/50000000000000000000 : ℝ) := by
    have hpowers : (5549/50000 : ℝ)^4621 ≤ (2457255579462299/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5549 : ℕ)^4621*50000000000000000000^1024 ≤ 2457255579462299^1024*50000^4621 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5549 50000 2457255579462299 50000000000000000000 4621 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5549/50000 : ℝ)) (X := (2457255579462299/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4621/1024 : ℝ) ≤ (5524031188728493/25000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4621 ≤ (5524031188728493/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4621*25000000000000000000^1024 ≤ 5524031188728493^1024*20000^4621 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 5524031188728493 25000000000000000000 4621 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (5524031188728493/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002457255579462299/25000000000000000000 : ℝ) ≤ (2000043559982019/2000000000000000 : ℝ) ^ (4621/1024 : ℝ) := by
    have hpowers : (25002457255579462299/25000000000000000000 : ℝ)^1024 ≤ (2000043559982019/2000000000000000 : ℝ)^4621 := by
      have hnat : (25002457255579462299 : ℕ)^1024*2000000000000000^4621 ≤ 2000043559982019^4621*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002457255579462299 25000000000000000000 2000043559982019 2000000000000000 1024 4621 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000043559982019/2000000000000000 : ℝ)) (X := (25002457255579462299/25000000000000000000 : ℝ)) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10002701063591383857/10000000000000000000 : ℝ) ≤ (1250074810603707/1250000000000000 : ℝ) ^ (4621/1024 : ℝ) := by
    have hpowers : (10002701063591383857/10000000000000000000 : ℝ)^1024 ≤ (1250074810603707/1250000000000000 : ℝ)^4621 := by
      have hnat : (10002701063591383857 : ℕ)^1024*1250000000000000^4621 ≤ 1250074810603707^4621*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002701063591383857 10000000000000000000 1250074810603707 1250000000000000 1024 4621 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250074810603707/1250000000000000 : ℝ)) (X := (10002701063591383857/10000000000000000000 : ℝ)) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505524031188728493/12500000000000000000 : ℝ) ≤ (10000979169749217/10000000000000000 : ℝ) ^ (4621/1024 : ℝ) := by
    have hpowers : (12505524031188728493/12500000000000000000 : ℝ)^1024 ≤ (10000979169749217/10000000000000000 : ℝ)^4621 := by
      have hnat : (12505524031188728493 : ℕ)^1024*10000000000000000^4621 ≤ 10000979169749217^4621*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505524031188728493 12500000000000000000 10000979169749217 10000000000000000 1024 4621 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000979169749217/10000000000000000 : ℝ)) (X := (12505524031188728493/12500000000000000000 : ℝ)) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2457255579462299/50000000000000000000 : ℝ) ≤ ((43862505805731010809/43870000000000000000 : ℝ)+2*(380684919561/438700000000000 : ℝ)*(5549/50000 : ℝ))^(4621/1024 : ℝ) := by
    rw [show (43862505805731010809/43870000000000000000 : ℝ)+2*(380684919561/438700000000000 : ℝ)*(5549/50000 : ℝ)=(2000043559982019/2000000000000000 : ℝ) by norm_num, show 1+2*(2457255579462299/50000000000000000000 : ℝ)=(25002457255579462299/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5524031188728493/25000000000000000000 : ℝ)+(2457255579462299/50000000000000000000 : ℝ) ≤ ((43862505805731010809/43870000000000000000 : ℝ)+(380684919561/438700000000000 : ℝ)*((3097/20000 : ℝ)+(5549/50000 : ℝ)))^(4621/1024 : ℝ) := by
    rw [show (43862505805731010809/43870000000000000000 : ℝ)+(380684919561/438700000000000 : ℝ)*((3097/20000 : ℝ)+(5549/50000 : ℝ))=(1250074810603707/1250000000000000 : ℝ) by norm_num, show 1+(5524031188728493/25000000000000000000 : ℝ)+(2457255579462299/50000000000000000000 : ℝ)=(10002701063591383857/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5524031188728493/25000000000000000000 : ℝ) ≤ ((43862505805731010809/43870000000000000000 : ℝ)+2*(380684919561/438700000000000 : ℝ)*(3097/20000 : ℝ))^(4621/1024 : ℝ) := by
    rw [show (43862505805731010809/43870000000000000000 : ℝ)+2*(380684919561/438700000000000 : ℝ)*(3097/20000 : ℝ)=(10000979169749217/10000000000000000 : ℝ) by norm_num, show 1+2*(5524031188728493/25000000000000000000 : ℝ)=(12505524031188728493/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43862505805731010809/43870000000000000000 : ℝ)*(X 1 0+X 2 0)+(380684919561/438700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4621/1024 : ℝ)) (lo := (5549/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (43862505805731010809/43870000000000000000 : ℝ)) (alpha := (380684919561/438700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43862505805731010809/43870000000000000000 : ℝ)*(X 0 1+X 2 1)+(380684919561/438700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4621/1024 : ℝ)) (lo := (5549/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (43862505805731010809/43870000000000000000 : ℝ)) (alpha := (380684919561/438700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43862505805731010809/43870000000000000000 : ℝ)*(X 0 2+X 1 2)+(380684919561/438700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4621/1024 : ℝ)) (lo := (5549/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (43862505805731010809/43870000000000000000 : ℝ)) (alpha := (380684919561/438700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-897610633/5000000000 : ℝ)*X 0 0+(5426675239/10000000000 : ℝ)*X 0 1+(5219823323/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348615841/10000000000 : ℝ)*X 1 0+(-1901057577/10000000000 : ℝ)*X 1 1+(5219825083/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334288527/625000000 : ℝ)*X 2 0+(1043964929/2000000000 : ℝ)*X 2 1+(-237632171/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1061649867/2500000000 : ℝ)*X 0 0+(160371311/400000000 : ℝ)*X 0 1+(4495237423/10000000000 : ℝ)*X 0 2+(1061649867/2500000000 : ℝ)*X 1 0+(160371311/400000000 : ℝ)*X 1 1+(4495237423/10000000000 : ℝ)*X 1 2+(1061649867/2500000000 : ℝ)*X 2 0+(160371311/400000000 : ℝ)*X 2 1+(4495237423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-22440629/125000000 : ℝ)*X 0 0+(1305224851/2500000000 : ℝ)*X 0 1+(5425589719/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1674305543/2000000000 : ℝ)*X 1 0+(-685919197/10000000000 : ℝ)*X 1 1+(2541661183/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1674096987/2000000000 : ℝ)*X 2 0+(1272702389/5000000000 : ℝ)*X 2 1+(-136521279/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174982729/250000000 : ℝ)*X 0 0+(167125393/625000000 : ℝ)*X 0 1+(668997463/2500000000 : ℝ)*X 0 2+(174982729/250000000 : ℝ)*X 1 0+(167125393/625000000 : ℝ)*X 1 1+(668997463/2500000000 : ℝ)*X 1 2+(174982729/250000000 : ℝ)*X 2 0+(167125393/625000000 : ℝ)*X 2 1+(668997463/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1969941110361980112307672989/2193500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (243026367/25000000000000 : ℝ)*(lower2) + (379342803/50000000000000 : ℝ)*(lower4) + (28872649/50000000000000 : ℝ)*(lower5) + (3446112695067331/100000000000000 : ℝ)*(major0) + (3446112695067331/100000000000000 : ℝ)*(major1) + (3446112695067331/100000000000000 : ℝ)*(major2) + (96687922026247/2000000000000 : ℝ)*(sp0) + (966883838050559/20000000000000 : ℝ)*(sp1) + (1208604857260073/25000000000000 : ℝ)*(sp2) + (1028901254702479/50000000000000 : ℝ)*(sp3) + (6097975647/25000000000000 : ℝ)*(sp4) + (40717567/3125000000000 : ℝ)*(sp5) + (1064174647/100000000000000 : ℝ)*(sp6) + (2357578717/100000000000000 : ℝ)*(sp7) + (514451216745919/25000000000000 : ℝ)*(f.failure) + (4834420493214939/100000000000000 : ℝ)*(f.sum) + (10888710315951/21935000000000000000000000000 : ℝ)*base65 + (31245927431836880779/4387000000000000000000000000000000 : ℝ)*base67 + (54617999869332880779/4387000000000000000000000000000000 : ℝ)*base69 + (47879999203559880779/4387000000000000000000000000000000 : ℝ)*base71 + (26352050720893/10967500000000000000000000000 : ℝ)*base73 + (14981974663027880779/4387000000000000000000000000000000 : ℝ)*base75 + (36998596122901880779/4387000000000000000000000000000000 : ℝ)*base77 + (1788536320788880779/4387000000000000000000000000000000 : ℝ)*base79 + (15237535698499/5483750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (185861/100000000000000000000 : ℝ)*base89 + (185861/100000000000000000000 : ℝ)*base91 + (185861/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1563_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6698619/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5549/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11099/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1563_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1563_box_0 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-159028721/1000000000 : ℝ)*x 0 + (5397342417/10000000000 : ℝ)*x 1 + (5397341553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (159028721/1000000000 : ℝ)^4623 ≤ (2356224269577/25000000000000 : ℝ)^3599 := by
    have hnat : (159028721 : ℕ)^4623*25000000000000^3599 ≤ 2356224269577^3599*1000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159028721 1000000000 2356224269577 25000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397342417/10000000000 : ℝ)^4623 ≤ (2264377805521/5000000000000 : ℝ)^3599 := by
    have hnat : (5397342417 : ℕ)^4623*5000000000000^3599 ≤ 2264377805521^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397342417 10000000000 2264377805521 5000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397341553/10000000000 : ℝ)^4623 ≤ (5660943349771/12500000000000 : ℝ)^3599 := by
    have hnat : (5397341553 : ℕ)^4623*12500000000000^3599 ≤ 5660943349771^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397341553 10000000000 5660943349771 12500000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-159028721/1000000000 : ℝ), (5397342417/10000000000 : ℝ), (5397341553/10000000000 : ℝ)] ![(2356224269577/25000000000000 : ℝ), (2264377805521/5000000000000 : ℝ), (5660943349771/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-159028721/1000000000 : ℝ)|^4623 ≤ (2356224269577/25000000000000 : ℝ)^3599
        have hw : |(-159028721/1000000000 : ℝ)|=(159028721/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397342417/10000000000 : ℝ)|^4623 ≤ (2264377805521/5000000000000 : ℝ)^3599
        have hw : |(5397342417/10000000000 : ℝ)|=(5397342417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397341553/10000000000 : ℝ)|^4623 ≤ (5660943349771/12500000000000 : ℝ)^3599
        have hw : |(5397341553/10000000000 : ℝ)|=(5397341553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_box_1 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (658892247/1250000000 : ℝ)*x 0 + (-176568437/1000000000 : ℝ)*x 1 + (5397342123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (658892247/1250000000 : ℝ)^4623 ≤ (43931866212821/100000000000000 : ℝ)^3599 := by
    have hnat : (658892247 : ℕ)^4623*100000000000000^3599 ≤ 43931866212821^3599*1250000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658892247 1250000000 43931866212821 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (176568437/1000000000 : ℝ)^4623 ≤ (10780580832227/100000000000000 : ℝ)^3599 := by
    have hnat : (176568437 : ℕ)^4623*100000000000000^3599 ≤ 10780580832227^3599*1000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176568437 1000000000 10780580832227 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397342123/10000000000 : ℝ)^4623 ≤ (11321888235417/25000000000000 : ℝ)^3599 := by
    have hnat : (5397342123 : ℕ)^4623*25000000000000^3599 ≤ 11321888235417^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397342123 10000000000 11321888235417 25000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(658892247/1250000000 : ℝ), (-176568437/1000000000 : ℝ), (5397342123/10000000000 : ℝ)] ![(43931866212821/100000000000000 : ℝ), (10780580832227/100000000000000 : ℝ), (11321888235417/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(658892247/1250000000 : ℝ)|^4623 ≤ (43931866212821/100000000000000 : ℝ)^3599
        have hw : |(658892247/1250000000 : ℝ)|=(658892247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-176568437/1000000000 : ℝ)|^4623 ≤ (10780580832227/100000000000000 : ℝ)^3599
        have hw : |(-176568437/1000000000 : ℝ)|=(176568437/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397342123/10000000000 : ℝ)|^4623 ≤ (11321888235417/25000000000000 : ℝ)^3599
        have hw : |(5397342123/10000000000 : ℝ)|=(5397342123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_box_2 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635569313/5000000000 : ℝ)*x 0 + (5397341893/10000000000 : ℝ)*x 1 + (-8828419/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635569313/5000000000 : ℝ)^4623 ≤ (21965936585781/50000000000000 : ℝ)^3599 := by
    have hnat : (2635569313 : ℕ)^4623*50000000000000^3599 ≤ 21965936585781^3599*5000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635569313 5000000000 21965936585781 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397341893/10000000000 : ℝ)^4623 ≤ (5660943807839/12500000000000 : ℝ)^3599 := by
    have hnat : (5397341893 : ℕ)^4623*12500000000000^3599 ≤ 5660943807839^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397341893 10000000000 5660943807839 12500000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8828419/50000000 : ℝ)^4623 ≤ (10780576361831/100000000000000 : ℝ)^3599 := by
    have hnat : (8828419 : ℕ)^4623*100000000000000^3599 ≤ 10780576361831^3599*50000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8828419 50000000 10780576361831 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635569313/5000000000 : ℝ), (5397341893/10000000000 : ℝ), (-8828419/50000000 : ℝ)] ![(21965936585781/50000000000000 : ℝ), (5660943807839/12500000000000 : ℝ), (10780576361831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635569313/5000000000 : ℝ)|^4623 ≤ (21965936585781/50000000000000 : ℝ)^3599
        have hw : |(2635569313/5000000000 : ℝ)|=(2635569313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397341893/10000000000 : ℝ)|^4623 ≤ (5660943807839/12500000000000 : ℝ)^3599
        have hw : |(5397341893/10000000000 : ℝ)|=(5397341893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8828419/50000000 : ℝ)|^4623 ≤ (10780576361831/100000000000000 : ℝ)^3599
        have hw : |(-8828419/50000000 : ℝ)|=(8828419/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_box_3 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4447546759/10000000000 : ℝ)*x 0 + (2076399111/5000000000 : ℝ)*x 1 + (4152799541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4447546759/10000000000 : ℝ)^4623 ≤ (8829631083137/25000000000000 : ℝ)^3599 := by
    have hnat : (4447546759 : ℕ)^4623*25000000000000^3599 ≤ 8829631083137^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4447546759 10000000000 8829631083137 25000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2076399111/5000000000 : ℝ)^4623 ≤ (8085182807607/25000000000000 : ℝ)^3599 := by
    have hnat : (2076399111 : ℕ)^4623*25000000000000^3599 ≤ 8085182807607^3599*5000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076399111 5000000000 8085182807607 25000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4152799541/10000000000 : ℝ)^4623 ≤ (32340744425017/100000000000000 : ℝ)^3599 := by
    have hnat : (4152799541 : ℕ)^4623*100000000000000^3599 ≤ 32340744425017^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152799541 10000000000 32340744425017 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4447546759/10000000000 : ℝ), (2076399111/5000000000 : ℝ), (4152799541/10000000000 : ℝ)] ![(8829631083137/25000000000000 : ℝ), (8085182807607/25000000000000 : ℝ), (32340744425017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4447546759/10000000000 : ℝ)|^4623 ≤ (8829631083137/25000000000000 : ℝ)^3599
        have hw : |(4447546759/10000000000 : ℝ)|=(4447546759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2076399111/5000000000 : ℝ)|^4623 ≤ (8085182807607/25000000000000 : ℝ)^3599
        have hw : |(2076399111/5000000000 : ℝ)|=(2076399111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4152799541/10000000000 : ℝ)|^4623 ≤ (32340744425017/100000000000000 : ℝ)^3599
        have hw : |(4152799541/10000000000 : ℝ)|=(4152799541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_box_4 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2005553497/10000000000 : ℝ)*x 0 + (163903987/312500000 : ℝ)*x 1 + (5244927979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2005553497/10000000000 : ℝ)^4623 ≤ (12697069967487/100000000000000 : ℝ)^3599 := by
    have hnat : (2005553497 : ℕ)^4623*100000000000000^3599 ≤ 12697069967487^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005553497 10000000000 12697069967487 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163903987/312500000 : ℝ)^4623 ≤ (43651462898513/100000000000000 : ℝ)^3599 := by
    have hnat : (163903987 : ℕ)^4623*100000000000000^3599 ≤ 43651462898513^3599*312500000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163903987 312500000 43651462898513 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244927979/10000000000 : ℝ)^4623 ≤ (43651467121293/100000000000000 : ℝ)^3599 := by
    have hnat : (5244927979 : ℕ)^4623*100000000000000^3599 ≤ 43651467121293^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244927979 10000000000 43651467121293 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2005553497/10000000000 : ℝ), (163903987/312500000 : ℝ), (5244927979/10000000000 : ℝ)] ![(12697069967487/100000000000000 : ℝ), (43651462898513/100000000000000 : ℝ), (43651467121293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2005553497/10000000000 : ℝ)|^4623 ≤ (12697069967487/100000000000000 : ℝ)^3599
        have hw : |(-2005553497/10000000000 : ℝ)|=(2005553497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163903987/312500000 : ℝ)|^4623 ≤ (43651462898513/100000000000000 : ℝ)^3599
        have hw : |(163903987/312500000 : ℝ)|=(163903987/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244927979/10000000000 : ℝ)|^4623 ≤ (43651467121293/100000000000000 : ℝ)^3599
        have hw : |(5244927979/10000000000 : ℝ)|=(5244927979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_box_5 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688421583/5000000000 : ℝ)*x 0 + (-228658707/1250000000 : ℝ)*x 1 + (1311231969/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688421583/5000000000 : ℝ)^4623 ≤ (140833541421/312500000000 : ℝ)^3599 := by
    have hnat : (2688421583 : ℕ)^4623*312500000000^3599 ≤ 140833541421^3599*5000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688421583 5000000000 140833541421 312500000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (228658707/1250000000 : ℝ)^4623 ≤ (176278136123/1562500000000 : ℝ)^3599 := by
    have hnat : (228658707 : ℕ)^4623*1562500000000^3599 ≤ 176278136123^3599*1250000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228658707 1250000000 176278136123 1562500000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311231969/2500000000 : ℝ)^4623 ≤ (43651466020163/100000000000000 : ℝ)^3599 := by
    have hnat : (1311231969 : ℕ)^4623*100000000000000^3599 ≤ 43651466020163^3599*2500000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311231969 2500000000 43651466020163 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688421583/5000000000 : ℝ), (-228658707/1250000000 : ℝ), (1311231969/2500000000 : ℝ)] ![(140833541421/312500000000 : ℝ), (176278136123/1562500000000 : ℝ), (43651466020163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688421583/5000000000 : ℝ)|^4623 ≤ (140833541421/312500000000 : ℝ)^3599
        have hw : |(2688421583/5000000000 : ℝ)|=(2688421583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-228658707/1250000000 : ℝ)|^4623 ≤ (176278136123/1562500000000 : ℝ)^3599
        have hw : |(-228658707/1250000000 : ℝ)|=(228658707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311231969/2500000000 : ℝ)|^4623 ≤ (43651466020163/100000000000000 : ℝ)^3599
        have hw : |(1311231969/2500000000 : ℝ)|=(1311231969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_box_6 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376842909/10000000000 : ℝ)*x 0 + (163904007/312500000 : ℝ)*x 1 + (-365853907/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376842909/10000000000 : ℝ)^4623 ≤ (22533365243877/50000000000000 : ℝ)^3599 := by
    have hnat : (5376842909 : ℕ)^4623*50000000000000^3599 ≤ 22533365243877^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376842909 10000000000 22533365243877 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163904007/312500000 : ℝ)^4623 ≤ (21825734870243/50000000000000 : ℝ)^3599 := by
    have hnat : (163904007 : ℕ)^4623*50000000000000^3599 ≤ 21825734870243^3599*312500000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163904007 312500000 21825734870243 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (365853907/2000000000 : ℝ)^4623 ≤ (2820449938323/25000000000000 : ℝ)^3599 := by
    have hnat : (365853907 : ℕ)^4623*25000000000000^3599 ≤ 2820449938323^3599*2000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365853907 2000000000 2820449938323 25000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376842909/10000000000 : ℝ), (163904007/312500000 : ℝ), (-365853907/2000000000 : ℝ)] ![(22533365243877/50000000000000 : ℝ), (21825734870243/50000000000000 : ℝ), (2820449938323/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376842909/10000000000 : ℝ)|^4623 ≤ (22533365243877/50000000000000 : ℝ)^3599
        have hw : |(5376842909/10000000000 : ℝ)|=(5376842909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163904007/312500000 : ℝ)|^4623 ≤ (21825734870243/50000000000000 : ℝ)^3599
        have hw : |(163904007/312500000 : ℝ)|=(163904007/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-365853907/2000000000 : ℝ)|^4623 ≤ (2820449938323/25000000000000 : ℝ)^3599
        have hw : |(-365853907/2000000000 : ℝ)|=(365853907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_box_7 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (404299313/1000000000 : ℝ)*x 0 + (1088737001/2500000000 : ℝ)*x 1 + (4354947011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (404299313/1000000000 : ℝ)^4623 ≤ (31246456524131/100000000000000 : ℝ)^3599 := by
    have hnat : (404299313 : ℕ)^4623*100000000000000^3599 ≤ 31246456524131^3599*1000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404299313 1000000000 31246456524131 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088737001/2500000000 : ℝ)^4623 ≤ (34376776770349/100000000000000 : ℝ)^3599 := by
    have hnat : (1088737001 : ℕ)^4623*100000000000000^3599 ≤ 34376776770349^3599*2500000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088737001 2500000000 34376776770349 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4354947011/10000000000 : ℝ)^4623 ≤ (2148547918853/6250000000000 : ℝ)^3599 := by
    have hnat : (4354947011 : ℕ)^4623*6250000000000^3599 ≤ 2148547918853^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354947011 10000000000 2148547918853 6250000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(404299313/1000000000 : ℝ), (1088737001/2500000000 : ℝ), (4354947011/10000000000 : ℝ)] ![(31246456524131/100000000000000 : ℝ), (34376776770349/100000000000000 : ℝ), (2148547918853/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(404299313/1000000000 : ℝ)|^4623 ≤ (31246456524131/100000000000000 : ℝ)^3599
        have hw : |(404299313/1000000000 : ℝ)|=(404299313/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088737001/2500000000 : ℝ)|^4623 ≤ (34376776770349/100000000000000 : ℝ)^3599
        have hw : |(1088737001/2500000000 : ℝ)|=(1088737001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4354947011/10000000000 : ℝ)|^4623 ≤ (2148547918853/6250000000000 : ℝ)^3599
        have hw : |(4354947011/10000000000 : ℝ)|=(4354947011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_box_8 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1917560451/10000000000 : ℝ)*x 0 + (5137618107/10000000000 : ℝ)*x 1 + (2708817169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1917560451/10000000000 : ℝ)^4623 ≤ (11986001631949/100000000000000 : ℝ)^3599 := by
    have hnat : (1917560451 : ℕ)^4623*100000000000000^3599 ≤ 11986001631949^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917560451 10000000000 11986001631949 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5137618107/10000000000 : ℝ)^4623 ≤ (42507617636069/100000000000000 : ℝ)^3599 := by
    have hnat : (5137618107 : ℕ)^4623*100000000000000^3599 ≤ 42507617636069^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137618107 10000000000 42507617636069 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708817169/5000000000 : ℝ)^4623 ≤ (45506380706519/100000000000000 : ℝ)^3599 := by
    have hnat : (2708817169 : ℕ)^4623*100000000000000^3599 ≤ 45506380706519^3599*5000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708817169 5000000000 45506380706519 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1917560451/10000000000 : ℝ), (5137618107/10000000000 : ℝ), (2708817169/5000000000 : ℝ)] ![(11986001631949/100000000000000 : ℝ), (42507617636069/100000000000000 : ℝ), (45506380706519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1917560451/10000000000 : ℝ)|^4623 ≤ (11986001631949/100000000000000 : ℝ)^3599
        have hw : |(-1917560451/10000000000 : ℝ)|=(1917560451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5137618107/10000000000 : ℝ)|^4623 ≤ (42507617636069/100000000000000 : ℝ)^3599
        have hw : |(5137618107/10000000000 : ℝ)|=(5137618107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708817169/5000000000 : ℝ)|^4623 ≤ (45506380706519/100000000000000 : ℝ)^3599
        have hw : |(2708817169/5000000000 : ℝ)|=(2708817169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_box_9 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164283139/312500000 : ℝ)*x 0 + (-1756984729/10000000000 : ℝ)*x 1 + (2708817501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164283139/312500000 : ℝ)^4623 ≤ (43781212938887/100000000000000 : ℝ)^3599 := by
    have hnat : (164283139 : ℕ)^4623*100000000000000^3599 ≤ 43781212938887^3599*312500000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164283139 312500000 43781212938887 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1756984729/10000000000 : ℝ)^4623 ≤ (1339049896167/12500000000000 : ℝ)^3599 := by
    have hnat : (1756984729 : ℕ)^4623*12500000000000^3599 ≤ 1339049896167^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1756984729 10000000000 1339049896167 12500000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708817501/5000000000 : ℝ)^4623 ≤ (22753193935401/50000000000000 : ℝ)^3599 := by
    have hnat : (2708817501 : ℕ)^4623*50000000000000^3599 ≤ 22753193935401^3599*5000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708817501 5000000000 22753193935401 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164283139/312500000 : ℝ), (-1756984729/10000000000 : ℝ), (2708817501/5000000000 : ℝ)] ![(43781212938887/100000000000000 : ℝ), (1339049896167/12500000000000 : ℝ), (22753193935401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164283139/312500000 : ℝ)|^4623 ≤ (43781212938887/100000000000000 : ℝ)^3599
        have hw : |(164283139/312500000 : ℝ)|=(164283139/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1756984729/10000000000 : ℝ)|^4623 ≤ (1339049896167/12500000000000 : ℝ)^3599
        have hw : |(-1756984729/10000000000 : ℝ)|=(1756984729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708817501/5000000000 : ℝ)|^4623 ≤ (22753193935401/50000000000000 : ℝ)^3599
        have hw : |(2708817501/5000000000 : ℝ)|=(2708817501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_box_10 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164283117/312500000 : ℝ)*x 0 + (5417636383/10000000000 : ℝ)*x 1 + (-175698379/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164283117/312500000 : ℝ)^4623 ≤ (5472650675971/12500000000000 : ℝ)^3599 := by
    have hnat : (164283117 : ℕ)^4623*12500000000000^3599 ≤ 5472650675971^3599*312500000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164283117 312500000 5472650675971 12500000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417636383/10000000000 : ℝ)^4623 ≤ (45506402771217/100000000000000 : ℝ)^3599 := by
    have hnat : (5417636383 : ℕ)^4623*100000000000000^3599 ≤ 45506402771217^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417636383 10000000000 45506402771217 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (175698379/1000000000 : ℝ)^4623 ≤ (10712391815289/100000000000000 : ℝ)^3599 := by
    have hnat : (175698379 : ℕ)^4623*100000000000000^3599 ≤ 10712391815289^3599*1000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175698379 1000000000 10712391815289 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164283117/312500000 : ℝ), (5417636383/10000000000 : ℝ), (-175698379/1000000000 : ℝ)] ![(5472650675971/12500000000000 : ℝ), (45506402771217/100000000000000 : ℝ), (10712391815289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164283117/312500000 : ℝ)|^4623 ≤ (5472650675971/12500000000000 : ℝ)^3599
        have hw : |(164283117/312500000 : ℝ)|=(164283117/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417636383/10000000000 : ℝ)|^4623 ≤ (45506402771217/100000000000000 : ℝ)^3599
        have hw : |(5417636383/10000000000 : ℝ)|=(5417636383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-175698379/1000000000 : ℝ)|^4623 ≤ (10712391815289/100000000000000 : ℝ)^3599
        have hw : |(-175698379/1000000000 : ℝ)|=(175698379/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_box_11 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (450026583/1000000000 : ℝ)*x 0 + (825169989/2000000000 : ℝ)*x 1 + (4125849877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (450026583/1000000000 : ℝ)^4623 ≤ (286857541877/800000000000 : ℝ)^3599 := by
    have hnat : (450026583 : ℕ)^4623*800000000000^3599 ≤ 286857541877^3599*1000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450026583 1000000000 286857541877 800000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (825169989/2000000000 : ℝ)^4623 ≤ (16035701982257/50000000000000 : ℝ)^3599 := by
    have hnat : (825169989 : ℕ)^4623*50000000000000^3599 ≤ 16035701982257^3599*2000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825169989 2000000000 16035701982257 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4125849877/10000000000 : ℝ)^4623 ≤ (32071403285537/100000000000000 : ℝ)^3599 := by
    have hnat : (4125849877 : ℕ)^4623*100000000000000^3599 ≤ 32071403285537^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4125849877 10000000000 32071403285537 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(450026583/1000000000 : ℝ), (825169989/2000000000 : ℝ), (4125849877/10000000000 : ℝ)] ![(286857541877/800000000000 : ℝ), (16035701982257/50000000000000 : ℝ), (32071403285537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(450026583/1000000000 : ℝ)|^4623 ≤ (286857541877/800000000000 : ℝ)^3599
        have hw : |(450026583/1000000000 : ℝ)|=(450026583/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(825169989/2000000000 : ℝ)|^4623 ≤ (16035701982257/50000000000000 : ℝ)^3599
        have hw : |(825169989/2000000000 : ℝ)|=(825169989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4125849877/10000000000 : ℝ)|^4623 ≤ (32071403285537/100000000000000 : ℝ)^3599
        have hw : |(4125849877/10000000000 : ℝ)|=(4125849877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_box_12 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-419493601/2500000000 : ℝ)*x 0 + (1375340513/2500000000 : ℝ)*x 1 + (5229878399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419493601/2500000000 : ℝ)^4623 ≤ (10097609178399/100000000000000 : ℝ)^3599 := by
    have hnat : (419493601 : ℕ)^4623*100000000000000^3599 ≤ 10097609178399^3599*2500000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419493601 2500000000 10097609178399 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1375340513/2500000000 : ℝ)^4623 ≤ (46411746732993/100000000000000 : ℝ)^3599 := by
    have hnat : (1375340513 : ℕ)^4623*100000000000000^3599 ≤ 46411746732993^3599*2500000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375340513 2500000000 46411746732993 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229878399/10000000000 : ℝ)^4623 ≤ (43490644066991/100000000000000 : ℝ)^3599 := by
    have hnat : (5229878399 : ℕ)^4623*100000000000000^3599 ≤ 43490644066991^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229878399 10000000000 43490644066991 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-419493601/2500000000 : ℝ), (1375340513/2500000000 : ℝ), (5229878399/10000000000 : ℝ)] ![(10097609178399/100000000000000 : ℝ), (46411746732993/100000000000000 : ℝ), (43490644066991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-419493601/2500000000 : ℝ)|^4623 ≤ (10097609178399/100000000000000 : ℝ)^3599
        have hw : |(-419493601/2500000000 : ℝ)|=(419493601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1375340513/2500000000 : ℝ)|^4623 ≤ (46411746732993/100000000000000 : ℝ)^3599
        have hw : |(1375340513/2500000000 : ℝ)|=(1375340513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229878399/10000000000 : ℝ)|^4623 ≤ (43490644066991/100000000000000 : ℝ)^3599
        have hw : |(5229878399/10000000000 : ℝ)|=(5229878399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_box_13 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5387281061/10000000000 : ℝ)*x 0 + (-367075529/2000000000 : ℝ)*x 1 + (522987849/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387281061/10000000000 : ℝ)^4623 ≤ (45179142891997/100000000000000 : ℝ)^3599 := by
    have hnat : (5387281061 : ℕ)^4623*100000000000000^3599 ≤ 45179142891997^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387281061 10000000000 45179142891997 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (367075529/2000000000 : ℝ)^4623 ≤ (2266042409633/20000000000000 : ℝ)^3599 := by
    have hnat : (367075529 : ℕ)^4623*20000000000000^3599 ≤ 2266042409633^3599*2000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367075529 2000000000 2266042409633 20000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522987849/1000000000 : ℝ)^4623 ≤ (43490645039039/100000000000000 : ℝ)^3599 := by
    have hnat : (522987849 : ℕ)^4623*100000000000000^3599 ≤ 43490645039039^3599*1000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522987849 1000000000 43490645039039 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387281061/10000000000 : ℝ), (-367075529/2000000000 : ℝ), (522987849/1000000000 : ℝ)] ![(45179142891997/100000000000000 : ℝ), (2266042409633/20000000000000 : ℝ), (43490645039039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387281061/10000000000 : ℝ)|^4623 ≤ (45179142891997/100000000000000 : ℝ)^3599
        have hw : |(5387281061/10000000000 : ℝ)|=(5387281061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-367075529/2000000000 : ℝ)|^4623 ≤ (2266042409633/20000000000000 : ℝ)^3599
        have hw : |(-367075529/2000000000 : ℝ)|=(367075529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522987849/1000000000 : ℝ)|^4623 ≤ (43490645039039/100000000000000 : ℝ)^3599
        have hw : |(522987849/1000000000 : ℝ)|=(522987849/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_box_14 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5387282307/10000000000 : ℝ)*x 0 + (522987749/1000000000 : ℝ)*x 1 + (-18353773/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387282307/10000000000 : ℝ)^4623 ≤ (5647394539293/12500000000000 : ℝ)^3599 := by
    have hnat : (5387282307 : ℕ)^4623*12500000000000^3599 ≤ 5647394539293^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387282307 10000000000 5647394539293 12500000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522987749/1000000000 : ℝ)^4623 ≤ (43490634357193/100000000000000 : ℝ)^3599 := by
    have hnat : (522987749 : ℕ)^4623*100000000000000^3599 ≤ 43490634357193^3599*1000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522987749 1000000000 43490634357193 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18353773/100000000 : ℝ)^4623 ≤ (708138082027/6250000000000 : ℝ)^3599 := by
    have hnat : (18353773 : ℕ)^4623*6250000000000^3599 ≤ 708138082027^3599*100000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18353773 100000000 708138082027 6250000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387282307/10000000000 : ℝ), (522987749/1000000000 : ℝ), (-18353773/100000000 : ℝ)] ![(5647394539293/12500000000000 : ℝ), (43490634357193/100000000000000 : ℝ), (708138082027/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387282307/10000000000 : ℝ)|^4623 ≤ (5647394539293/12500000000000 : ℝ)^3599
        have hw : |(5387282307/10000000000 : ℝ)|=(5387282307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522987749/1000000000 : ℝ)|^4623 ≤ (43490634357193/100000000000000 : ℝ)^3599
        have hw : |(522987749/1000000000 : ℝ)|=(522987749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18353773/100000000 : ℝ)|^4623 ≤ (708138082027/6250000000000 : ℝ)^3599
        have hw : |(-18353773/100000000 : ℝ)|=(18353773/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_box_15 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2001093027/5000000000 : ℝ)*x 0 + (273430191/625000000 : ℝ)*x 1 + (4374881671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2001093027/5000000000 : ℝ)^4623 ≤ (240952558223/781250000000 : ℝ)^3599 := by
    have hnat : (2001093027 : ℕ)^4623*781250000000^3599 ≤ 240952558223^3599*5000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001093027 5000000000 240952558223 781250000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273430191/625000000 : ℝ)^4623 ≤ (6915808659459/20000000000000 : ℝ)^3599 := by
    have hnat : (273430191 : ℕ)^4623*20000000000000^3599 ≤ 6915808659459^3599*625000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273430191 625000000 6915808659459 20000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4374881671/10000000000 : ℝ)^4623 ≤ (17289514617789/50000000000000 : ℝ)^3599 := by
    have hnat : (4374881671 : ℕ)^4623*50000000000000^3599 ≤ 17289514617789^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374881671 10000000000 17289514617789 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2001093027/5000000000 : ℝ), (273430191/625000000 : ℝ), (4374881671/10000000000 : ℝ)] ![(240952558223/781250000000 : ℝ), (6915808659459/20000000000000 : ℝ), (17289514617789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2001093027/5000000000 : ℝ)|^4623 ≤ (240952558223/781250000000 : ℝ)^3599
        have hw : |(2001093027/5000000000 : ℝ)|=(2001093027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273430191/625000000 : ℝ)|^4623 ≤ (6915808659459/20000000000000 : ℝ)^3599
        have hw : |(273430191/625000000 : ℝ)|=(273430191/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4374881671/10000000000 : ℝ)|^4623 ≤ (17289514617789/50000000000000 : ℝ)^3599
        have hw : |(4374881671/10000000000 : ℝ)|=(4374881671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1563_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6698619/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11099/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(7977/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58869/100000 : ℝ) ∧ (1617/2000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (86323/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11099/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11099/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11099/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11099/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11099/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11099/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11099/100000 : ℝ) ^ (4621/1024 : ℝ) ≤ (49165098254891/1000000000000000000 : ℝ) := by
    have hpowers : (11099/100000 : ℝ)^4621 ≤ (49165098254891/1000000000000000000 : ℝ)^1024 := by
      have hnat : (11099 : ℕ)^4621*1000000000000000000^1024 ≤ 49165098254891^1024*100000^4621 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11099 100000 49165098254891 1000000000000000000 4621 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11099/100000 : ℝ)) (X := (49165098254891/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4621/1024 : ℝ) ≤ (5524031188728493/25000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4621 ≤ (5524031188728493/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4621*25000000000000000000^1024 ≤ 5524031188728493^1024*20000^4621 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 5524031188728493 25000000000000000000 4621 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (5524031188728493/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (500049165098254891/500000000000000000 : ℝ) ≤ (10000217888483043/10000000000000000 : ℝ) ^ (4621/1024 : ℝ) := by
    have hpowers : (500049165098254891/500000000000000000 : ℝ)^1024 ≤ (10000217888483043/10000000000000000 : ℝ)^4621 := by
      have hnat : (500049165098254891 : ℕ)^1024*10000000000000000^4621 ≤ 10000217888483043^4621*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500049165098254891 500000000000000000 10000217888483043 10000000000000000 1024 4621 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000217888483043/10000000000000000 : ℝ)) (X := (500049165098254891/500000000000000000 : ℝ)) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (781461036207659399/781250000000000000 : ℝ) ≤ (10000598529110209/10000000000000000 : ℝ) ^ (4621/1024 : ℝ) := by
    have hpowers : (781461036207659399/781250000000000000 : ℝ)^1024 ≤ (10000598529110209/10000000000000000 : ℝ)^4621 := by
      have hnat : (781461036207659399 : ℕ)^1024*10000000000000000^4621 ≤ 10000598529110209^4621*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781461036207659399 781250000000000000 10000598529110209 10000000000000000 1024 4621 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000598529110209/10000000000000000 : ℝ)) (X := (781461036207659399/781250000000000000 : ℝ)) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505524031188728493/12500000000000000000 : ℝ) ≤ (80007833357899/80000000000000 : ℝ) ^ (4621/1024 : ℝ) := by
    have hpowers : (12505524031188728493/12500000000000000000 : ℝ)^1024 ≤ (80007833357899/80000000000000 : ℝ)^4621 := by
      have hnat : (12505524031188728493 : ℕ)^1024*80000000000000^4621 ≤ 80007833357899^4621*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505524031188728493 12500000000000000000 80007833357899 80000000000000 1024 4621 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80007833357899/80000000000000 : ℝ)) (X := (12505524031188728493/12500000000000000000 : ℝ)) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(49165098254891/1000000000000000000 : ℝ) ≤ ((4385250619824479573/4386000000000000000 : ℝ)+2*(190320313583/219300000000000 : ℝ)*(11099/100000 : ℝ))^(4621/1024 : ℝ) := by
    rw [show (4385250619824479573/4386000000000000000 : ℝ)+2*(190320313583/219300000000000 : ℝ)*(11099/100000 : ℝ)=(10000217888483043/10000000000000000 : ℝ) by norm_num, show 1+2*(49165098254891/1000000000000000000 : ℝ)=(500049165098254891/500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5524031188728493/25000000000000000000 : ℝ)+(49165098254891/1000000000000000000 : ℝ) ≤ ((4385250619824479573/4386000000000000000 : ℝ)+(190320313583/219300000000000 : ℝ)*((3097/20000 : ℝ)+(11099/100000 : ℝ)))^(4621/1024 : ℝ) := by
    rw [show (4385250619824479573/4386000000000000000 : ℝ)+(190320313583/219300000000000 : ℝ)*((3097/20000 : ℝ)+(11099/100000 : ℝ))=(10000598529110209/10000000000000000 : ℝ) by norm_num, show 1+(5524031188728493/25000000000000000000 : ℝ)+(49165098254891/1000000000000000000 : ℝ)=(781461036207659399/781250000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5524031188728493/25000000000000000000 : ℝ) ≤ ((4385250619824479573/4386000000000000000 : ℝ)+2*(190320313583/219300000000000 : ℝ)*(3097/20000 : ℝ))^(4621/1024 : ℝ) := by
    rw [show (4385250619824479573/4386000000000000000 : ℝ)+2*(190320313583/219300000000000 : ℝ)*(3097/20000 : ℝ)=(80007833357899/80000000000000 : ℝ) by norm_num, show 1+2*(5524031188728493/25000000000000000000 : ℝ)=(12505524031188728493/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4385250619824479573/4386000000000000000 : ℝ)*(X 1 0+X 2 0)+(190320313583/219300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4621/1024 : ℝ)) (lo := (11099/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (4385250619824479573/4386000000000000000 : ℝ)) (alpha := (190320313583/219300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4385250619824479573/4386000000000000000 : ℝ)*(X 0 1+X 2 1)+(190320313583/219300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4621/1024 : ℝ)) (lo := (11099/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (4385250619824479573/4386000000000000000 : ℝ)) (alpha := (190320313583/219300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4385250619824479573/4386000000000000000 : ℝ)*(X 0 2+X 1 2)+(190320313583/219300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4621/1024 : ℝ)) (lo := (11099/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (4385250619824479573/4386000000000000000 : ℝ)) (alpha := (190320313583/219300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-159028721/1000000000 : ℝ)*X 0 0+(5397342417/10000000000 : ℝ)*X 0 1+(5397341553/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((658892247/1250000000 : ℝ)*X 1 0+(-176568437/1000000000 : ℝ)*X 1 1+(5397342123/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2635569313/5000000000 : ℝ)*X 2 0+(5397341893/10000000000 : ℝ)*X 2 1+(-8828419/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4447546759/10000000000 : ℝ)*X 0 0+(2076399111/5000000000 : ℝ)*X 0 1+(4152799541/10000000000 : ℝ)*X 0 2+(4447546759/10000000000 : ℝ)*X 1 0+(2076399111/5000000000 : ℝ)*X 1 1+(4152799541/10000000000 : ℝ)*X 1 2+(4447546759/10000000000 : ℝ)*X 2 0+(2076399111/5000000000 : ℝ)*X 2 1+(4152799541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2005553497/10000000000 : ℝ)*X 0 0+(163903987/312500000 : ℝ)*X 0 1+(5244927979/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2688421583/5000000000 : ℝ)*X 1 0+(-228658707/1250000000 : ℝ)*X 1 1+(1311231969/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5376842909/10000000000 : ℝ)*X 2 0+(163904007/312500000 : ℝ)*X 2 1+(-365853907/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((404299313/1000000000 : ℝ)*X 0 0+(1088737001/2500000000 : ℝ)*X 0 1+(4354947011/10000000000 : ℝ)*X 0 2+(404299313/1000000000 : ℝ)*X 1 0+(1088737001/2500000000 : ℝ)*X 1 1+(4354947011/10000000000 : ℝ)*X 1 2+(404299313/1000000000 : ℝ)*X 2 0+(1088737001/2500000000 : ℝ)*X 2 1+(4354947011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1917560451/10000000000 : ℝ)*X 0 0+(5137618107/10000000000 : ℝ)*X 0 1+(2708817169/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((164283139/312500000 : ℝ)*X 1 0+(-1756984729/10000000000 : ℝ)*X 1 1+(2708817501/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((164283117/312500000 : ℝ)*X 2 0+(5417636383/10000000000 : ℝ)*X 2 1+(-175698379/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((450026583/1000000000 : ℝ)*X 0 0+(825169989/2000000000 : ℝ)*X 0 1+(4125849877/10000000000 : ℝ)*X 0 2+(450026583/1000000000 : ℝ)*X 1 0+(825169989/2000000000 : ℝ)*X 1 1+(4125849877/10000000000 : ℝ)*X 1 2+(450026583/1000000000 : ℝ)*X 2 0+(825169989/2000000000 : ℝ)*X 2 1+(4125849877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-419493601/2500000000 : ℝ)*X 0 0+(1375340513/2500000000 : ℝ)*X 0 1+(5229878399/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5387281061/10000000000 : ℝ)*X 1 0+(-367075529/2000000000 : ℝ)*X 1 1+(522987849/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5387282307/10000000000 : ℝ)*X 2 0+(522987749/1000000000 : ℝ)*X 2 1+(-18353773/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2001093027/5000000000 : ℝ)*X 0 0+(273430191/625000000 : ℝ)*X 0 1+(4374881671/10000000000 : ℝ)*X 0 2+(2001093027/5000000000 : ℝ)*X 1 0+(273430191/625000000 : ℝ)*X 1 1+(4374881671/10000000000 : ℝ)*X 1 2+(2001093027/5000000000 : ℝ)*X 2 0+(273430191/625000000 : ℝ)*X 2 1+(4374881671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-7977/12500 : ℝ) ≤ (-23324009068179426824764112369971/36550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1127441/800000000000 : ℝ)*(lower0) + (147057/6250000000000 : ℝ)*(lower2) + (1136781/10000000000000 : ℝ)*(lower4) + (1148860478991491/50000000000000 : ℝ)*(major0) + (1148860478991491/50000000000000 : ℝ)*(major1) + (1148860478991491/50000000000000 : ℝ)*(major2) + (2479263201/100000000000000 : ℝ)*(sp1) + (324465647544943/10000000000000 : ℝ)*(sp4) + (3244654249074357/100000000000000 : ℝ)*(sp5) + (324461058996663/10000000000000 : ℝ)*(sp6) + (1372042206638881/100000000000000 : ℝ)*(sp7) + (252888127/100000000000000 : ℝ)*(sp8) + (46138370927/100000000000000 : ℝ)*(sp14) + (223548267/1562500000000 : ℝ)*(sp15) + (42876766053999/3125000000000 : ℝ)*(f.failure) + (3244656728337557/100000000000000 : ℝ)*(f.sum) + (59656766250169/10965000000000000000000000000 : ℝ)*base66 + (727956350530642219/73100000000000000000000000000000 : ℝ)*base68 + (491778910980042219/73100000000000000000000000000000 : ℝ)*base70 + (669874932593542219/73100000000000000000000000000000 : ℝ)*base72 + (894790393207/1370625000000000000000000000 : ℝ)*base73 + (1111146772242942219/73100000000000000000000000000000 : ℝ)*base76 + (694780089508642219/73100000000000000000000000000000 : ℝ)*base78 + (784119492887742219/73100000000000000000000000000000 : ℝ)*base80 + (21761970703879/10965000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (22619/12500000000000000000 : ℝ)*base90 + (22619/12500000000000000000 : ℝ)*base92 + (22619/12500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (58869/100000 : ℝ) ≤ (8607029802720176422268912584597/14620000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26896713/100000000000000 : ℝ)*(upper0) + (150972037/50000000000000 : ℝ)*(lower1) + (292226401/100000000000000 : ℝ)*(upper4) + (475494663958763/20000000000000 : ℝ)*(major0) + (475494663958763/20000000000000 : ℝ)*(major1) + (475494663958763/20000000000000 : ℝ)*(major2) + (51806842644351/1562500000000 : ℝ)*(sp0) + (1657791134075871/50000000000000 : ℝ)*(sp1) + (1657818379788637/50000000000000 : ℝ)*(sp2) + (1419674198508503/100000000000000 : ℝ)*(sp3) + (1370403229/25000000000000 : ℝ)*(sp7) + (5159268507/100000000000000 : ℝ)*(sp8) + (60820355229/100000000000000 : ℝ)*(sp9) + (6328929697/100000000000000 : ℝ)*(sp10) + (1419679680121419/100000000000000 : ℝ)*(f.failure) + (3315643088506971/100000000000000 : ℝ)*(f.sum) + (1027325916851/2193000000000000000000000000 : ℝ)*base66 + (188642251370937267/29240000000000000000000000000000 : ℝ)*base68 + (8164026562537267/29240000000000000000000000000000 : ℝ)*base70 + (292307132554697267/29240000000000000000000000000000 : ℝ)*base72 + (6435911706493/548250000000000000000000000 : ℝ)*base73 + (104020517560377267/29240000000000000000000000000000 : ℝ)*base76 + (200065643400617267/29240000000000000000000000000000 : ℝ)*base78 + (339348775609977267/29240000000000000000000000000000 : ℝ)*base80 + (564983423653/548250000000000000000000000 : ℝ)*base81 + (379639/400000000000000000000 : ℝ)*base90 + (379639/400000000000000000000 : ℝ)*base92 + (379639/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (1617/2000 : ℝ) ≤ (29551536294523733547821301924327/36550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (107674959/100000000000000 : ℝ)*(lower3) + (23612737/20000000000000 : ℝ)*(upper4) + (11038923/100000000000000 : ℝ)*(lower5) + (1282451892644299/50000000000000 : ℝ)*(major0) + (1282451892644299/50000000000000 : ℝ)*(major1) + (1282451892644299/50000000000000 : ℝ)*(major2) + (5767325251/20000000000000 : ℝ)*(sp0) + (198751420733/100000000000000 : ℝ)*(sp1) + (92233591297/20000000000000 : ℝ)*(sp2) + (3612328233/2500000000000 : ℝ)*(sp3) + (892806603424829/25000000000000 : ℝ)*(sp8) + (3571056498904837/100000000000000 : ℝ)*(sp9) + (714158816473817/20000000000000 : ℝ)*(sp10) + (1531457041627977/100000000000000 : ℝ)*(sp11) + (1531601534757297/100000000000000 : ℝ)*(f.failure) + (357125525032557/10000000000000 : ℝ)*(f.sum) + (46011745351487/5482500000000000000000000000 : ℝ)*base65 + (7697977758951891/73100000000000000000000000000000 : ℝ)*base68 + (696042981550951891/73100000000000000000000000000000 : ℝ)*base70 + (501583163562848109/73100000000000000000000000000000 : ℝ)*base71 + (6037222110863/1370625000000000000000000000 : ℝ)*base73 + (367367399681951891/73100000000000000000000000000000 : ℝ)*base76 + (143710383498248109/73100000000000000000000000000000 : ℝ)*base77 + (109999418459251891/73100000000000000000000000000000 : ℝ)*base80 + (13422795290599/10965000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1927157/400000000000000000000 : ℝ)*base90 + (1927157/400000000000000000000 : ℝ)*base92 + (1927157/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-86323/100000 : ℝ) ≤ (-3943776901407901721114666445009/4568750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (75517429/20000000000000 : ℝ)*(lower2) + (49389801/25000000000000 : ℝ)*(upper3) + (78383067/50000000000000 : ℝ)*(upper5) + (162823043207339/6250000000000 : ℝ)*(major0) + (162823043207339/6250000000000 : ℝ)*(major1) + (162823043207339/6250000000000 : ℝ)*(major2) + (2604877021/25000000000000 : ℝ)*(sp0) + (224944748921/100000000000000 : ℝ)*(sp5) + (151430019647/50000000000000 : ℝ)*(sp6) + (2240814017/20000000000000 : ℝ)*(sp7) + (920863822177843/25000000000000 : ℝ)*(sp12) + (736648152694107/20000000000000 : ℝ)*(sp13) + (1841581424090081/50000000000000 : ℝ)*(sp14) + (777817018214721/50000000000000 : ℝ)*(sp15) + (777822620249763/50000000000000 : ℝ)*(f.failure) + (57554151690929/1562500000000 : ℝ)*(f.sum) + (29438882235079/5482500000000000000000000000 : ℝ)*base66 + (91578008019991251/9137500000000000000000000000000 : ℝ)*base68 + (47489039932778751/9137500000000000000000000000000 : ℝ)*base70 + (64528540666553751/9137500000000000000000000000000 : ℝ)*base72 + (15331076746373/10965000000000000000000000000 : ℝ)*base74 + (118378185860853751/9137500000000000000000000000000 : ℝ)*base76 + (101028270335666251/9137500000000000000000000000000 : ℝ)*base78 + (88002804564791251/9137500000000000000000000000000 : ℝ)*base80 + (5688771384863/10965000000000000000000000000 : ℝ)*base82 + (822703/200000000000000000000 : ℝ)*base90 + (822703/200000000000000000000 : ℝ)*base92 + (822703/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1563_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6698619/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11099/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7977/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(58869/100000 : ℝ) else (1617/2000 : ℝ) ≤ X j i ∧ X j i ≤ (86323/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1563_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1563_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6698619/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5549/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7977/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(58869/100000 : ℝ) else (1617/2000 : ℝ) ≤ X j i ∧ X j i ≤ (86323/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1563_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1563_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6698619/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5549/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7977/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(58869/100000 : ℝ) else (1617/2000 : ℝ) ≤ X j i ∧ X j i ≤ (86323/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1563_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

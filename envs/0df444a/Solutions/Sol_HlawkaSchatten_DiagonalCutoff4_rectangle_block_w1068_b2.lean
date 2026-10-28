-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1068_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:08:13.557805+00:00
-- url     : https://prove2.me/submissions/ec5ba39e-e625-4770-8298-2283356c7a06

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
theorem support_rectangle_w1068_s6_0 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1101367433/5000000000 : ℝ)*x 0 + (2697436907/5000000000 : ℝ)*x 1 + (5263970161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1101367433/5000000000 : ℝ)^8261 ≤ (3344428700119/25000000000000 : ℝ)^6213 := by
    have hnat : (1101367433 : ℕ)^8261*25000000000000^6213 ≤ 3344428700119^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101367433 5000000000 3344428700119 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697436907/5000000000 : ℝ)^8261 ≤ (44018364659293/100000000000000 : ℝ)^6213 := by
    have hnat : (2697436907 : ℕ)^8261*100000000000000^6213 ≤ 44018364659293^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697436907 5000000000 44018364659293 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263970161/10000000000 : ℝ)^8261 ≤ (42603920524817/100000000000000 : ℝ)^6213 := by
    have hnat : (5263970161 : ℕ)^8261*100000000000000^6213 ≤ 42603920524817^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263970161 10000000000 42603920524817 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1101367433/5000000000 : ℝ), (2697436907/5000000000 : ℝ), (5263970161/10000000000 : ℝ)] ![(3344428700119/25000000000000 : ℝ), (44018364659293/100000000000000 : ℝ), (42603920524817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1101367433/5000000000 : ℝ)|^8261 ≤ (3344428700119/25000000000000 : ℝ)^6213
        have hw : |(-1101367433/5000000000 : ℝ)|=(1101367433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697436907/5000000000 : ℝ)|^8261 ≤ (44018364659293/100000000000000 : ℝ)^6213
        have hw : |(2697436907/5000000000 : ℝ)|=(2697436907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263970161/10000000000 : ℝ)|^8261 ≤ (42603920524817/100000000000000 : ℝ)^6213
        have hw : |(5263970161/10000000000 : ℝ)|=(5263970161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s6_1 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345112577/10000000000 : ℝ)*x 0 + (-2269158533/10000000000 : ℝ)*x 1 + (5263970197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345112577/10000000000 : ℝ)^8261 ≤ (43479334639737/100000000000000 : ℝ)^6213 := by
    have hnat : (5345112577 : ℕ)^8261*100000000000000^6213 ≤ 43479334639737^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345112577 10000000000 43479334639737 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2269158533/10000000000 : ℝ)^8261 ≤ (13916744433833/100000000000000 : ℝ)^6213 := by
    have hnat : (2269158533 : ℕ)^8261*100000000000000^6213 ≤ 13916744433833^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269158533 10000000000 13916744433833 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263970197/10000000000 : ℝ)^8261 ≤ (21301960456113/50000000000000 : ℝ)^6213 := by
    have hnat : (5263970197 : ℕ)^8261*50000000000000^6213 ≤ 21301960456113^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263970197 10000000000 21301960456113 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345112577/10000000000 : ℝ), (-2269158533/10000000000 : ℝ), (5263970197/10000000000 : ℝ)] ![(43479334639737/100000000000000 : ℝ), (13916744433833/100000000000000 : ℝ), (21301960456113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345112577/10000000000 : ℝ)|^8261 ≤ (43479334639737/100000000000000 : ℝ)^6213
        have hw : |(5345112577/10000000000 : ℝ)|=(5345112577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2269158533/10000000000 : ℝ)|^8261 ≤ (13916744433833/100000000000000 : ℝ)^6213
        have hw : |(-2269158533/10000000000 : ℝ)|=(2269158533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263970197/10000000000 : ℝ)|^8261 ≤ (21301960456113/50000000000000 : ℝ)^6213
        have hw : |(5263970197/10000000000 : ℝ)|=(5263970197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s6_2 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069022487/2000000000 : ℝ)*x 0 + (1315992569/2500000000 : ℝ)*x 1 + (-2269158617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069022487/2000000000 : ℝ)^8261 ≤ (21739666551949/50000000000000 : ℝ)^6213 := by
    have hnat : (1069022487 : ℕ)^8261*50000000000000^6213 ≤ 21739666551949^6213*2000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069022487 2000000000 21739666551949 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315992569/2500000000 : ℝ)^8261 ≤ (21301960881187/50000000000000 : ℝ)^6213 := by
    have hnat : (1315992569 : ℕ)^8261*50000000000000^6213 ≤ 21301960881187^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315992569 2500000000 21301960881187 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2269158617/10000000000 : ℝ)^8261 ≤ (6958372559411/50000000000000 : ℝ)^6213 := by
    have hnat : (2269158617 : ℕ)^8261*50000000000000^6213 ≤ 6958372559411^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269158617 10000000000 6958372559411 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069022487/2000000000 : ℝ), (1315992569/2500000000 : ℝ), (-2269158617/10000000000 : ℝ)] ![(21739666551949/50000000000000 : ℝ), (21301960881187/50000000000000 : ℝ), (6958372559411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069022487/2000000000 : ℝ)|^8261 ≤ (21739666551949/50000000000000 : ℝ)^6213
        have hw : |(1069022487/2000000000 : ℝ)|=(1069022487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315992569/2500000000 : ℝ)|^8261 ≤ (21301960881187/50000000000000 : ℝ)^6213
        have hw : |(1315992569/2500000000 : ℝ)|=(1315992569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2269158617/10000000000 : ℝ)|^8261 ≤ (6958372559411/50000000000000 : ℝ)^6213
        have hw : |(-2269158617/10000000000 : ℝ)|=(2269158617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s6_3 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187588623/5000000000 : ℝ)*x 0 + (132773609/312500000 : ℝ)*x 1 + (1126352583/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187588623/5000000000 : ℝ)^8261 ≤ (16658141380151/50000000000000 : ℝ)^6213 := by
    have hnat : (2187588623 : ℕ)^8261*50000000000000^6213 ≤ 16658141380151^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187588623 5000000000 16658141380151 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132773609/312500000 : ℝ)^8261 ≤ (3204240669187/10000000000000 : ℝ)^6213 := by
    have hnat : (132773609 : ℕ)^8261*10000000000000^6213 ≤ 3204240669187^6213*312500000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132773609 312500000 3204240669187 10000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126352583/2500000000 : ℝ)^8261 ≤ (2165081908253/6250000000000 : ℝ)^6213 := by
    have hnat : (1126352583 : ℕ)^8261*6250000000000^6213 ≤ 2165081908253^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126352583 2500000000 2165081908253 6250000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187588623/5000000000 : ℝ), (132773609/312500000 : ℝ), (1126352583/2500000000 : ℝ)] ![(16658141380151/50000000000000 : ℝ), (3204240669187/10000000000000 : ℝ), (2165081908253/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187588623/5000000000 : ℝ)|^8261 ≤ (16658141380151/50000000000000 : ℝ)^6213
        have hw : |(2187588623/5000000000 : ℝ)|=(2187588623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132773609/312500000 : ℝ)|^8261 ≤ (3204240669187/10000000000000 : ℝ)^6213
        have hw : |(132773609/312500000 : ℝ)|=(132773609/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126352583/2500000000 : ℝ)|^8261 ≤ (2165081908253/6250000000000 : ℝ)^6213
        have hw : |(1126352583/2500000000 : ℝ)|=(1126352583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s6_4 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1101370069/5000000000 : ℝ)*x 0 + (1052860169/2000000000 : ℝ)*x 1 + (2697270933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1101370069/5000000000 : ℝ)^8261 ≤ (13377757372721/100000000000000 : ℝ)^6213 := by
    have hnat : (1101370069 : ℕ)^8261*100000000000000^6213 ≤ 13377757372721^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101370069 5000000000 13377757372721 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052860169/2000000000 : ℝ)^8261 ≤ (21303739586663/50000000000000 : ℝ)^6213 := by
    have hnat : (1052860169 : ℕ)^8261*50000000000000^6213 ≤ 21303739586663^6213*2000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052860169 2000000000 21303739586663 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697270933/5000000000 : ℝ)^8261 ≤ (44014763440287/100000000000000 : ℝ)^6213 := by
    have hnat : (2697270933 : ℕ)^8261*100000000000000^6213 ≤ 44014763440287^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697270933 5000000000 44014763440287 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1101370069/5000000000 : ℝ), (1052860169/2000000000 : ℝ), (2697270933/5000000000 : ℝ)] ![(13377757372721/100000000000000 : ℝ), (21303739586663/50000000000000 : ℝ), (44014763440287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1101370069/5000000000 : ℝ)|^8261 ≤ (13377757372721/100000000000000 : ℝ)^6213
        have hw : |(-1101370069/5000000000 : ℝ)|=(1101370069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052860169/2000000000 : ℝ)|^8261 ≤ (21303739586663/50000000000000 : ℝ)^6213
        have hw : |(1052860169/2000000000 : ℝ)|=(1052860169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697270933/5000000000 : ℝ)|^8261 ≤ (44014763440287/100000000000000 : ℝ)^6213
        have hw : |(2697270933/5000000000 : ℝ)|=(2697270933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s6_5 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328033839/2500000000 : ℝ)*x 0 + (-2138586803/10000000000 : ℝ)*x 1 + (5394541943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328033839/2500000000 : ℝ)^8261 ≤ (43123023902949/100000000000000 : ℝ)^6213 := by
    have hnat : (1328033839 : ℕ)^8261*100000000000000^6213 ≤ 43123023902949^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328033839 2500000000 43123023902949 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2138586803/10000000000 : ℝ)^8261 ≤ (401944118889/3125000000000 : ℝ)^6213 := by
    have hnat : (2138586803 : ℕ)^8261*3125000000000^6213 ≤ 401944118889^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138586803 10000000000 401944118889 3125000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394541943/10000000000 : ℝ)^8261 ≤ (2750922767227/6250000000000 : ℝ)^6213 := by
    have hnat : (5394541943 : ℕ)^8261*6250000000000^6213 ≤ 2750922767227^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394541943 10000000000 2750922767227 6250000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328033839/2500000000 : ℝ), (-2138586803/10000000000 : ℝ), (5394541943/10000000000 : ℝ)] ![(43123023902949/100000000000000 : ℝ), (401944118889/3125000000000 : ℝ), (2750922767227/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328033839/2500000000 : ℝ)|^8261 ≤ (43123023902949/100000000000000 : ℝ)^6213
        have hw : |(1328033839/2500000000 : ℝ)|=(1328033839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2138586803/10000000000 : ℝ)|^8261 ≤ (401944118889/3125000000000 : ℝ)^6213
        have hw : |(-2138586803/10000000000 : ℝ)|=(2138586803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394541943/10000000000 : ℝ)|^8261 ≤ (2750922767227/6250000000000 : ℝ)^6213
        have hw : |(5394541943/10000000000 : ℝ)|=(5394541943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s6_6 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664016883/1250000000 : ℝ)*x 0 + (674317789/1250000000 : ℝ)*x 1 + (-267323337/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664016883/1250000000 : ℝ)^8261 ≤ (43123020751181/100000000000000 : ℝ)^6213 := by
    have hnat : (664016883 : ℕ)^8261*100000000000000^6213 ≤ 43123020751181^6213*1250000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664016883 1250000000 43123020751181 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674317789/1250000000 : ℝ)^8261 ≤ (22007384139389/50000000000000 : ℝ)^6213 := by
    have hnat : (674317789 : ℕ)^8261*50000000000000^6213 ≤ 22007384139389^6213*1250000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674317789 1250000000 22007384139389 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (267323337/1250000000 : ℝ)^8261 ≤ (12862210948783/100000000000000 : ℝ)^6213 := by
    have hnat : (267323337 : ℕ)^8261*100000000000000^6213 ≤ 12862210948783^6213*1250000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267323337 1250000000 12862210948783 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664016883/1250000000 : ℝ), (674317789/1250000000 : ℝ), (-267323337/1250000000 : ℝ)] ![(43123020751181/100000000000000 : ℝ), (22007384139389/50000000000000 : ℝ), (12862210948783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664016883/1250000000 : ℝ)|^8261 ≤ (43123020751181/100000000000000 : ℝ)^6213
        have hw : |(664016883/1250000000 : ℝ)|=(664016883/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674317789/1250000000 : ℝ)|^8261 ≤ (22007384139389/50000000000000 : ℝ)^6213
        have hw : |(674317789/1250000000 : ℝ)|=(674317789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-267323337/1250000000 : ℝ)|^8261 ≤ (12862210948783/100000000000000 : ℝ)^6213
        have hw : |(-267323337/1250000000 : ℝ)|=(267323337/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s6_7 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4375187453/10000000000 : ℝ)*x 0 + (2252381031/5000000000 : ℝ)*x 1 + (169976243/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375187453/10000000000 : ℝ)^8261 ≤ (8329096526383/25000000000000 : ℝ)^6213 := by
    have hnat : (4375187453 : ℕ)^8261*25000000000000^6213 ≤ 8329096526383^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375187453 10000000000 8329096526383 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252381031/5000000000 : ℝ)^8261 ≤ (8658670807151/25000000000000 : ℝ)^6213 := by
    have hnat : (2252381031 : ℕ)^8261*25000000000000^6213 ≤ 8658670807151^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252381031 5000000000 8658670807151 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169976243/400000000 : ℝ)^8261 ≤ (32048930647507/100000000000000 : ℝ)^6213 := by
    have hnat : (169976243 : ℕ)^8261*100000000000000^6213 ≤ 32048930647507^6213*400000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169976243 400000000 32048930647507 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375187453/10000000000 : ℝ), (2252381031/5000000000 : ℝ), (169976243/400000000 : ℝ)] ![(8329096526383/25000000000000 : ℝ), (8658670807151/25000000000000 : ℝ), (32048930647507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375187453/10000000000 : ℝ)|^8261 ≤ (8329096526383/25000000000000 : ℝ)^6213
        have hw : |(4375187453/10000000000 : ℝ)|=(4375187453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252381031/5000000000 : ℝ)|^8261 ≤ (8658670807151/25000000000000 : ℝ)^6213
        have hw : |(2252381031/5000000000 : ℝ)|=(2252381031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169976243/400000000 : ℝ)|^8261 ≤ (32048930647507/100000000000000 : ℝ)^6213
        have hw : |(169976243/400000000 : ℝ)|=(169976243/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1068_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5601/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11243/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (438/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14059/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5601/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14059/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5601/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14059/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5601/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14059/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5601/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14059/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5601/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14059/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5601/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5601/50000 : ℝ) ^ (2065/512 : ℝ) ≤ (14642523012541273/100000000000000000000 : ℝ) := by
    have hpowers : (5601/50000 : ℝ)^2065 ≤ (14642523012541273/100000000000000000000 : ℝ)^512 := by
      have hnat : (5601 : ℕ)^2065*100000000000000000000^512 ≤ 14642523012541273^512*50000^2065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5601 50000 14642523012541273 100000000000000000000 2065 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5601/50000 : ℝ)) (X := (14642523012541273/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14059/100000 : ℝ) ^ (2065/512 : ℝ) ≤ (36603882130022259/100000000000000000000 : ℝ) := by
    have hpowers : (14059/100000 : ℝ)^2065 ≤ (36603882130022259/100000000000000000000 : ℝ)^512 := by
      have hnat : (14059 : ℕ)^2065*100000000000000000000^512 ≤ 36603882130022259^512*100000^2065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14059 100000 36603882130022259 100000000000000000000 2065 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14059/100000 : ℝ)) (X := (36603882130022259/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014642523012541273/50000000000000000000 : ℝ) ≤ (2500181504754357/2500000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (50014642523012541273/50000000000000000000 : ℝ)^512 ≤ (2500181504754357/2500000000000000 : ℝ)^2065 := by
      have hnat : (50014642523012541273 : ℕ)^512*2500000000000000^2065 ≤ 2500181504754357^2065*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014642523012541273 50000000000000000000 2500181504754357 2500000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500181504754357/2500000000000000 : ℝ)) (X := (50014642523012541273/50000000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012811601285640883/25000000000000000000 : ℝ) ≤ (10001270368271979/10000000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (25012811601285640883/25000000000000000000 : ℝ)^512 ≤ (10001270368271979/10000000000000000 : ℝ)^2065 := by
      have hnat : (25012811601285640883 : ℕ)^512*10000000000000000^2065 ≤ 10001270368271979^2065*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012811601285640883 25000000000000000000 10001270368271979 10000000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001270368271979/10000000000000000 : ℝ)) (X := (25012811601285640883/25000000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036603882130022259/50000000000000000000 : ℝ) ≤ (1000181471752653/1000000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (50036603882130022259/50000000000000000000 : ℝ)^512 ≤ (1000181471752653/1000000000000000 : ℝ)^2065 := by
      have hnat : (50036603882130022259 : ℕ)^512*1000000000000000^2065 ≤ 1000181471752653^2065*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036603882130022259 50000000000000000000 1000181471752653 1000000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000181471752653/1000000000000000 : ℝ)) (X := (50036603882130022259/50000000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14642523012541273/100000000000000000000 : ℝ) ≤ ((3569984829454228899/3571250000000000000 : ℝ)+2*(544349254551/285700000000000 : ℝ)*(5601/50000 : ℝ))^(2065/512 : ℝ) := by
    rw [show (3569984829454228899/3571250000000000000 : ℝ)+2*(544349254551/285700000000000 : ℝ)*(5601/50000 : ℝ)=(2500181504754357/2500000000000000 : ℝ) by norm_num, show 1+2*(14642523012541273/100000000000000000000 : ℝ)=(50014642523012541273/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36603882130022259/100000000000000000000 : ℝ)+(14642523012541273/100000000000000000000 : ℝ) ≤ ((3569984829454228899/3571250000000000000 : ℝ)+(544349254551/285700000000000 : ℝ)*((14059/100000 : ℝ)+(5601/50000 : ℝ)))^(2065/512 : ℝ) := by
    rw [show (3569984829454228899/3571250000000000000 : ℝ)+(544349254551/285700000000000 : ℝ)*((14059/100000 : ℝ)+(5601/50000 : ℝ))=(10001270368271979/10000000000000000 : ℝ) by norm_num, show 1+(36603882130022259/100000000000000000000 : ℝ)+(14642523012541273/100000000000000000000 : ℝ)=(25012811601285640883/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36603882130022259/100000000000000000000 : ℝ) ≤ ((3569984829454228899/3571250000000000000 : ℝ)+2*(544349254551/285700000000000 : ℝ)*(14059/100000 : ℝ))^(2065/512 : ℝ) := by
    rw [show (3569984829454228899/3571250000000000000 : ℝ)+2*(544349254551/285700000000000 : ℝ)*(14059/100000 : ℝ)=(1000181471752653/1000000000000000 : ℝ) by norm_num, show 1+2*(36603882130022259/100000000000000000000 : ℝ)=(50036603882130022259/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3569984829454228899/3571250000000000000 : ℝ)*(X 1 0+X 2 0)+(544349254551/285700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (5601/50000 : ℝ)) (hi := (14059/100000 : ℝ)) (c := (3569984829454228899/3571250000000000000 : ℝ)) (alpha := (544349254551/285700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3569984829454228899/3571250000000000000 : ℝ)*(X 0 1+X 2 1)+(544349254551/285700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (5601/50000 : ℝ)) (hi := (14059/100000 : ℝ)) (c := (3569984829454228899/3571250000000000000 : ℝ)) (alpha := (544349254551/285700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3569984829454228899/3571250000000000000 : ℝ)*(X 0 2+X 1 2)+(544349254551/285700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (5601/50000 : ℝ)) (hi := (14059/100000 : ℝ)) (c := (3569984829454228899/3571250000000000000 : ℝ)) (alpha := (544349254551/285700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1101367433/5000000000 : ℝ)*X 0 0+(2697436907/5000000000 : ℝ)*X 0 1+(5263970161/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345112577/10000000000 : ℝ)*X 1 0+(-2269158533/10000000000 : ℝ)*X 1 1+(5263970197/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069022487/2000000000 : ℝ)*X 2 0+(1315992569/2500000000 : ℝ)*X 2 1+(-2269158617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187588623/5000000000 : ℝ)*X 0 0+(132773609/312500000 : ℝ)*X 0 1+(1126352583/2500000000 : ℝ)*X 0 2+(2187588623/5000000000 : ℝ)*X 1 0+(132773609/312500000 : ℝ)*X 1 1+(1126352583/2500000000 : ℝ)*X 1 2+(2187588623/5000000000 : ℝ)*X 2 0+(132773609/312500000 : ℝ)*X 2 1+(1126352583/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1101370069/5000000000 : ℝ)*X 0 0+(1052860169/2000000000 : ℝ)*X 0 1+(2697270933/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328033839/2500000000 : ℝ)*X 1 0+(-2138586803/10000000000 : ℝ)*X 1 1+(5394541943/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664016883/1250000000 : ℝ)*X 2 0+(674317789/1250000000 : ℝ)*X 2 1+(-267323337/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4375187453/10000000000 : ℝ)*X 0 0+(2252381031/5000000000 : ℝ)*X 0 1+(169976243/400000000 : ℝ)*X 0 2+(4375187453/10000000000 : ℝ)*X 1 0+(2252381031/5000000000 : ℝ)*X 1 1+(169976243/400000000 : ℝ)*X 1 2+(4375187453/10000000000 : ℝ)*X 2 0+(2252381031/5000000000 : ℝ)*X 2 1+(169976243/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (163902304877175149892900549/22320312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1587757447/100000000000000 : ℝ)*(base19) + (672308497/50000000000000 : ℝ)*(base23) + (10741667/50000000000000 : ℝ)*(lower2) + (268977301/100000000000000 : ℝ)*(upper3) + (34572691/50000000000000 : ℝ)*(upper5) + (1441953142237367/25000000000000 : ℝ)*(major0) + (1441953142237367/25000000000000 : ℝ)*(major1) + (1441953142237367/25000000000000 : ℝ)*(major2) + (3819628098088979/50000000000000 : ℝ)*(sp0) + (3819646852504489/50000000000000 : ℝ)*(sp1) + (7639293948149431/100000000000000 : ℝ)*(sp2) + (487038106690667/12500000000000 : ℝ)*(sp3) + (9774147117/25000000000000 : ℝ)*(sp4) + (24746834151/100000000000000 : ℝ)*(sp7) + (60880150005617/1562500000000 : ℝ)*(f.failure) + (305571811710657/4000000000000 : ℝ)*(f.sum) + (78016790214473/14285000000000000000000000000 : ℝ)*base65 + (1162765856360531067/89281250000000000000000000000000 : ℝ)*base68 + (1406626948499812317/89281250000000000000000000000000 : ℝ)*base70 + (792675852111625183/89281250000000000000000000000000 : ℝ)*base71 + (8056975065273/3571250000000000000000000000 : ℝ)*base74 + (357814761374187317/89281250000000000000000000000000 : ℝ)*base76 + (338567420307218567/89281250000000000000000000000000 : ℝ)*base78 + (161250370710156067/89281250000000000000000000000000 : ℝ)*base80 + (34453322136559/7142500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1696299/156250000000000000000 : ℝ)*base89 + (1696299/156250000000000000000 : ℝ)*base91 + (1696299/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (113799464089966698696903/14285000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43498781/2500000000000 : ℝ)*(base19) + (285262907/20000000000000 : ℝ)*(base23) + (12409603/50000000000000 : ℝ)*(upper2) + (285649253/100000000000000 : ℝ)*(upper3) + (79381691/50000000000000 : ℝ)*(upper5) + (5797082215048877/100000000000000 : ℝ)*(major0) + (5797082215048877/100000000000000 : ℝ)*(major1) + (5797082215048877/100000000000000 : ℝ)*(major2) + (11005425907/25000000000000 : ℝ)*(sp1) + (53959257741/100000000000000 : ℝ)*(sp2) + (383903102217331/5000000000000 : ℝ)*(sp4) + (7678016282691753/100000000000000 : ℝ)*(sp5) + (1535601331754869/20000000000000 : ℝ)*(sp6) + (3916102120205767/100000000000000 : ℝ)*(sp7) + (3916102120205767/100000000000000 : ℝ)*(f.failure) + (383903102217331/5000000000000 : ℝ)*(f.sum) + (4476765758427/3571250000000000000000000000 : ℝ)*base66 + (2494851286013516077/357125000000000000000000000000000 : ℝ)*base68 + (167293460450608923/357125000000000000000000000000000 : ℝ)*base69 + (1411780365136858923/357125000000000000000000000000000 : ℝ)*base71 + (19337487970877/3571250000000000000000000000 : ℝ)*base74 + (1708283425658766077/357125000000000000000000000000000 : ℝ)*base76 + (991446386100983923/357125000000000000000000000000000 : ℝ)*base77 + (4162838688187516077/357125000000000000000000000000000 : ℝ)*base80 + (118539292842053/14285000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (29638349/10000000000000000000000 : ℝ)*base89 + (29638349/10000000000000000000000 : ℝ)*base91 + (29638349/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1068_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5601/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (438/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1068_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1068_s7_0 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2202775099/10000000000 : ℝ)*x 0 + (84287787/156250000 : ℝ)*x 1 + (5264399107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2202775099/10000000000 : ℝ)^8261 ≤ (6689019844623/50000000000000 : ℝ)^6213 := by
    have hnat : (2202775099 : ℕ)^8261*50000000000000^6213 ≤ 6689019844623^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202775099 10000000000 6689019844623 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84287787/156250000 : ℝ)^8261 ≤ (22006711830347/50000000000000 : ℝ)^6213 := by
    have hnat : (84287787 : ℕ)^8261*50000000000000^6213 ≤ 22006711830347^6213*156250000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84287787 156250000 22006711830347 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264399107/10000000000 : ℝ)^8261 ≤ (21304268315927/50000000000000 : ℝ)^6213 := by
    have hnat : (5264399107 : ℕ)^8261*50000000000000^6213 ≤ 21304268315927^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264399107 10000000000 21304268315927 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2202775099/10000000000 : ℝ), (84287787/156250000 : ℝ), (5264399107/10000000000 : ℝ)] ![(6689019844623/50000000000000 : ℝ), (22006711830347/50000000000000 : ℝ), (21304268315927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2202775099/10000000000 : ℝ)|^8261 ≤ (6689019844623/50000000000000 : ℝ)^6213
        have hw : |(-2202775099/10000000000 : ℝ)|=(2202775099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84287787/156250000 : ℝ)|^8261 ≤ (22006711830347/50000000000000 : ℝ)^6213
        have hw : |(84287787/156250000 : ℝ)|=(84287787/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264399107/10000000000 : ℝ)|^8261 ≤ (21304268315927/50000000000000 : ℝ)^6213
        have hw : |(5264399107/10000000000 : ℝ)|=(5264399107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s7_1 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344998719/10000000000 : ℝ)*x 0 + (-2268742949/10000000000 : ℝ)*x 1 + (5264399531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344998719/10000000000 : ℝ)^8261 ≤ (21739051591261/50000000000000 : ℝ)^6213 := by
    have hnat : (5344998719 : ℕ)^8261*50000000000000^6213 ≤ 21739051591261^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344998719 10000000000 21739051591261 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2268742949/10000000000 : ℝ)^8261 ≤ (13913355603773/100000000000000 : ℝ)^6213 := by
    have hnat : (2268742949 : ℕ)^8261*100000000000000^6213 ≤ 13913355603773^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2268742949 10000000000 13913355603773 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264399531/10000000000 : ℝ)^8261 ≤ (10652135298699/25000000000000 : ℝ)^6213 := by
    have hnat : (5264399531 : ℕ)^8261*25000000000000^6213 ≤ 10652135298699^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264399531 10000000000 10652135298699 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344998719/10000000000 : ℝ), (-2268742949/10000000000 : ℝ), (5264399531/10000000000 : ℝ)] ![(21739051591261/50000000000000 : ℝ), (13913355603773/100000000000000 : ℝ), (10652135298699/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344998719/10000000000 : ℝ)|^8261 ≤ (21739051591261/50000000000000 : ℝ)^6213
        have hw : |(5344998719/10000000000 : ℝ)|=(5344998719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2268742949/10000000000 : ℝ)|^8261 ≤ (13913355603773/100000000000000 : ℝ)^6213
        have hw : |(-2268742949/10000000000 : ℝ)|=(2268742949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264399531/10000000000 : ℝ)|^8261 ≤ (10652135298699/25000000000000 : ℝ)^6213
        have hw : |(5264399531/10000000000 : ℝ)|=(5264399531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s7_2 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267249943/500000000 : ℝ)*x 0 + (329024949/625000000 : ℝ)*x 1 + (-113437161/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267249943/500000000 : ℝ)^8261 ≤ (8695620941507/20000000000000 : ℝ)^6213 := by
    have hnat : (267249943 : ℕ)^8261*20000000000000^6213 ≤ 8695620941507^6213*500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267249943 500000000 8695620941507 20000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329024949/625000000 : ℝ)^8261 ≤ (42608537460501/100000000000000 : ℝ)^6213 := by
    have hnat : (329024949 : ℕ)^8261*100000000000000^6213 ≤ 42608537460501^6213*625000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329024949 625000000 42608537460501 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113437161/500000000 : ℝ)^8261 ≤ (1739169726693/12500000000000 : ℝ)^6213 := by
    have hnat : (113437161 : ℕ)^8261*12500000000000^6213 ≤ 1739169726693^6213*500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113437161 500000000 1739169726693 12500000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267249943/500000000 : ℝ), (329024949/625000000 : ℝ), (-113437161/500000000 : ℝ)] ![(8695620941507/20000000000000 : ℝ), (42608537460501/100000000000000 : ℝ), (1739169726693/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267249943/500000000 : ℝ)|^8261 ≤ (8695620941507/20000000000000 : ℝ)^6213
        have hw : |(267249943/500000000 : ℝ)|=(267249943/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329024949/625000000 : ℝ)|^8261 ≤ (42608537460501/100000000000000 : ℝ)^6213
        have hw : |(329024949/625000000 : ℝ)|=(329024949/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-113437161/500000000 : ℝ)|^8261 ≤ (1739169726693/12500000000000 : ℝ)^6213
        have hw : |(-113437161/500000000 : ℝ)|=(113437161/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s7_3 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (875039957/2000000000 : ℝ)*x 0 + (4249620251/10000000000 : ℝ)*x 1 + (18018159/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875039957/2000000000 : ℝ)^8261 ≤ (832912774159/2500000000000 : ℝ)^6213 := by
    have hnat : (875039957 : ℕ)^8261*2500000000000^6213 ≤ 832912774159^6213*2000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875039957 2000000000 832912774159 2500000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4249620251/10000000000 : ℝ)^8261 ≤ (16025539216707/50000000000000 : ℝ)^6213 := by
    have hnat : (4249620251 : ℕ)^8261*50000000000000^6213 ≤ 16025539216707^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249620251 10000000000 16025539216707 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18018159/40000000 : ℝ)^8261 ≤ (865810264799/2500000000000 : ℝ)^6213 := by
    have hnat : (18018159 : ℕ)^8261*2500000000000^6213 ≤ 865810264799^6213*40000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18018159 40000000 865810264799 2500000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875039957/2000000000 : ℝ), (4249620251/10000000000 : ℝ), (18018159/40000000 : ℝ)] ![(832912774159/2500000000000 : ℝ), (16025539216707/50000000000000 : ℝ), (865810264799/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875039957/2000000000 : ℝ)|^8261 ≤ (832912774159/2500000000000 : ℝ)^6213
        have hw : |(875039957/2000000000 : ℝ)|=(875039957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4249620251/10000000000 : ℝ)|^8261 ≤ (16025539216707/50000000000000 : ℝ)^6213
        have hw : |(4249620251/10000000000 : ℝ)|=(4249620251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(18018159/40000000 : ℝ)|^8261 ≤ (865810264799/2500000000000 : ℝ)^6213
        have hw : |(18018159/40000000 : ℝ)|=(18018159/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s7_4 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-550694993/2500000000 : ℝ)*x 0 + (1316181367/2500000000 : ℝ)*x 1 + (5394090987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (550694993/2500000000 : ℝ)^8261 ≤ (6689039519869/50000000000000 : ℝ)^6213 := by
    have hnat : (550694993 : ℕ)^8261*50000000000000^6213 ≤ 6689039519869^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550694993 2500000000 6689039519869 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316181367/2500000000 : ℝ)^8261 ≤ (42612048852351/100000000000000 : ℝ)^6213 := by
    have hnat : (1316181367 : ℕ)^8261*100000000000000^6213 ≤ 42612048852351^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316181367 2500000000 42612048852351 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394090987/10000000000 : ℝ)^8261 ≤ (44009872086251/100000000000000 : ℝ)^6213 := by
    have hnat : (5394090987 : ℕ)^8261*100000000000000^6213 ≤ 44009872086251^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394090987 10000000000 44009872086251 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-550694993/2500000000 : ℝ), (1316181367/2500000000 : ℝ), (5394090987/10000000000 : ℝ)] ![(6689039519869/50000000000000 : ℝ), (42612048852351/100000000000000 : ℝ), (44009872086251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-550694993/2500000000 : ℝ)|^8261 ≤ (6689039519869/50000000000000 : ℝ)^6213
        have hw : |(-550694993/2500000000 : ℝ)|=(550694993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316181367/2500000000 : ℝ)|^8261 ≤ (42612048852351/100000000000000 : ℝ)^6213
        have hw : |(1316181367/2500000000 : ℝ)|=(1316181367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394090987/10000000000 : ℝ)|^8261 ≤ (44009872086251/100000000000000 : ℝ)^6213
        have hw : |(5394090987/10000000000 : ℝ)|=(5394090987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s7_5 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656122133/5000000000 : ℝ)*x 0 + (-2139051609/10000000000 : ℝ)*x 1 + (2697045471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656122133/5000000000 : ℝ)^8261 ≤ (8624839890299/20000000000000 : ℝ)^6213 := by
    have hnat : (2656122133 : ℕ)^8261*20000000000000^6213 ≤ 8624839890299^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656122133 5000000000 8624839890299 20000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2139051609/10000000000 : ℝ)^8261 ≤ (6432964465403/50000000000000 : ℝ)^6213 := by
    have hnat : (2139051609 : ℕ)^8261*50000000000000^6213 ≤ 6432964465403^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139051609 10000000000 6432964465403 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697045471/5000000000 : ℝ)^8261 ≤ (11002467899519/25000000000000 : ℝ)^6213 := by
    have hnat : (2697045471 : ℕ)^8261*25000000000000^6213 ≤ 11002467899519^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697045471 5000000000 11002467899519 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656122133/5000000000 : ℝ), (-2139051609/10000000000 : ℝ), (2697045471/5000000000 : ℝ)] ![(8624839890299/20000000000000 : ℝ), (6432964465403/50000000000000 : ℝ), (11002467899519/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656122133/5000000000 : ℝ)|^8261 ≤ (8624839890299/20000000000000 : ℝ)^6213
        have hw : |(2656122133/5000000000 : ℝ)|=(2656122133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2139051609/10000000000 : ℝ)|^8261 ≤ (6432964465403/50000000000000 : ℝ)^6213
        have hw : |(-2139051609/10000000000 : ℝ)|=(2139051609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697045471/5000000000 : ℝ)|^8261 ≤ (11002467899519/25000000000000 : ℝ)^6213
        have hw : |(2697045471/5000000000 : ℝ)|=(2697045471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s7_6 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664030533/1250000000 : ℝ)*x 0 + (5394090921/10000000000 : ℝ)*x 1 + (-1069525821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664030533/1250000000 : ℝ)^8261 ≤ (10781049857477/25000000000000 : ℝ)^6213 := by
    have hnat : (664030533 : ℕ)^8261*25000000000000^6213 ≤ 10781049857477^6213*1250000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664030533 1250000000 10781049857477 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394090921/10000000000 : ℝ)^8261 ≤ (44009871370261/100000000000000 : ℝ)^6213 := by
    have hnat : (5394090921 : ℕ)^8261*100000000000000^6213 ≤ 44009871370261^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394090921 10000000000 44009871370261 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1069525821/5000000000 : ℝ)^8261 ≤ (6432964597361/50000000000000 : ℝ)^6213 := by
    have hnat : (1069525821 : ℕ)^8261*50000000000000^6213 ≤ 6432964597361^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069525821 5000000000 6432964597361 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664030533/1250000000 : ℝ), (5394090921/10000000000 : ℝ), (-1069525821/5000000000 : ℝ)] ![(10781049857477/25000000000000 : ℝ), (44009871370261/100000000000000 : ℝ), (6432964597361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664030533/1250000000 : ℝ)|^8261 ≤ (10781049857477/25000000000000 : ℝ)^6213
        have hw : |(664030533/1250000000 : ℝ)|=(664030533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394090921/10000000000 : ℝ)|^8261 ≤ (44009871370261/100000000000000 : ℝ)^6213
        have hw : |(5394090921/10000000000 : ℝ)|=(5394090921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1069525821/5000000000 : ℝ)|^8261 ≤ (6432964597361/50000000000000 : ℝ)^6213
        have hw : |(-1069525821/5000000000 : ℝ)|=(1069525821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s7_7 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187604959/5000000000 : ℝ)*x 0 + (4503900519/10000000000 : ℝ)*x 1 + (4250261613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187604959/5000000000 : ℝ)^8261 ≤ (33316613562519/100000000000000 : ℝ)^6213 := by
    have hnat : (2187604959 : ℕ)^8261*100000000000000^6213 ≤ 33316613562519^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187604959 5000000000 33316613562519 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503900519/10000000000 : ℝ)^8261 ≤ (17312938054447/50000000000000 : ℝ)^6213 := by
    have hnat : (4503900519 : ℕ)^8261*50000000000000^6213 ≤ 17312938054447^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503900519 10000000000 17312938054447 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4250261613/10000000000 : ℝ)^8261 ≤ (16028755155867/50000000000000 : ℝ)^6213 := by
    have hnat : (4250261613 : ℕ)^8261*50000000000000^6213 ≤ 16028755155867^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250261613 10000000000 16028755155867 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187604959/5000000000 : ℝ), (4503900519/10000000000 : ℝ), (4250261613/10000000000 : ℝ)] ![(33316613562519/100000000000000 : ℝ), (17312938054447/50000000000000 : ℝ), (16028755155867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187604959/5000000000 : ℝ)|^8261 ≤ (33316613562519/100000000000000 : ℝ)^6213
        have hw : |(2187604959/5000000000 : ℝ)|=(2187604959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503900519/10000000000 : ℝ)|^8261 ≤ (17312938054447/50000000000000 : ℝ)^6213
        have hw : |(4503900519/10000000000 : ℝ)|=(4503900519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4250261613/10000000000 : ℝ)|^8261 ≤ (16028755155867/50000000000000 : ℝ)^6213
        have hw : |(4250261613/10000000000 : ℝ)|=(4250261613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1068_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (438/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2813/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7003/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (438/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (438/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (438/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (438/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (438/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (438/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11243/100000 : ℝ) ^ (2065/512 : ℝ) ≤ (7429937668775473/50000000000000000000 : ℝ) := by
    have hpowers : (11243/100000 : ℝ)^2065 ≤ (7429937668775473/50000000000000000000 : ℝ)^512 := by
      have hnat : (11243 : ℕ)^2065*50000000000000000000^512 ≤ 7429937668775473^512*100000^2065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11243 100000 7429937668775473 50000000000000000000 2065 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11243/100000 : ℝ)) (X := (7429937668775473/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hpowhi : (438/3125 : ℝ) ^ (2065/512 : ℝ) ≤ (7230887486473713/20000000000000000000 : ℝ) := by
    have hpowers : (438/3125 : ℝ)^2065 ≤ (7230887486473713/20000000000000000000 : ℝ)^512 := by
      have hnat : (438 : ℕ)^2065*20000000000000000000^512 ≤ 7230887486473713^512*3125^2065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        438 3125 7230887486473713 20000000000000000000 2065 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (438/3125 : ℝ)) (X := (7230887486473713/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007429937668775473/25000000000000000000 : ℝ) ≤ (5000368397387917/5000000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (25007429937668775473/25000000000000000000 : ℝ)^512 ≤ (5000368397387917/5000000000000000 : ℝ)^2065 := by
      have hnat : (25007429937668775473 : ℕ)^512*5000000000000000^2065 ≤ 5000368397387917^2065*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007429937668775473 25000000000000000000 5000368397387917 5000000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000368397387917/5000000000000000 : ℝ)) (X := (25007429937668775473/25000000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051014312769919511/100000000000000000000 : ℝ) ≤ (10001264615941661/10000000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (100051014312769919511/100000000000000000000 : ℝ)^512 ≤ (10001264615941661/10000000000000000 : ℝ)^2065 := by
      have hnat : (100051014312769919511 : ℕ)^512*10000000000000000^2065 ≤ 10001264615941661^2065*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051014312769919511 100000000000000000000 10001264615941661 10000000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001264615941661/10000000000000000 : ℝ)) (X := (100051014312769919511/100000000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007230887486473713/10000000000000000000 : ℝ) ≤ (312556013659609/312500000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (10007230887486473713/10000000000000000000 : ℝ)^512 ≤ (312556013659609/312500000000000 : ℝ)^2065 := by
      have hnat : (10007230887486473713 : ℕ)^512*312500000000000^2065 ≤ 312556013659609^2065*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007230887486473713 10000000000000000000 312556013659609 312500000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312556013659609/312500000000000 : ℝ)) (X := (10007230887486473713/10000000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7429937668775473/50000000000000000000 : ℝ) ≤ ((173251090907366261/173312500000000000 : ℝ)+2*(527821165827/277300000000000 : ℝ)*(11243/100000 : ℝ))^(2065/512 : ℝ) := by
    rw [show (173251090907366261/173312500000000000 : ℝ)+2*(527821165827/277300000000000 : ℝ)*(11243/100000 : ℝ)=(5000368397387917/5000000000000000 : ℝ) by norm_num, show 1+2*(7429937668775473/50000000000000000000 : ℝ)=(25007429937668775473/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7230887486473713/20000000000000000000 : ℝ)+(7429937668775473/50000000000000000000 : ℝ) ≤ ((173251090907366261/173312500000000000 : ℝ)+(527821165827/277300000000000 : ℝ)*((438/3125 : ℝ)+(11243/100000 : ℝ)))^(2065/512 : ℝ) := by
    rw [show (173251090907366261/173312500000000000 : ℝ)+(527821165827/277300000000000 : ℝ)*((438/3125 : ℝ)+(11243/100000 : ℝ))=(10001264615941661/10000000000000000 : ℝ) by norm_num, show 1+(7230887486473713/20000000000000000000 : ℝ)+(7429937668775473/50000000000000000000 : ℝ)=(100051014312769919511/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7230887486473713/20000000000000000000 : ℝ) ≤ ((173251090907366261/173312500000000000 : ℝ)+2*(527821165827/277300000000000 : ℝ)*(438/3125 : ℝ))^(2065/512 : ℝ) := by
    rw [show (173251090907366261/173312500000000000 : ℝ)+2*(527821165827/277300000000000 : ℝ)*(438/3125 : ℝ)=(312556013659609/312500000000000 : ℝ) by norm_num, show 1+2*(7230887486473713/20000000000000000000 : ℝ)=(10007230887486473713/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (173251090907366261/173312500000000000 : ℝ)*(X 1 0+X 2 0)+(527821165827/277300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (11243/100000 : ℝ)) (hi := (438/3125 : ℝ)) (c := (173251090907366261/173312500000000000 : ℝ)) (alpha := (527821165827/277300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (173251090907366261/173312500000000000 : ℝ)*(X 0 1+X 2 1)+(527821165827/277300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (11243/100000 : ℝ)) (hi := (438/3125 : ℝ)) (c := (173251090907366261/173312500000000000 : ℝ)) (alpha := (527821165827/277300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (173251090907366261/173312500000000000 : ℝ)*(X 0 2+X 1 2)+(527821165827/277300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (11243/100000 : ℝ)) (hi := (438/3125 : ℝ)) (c := (173251090907366261/173312500000000000 : ℝ)) (alpha := (527821165827/277300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2202775099/10000000000 : ℝ)*X 0 0+(84287787/156250000 : ℝ)*X 0 1+(5264399107/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344998719/10000000000 : ℝ)*X 1 0+(-2268742949/10000000000 : ℝ)*X 1 1+(5264399531/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267249943/500000000 : ℝ)*X 2 0+(329024949/625000000 : ℝ)*X 2 1+(-113437161/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((875039957/2000000000 : ℝ)*X 0 0+(4249620251/10000000000 : ℝ)*X 0 1+(18018159/40000000 : ℝ)*X 0 2+(875039957/2000000000 : ℝ)*X 1 0+(4249620251/10000000000 : ℝ)*X 1 1+(18018159/40000000 : ℝ)*X 1 2+(875039957/2000000000 : ℝ)*X 2 0+(4249620251/10000000000 : ℝ)*X 2 1+(18018159/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-550694993/2500000000 : ℝ)*X 0 0+(1316181367/2500000000 : ℝ)*X 0 1+(5394090987/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656122133/5000000000 : ℝ)*X 1 0+(-2139051609/10000000000 : ℝ)*X 1 1+(2697045471/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664030533/1250000000 : ℝ)*X 2 0+(5394090921/10000000000 : ℝ)*X 2 1+(-1069525821/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2187604959/5000000000 : ℝ)*X 0 0+(4503900519/10000000000 : ℝ)*X 0 1+(4250261613/10000000000 : ℝ)*X 0 2+(2187604959/5000000000 : ℝ)*X 1 0+(4503900519/10000000000 : ℝ)*X 1 1+(4250261613/10000000000 : ℝ)*X 1 2+(2187604959/5000000000 : ℝ)*X 2 0+(4503900519/10000000000 : ℝ)*X 2 1+(4250261613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60953732267371210309123929/8665625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2058054977/100000000000000 : ℝ)*(base19) + (112010553/5000000000000 : ℝ)*(base23) + (75100111/100000000000000 : ℝ)*(upper2) + (402611609/100000000000000 : ℝ)*(upper3) + (10773167/12500000000000 : ℝ)*(upper4) + (5807094751894513/100000000000000 : ℝ)*(major0) + (5807094751894513/100000000000000 : ℝ)*(major1) + (5807094751894513/100000000000000 : ℝ)*(major2) + (384562706588831/5000000000000 : ℝ)*(sp0) + (3845660661739167/50000000000000 : ℝ)*(sp1) + (7691321141322251/100000000000000 : ℝ)*(sp2) + (1961415874279381/50000000000000 : ℝ)*(sp3) + (17312439173/25000000000000 : ℝ)*(sp4) + (34139231333/100000000000000 : ℝ)*(sp7) + (245179117986881/6250000000000 : ℝ)*(f.failure) + (7691323381533311/100000000000000 : ℝ)*(f.sum) + (82549961663351/13865000000000000000000000000 : ℝ)*base65 + (2379677778386741/8665625000000000000000000000000 : ℝ)*base68 + (8475890452975759/8665625000000000000000000000000 : ℝ)*base69 + (12503860455701183/4332812500000000000000000000000 : ℝ)*base72 + (5249625997/6770019531250000000000000 : ℝ)*base73 + (26789406291319509/8665625000000000000000000000000 : ℝ)*base75 + (1906021999720851/541601562500000000000000000000 : ℝ)*base78 + (56701492718586741/8665625000000000000000000000000 : ℝ)*base80 + (31556638035733/6932500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (8637307/625000000000000000000 : ℝ)*base89 + (8637307/625000000000000000000 : ℝ)*base91 + (8637307/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15454744275127303727922903/4332812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (101442189/12500000000000 : ℝ)*(base19) + (870723571/100000000000000 : ℝ)*(base23) + (13416501/25000000000000 : ℝ)*(upper3) + (20192841/50000000000000 : ℝ)*(lower4) + (57204151/50000000000000 : ℝ)*(upper5) + (5836323920591719/100000000000000 : ℝ)*(major0) + (5836323920591719/100000000000000 : ℝ)*(major1) + (5836323920591719/100000000000000 : ℝ)*(major2) + (1375069999/6250000000000 : ℝ)*(sp1) + (19742227919/100000000000000 : ℝ)*(sp2) + (3865018329171919/50000000000000 : ℝ)*(sp4) + (7730013845686341/100000000000000 : ℝ)*(sp5) + (1932504011348087/25000000000000 : ℝ)*(sp6) + (78852221278853/2000000000000 : ℝ)*(sp7) + (78852221278853/2000000000000 : ℝ)*(f.failure) + (3865018329171919/50000000000000 : ℝ)*(f.sum) + (53993729637247/13865000000000000000000000000 : ℝ)*base66 + (69040080185727929/4332812500000000000000000000000 : ℝ)*base68 + (5367440028600769/270800781250000000000000000000 : ℝ)*base70 + (18718676086452929/4332812500000000000000000000000 : ℝ)*base72 + (23431594672903/3466250000000000000000000000 : ℝ)*base74 + (17165270811040527/2166406250000000000000000000000 : ℝ)*base76 + (10118864931296777/2166406250000000000000000000000 : ℝ)*base78 + (98225144430509179/4332812500000000000000000000000 : ℝ)*base80 + (121262684489097/13865000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1516791/200000000000000000000 : ℝ)*base89 + (1516791/200000000000000000000 : ℝ)*base91 + (1516791/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1068_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (438/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2813/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7003/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1068_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1068_s8_0 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-440557139/2000000000 : ℝ)*x 0 + (5394315741/10000000000 : ℝ)*x 1 + (5264494611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (440557139/2000000000 : ℝ)^8261 ≤ (13378125254193/100000000000000 : ℝ)^6213 := by
    have hnat : (440557139 : ℕ)^8261*100000000000000^6213 ≤ 13378125254193^6213*2000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440557139 2000000000 13378125254193 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394315741/10000000000 : ℝ)^8261 ≤ (44012310309787/100000000000000 : ℝ)^6213 := by
    have hnat : (5394315741 : ℕ)^8261*100000000000000^6213 ≤ 44012310309787^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394315741 10000000000 44012310309787 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264494611/10000000000 : ℝ)^8261 ≤ (21304782208031/50000000000000 : ℝ)^6213 := by
    have hnat : (5264494611 : ℕ)^8261*50000000000000^6213 ≤ 21304782208031^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264494611 10000000000 21304782208031 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-440557139/2000000000 : ℝ), (5394315741/10000000000 : ℝ), (5264494611/10000000000 : ℝ)] ![(13378125254193/100000000000000 : ℝ), (44012310309787/100000000000000 : ℝ), (21304782208031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-440557139/2000000000 : ℝ)|^8261 ≤ (13378125254193/100000000000000 : ℝ)^6213
        have hw : |(-440557139/2000000000 : ℝ)|=(440557139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394315741/10000000000 : ℝ)|^8261 ≤ (44012310309787/100000000000000 : ℝ)^6213
        have hw : |(5394315741/10000000000 : ℝ)|=(5394315741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264494611/10000000000 : ℝ)|^8261 ≤ (21304782208031/50000000000000 : ℝ)^6213
        have hw : |(5264494611/10000000000 : ℝ)|=(5264494611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s8_1 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (167030391/312500000 : ℝ)*x 0 + (-90746089/400000000 : ℝ)*x 1 + (5264494611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167030391/312500000 : ℝ)^8261 ≤ (869556394719/2000000000000 : ℝ)^6213 := by
    have hnat : (167030391 : ℕ)^8261*2000000000000^6213 ≤ 869556394719^6213*312500000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167030391 312500000 869556394719 2000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90746089/400000000 : ℝ)^8261 ≤ (13912615832967/100000000000000 : ℝ)^6213 := by
    have hnat : (90746089 : ℕ)^8261*100000000000000^6213 ≤ 13912615832967^6213*400000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90746089 400000000 13912615832967 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264494611/10000000000 : ℝ)^8261 ≤ (21304782208031/50000000000000 : ℝ)^6213 := by
    have hnat : (5264494611 : ℕ)^8261*50000000000000^6213 ≤ 21304782208031^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264494611 10000000000 21304782208031 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167030391/312500000 : ℝ), (-90746089/400000000 : ℝ), (5264494611/10000000000 : ℝ)] ![(869556394719/2000000000000 : ℝ), (13912615832967/100000000000000 : ℝ), (21304782208031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167030391/312500000 : ℝ)|^8261 ≤ (869556394719/2000000000000 : ℝ)^6213
        have hw : |(167030391/312500000 : ℝ)|=(167030391/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-90746089/400000000 : ℝ)|^8261 ≤ (13912615832967/100000000000000 : ℝ)^6213
        have hw : |(-90746089/400000000 : ℝ)|=(90746089/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264494611/10000000000 : ℝ)|^8261 ≤ (21304782208031/50000000000000 : ℝ)^6213
        have hw : |(5264494611/10000000000 : ℝ)|=(5264494611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s8_2 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534497251/1000000000 : ℝ)*x 0 + (5264494611/10000000000 : ℝ)*x 1 + (-567163057/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534497251/1000000000 : ℝ)^8261 ≤ (43477819714319/100000000000000 : ℝ)^6213 := by
    have hnat : (534497251 : ℕ)^8261*100000000000000^6213 ≤ 43477819714319^6213*1000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534497251 1000000000 43477819714319 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264494611/10000000000 : ℝ)^8261 ≤ (21304782208031/50000000000000 : ℝ)^6213 := by
    have hnat : (5264494611 : ℕ)^8261*50000000000000^6213 ≤ 21304782208031^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264494611 10000000000 21304782208031 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (567163057/2500000000 : ℝ)^8261 ≤ (13912615857429/100000000000000 : ℝ)^6213 := by
    have hnat : (567163057 : ℕ)^8261*100000000000000^6213 ≤ 13912615857429^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567163057 2500000000 13912615857429 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534497251/1000000000 : ℝ), (5264494611/10000000000 : ℝ), (-567163057/2500000000 : ℝ)] ![(43477819714319/100000000000000 : ℝ), (21304782208031/50000000000000 : ℝ), (13912615857429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534497251/1000000000 : ℝ)|^8261 ≤ (43477819714319/100000000000000 : ℝ)^6213
        have hw : |(534497251/1000000000 : ℝ)|=(534497251/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264494611/10000000000 : ℝ)|^8261 ≤ (21304782208031/50000000000000 : ℝ)^6213
        have hw : |(5264494611/10000000000 : ℝ)|=(5264494611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-567163057/2500000000 : ℝ)|^8261 ≤ (13912615857429/100000000000000 : ℝ)^6213
        have hw : |(-567163057/2500000000 : ℝ)|=(567163057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s8_3 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187602477/5000000000 : ℝ)*x 0 + (4249813087/10000000000 : ℝ)*x 1 + (2252172729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187602477/5000000000 : ℝ)^8261 ≤ (33316563302237/100000000000000 : ℝ)^6213 := by
    have hnat : (2187602477 : ℕ)^8261*100000000000000^6213 ≤ 33316563302237^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187602477 5000000000 33316563302237 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4249813087/10000000000 : ℝ)^8261 ≤ (32053012249439/100000000000000 : ℝ)^6213 := by
    have hnat : (4249813087 : ℕ)^8261*100000000000000^6213 ≤ 32053012249439^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249813087 10000000000 32053012249439 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252172729/5000000000 : ℝ)^8261 ≤ (270550190833/781250000000 : ℝ)^6213 := by
    have hnat : (2252172729 : ℕ)^8261*781250000000^6213 ≤ 270550190833^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252172729 5000000000 270550190833 781250000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187602477/5000000000 : ℝ), (4249813087/10000000000 : ℝ), (2252172729/5000000000 : ℝ)] ![(33316563302237/100000000000000 : ℝ), (32053012249439/100000000000000 : ℝ), (270550190833/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187602477/5000000000 : ℝ)|^8261 ≤ (33316563302237/100000000000000 : ℝ)^6213
        have hw : |(2187602477/5000000000 : ℝ)|=(2187602477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4249813087/10000000000 : ℝ)|^8261 ≤ (32053012249439/100000000000000 : ℝ)^6213
        have hw : |(4249813087/10000000000 : ℝ)|=(4249813087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2252172729/5000000000 : ℝ)|^8261 ≤ (270550190833/781250000000 : ℝ)^6213
        have hw : |(2252172729/5000000000 : ℝ)|=(2252172729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s8_4 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-220279073/1000000000 : ℝ)*x 0 + (5264819833/10000000000 : ℝ)*x 1 + (2696994683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220279073/1000000000 : ℝ)^8261 ≤ (13378165912933/100000000000000 : ℝ)^6213 := by
    have hnat : (220279073 : ℕ)^8261*100000000000000^6213 ≤ 13378165912933^6213*1000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220279073 1000000000 13378165912933 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264819833/10000000000 : ℝ)^8261 ≤ (42613064399713/100000000000000 : ℝ)^6213 := by
    have hnat : (5264819833 : ℕ)^8261*100000000000000^6213 ≤ 42613064399713^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264819833 10000000000 42613064399713 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696994683/5000000000 : ℝ)^8261 ≤ (1760350786839/4000000000000 : ℝ)^6213 := by
    have hnat : (2696994683 : ℕ)^8261*4000000000000^6213 ≤ 1760350786839^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696994683 5000000000 1760350786839 4000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-220279073/1000000000 : ℝ), (5264819833/10000000000 : ℝ), (2696994683/5000000000 : ℝ)] ![(13378165912933/100000000000000 : ℝ), (42613064399713/100000000000000 : ℝ), (1760350786839/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-220279073/1000000000 : ℝ)|^8261 ≤ (13378165912933/100000000000000 : ℝ)^6213
        have hw : |(-220279073/1000000000 : ℝ)|=(220279073/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264819833/10000000000 : ℝ)|^8261 ≤ (42613064399713/100000000000000 : ℝ)^6213
        have hw : |(5264819833/10000000000 : ℝ)|=(5264819833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696994683/5000000000 : ℝ)|^8261 ≤ (1760350786839/4000000000000 : ℝ)^6213
        have hw : |(2696994683/5000000000 : ℝ)|=(2696994683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s8_5 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328066973/2500000000 : ℝ)*x 0 + (-1069578721/5000000000 : ℝ)*x 1 + (5393989413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328066973/2500000000 : ℝ)^8261 ≤ (43124454465949/100000000000000 : ℝ)^6213 := by
    have hnat : (1328066973 : ℕ)^8261*100000000000000^6213 ≤ 43124454465949^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328066973 2500000000 43124454465949 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1069578721/5000000000 : ℝ)^8261 ≤ (6433387665547/50000000000000 : ℝ)^6213 := by
    have hnat : (1069578721 : ℕ)^8261*50000000000000^6213 ≤ 6433387665547^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069578721 5000000000 6433387665547 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393989413/10000000000 : ℝ)^8261 ≤ (44008770180843/100000000000000 : ℝ)^6213 := by
    have hnat : (5393989413 : ℕ)^8261*100000000000000^6213 ≤ 44008770180843^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393989413 10000000000 44008770180843 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328066973/2500000000 : ℝ), (-1069578721/5000000000 : ℝ), (5393989413/10000000000 : ℝ)] ![(43124454465949/100000000000000 : ℝ), (6433387665547/50000000000000 : ℝ), (44008770180843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328066973/2500000000 : ℝ)|^8261 ≤ (43124454465949/100000000000000 : ℝ)^6213
        have hw : |(1328066973/2500000000 : ℝ)|=(1328066973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1069578721/5000000000 : ℝ)|^8261 ≤ (6433387665547/50000000000000 : ℝ)^6213
        have hw : |(-1069578721/5000000000 : ℝ)|=(1069578721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393989413/10000000000 : ℝ)|^8261 ≤ (44008770180843/100000000000000 : ℝ)^6213
        have hw : |(5393989413/10000000000 : ℝ)|=(5393989413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s8_6 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664033483/1250000000 : ℝ)*x 0 + (1348497367/2500000000 : ℝ)*x 1 + (-1069578703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664033483/1250000000 : ℝ)^8261 ≤ (21562227081861/50000000000000 : ℝ)^6213 := by
    have hnat : (664033483 : ℕ)^8261*50000000000000^6213 ≤ 21562227081861^6213*1250000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664033483 1250000000 21562227081861 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348497367/2500000000 : ℝ)^8261 ≤ (22004385388749/50000000000000 : ℝ)^6213 := by
    have hnat : (1348497367 : ℕ)^8261*50000000000000^6213 ≤ 22004385388749^6213*2500000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348497367 2500000000 22004385388749 50000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1069578703/5000000000 : ℝ)^8261 ≤ (12866775043181/100000000000000 : ℝ)^6213 := by
    have hnat : (1069578703 : ℕ)^8261*100000000000000^6213 ≤ 12866775043181^6213*5000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069578703 5000000000 12866775043181 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664033483/1250000000 : ℝ), (1348497367/2500000000 : ℝ), (-1069578703/5000000000 : ℝ)] ![(21562227081861/50000000000000 : ℝ), (22004385388749/50000000000000 : ℝ), (12866775043181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664033483/1250000000 : ℝ)|^8261 ≤ (21562227081861/50000000000000 : ℝ)^6213
        have hw : |(664033483/1250000000 : ℝ)|=(664033483/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348497367/2500000000 : ℝ)|^8261 ≤ (22004385388749/50000000000000 : ℝ)^6213
        have hw : |(1348497367/2500000000 : ℝ)|=(1348497367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1069578703/5000000000 : ℝ)|^8261 ≤ (12866775043181/100000000000000 : ℝ)^6213
        have hw : |(-1069578703/5000000000 : ℝ)|=(1069578703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1068_s8_7 (p : ℝ) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (437521489/1000000000 : ℝ)*x 0 + (4503707927/10000000000 : ℝ)*x 1 + (4250452897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437521489/1000000000 : ℝ)^8261 ≤ (33316663903819/100000000000000 : ℝ)^6213 := by
    have hnat : (437521489 : ℕ)^8261*100000000000000^6213 ≤ 33316663903819^6213*1000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437521489 1000000000 33316663903819 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503707927/10000000000 : ℝ)^8261 ≤ (34623907413921/100000000000000 : ℝ)^6213 := by
    have hnat : (4503707927 : ℕ)^8261*100000000000000^6213 ≤ 34623907413921^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503707927 10000000000 34623907413921 100000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4250452897/10000000000 : ℝ)^8261 ≤ (8014857164789/25000000000000 : ℝ)^6213 := by
    have hnat : (4250452897 : ℕ)^8261*25000000000000^6213 ≤ 8014857164789^6213*10000000000^8261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250452897 10000000000 8014857164789 25000000000000 8261 6213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8261/2048 : ℝ)) 8261 6213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437521489/1000000000 : ℝ), (4503707927/10000000000 : ℝ), (4250452897/10000000000 : ℝ)] ![(33316663903819/100000000000000 : ℝ), (34623907413921/100000000000000 : ℝ), (8014857164789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437521489/1000000000 : ℝ)|^8261 ≤ (33316663903819/100000000000000 : ℝ)^6213
        have hw : |(437521489/1000000000 : ℝ)|=(437521489/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503707927/10000000000 : ℝ)|^8261 ≤ (34623907413921/100000000000000 : ℝ)^6213
        have hw : |(4503707927/10000000000 : ℝ)|=(4503707927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4250452897/10000000000 : ℝ)|^8261 ≤ (8014857164789/25000000000000 : ℝ)^6213
        have hw : |(4250452897/10000000000 : ℝ)|=(4250452897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1068_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7003/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2813/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5627/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3501/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7003/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2813/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7003/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2813/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7003/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2813/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7003/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2813/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7003/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2813/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7003/50000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (2813/25000 : ℝ) ^ (2065/512 : ℝ) ≤ (14907909782340403/100000000000000000000 : ℝ) := by
    have hpowers : (2813/25000 : ℝ)^2065 ≤ (14907909782340403/100000000000000000000 : ℝ)^512 := by
      have hnat : (2813 : ℕ)^2065*100000000000000000000^512 ≤ 14907909782340403^512*25000^2065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2813 25000 14907909782340403 100000000000000000000 2065 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2813/25000 : ℝ)) (X := (14907909782340403/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7003/50000 : ℝ) ^ (2065/512 : ℝ) ≤ (36050513000495279/100000000000000000000 : ℝ) := by
    have hpowers : (7003/50000 : ℝ)^2065 ≤ (36050513000495279/100000000000000000000 : ℝ)^512 := by
      have hnat : (7003 : ℕ)^2065*100000000000000000000^512 ≤ 36050513000495279^512*50000^2065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7003 50000 36050513000495279 100000000000000000000 2065 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7003/50000 : ℝ)) (X := (36050513000495279/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014907909782340403/50000000000000000000 : ℝ) ≤ (2500184794048229/2500000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (50014907909782340403/50000000000000000000 : ℝ)^512 ≤ (2500184794048229/2500000000000000 : ℝ)^2065 := by
      have hnat : (50014907909782340403 : ℕ)^512*2500000000000000^2065 ≤ 2500184794048229^2065*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014907909782340403 50000000000000000000 2500184794048229 2500000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500184794048229/2500000000000000 : ℝ)) (X := (50014907909782340403/50000000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025479211391417841/50000000000000000000 : ℝ) ≤ (10001263230725889/10000000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (50025479211391417841/50000000000000000000 : ℝ)^512 ≤ (10001263230725889/10000000000000000 : ℝ)^2065 := by
      have hnat : (50025479211391417841 : ℕ)^512*10000000000000000^2065 ≤ 10001263230725889^2065*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025479211391417841 50000000000000000000 10001263230725889 10000000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001263230725889/10000000000000000 : ℝ)) (X := (50025479211391417841/50000000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036050513000495279/50000000000000000000 : ℝ) ≤ (5000893642629431/5000000000000000 : ℝ) ^ (2065/512 : ℝ) := by
    have hpowers : (50036050513000495279/50000000000000000000 : ℝ)^512 ≤ (5000893642629431/5000000000000000 : ℝ)^2065 := by
      have hnat : (50036050513000495279 : ℕ)^512*5000000000000000^2065 ≤ 5000893642629431^2065*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036050513000495279 50000000000000000000 5000893642629431 5000000000000000 512 2065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000893642629431/5000000000000000 : ℝ)) (X := (50036050513000495279/50000000000000000000 : ℝ)) (by norm_num) 2065 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14907909782340403/100000000000000000000 : ℝ) ≤ ((860320074000789571/860625000000000000 : ℝ)+2*(524054532973/275400000000000 : ℝ)*(2813/25000 : ℝ))^(2065/512 : ℝ) := by
    rw [show (860320074000789571/860625000000000000 : ℝ)+2*(524054532973/275400000000000 : ℝ)*(2813/25000 : ℝ)=(2500184794048229/2500000000000000 : ℝ) by norm_num, show 1+2*(14907909782340403/100000000000000000000 : ℝ)=(50014907909782340403/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36050513000495279/100000000000000000000 : ℝ)+(14907909782340403/100000000000000000000 : ℝ) ≤ ((860320074000789571/860625000000000000 : ℝ)+(524054532973/275400000000000 : ℝ)*((7003/50000 : ℝ)+(2813/25000 : ℝ)))^(2065/512 : ℝ) := by
    rw [show (860320074000789571/860625000000000000 : ℝ)+(524054532973/275400000000000 : ℝ)*((7003/50000 : ℝ)+(2813/25000 : ℝ))=(10001263230725889/10000000000000000 : ℝ) by norm_num, show 1+(36050513000495279/100000000000000000000 : ℝ)+(14907909782340403/100000000000000000000 : ℝ)=(50025479211391417841/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36050513000495279/100000000000000000000 : ℝ) ≤ ((860320074000789571/860625000000000000 : ℝ)+2*(524054532973/275400000000000 : ℝ)*(7003/50000 : ℝ))^(2065/512 : ℝ) := by
    rw [show (860320074000789571/860625000000000000 : ℝ)+2*(524054532973/275400000000000 : ℝ)*(7003/50000 : ℝ)=(5000893642629431/5000000000000000 : ℝ) by norm_num, show 1+2*(36050513000495279/100000000000000000000 : ℝ)=(50036050513000495279/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (860320074000789571/860625000000000000 : ℝ)*(X 1 0+X 2 0)+(524054532973/275400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (2813/25000 : ℝ)) (hi := (7003/50000 : ℝ)) (c := (860320074000789571/860625000000000000 : ℝ)) (alpha := (524054532973/275400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (860320074000789571/860625000000000000 : ℝ)*(X 0 1+X 2 1)+(524054532973/275400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (2813/25000 : ℝ)) (hi := (7003/50000 : ℝ)) (c := (860320074000789571/860625000000000000 : ℝ)) (alpha := (524054532973/275400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (860320074000789571/860625000000000000 : ℝ)*(X 0 2+X 1 2)+(524054532973/275400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2065/512 : ℝ)) (lo := (2813/25000 : ℝ)) (hi := (7003/50000 : ℝ)) (c := (860320074000789571/860625000000000000 : ℝ)) (alpha := (524054532973/275400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-440557139/2000000000 : ℝ)*X 0 0+(5394315741/10000000000 : ℝ)*X 0 1+(5264494611/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167030391/312500000 : ℝ)*X 1 0+(-90746089/400000000 : ℝ)*X 1 1+(5264494611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534497251/1000000000 : ℝ)*X 2 0+(5264494611/10000000000 : ℝ)*X 2 1+(-567163057/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187602477/5000000000 : ℝ)*X 0 0+(4249813087/10000000000 : ℝ)*X 0 1+(2252172729/5000000000 : ℝ)*X 0 2+(2187602477/5000000000 : ℝ)*X 1 0+(4249813087/10000000000 : ℝ)*X 1 1+(2252172729/5000000000 : ℝ)*X 1 2+(2187602477/5000000000 : ℝ)*X 2 0+(4249813087/10000000000 : ℝ)*X 2 1+(2252172729/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-220279073/1000000000 : ℝ)*X 0 0+(5264819833/10000000000 : ℝ)*X 0 1+(2696994683/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328066973/2500000000 : ℝ)*X 1 0+(-1069578721/5000000000 : ℝ)*X 1 1+(5393989413/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664033483/1250000000 : ℝ)*X 2 0+(1348497367/2500000000 : ℝ)*X 2 1+(-1069578703/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((437521489/1000000000 : ℝ)*X 0 0+(4503707927/10000000000 : ℝ)*X 0 1+(4250452897/10000000000 : ℝ)*X 0 2+(437521489/1000000000 : ℝ)*X 1 0+(4503707927/10000000000 : ℝ)*X 1 1+(4250452897/10000000000 : ℝ)*X 1 2+(437521489/1000000000 : ℝ)*X 2 0+(4503707927/10000000000 : ℝ)*X 2 1+(4250452897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1068_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64906572606074435657242667/7171875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9172519/500000000000 : ℝ)*(base19) + (214404899/12500000000000 : ℝ)*(base23) + (15551501/25000000000000 : ℝ)*(lower2) + (115510781/50000000000000 : ℝ)*(upper3) + (13933343/10000000000000 : ℝ)*(upper5) + (1453979087136683/25000000000000 : ℝ)*(major0) + (1453979087136683/25000000000000 : ℝ)*(major1) + (1453979087136683/25000000000000 : ℝ)*(major2) + (7702958009796217/100000000000000 : ℝ)*(sp0) + (1925751355300521/25000000000000 : ℝ)*(sp1) + (1925751385116673/25000000000000 : ℝ)*(sp2) + (1964398980254621/50000000000000 : ℝ)*(sp3) + (12311477417/25000000000000 : ℝ)*(sp4) + (27179206533/100000000000000 : ℝ)*(sp7) + (157153005588631/4000000000000 : ℝ)*(f.failure) + (1925751813926471/25000000000000 : ℝ)*(f.sum) + (6886941488837/6885000000000000000000000000 : ℝ)*base66 + (24571139902233103/3585937500000000000000000000000 : ℝ)*base67 + (4937854297999841/448242187500000000000000000000 : ℝ)*base69 + (22114622607389353/3585937500000000000000000000000 : ℝ)*base71 + (5027327510293/6885000000000000000000000000 : ℝ)*base73 + (89285172794700581/7171875000000000000000000000000 : ℝ)*base75 + (20918633876076853/3585937500000000000000000000000 : ℝ)*base77 + (173353420381200581/7171875000000000000000000000000 : ℝ)*base79 + (1294540876367/6885000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (5443/400000000000000000000 : ℝ)*base90 + (5443/400000000000000000000 : ℝ)*base92 + (5443/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28984477802955561582037/5312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (180109247/20000000000000 : ℝ)*(base19) + (512029157/50000000000000 : ℝ)*(base23) + (8863507/6250000000000 : ℝ)*(upper3) + (61134501/100000000000000 : ℝ)*(lower4) + (8970143/12500000000000 : ℝ)*(upper5) + (116903484812787/2000000000000 : ℝ)*(major0) + (116903484812787/2000000000000 : ℝ)*(major1) + (116903484812787/2000000000000 : ℝ)*(major2) + (1493123171/6250000000000 : ℝ)*(sp1) + (31887391969/100000000000000 : ℝ)*(sp2) + (967719822504471/12500000000000 : ℝ)*(sp4) + (3870866894759399/50000000000000 : ℝ)*(sp5) + (7741725668585487/100000000000000 : ℝ)*(sp6) + (1974294859689763/50000000000000 : ℝ)*(sp7) + (1974294859689763/50000000000000 : ℝ)*(f.failure) + (967719822504471/12500000000000 : ℝ)*(f.sum) + (252816286217/91800000000000000000000000 : ℝ)*base65 + (452434799975191/23906250000000000000000000000 : ℝ)*base67 + (4566532308533/11953125000000000000000000000 : ℝ)*base69 + (553433599129757/47812500000000000000000000000 : ℝ)*base71 + (4881777698311/459000000000000000000000000 : ℝ)*base73 + (24982485092743/47812500000000000000000000000 : ℝ)*base76 + (188827400435191/23906250000000000000000000000 : ℝ)*base77 + (654043059063611/95625000000000000000000000000 : ℝ)*base80 + (901310015473/459000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/50000000000000 : ℝ)*base87 + (67141439/5000000000000000000000 : ℝ)*base90 + (67141439/5000000000000000000000 : ℝ)*base92 + (67141439/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1068_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7003/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2813/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5627/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3501/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1068_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1068_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5601/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5627/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3501/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1068_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1068_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1068_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2065/512 : ℝ) ≤ p) (hpb : p ≤ (8261/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148031947/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5601/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5627/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3501/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1068_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

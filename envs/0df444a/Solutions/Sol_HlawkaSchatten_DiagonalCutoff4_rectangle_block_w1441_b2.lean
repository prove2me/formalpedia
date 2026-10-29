-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1441_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:56:47.537317+00:00
-- url     : https://prove2.me/submissions/4c2b90a0-2170-42f5-8392-b7071c7266ea

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
theorem support_rectangle_w1441_s6_0 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1961433579/10000000000 : ℝ)*x 0 + (108152119/200000000 : ℝ)*x 1 + (2623582059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1961433579/10000000000 : ℝ)^4401 ≤ (5984561302153/50000000000000 : ℝ)^3377 := by
    have hnat : (1961433579 : ℕ)^4401*50000000000000^3377 ≤ 5984561302153^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961433579 10000000000 5984561302153 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108152119/200000000 : ℝ)^4401 ≤ (44879164606287/100000000000000 : ℝ)^3377 := by
    have hnat : (108152119 : ℕ)^4401*100000000000000^3377 ≤ 44879164606287^3377*200000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108152119 200000000 44879164606287 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623582059/5000000000 : ℝ)^4401 ≤ (2157585639363/5000000000000 : ℝ)^3377 := by
    have hnat : (2623582059 : ℕ)^4401*5000000000000^3377 ≤ 2157585639363^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623582059 5000000000 2157585639363 5000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1961433579/10000000000 : ℝ), (108152119/200000000 : ℝ), (2623582059/5000000000 : ℝ)] ![(5984561302153/50000000000000 : ℝ), (44879164606287/100000000000000 : ℝ), (2157585639363/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1961433579/10000000000 : ℝ)|^4401 ≤ (5984561302153/50000000000000 : ℝ)^3377
        have hw : |(-1961433579/10000000000 : ℝ)|=(1961433579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108152119/200000000 : ℝ)|^4401 ≤ (44879164606287/100000000000000 : ℝ)^3377
        have hw : |(108152119/200000000 : ℝ)|=(108152119/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623582059/5000000000 : ℝ)|^4401 ≤ (2157585639363/5000000000000 : ℝ)^3377
        have hw : |(2623582059/5000000000 : ℝ)|=(2623582059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s6_1 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106941473/200000000 : ℝ)*x 0 + (-1021554487/5000000000 : ℝ)*x 1 + (5247164119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106941473/200000000 : ℝ)^4401 ≤ (44225571306261/100000000000000 : ℝ)^3377 := by
    have hnat : (106941473 : ℕ)^4401*100000000000000^3377 ≤ 44225571306261^3377*200000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106941473 200000000 44225571306261 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1021554487/5000000000 : ℝ)^4401 ≤ (6311357941939/50000000000000 : ℝ)^3377 := by
    have hnat : (1021554487 : ℕ)^4401*50000000000000^3377 ≤ 6311357941939^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021554487 5000000000 6311357941939 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247164119/10000000000 : ℝ)^4401 ≤ (43151712797977/100000000000000 : ℝ)^3377 := by
    have hnat : (5247164119 : ℕ)^4401*100000000000000^3377 ≤ 43151712797977^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247164119 10000000000 43151712797977 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106941473/200000000 : ℝ), (-1021554487/5000000000 : ℝ), (5247164119/10000000000 : ℝ)] ![(44225571306261/100000000000000 : ℝ), (6311357941939/50000000000000 : ℝ), (43151712797977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106941473/200000000 : ℝ)|^4401 ≤ (44225571306261/100000000000000 : ℝ)^3377
        have hw : |(106941473/200000000 : ℝ)|=(106941473/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1021554487/5000000000 : ℝ)|^4401 ≤ (6311357941939/50000000000000 : ℝ)^3377
        have hw : |(-1021554487/5000000000 : ℝ)|=(1021554487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247164119/10000000000 : ℝ)|^4401 ≤ (43151712797977/100000000000000 : ℝ)^3377
        have hw : |(5247164119/10000000000 : ℝ)|=(5247164119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s6_2 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347073649/10000000000 : ℝ)*x 0 + (5247164119/10000000000 : ℝ)*x 1 + (-127694311/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347073649/10000000000 : ℝ)^4401 ≤ (22112785647741/50000000000000 : ℝ)^3377 := by
    have hnat : (5347073649 : ℕ)^4401*50000000000000^3377 ≤ 22112785647741^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347073649 10000000000 22112785647741 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247164119/10000000000 : ℝ)^4401 ≤ (43151712797977/100000000000000 : ℝ)^3377 := by
    have hnat : (5247164119 : ℕ)^4401*100000000000000^3377 ≤ 43151712797977^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247164119 10000000000 43151712797977 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127694311/625000000 : ℝ)^4401 ≤ (12622715899981/100000000000000 : ℝ)^3377 := by
    have hnat : (127694311 : ℕ)^4401*100000000000000^3377 ≤ 12622715899981^3377*625000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127694311 625000000 12622715899981 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347073649/10000000000 : ℝ), (5247164119/10000000000 : ℝ), (-127694311/625000000 : ℝ)] ![(22112785647741/50000000000000 : ℝ), (43151712797977/100000000000000 : ℝ), (12622715899981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347073649/10000000000 : ℝ)|^4401 ≤ (22112785647741/50000000000000 : ℝ)^3377
        have hw : |(5347073649/10000000000 : ℝ)|=(5347073649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247164119/10000000000 : ℝ)|^4401 ≤ (43151712797977/100000000000000 : ℝ)^3377
        have hw : |(5247164119/10000000000 : ℝ)|=(5247164119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-127694311/625000000 : ℝ)|^4401 ≤ (12622715899981/100000000000000 : ℝ)^3377
        have hw : |(-127694311/625000000 : ℝ)|=(127694311/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s6_3 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4301381407/10000000000 : ℝ)*x 0 + (2065116899/5000000000 : ℝ)*x 1 + (4478849747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4301381407/10000000000 : ℝ)^4401 ≤ (33304868999707/100000000000000 : ℝ)^3377 := by
    have hnat : (4301381407 : ℕ)^4401*100000000000000^3377 ≤ 33304868999707^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301381407 10000000000 33304868999707 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065116899/5000000000 : ℝ)^4401 ≤ (15794195386849/50000000000000 : ℝ)^3377 := by
    have hnat : (2065116899 : ℕ)^4401*50000000000000^3377 ≤ 15794195386849^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065116899 5000000000 15794195386849 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4478849747/10000000000 : ℝ)^4401 ≤ (280853921681/800000000000 : ℝ)^3377 := by
    have hnat : (4478849747 : ℕ)^4401*800000000000^3377 ≤ 280853921681^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478849747 10000000000 280853921681 800000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4301381407/10000000000 : ℝ), (2065116899/5000000000 : ℝ), (4478849747/10000000000 : ℝ)] ![(33304868999707/100000000000000 : ℝ), (15794195386849/50000000000000 : ℝ), (280853921681/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4301381407/10000000000 : ℝ)|^4401 ≤ (33304868999707/100000000000000 : ℝ)^3377
        have hw : |(4301381407/10000000000 : ℝ)|=(4301381407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2065116899/5000000000 : ℝ)|^4401 ≤ (15794195386849/50000000000000 : ℝ)^3377
        have hw : |(2065116899/5000000000 : ℝ)|=(2065116899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4478849747/10000000000 : ℝ)|^4401 ≤ (280853921681/800000000000 : ℝ)^3377
        have hw : |(4478849747/10000000000 : ℝ)|=(4478849747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s6_4 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1961444747/10000000000 : ℝ)*x 0 + (655967957/1250000000 : ℝ)*x 1 + (675877931/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1961444747/10000000000 : ℝ)^4401 ≤ (2393842283799/20000000000000 : ℝ)^3377 := by
    have hnat : (1961444747 : ℕ)^4401*20000000000000^3377 ≤ 2393842283799^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961444747 10000000000 2393842283799 20000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655967957/1250000000 : ℝ)^4401 ≤ (43157924092731/100000000000000 : ℝ)^3377 := by
    have hnat : (655967957 : ℕ)^4401*100000000000000^3377 ≤ 43157924092731^3377*1250000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655967957 1250000000 43157924092731 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675877931/1250000000 : ℝ)^4401 ≤ (44872864463931/100000000000000 : ℝ)^3377 := by
    have hnat : (675877931 : ℕ)^4401*100000000000000^3377 ≤ 44872864463931^3377*1250000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675877931 1250000000 44872864463931 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1961444747/10000000000 : ℝ), (655967957/1250000000 : ℝ), (675877931/1250000000 : ℝ)] ![(2393842283799/20000000000000 : ℝ), (43157924092731/100000000000000 : ℝ), (44872864463931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1961444747/10000000000 : ℝ)|^4401 ≤ (2393842283799/20000000000000 : ℝ)^3377
        have hw : |(-1961444747/10000000000 : ℝ)|=(1961444747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655967957/1250000000 : ℝ)|^4401 ≤ (43157924092731/100000000000000 : ℝ)^3377
        have hw : |(655967957/1250000000 : ℝ)|=(655967957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675877931/1250000000 : ℝ)|^4401 ≤ (44872864463931/100000000000000 : ℝ)^3377
        have hw : |(675877931/1250000000 : ℝ)|=(675877931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s6_5 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165791073/312500000 : ℝ)*x 0 + (-376649919/2000000000 : ℝ)*x 1 + (5407023743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165791073/312500000 : ℝ)^4401 ≤ (43775982516101/100000000000000 : ℝ)^3377 := by
    have hnat : (165791073 : ℕ)^4401*100000000000000^3377 ≤ 43775982516101^3377*312500000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165791073 312500000 43775982516101 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (376649919/2000000000 : ℝ)^4401 ≤ (11351149809917/100000000000000 : ℝ)^3377 := by
    have hnat : (376649919 : ℕ)^4401*100000000000000^3377 ≤ 11351149809917^3377*2000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376649919 2000000000 11351149809917 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407023743/10000000000 : ℝ)^4401 ≤ (22436433827249/50000000000000 : ℝ)^3377 := by
    have hnat : (5407023743 : ℕ)^4401*50000000000000^3377 ≤ 22436433827249^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407023743 10000000000 22436433827249 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165791073/312500000 : ℝ), (-376649919/2000000000 : ℝ), (5407023743/10000000000 : ℝ)] ![(43775982516101/100000000000000 : ℝ), (11351149809917/100000000000000 : ℝ), (22436433827249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165791073/312500000 : ℝ)|^4401 ≤ (43775982516101/100000000000000 : ℝ)^3377
        have hw : |(165791073/312500000 : ℝ)|=(165791073/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-376649919/2000000000 : ℝ)|^4401 ≤ (11351149809917/100000000000000 : ℝ)^3377
        have hw : |(-376649919/2000000000 : ℝ)|=(376649919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407023743/10000000000 : ℝ)|^4401 ≤ (22436433827249/50000000000000 : ℝ)^3377
        have hw : |(5407023743/10000000000 : ℝ)|=(5407023743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s6_6 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305315133/10000000000 : ℝ)*x 0 + (135175579/250000000 : ℝ)*x 1 + (-1883249307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305315133/10000000000 : ℝ)^4401 ≤ (43775991086547/100000000000000 : ℝ)^3377 := by
    have hnat : (5305315133 : ℕ)^4401*100000000000000^3377 ≤ 43775991086547^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305315133 10000000000 43775991086547 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135175579/250000000 : ℝ)^4401 ≤ (2804553834317/6250000000000 : ℝ)^3377 := by
    have hnat : (135175579 : ℕ)^4401*6250000000000^3377 ≤ 2804553834317^3377*250000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135175579 250000000 2804553834317 6250000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1883249307/10000000000 : ℝ)^4401 ≤ (5675573773823/50000000000000 : ℝ)^3377 := by
    have hnat : (1883249307 : ℕ)^4401*50000000000000^3377 ≤ 5675573773823^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1883249307 10000000000 5675573773823 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305315133/10000000000 : ℝ), (135175579/250000000 : ℝ), (-1883249307/10000000000 : ℝ)] ![(43775991086547/100000000000000 : ℝ), (2804553834317/6250000000000 : ℝ), (5675573773823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305315133/10000000000 : ℝ)|^4401 ≤ (43775991086547/100000000000000 : ℝ)^3377
        have hw : |(5305315133/10000000000 : ℝ)|=(5305315133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135175579/250000000 : ℝ)|^4401 ≤ (2804553834317/6250000000000 : ℝ)^3377
        have hw : |(135175579/250000000 : ℝ)|=(135175579/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1883249307/10000000000 : ℝ)|^4401 ≤ (5675573773823/50000000000000 : ℝ)^3377
        have hw : |(-1883249307/10000000000 : ℝ)|=(1883249307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s6_7 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268837837/625000000 : ℝ)*x 0 + (4477591437/10000000000 : ℝ)*x 1 + (4131499013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268837837/625000000 : ℝ)^4401 ≤ (33305111024677/100000000000000 : ℝ)^3377 := by
    have hnat : (268837837 : ℕ)^4401*100000000000000^3377 ≤ 33305111024677^3377*625000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268837837 625000000 33305111024677 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4477591437/10000000000 : ℝ)^4401 ≤ (7018777388989/20000000000000 : ℝ)^3377 := by
    have hnat : (4477591437 : ℕ)^4401*20000000000000^3377 ≤ 7018777388989^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477591437 10000000000 7018777388989 20000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4131499013/10000000000 : ℝ)^4401 ≤ (6320200402063/20000000000000 : ℝ)^3377 := by
    have hnat : (4131499013 : ℕ)^4401*20000000000000^3377 ≤ 6320200402063^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131499013 10000000000 6320200402063 20000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268837837/625000000 : ℝ), (4477591437/10000000000 : ℝ), (4131499013/10000000000 : ℝ)] ![(33305111024677/100000000000000 : ℝ), (7018777388989/20000000000000 : ℝ), (6320200402063/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268837837/625000000 : ℝ)|^4401 ≤ (33305111024677/100000000000000 : ℝ)^3377
        have hw : |(268837837/625000000 : ℝ)|=(268837837/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4477591437/10000000000 : ℝ)|^4401 ≤ (7018777388989/20000000000000 : ℝ)^3377
        have hw : |(4477591437/10000000000 : ℝ)|=(4477591437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4131499013/10000000000 : ℝ)|^4401 ≤ (6320200402063/20000000000000 : ℝ)^3377
        have hw : |(4131499013/10000000000 : ℝ)|=(4131499013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1441_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2841/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14763/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11361/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11361/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11361/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11361/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11361/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (11361/100000 : ℝ) ^ (275/64 : ℝ) ≤ (13975360297853/160000000000000000 : ℝ) := by
    have hpowers : (11361/100000 : ℝ)^275 ≤ (13975360297853/160000000000000000 : ℝ)^64 := by
      have hnat : (11361 : ℕ)^275*160000000000000000^64 ≤ 13975360297853^64*100000^275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11361 100000 13975360297853 160000000000000000 275 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11361/100000 : ℝ)) (X := (13975360297853/160000000000000000 : ℝ)) (by norm_num) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hpowhi : (14767/100000 : ℝ) ^ (275/64 : ℝ) ≤ (13474813033745431/50000000000000000000 : ℝ) := by
    have hpowers : (14767/100000 : ℝ)^275 ≤ (13474813033745431/50000000000000000000 : ℝ)^64 := by
      have hnat : (14767 : ℕ)^275*50000000000000000000^64 ≤ 13474813033745431^64*100000^275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14767 100000 13474813033745431 50000000000000000000 275 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14767/100000 : ℝ)) (X := (13474813033745431/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (80013975360297853/80000000000000000 : ℝ) ≤ (10000406528692093/10000000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (80013975360297853/80000000000000000 : ℝ)^64 ≤ (10000406528692093/10000000000000000 : ℝ)^275 := by
      have hnat : (80013975360297853 : ℕ)^64*10000000000000000^275 ≤ 10000406528692093^275*80000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80013975360297853 80000000000000000 10000406528692093 10000000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000406528692093/10000000000000000 : ℝ)) (X := (80013975360297853/80000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035684226253648987/100000000000000000000 : ℝ) ≤ (10000830355600127/10000000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (100035684226253648987/100000000000000000000 : ℝ)^64 ≤ (10000830355600127/10000000000000000 : ℝ)^275 := by
      have hnat : (100035684226253648987 : ℕ)^64*10000000000000000^275 ≤ 10000830355600127^275*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035684226253648987 100000000000000000000 10000830355600127 10000000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000830355600127/10000000000000000 : ℝ)) (X := (100035684226253648987/100000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013474813033745431/25000000000000000000 : ℝ) ≤ (10001254182508161/10000000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (25013474813033745431/25000000000000000000 : ℝ)^64 ≤ (10001254182508161/10000000000000000 : ℝ)^275 := by
      have hnat : (25013474813033745431 : ℕ)^64*10000000000000000^275 ≤ 10001254182508161^275*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013474813033745431 25000000000000000000 10001254182508161 10000000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001254182508161/10000000000000000 : ℝ)) (X := (25013474813033745431/25000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13975360297853/160000000000000000 : ℝ) ≤ ((3405175444172092021/3406000000000000000 : ℝ)+2*(211913454017/170300000000000 : ℝ)*(11361/100000 : ℝ))^(275/64 : ℝ) := by
    rw [show (3405175444172092021/3406000000000000000 : ℝ)+2*(211913454017/170300000000000 : ℝ)*(11361/100000 : ℝ)=(10000406528692093/10000000000000000 : ℝ) by norm_num, show 1+2*(13975360297853/160000000000000000 : ℝ)=(80013975360297853/80000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13474813033745431/50000000000000000000 : ℝ)+(13975360297853/160000000000000000 : ℝ) ≤ ((3405175444172092021/3406000000000000000 : ℝ)+(211913454017/170300000000000 : ℝ)*((14767/100000 : ℝ)+(11361/100000 : ℝ)))^(275/64 : ℝ) := by
    rw [show (3405175444172092021/3406000000000000000 : ℝ)+(211913454017/170300000000000 : ℝ)*((14767/100000 : ℝ)+(11361/100000 : ℝ))=(10000830355600127/10000000000000000 : ℝ) by norm_num, show 1+(13474813033745431/50000000000000000000 : ℝ)+(13975360297853/160000000000000000 : ℝ)=(100035684226253648987/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13474813033745431/50000000000000000000 : ℝ) ≤ ((3405175444172092021/3406000000000000000 : ℝ)+2*(211913454017/170300000000000 : ℝ)*(14767/100000 : ℝ))^(275/64 : ℝ) := by
    rw [show (3405175444172092021/3406000000000000000 : ℝ)+2*(211913454017/170300000000000 : ℝ)*(14767/100000 : ℝ)=(10001254182508161/10000000000000000 : ℝ) by norm_num, show 1+2*(13474813033745431/50000000000000000000 : ℝ)=(25013474813033745431/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3405175444172092021/3406000000000000000 : ℝ)*(X 1 0+X 2 0)+(211913454017/170300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (11361/100000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (3405175444172092021/3406000000000000000 : ℝ)) (alpha := (211913454017/170300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3405175444172092021/3406000000000000000 : ℝ)*(X 0 1+X 2 1)+(211913454017/170300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (11361/100000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (3405175444172092021/3406000000000000000 : ℝ)) (alpha := (211913454017/170300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3405175444172092021/3406000000000000000 : ℝ)*(X 0 2+X 1 2)+(211913454017/170300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (11361/100000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (3405175444172092021/3406000000000000000 : ℝ)) (alpha := (211913454017/170300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1961433579/10000000000 : ℝ)*X 0 0+(108152119/200000000 : ℝ)*X 0 1+(2623582059/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((106941473/200000000 : ℝ)*X 1 0+(-1021554487/5000000000 : ℝ)*X 1 1+(5247164119/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347073649/10000000000 : ℝ)*X 2 0+(5247164119/10000000000 : ℝ)*X 2 1+(-127694311/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4301381407/10000000000 : ℝ)*X 0 0+(2065116899/5000000000 : ℝ)*X 0 1+(4478849747/10000000000 : ℝ)*X 0 2+(4301381407/10000000000 : ℝ)*X 1 0+(2065116899/5000000000 : ℝ)*X 1 1+(4478849747/10000000000 : ℝ)*X 1 2+(4301381407/10000000000 : ℝ)*X 2 0+(2065116899/5000000000 : ℝ)*X 2 1+(4478849747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1961444747/10000000000 : ℝ)*X 0 0+(655967957/1250000000 : ℝ)*X 0 1+(675877931/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165791073/312500000 : ℝ)*X 1 0+(-376649919/2000000000 : ℝ)*X 1 1+(5407023743/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305315133/10000000000 : ℝ)*X 2 0+(135175579/250000000 : ℝ)*X 2 1+(-1883249307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((268837837/625000000 : ℝ)*X 0 0+(4477591437/10000000000 : ℝ)*X 0 1+(4131499013/10000000000 : ℝ)*X 0 2+(268837837/625000000 : ℝ)*X 1 0+(4477591437/10000000000 : ℝ)*X 1 1+(4131499013/10000000000 : ℝ)*X 1 2+(268837837/625000000 : ℝ)*X 2 0+(4477591437/10000000000 : ℝ)*X 2 1+(4131499013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8084015685486007509183/851500000000000000000000000 : ℝ) := by norm_num
    linear_combination (858358857/50000000000000 : ℝ)*(base19) + (1598713681/100000000000000 : ℝ)*(base23) + (3123717/5000000000000 : ℝ)*(lower2) + (237350113/100000000000000 : ℝ)*(upper3) + (150125971/100000000000000 : ℝ)*(upper5) + (91013832630537/2000000000000 : ℝ)*(major0) + (91013832630537/2000000000000 : ℝ)*(major1) + (91013832630537/2000000000000 : ℝ)*(major2) + (1558206594149229/25000000000000 : ℝ)*(sp0) + (155821522294799/2500000000000 : ℝ)*(sp1) + (779107626224499/12500000000000 : ℝ)*(sp2) + (4482034782213/156250000000 : ℝ)*(sp3) + (18115956379/50000000000000 : ℝ)*(sp4) + (18077465933/100000000000000 : ℝ)*(sp7) + (717130084520563/25000000000000 : ℝ)*(f.failure) + (3116431304254837/50000000000000 : ℝ)*(f.sum) + (379363492483/425750000000000000000000000 : ℝ)*base65 + (10500856146322723/6812000000000000000000000000000 : ℝ)*base68 + (70020653775666723/6812000000000000000000000000000 : ℝ)*base70 + (25586809759286723/6812000000000000000000000000000 : ℝ)*base72 + (8083551948533/1703000000000000000000000000 : ℝ)*base74 + (44804641879117277/6812000000000000000000000000000 : ℝ)*base75 + (48724202816617277/6812000000000000000000000000000 : ℝ)*base77 + (40730849802477277/6812000000000000000000000000000 : ℝ)*base79 + (8807873502541/1703000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (15903569/1250000000000000000000 : ℝ)*base90 + (15903569/1250000000000000000000 : ℝ)*base92 + (15903569/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (79089994324736781002428953/17030000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (372904947/100000000000000 : ℝ)*(base19) + (390776547/25000000000000 : ℝ)*(base23) + (62304333/20000000000000 : ℝ)*(lower1) + (1263711/2500000000000 : ℝ)*(upper2) + (11240237/25000000000000 : ℝ)*(upper3) + (458382647134323/10000000000000 : ℝ)*(major0) + (458382647134323/10000000000000 : ℝ)*(major1) + (458382647134323/10000000000000 : ℝ)*(major2) + (19281013381/100000000000000 : ℝ)*(sp2) + (5052942691/100000000000000 : ℝ)*(sp3) + (784780745341369/12500000000000 : ℝ)*(sp4) + (1255649117965201/20000000000000 : ℝ)*(sp5) + (6278225118611383/100000000000000 : ℝ)*(sp6) + (288940177220757/10000000000000 : ℝ)*(sp7) + (1444703412575131/50000000000000 : ℝ)*(f.failure) + (784780745341369/12500000000000 : ℝ)*(f.sum) + (15221581781283/1703000000000000000000000000 : ℝ)*base65 + (671301093992156783/34060000000000000000000000000000 : ℝ)*base67 + (99799802786376783/34060000000000000000000000000000 : ℝ)*base69 + (383607093593936783/34060000000000000000000000000000 : ℝ)*base71 + (4600522553283/1703000000000000000000000000 : ℝ)*base73 + (212386010887236783/34060000000000000000000000000000 : ℝ)*base75 + (871845322730256783/34060000000000000000000000000000 : ℝ)*base77 + (675733454387736783/34060000000000000000000000000000 : ℝ)*base79 + (57116532117/425750000000000000000000000 : ℝ)*base82 + (3642953/2500000000000000000000 : ℝ)*base90 + (3642953/2500000000000000000000 : ℝ)*base92 + (3642953/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1441_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2841/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1441_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1441_s7_0 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1961438649/10000000000 : ℝ)*x 0 + (1351895053/2500000000 : ℝ)*x 1 + (655898291/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1961438649/10000000000 : ℝ)^4401 ≤ (11969162923993/100000000000000 : ℝ)^3377 := by
    have hnat : (1961438649 : ℕ)^4401*100000000000000^3377 ≤ 11969162923993^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961438649 10000000000 11969162923993 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351895053/2500000000 : ℝ)^4401 ≤ (22439443114269/50000000000000 : ℝ)^3377 := by
    have hnat : (1351895053 : ℕ)^4401*50000000000000^3377 ≤ 22439443114269^3377*2500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351895053 2500000000 22439443114269 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655898291/1250000000 : ℝ)^4401 ≤ (43151950823201/100000000000000 : ℝ)^3377 := by
    have hnat : (655898291 : ℕ)^4401*100000000000000^3377 ≤ 43151950823201^3377*1250000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655898291 1250000000 43151950823201 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1961438649/10000000000 : ℝ), (1351895053/2500000000 : ℝ), (655898291/1250000000 : ℝ)] ![(11969162923993/100000000000000 : ℝ), (22439443114269/50000000000000 : ℝ), (43151950823201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1961438649/10000000000 : ℝ)|^4401 ≤ (11969162923993/100000000000000 : ℝ)^3377
        have hw : |(-1961438649/10000000000 : ℝ)|=(1961438649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351895053/2500000000 : ℝ)|^4401 ≤ (22439443114269/50000000000000 : ℝ)^3377
        have hw : |(1351895053/2500000000 : ℝ)|=(1351895053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655898291/1250000000 : ℝ)|^4401 ≤ (43151950823201/100000000000000 : ℝ)^3377
        have hw : |(655898291/1250000000 : ℝ)|=(655898291/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s7_1 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069413321/2000000000 : ℝ)*x 0 + (-2043088607/10000000000 : ℝ)*x 1 + (1049437301/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069413321/2000000000 : ℝ)^4401 ≤ (353803962947/800000000000 : ℝ)^3377 := by
    have hnat : (1069413321 : ℕ)^4401*800000000000^3377 ≤ 353803962947^3377*2000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069413321 2000000000 353803962947 800000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2043088607/10000000000 : ℝ)^4401 ≤ (6311275948709/50000000000000 : ℝ)^3377 := by
    have hnat : (2043088607 : ℕ)^4401*50000000000000^3377 ≤ 6311275948709^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043088607 10000000000 6311275948709 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049437301/2000000000 : ℝ)^4401 ≤ (21575976360101/50000000000000 : ℝ)^3377 := by
    have hnat : (1049437301 : ℕ)^4401*50000000000000^3377 ≤ 21575976360101^3377*2000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049437301 2000000000 21575976360101 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069413321/2000000000 : ℝ), (-2043088607/10000000000 : ℝ), (1049437301/2000000000 : ℝ)] ![(353803962947/800000000000 : ℝ), (6311275948709/50000000000000 : ℝ), (21575976360101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069413321/2000000000 : ℝ)|^4401 ≤ (353803962947/800000000000 : ℝ)^3377
        have hw : |(1069413321/2000000000 : ℝ)|=(1069413321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2043088607/10000000000 : ℝ)|^4401 ≤ (6311275948709/50000000000000 : ℝ)^3377
        have hw : |(-2043088607/10000000000 : ℝ)|=(2043088607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049437301/2000000000 : ℝ)|^4401 ≤ (21575976360101/50000000000000 : ℝ)^3377
        have hw : |(1049437301/2000000000 : ℝ)|=(1049437301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s7_2 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668383309/1250000000 : ℝ)*x 0 + (5247186737/10000000000 : ℝ)*x 1 + (-510772119/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668383309/1250000000 : ℝ)^4401 ≤ (44225493934771/100000000000000 : ℝ)^3377 := by
    have hnat : (668383309 : ℕ)^4401*100000000000000^3377 ≤ 44225493934771^3377*1250000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668383309 1250000000 44225493934771 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247186737/10000000000 : ℝ)^4401 ≤ (21575977603333/50000000000000 : ℝ)^3377 := by
    have hnat : (5247186737 : ℕ)^4401*50000000000000^3377 ≤ 21575977603333^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247186737 10000000000 21575977603333 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (510772119/2500000000 : ℝ)^4401 ≤ (12622550842663/100000000000000 : ℝ)^3377 := by
    have hnat : (510772119 : ℕ)^4401*100000000000000^3377 ≤ 12622550842663^3377*2500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510772119 2500000000 12622550842663 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668383309/1250000000 : ℝ), (5247186737/10000000000 : ℝ), (-510772119/2500000000 : ℝ)] ![(44225493934771/100000000000000 : ℝ), (21575977603333/50000000000000 : ℝ), (12622550842663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668383309/1250000000 : ℝ)|^4401 ≤ (44225493934771/100000000000000 : ℝ)^3377
        have hw : |(668383309/1250000000 : ℝ)|=(668383309/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247186737/10000000000 : ℝ)|^4401 ≤ (21575977603333/50000000000000 : ℝ)^3377
        have hw : |(5247186737/10000000000 : ℝ)|=(5247186737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-510772119/2500000000 : ℝ)|^4401 ≤ (12622550842663/100000000000000 : ℝ)^3377
        have hw : |(-510772119/2500000000 : ℝ)|=(510772119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s7_3 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2150691449/5000000000 : ℝ)*x 0 + (2065143443/5000000000 : ℝ)*x 1 + (179151859/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150691449/5000000000 : ℝ)^4401 ≤ (333048840449/1000000000000 : ℝ)^3377 := by
    have hnat : (2150691449 : ℕ)^4401*1000000000000^3377 ≤ 333048840449^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150691449 5000000000 333048840449 1000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065143443/5000000000 : ℝ)^4401 ≤ (7897229978361/25000000000000 : ℝ)^3377 := by
    have hnat : (2065143443 : ℕ)^4401*25000000000000^3377 ≤ 7897229978361^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065143443 5000000000 7897229978361 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179151859/400000000 : ℝ)^4401 ≤ (8776549007543/25000000000000 : ℝ)^3377 := by
    have hnat : (179151859 : ℕ)^4401*25000000000000^3377 ≤ 8776549007543^3377*400000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179151859 400000000 8776549007543 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2150691449/5000000000 : ℝ), (2065143443/5000000000 : ℝ), (179151859/400000000 : ℝ)] ![(333048840449/1000000000000 : ℝ), (7897229978361/25000000000000 : ℝ), (8776549007543/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2150691449/5000000000 : ℝ)|^4401 ≤ (333048840449/1000000000000 : ℝ)^3377
        have hw : |(2150691449/5000000000 : ℝ)|=(2150691449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2065143443/5000000000 : ℝ)|^4401 ≤ (7897229978361/25000000000000 : ℝ)^3377
        have hw : |(2065143443/5000000000 : ℝ)|=(2065143443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(179151859/400000000 : ℝ)|^4401 ≤ (8776549007543/25000000000000 : ℝ)^3377
        have hw : |(179151859/400000000 : ℝ)|=(179151859/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s7_4 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1961449653/10000000000 : ℝ)*x 0 + (5247765593/10000000000 : ℝ)*x 1 + (2703499051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1961449653/10000000000 : ℝ)^4401 ≤ (5984625217261/50000000000000 : ℝ)^3377 := by
    have hnat : (1961449653 : ℕ)^4401*50000000000000^3377 ≤ 5984625217261^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961449653 10000000000 5984625217261 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247765593/10000000000 : ℝ)^4401 ≤ (43158159210663/100000000000000 : ℝ)^3377 := by
    have hnat : (5247765593 : ℕ)^4401*100000000000000^3377 ≤ 43158159210663^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247765593 10000000000 43158159210663 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703499051/5000000000 : ℝ)^4401 ≤ (22436295167469/50000000000000 : ℝ)^3377 := by
    have hnat : (2703499051 : ℕ)^4401*50000000000000^3377 ≤ 22436295167469^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703499051 5000000000 22436295167469 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1961449653/10000000000 : ℝ), (5247765593/10000000000 : ℝ), (2703499051/5000000000 : ℝ)] ![(5984625217261/50000000000000 : ℝ), (43158159210663/100000000000000 : ℝ), (22436295167469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1961449653/10000000000 : ℝ)|^4401 ≤ (5984625217261/50000000000000 : ℝ)^3377
        have hw : |(-1961449653/10000000000 : ℝ)|=(1961449653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247765593/10000000000 : ℝ)|^4401 ≤ (43158159210663/100000000000000 : ℝ)^3377
        have hw : |(5247765593/10000000000 : ℝ)|=(5247765593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703499051/5000000000 : ℝ)|^4401 ≤ (22436295167469/50000000000000 : ℝ)^3377
        have hw : |(2703499051/5000000000 : ℝ)|=(2703499051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s7_5 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4301408011/10000000000 : ℝ)*x 0 + (4477538277/10000000000 : ℝ)*x 1 + (826310167/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4301408011/10000000000 : ℝ)^4401 ≤ (16652568726097/50000000000000 : ℝ)^3377 := by
    have hnat : (4301408011 : ℕ)^4401*50000000000000^3377 ≤ 16652568726097^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301408011 10000000000 16652568726097 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4477538277/10000000000 : ℝ)^4401 ≤ (701866879107/2000000000000 : ℝ)^3377 := by
    have hnat : (4477538277 : ℕ)^4401*2000000000000^3377 ≤ 701866879107^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477538277 10000000000 701866879107 2000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (826310167/2000000000 : ℝ)^4401 ≤ (31601518579511/100000000000000 : ℝ)^3377 := by
    have hnat : (826310167 : ℕ)^4401*100000000000000^3377 ≤ 31601518579511^3377*2000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826310167 2000000000 31601518579511 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4301408011/10000000000 : ℝ), (4477538277/10000000000 : ℝ), (826310167/2000000000 : ℝ)] ![(16652568726097/50000000000000 : ℝ), (701866879107/2000000000000 : ℝ), (31601518579511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4301408011/10000000000 : ℝ)|^4401 ≤ (16652568726097/50000000000000 : ℝ)^3377
        have hw : |(4301408011/10000000000 : ℝ)|=(4301408011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4477538277/10000000000 : ℝ)|^4401 ≤ (701866879107/2000000000000 : ℝ)^3377
        have hw : |(4477538277/10000000000 : ℝ)|=(4477538277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(826310167/2000000000 : ℝ)|^4401 ≤ (31601518579511/100000000000000 : ℝ)^3377
        have hw : |(826310167/2000000000 : ℝ)|=(826310167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1441_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2841/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2273/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14763/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14763/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2841/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14763/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2841/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14763/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2841/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14763/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2841/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14763/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2841/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14763/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2841/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2841/25000 : ℝ) ^ (275/64 : ℝ) ≤ (8744515112353389/100000000000000000000 : ℝ) := by
    have hpowers : (2841/25000 : ℝ)^275 ≤ (8744515112353389/100000000000000000000 : ℝ)^64 := by
      have hnat : (2841 : ℕ)^275*100000000000000000000^64 ≤ 8744515112353389^64*25000^275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2841 25000 8744515112353389 100000000000000000000 275 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2841/25000 : ℝ)) (X := (8744515112353389/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hpowhi : (14763/100000 : ℝ) ^ (275/64 : ℝ) ≤ (2691827305640703/10000000000000000000 : ℝ) := by
    have hpowers : (14763/100000 : ℝ)^275 ≤ (2691827305640703/10000000000000000000 : ℝ)^64 := by
      have hnat : (14763 : ℕ)^275*10000000000000000000^64 ≤ 2691827305640703^64*100000^275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14763 100000 2691827305640703 10000000000000000000 275 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14763/100000 : ℝ)) (X := (2691827305640703/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008744515112353389/50000000000000000000 : ℝ) ≤ (2500101747531239/2500000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (50008744515112353389/50000000000000000000 : ℝ)^64 ≤ (2500101747531239/2500000000000000 : ℝ)^275 := by
      have hnat : (50008744515112353389 : ℕ)^64*2500000000000000^275 ≤ 2500101747531239^275*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008744515112353389 50000000000000000000 2500101747531239 2500000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500101747531239/2500000000000000 : ℝ)) (X := (50008744515112353389/50000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035662788168760419/100000000000000000000 : ℝ) ≤ (10000829856813943/10000000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (100035662788168760419/100000000000000000000 : ℝ)^64 ≤ (10000829856813943/10000000000000000 : ℝ)^275 := by
      have hnat : (100035662788168760419 : ℕ)^64*10000000000000000^275 ≤ 10000829856813943^275*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035662788168760419 100000000000000000000 10000829856813943 10000000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000829856813943/10000000000000000 : ℝ)) (X := (100035662788168760419/100000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002691827305640703/5000000000000000000 : ℝ) ≤ (1000125272350293/1000000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (5002691827305640703/5000000000000000000 : ℝ)^64 ≤ (1000125272350293/1000000000000000 : ℝ)^275 := by
      have hnat : (5002691827305640703 : ℕ)^64*1000000000000000^275 ≤ 1000125272350293^275*5000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002691827305640703 5000000000000000000 1000125272350293 1000000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000125272350293/1000000000000000 : ℝ)) (X := (5002691827305640703/5000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8744515112353389/100000000000000000000 : ℝ) ≤ ((2831814370443952409/2832500000000000000 : ℝ)+2*(422866688987/339900000000000 : ℝ)*(2841/25000 : ℝ))^(275/64 : ℝ) := by
    rw [show (2831814370443952409/2832500000000000000 : ℝ)+2*(422866688987/339900000000000 : ℝ)*(2841/25000 : ℝ)=(2500101747531239/2500000000000000 : ℝ) by norm_num, show 1+2*(8744515112353389/100000000000000000000 : ℝ)=(50008744515112353389/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2691827305640703/10000000000000000000 : ℝ)+(8744515112353389/100000000000000000000 : ℝ) ≤ ((2831814370443952409/2832500000000000000 : ℝ)+(422866688987/339900000000000 : ℝ)*((14763/100000 : ℝ)+(2841/25000 : ℝ)))^(275/64 : ℝ) := by
    rw [show (2831814370443952409/2832500000000000000 : ℝ)+(422866688987/339900000000000 : ℝ)*((14763/100000 : ℝ)+(2841/25000 : ℝ))=(10000829856813943/10000000000000000 : ℝ) by norm_num, show 1+(2691827305640703/10000000000000000000 : ℝ)+(8744515112353389/100000000000000000000 : ℝ)=(100035662788168760419/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2691827305640703/10000000000000000000 : ℝ) ≤ ((2831814370443952409/2832500000000000000 : ℝ)+2*(422866688987/339900000000000 : ℝ)*(14763/100000 : ℝ))^(275/64 : ℝ) := by
    rw [show (2831814370443952409/2832500000000000000 : ℝ)+2*(422866688987/339900000000000 : ℝ)*(14763/100000 : ℝ)=(1000125272350293/1000000000000000 : ℝ) by norm_num, show 1+2*(2691827305640703/10000000000000000000 : ℝ)=(5002691827305640703/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2831814370443952409/2832500000000000000 : ℝ)*(X 1 0+X 2 0)+(422866688987/339900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (2841/25000 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (2831814370443952409/2832500000000000000 : ℝ)) (alpha := (422866688987/339900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2831814370443952409/2832500000000000000 : ℝ)*(X 0 1+X 2 1)+(422866688987/339900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (2841/25000 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (2831814370443952409/2832500000000000000 : ℝ)) (alpha := (422866688987/339900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2831814370443952409/2832500000000000000 : ℝ)*(X 0 2+X 1 2)+(422866688987/339900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (2841/25000 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (2831814370443952409/2832500000000000000 : ℝ)) (alpha := (422866688987/339900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1961438649/10000000000 : ℝ)*X 0 0+(1351895053/2500000000 : ℝ)*X 0 1+(655898291/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069413321/2000000000 : ℝ)*X 1 0+(-2043088607/10000000000 : ℝ)*X 1 1+(1049437301/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668383309/1250000000 : ℝ)*X 2 0+(5247186737/10000000000 : ℝ)*X 2 1+(-510772119/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2150691449/5000000000 : ℝ)*X 0 0+(2065143443/5000000000 : ℝ)*X 0 1+(179151859/400000000 : ℝ)*X 0 2+(2150691449/5000000000 : ℝ)*X 1 0+(2065143443/5000000000 : ℝ)*X 1 1+(179151859/400000000 : ℝ)*X 1 2+(2150691449/5000000000 : ℝ)*X 2 0+(2065143443/5000000000 : ℝ)*X 2 1+(179151859/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1961449653/10000000000 : ℝ)*X 0 0+(5247765593/10000000000 : ℝ)*X 0 1+(2703499051/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4301408011/10000000000 : ℝ)*X 0 0+(4477538277/10000000000 : ℝ)*X 0 1+(826310167/2000000000 : ℝ)*X 0 2+(4301408011/10000000000 : ℝ)*X 1 0+(4477538277/10000000000 : ℝ)*X 1 1+(826310167/2000000000 : ℝ)*X 1 2+(4301408011/10000000000 : ℝ)*X 2 0+(4477538277/10000000000 : ℝ)*X 2 1+(826310167/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16801683953750062470478729/6437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (796250167/50000000000000 : ℝ)*(base19) + (825303069/100000000000000 : ℝ)*(base23) + (62781023/20000000000000 : ℝ)*(upper3) + (65460731/20000000000000 : ℝ)*(upper4) + (4886113/20000000000000 : ℝ)*(upper5) + (2276025617092403/50000000000000 : ℝ)*(major0) + (2276025617092403/50000000000000 : ℝ)*(major1) + (2276025617092403/50000000000000 : ℝ)*(major2) + (6234690395998461/100000000000000 : ℝ)*(sp0) + (6234723427682103/100000000000000 : ℝ)*(sp1) + (6234724194879369/100000000000000 : ℝ)*(sp2) + (573873263768589/20000000000000 : ℝ)*(sp3) + (34624183977/100000000000000 : ℝ)*(sp4) + (11042345211/100000000000000 : ℝ)*(sp5) + (717344340297039/25000000000000 : ℝ)*(f.failure) + (6234725020182437/100000000000000 : ℝ)*(f.sum) + (4053895859243/1545000000000000000000000000 : ℝ)*base66 + (142159419434783771/38625000000000000000000000000000 : ℝ)*base67 + (332489884266216229/38625000000000000000000000000000 : ℝ)*base70 + (375454711594283771/38625000000000000000000000000000 : ℝ)*base71 + (3047458618159/772500000000000000000000000 : ℝ)*base74 + (174055084449158771/38625000000000000000000000000000 : ℝ)*base75 + (109557321977841229/38625000000000000000000000000000 : ℝ)*base78 + (665791906342283771/38625000000000000000000000000000 : ℝ)*base79 + (3453568218109/772500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (5917243/1250000000000000000000 : ℝ)*base89 + (5917243/1250000000000000000000 : ℝ)*base91 + (5917243/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1441_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2841/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1441_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1441_box_0 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-360327063/2000000000 : ℝ)*x 0 + (1346435653/2500000000 : ℝ)*x 1 + (168304471/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (360327063/2000000000 : ℝ)^4401 ≤ (2678579027259/25000000000000 : ℝ)^3377 := by
    have hnat : (360327063 : ℕ)^4401*25000000000000^3377 ≤ 2678579027259^3377*2000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360327063 2000000000 2678579027259 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346435653/2500000000 : ℝ)^4401 ≤ (11160709862289/25000000000000 : ℝ)^3377 := by
    have hnat : (1346435653 : ℕ)^4401*25000000000000^3377 ≤ 11160709862289^3377*2500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346435653 2500000000 11160709862289 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168304471/312500000 : ℝ)^4401 ≤ (11160711104583/25000000000000 : ℝ)^3377 := by
    have hnat : (168304471 : ℕ)^4401*25000000000000^3377 ≤ 11160711104583^3377*312500000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168304471 312500000 11160711104583 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-360327063/2000000000 : ℝ), (1346435653/2500000000 : ℝ), (168304471/312500000 : ℝ)] ![(2678579027259/25000000000000 : ℝ), (11160709862289/25000000000000 : ℝ), (11160711104583/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-360327063/2000000000 : ℝ)|^4401 ≤ (2678579027259/25000000000000 : ℝ)^3377
        have hw : |(-360327063/2000000000 : ℝ)|=(360327063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346435653/2500000000 : ℝ)|^4401 ≤ (11160709862289/25000000000000 : ℝ)^3377
        have hw : |(1346435653/2500000000 : ℝ)|=(1346435653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168304471/312500000 : ℝ)|^4401 ≤ (11160711104583/25000000000000 : ℝ)^3377
        have hw : |(168304471/312500000 : ℝ)|=(168304471/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_box_1 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286145091/10000000000 : ℝ)*x 0 + (-484629127/2500000000 : ℝ)*x 1 + (5385742903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286145091/10000000000 : ℝ)^4401 ≤ (21784980656269/50000000000000 : ℝ)^3377 := by
    have hnat : (5286145091 : ℕ)^4401*50000000000000^3377 ≤ 21784980656269^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286145091 10000000000 21784980656269 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (484629127/2500000000 : ℝ)^4401 ≤ (11787196080677/100000000000000 : ℝ)^3377 := by
    have hnat : (484629127 : ℕ)^4401*100000000000000^3377 ≤ 11787196080677^3377*2500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484629127 2500000000 11787196080677 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385742903/10000000000 : ℝ)^4401 ≤ (446428425927/1000000000000 : ℝ)^3377 := by
    have hnat : (5385742903 : ℕ)^4401*1000000000000^3377 ≤ 446428425927^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385742903 10000000000 446428425927 1000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286145091/10000000000 : ℝ), (-484629127/2500000000 : ℝ), (5385742903/10000000000 : ℝ)] ![(21784980656269/50000000000000 : ℝ), (11787196080677/100000000000000 : ℝ), (446428425927/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286145091/10000000000 : ℝ)|^4401 ≤ (21784980656269/50000000000000 : ℝ)^3377
        have hw : |(5286145091/10000000000 : ℝ)|=(5286145091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-484629127/2500000000 : ℝ)|^4401 ≤ (11787196080677/100000000000000 : ℝ)^3377
        have hw : |(-484629127/2500000000 : ℝ)|=(484629127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385742903/10000000000 : ℝ)|^4401 ≤ (446428425927/1000000000000 : ℝ)^3377
        have hw : |(5385742903/10000000000 : ℝ)|=(5385742903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_box_2 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132153631/250000000 : ℝ)*x 0 + (5385742459/10000000000 : ℝ)*x 1 + (-121157307/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132153631/250000000 : ℝ)^4401 ≤ (21784981456517/50000000000000 : ℝ)^3377 := by
    have hnat : (132153631 : ℕ)^4401*50000000000000^3377 ≤ 21784981456517^3377*250000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132153631 250000000 21784981456517 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385742459/10000000000 : ℝ)^4401 ≤ (8928567559273/20000000000000 : ℝ)^3377 := by
    have hnat : (5385742459 : ℕ)^4401*20000000000000^3377 ≤ 8928567559273^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385742459 10000000000 8928567559273 20000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (121157307/625000000 : ℝ)^4401 ≤ (11787199282097/100000000000000 : ℝ)^3377 := by
    have hnat : (121157307 : ℕ)^4401*100000000000000^3377 ≤ 11787199282097^3377*625000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121157307 625000000 11787199282097 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132153631/250000000 : ℝ), (5385742459/10000000000 : ℝ), (-121157307/625000000 : ℝ)] ![(21784981456517/50000000000000 : ℝ), (8928567559273/20000000000000 : ℝ), (11787199282097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132153631/250000000 : ℝ)|^4401 ≤ (21784981456517/50000000000000 : ℝ)^3377
        have hw : |(132153631/250000000 : ℝ)|=(132153631/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385742459/10000000000 : ℝ)|^4401 ≤ (8928567559273/20000000000000 : ℝ)^3377
        have hw : |(5385742459/10000000000 : ℝ)|=(5385742459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-121157307/625000000 : ℝ)|^4401 ≤ (11787199282097/100000000000000 : ℝ)^3377
        have hw : |(-121157307/625000000 : ℝ)|=(121157307/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_box_3 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2223722447/5000000000 : ℝ)*x 0 + (4232037859/10000000000 : ℝ)*x 1 + (4232037629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2223722447/5000000000 : ℝ)^4401 ≤ (17393138421591/50000000000000 : ℝ)^3377 := by
    have hnat : (2223722447 : ℕ)^4401*50000000000000^3377 ≤ 17393138421591^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223722447 5000000000 17393138421591 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232037859/10000000000 : ℝ)^4401 ≤ (1304274508881/4000000000000 : ℝ)^3377 := by
    have hnat : (4232037859 : ℕ)^4401*4000000000000^3377 ≤ 1304274508881^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232037859 10000000000 1304274508881 4000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4232037629/10000000000 : ℝ)^4401 ≤ (1630343020629/5000000000000 : ℝ)^3377 := by
    have hnat : (4232037629 : ℕ)^4401*5000000000000^3377 ≤ 1630343020629^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232037629 10000000000 1630343020629 5000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2223722447/5000000000 : ℝ), (4232037859/10000000000 : ℝ), (4232037629/10000000000 : ℝ)] ![(17393138421591/50000000000000 : ℝ), (1304274508881/4000000000000 : ℝ), (1630343020629/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2223722447/5000000000 : ℝ)|^4401 ≤ (17393138421591/50000000000000 : ℝ)^3377
        have hw : |(2223722447/5000000000 : ℝ)|=(2223722447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232037859/10000000000 : ℝ)|^4401 ≤ (1304274508881/4000000000000 : ℝ)^3377
        have hw : |(4232037859/10000000000 : ℝ)|=(4232037859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4232037629/10000000000 : ℝ)|^4401 ≤ (1630343020629/5000000000000 : ℝ)^3377
        have hw : |(4232037629/10000000000 : ℝ)|=(4232037629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_box_4 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2123969219/10000000000 : ℝ)*x 0 + (5266697411/10000000000 : ℝ)*x 1 + (2633348769/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123969219/10000000000 : ℝ)^4401 ≤ (13277640603331/100000000000000 : ℝ)^3377 := by
    have hnat : (2123969219 : ℕ)^4401*100000000000000^3377 ≤ 13277640603331^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123969219 10000000000 13277640603331 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266697411/10000000000 : ℝ)^4401 ≤ (43361179009233/100000000000000 : ℝ)^3377 := by
    have hnat : (5266697411 : ℕ)^4401*100000000000000^3377 ≤ 43361179009233^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266697411 10000000000 43361179009233 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633348769/5000000000 : ℝ)^4401 ≤ (43361180371891/100000000000000 : ℝ)^3377 := by
    have hnat : (2633348769 : ℕ)^4401*100000000000000^3377 ≤ 43361180371891^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633348769 5000000000 43361180371891 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2123969219/10000000000 : ℝ), (5266697411/10000000000 : ℝ), (2633348769/5000000000 : ℝ)] ![(13277640603331/100000000000000 : ℝ), (43361179009233/100000000000000 : ℝ), (43361180371891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2123969219/10000000000 : ℝ)|^4401 ≤ (13277640603331/100000000000000 : ℝ)^3377
        have hw : |(-2123969219/10000000000 : ℝ)|=(2123969219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266697411/10000000000 : ℝ)|^4401 ≤ (43361179009233/100000000000000 : ℝ)^3377
        have hw : |(5266697411/10000000000 : ℝ)|=(5266697411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633348769/5000000000 : ℝ)|^4401 ≤ (43361180371891/100000000000000 : ℝ)^3377
        have hw : |(2633348769/5000000000 : ℝ)|=(2633348769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_box_5 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369418287/10000000000 : ℝ)*x 0 + (-1986925039/10000000000 : ℝ)*x 1 + (2633348737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369418287/10000000000 : ℝ)^4401 ≤ (44466576110921/100000000000000 : ℝ)^3377 := by
    have hnat : (5369418287 : ℕ)^4401*100000000000000^3377 ≤ 44466576110921^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369418287 10000000000 44466576110921 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1986925039/10000000000 : ℝ)^4401 ≤ (12172244184559/100000000000000 : ℝ)^3377 := by
    have hnat : (1986925039 : ℕ)^4401*100000000000000^3377 ≤ 12172244184559^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986925039 10000000000 12172244184559 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633348737/5000000000 : ℝ)^4401 ≤ (43361179685197/100000000000000 : ℝ)^3377 := by
    have hnat : (2633348737 : ℕ)^4401*100000000000000^3377 ≤ 43361179685197^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633348737 5000000000 43361179685197 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369418287/10000000000 : ℝ), (-1986925039/10000000000 : ℝ), (2633348737/5000000000 : ℝ)] ![(44466576110921/100000000000000 : ℝ), (12172244184559/100000000000000 : ℝ), (43361179685197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369418287/10000000000 : ℝ)|^4401 ≤ (44466576110921/100000000000000 : ℝ)^3377
        have hw : |(5369418287/10000000000 : ℝ)|=(5369418287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1986925039/10000000000 : ℝ)|^4401 ≤ (12172244184559/100000000000000 : ℝ)^3377
        have hw : |(-1986925039/10000000000 : ℝ)|=(1986925039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633348737/5000000000 : ℝ)|^4401 ≤ (43361179685197/100000000000000 : ℝ)^3377
        have hw : |(2633348737/5000000000 : ℝ)|=(2633348737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_box_6 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369418153/10000000000 : ℝ)*x 0 + (5266697501/10000000000 : ℝ)*x 1 + (-15522853/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369418153/10000000000 : ℝ)^4401 ≤ (4446657466471/10000000000000 : ℝ)^3377 := by
    have hnat : (5369418153 : ℕ)^4401*10000000000000^3377 ≤ 4446657466471^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369418153 10000000000 4446657466471 10000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266697501/10000000000 : ℝ)^4401 ≤ (2710073748431/6250000000000 : ℝ)^3377 := by
    have hnat : (5266697501 : ℕ)^4401*6250000000000^3377 ≤ 2710073748431^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266697501 10000000000 2710073748431 6250000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15522853/78125000 : ℝ)^4401 ≤ (12172245342209/100000000000000 : ℝ)^3377 := by
    have hnat : (15522853 : ℕ)^4401*100000000000000^3377 ≤ 12172245342209^3377*78125000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15522853 78125000 12172245342209 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369418153/10000000000 : ℝ), (5266697501/10000000000 : ℝ), (-15522853/78125000 : ℝ)] ![(4446657466471/10000000000000 : ℝ), (2710073748431/6250000000000 : ℝ), (12172245342209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369418153/10000000000 : ℝ)|^4401 ≤ (4446657466471/10000000000000 : ℝ)^3377
        have hw : |(5369418153/10000000000 : ℝ)|=(5369418153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266697501/10000000000 : ℝ)|^4401 ≤ (2710073748431/6250000000000 : ℝ)^3377
        have hw : |(5266697501/10000000000 : ℝ)|=(5266697501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15522853/78125000 : ℝ)|^4401 ≤ (12172245342209/100000000000000 : ℝ)^3377
        have hw : |(-15522853/78125000 : ℝ)|=(15522853/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_box_7 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (830851353/2000000000 : ℝ)*x 0 + (4378581097/10000000000 : ℝ)*x 1 + (2189290707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (830851353/2000000000 : ℝ)^4401 ≤ (7957010839029/25000000000000 : ℝ)^3377 := by
    have hnat : (830851353 : ℕ)^4401*25000000000000^3377 ≤ 7957010839029^3377*2000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830851353 2000000000 7957010839029 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4378581097/10000000000 : ℝ)^4401 ≤ (426074708859/1250000000000 : ℝ)^3377 := by
    have hnat : (4378581097 : ℕ)^4401*1250000000000^3377 ≤ 426074708859^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378581097 10000000000 426074708859 1250000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2189290707/5000000000 : ℝ)^4401 ≤ (8521494981191/25000000000000 : ℝ)^3377 := by
    have hnat : (2189290707 : ℕ)^4401*25000000000000^3377 ≤ 8521494981191^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189290707 5000000000 8521494981191 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(830851353/2000000000 : ℝ), (4378581097/10000000000 : ℝ), (2189290707/5000000000 : ℝ)] ![(7957010839029/25000000000000 : ℝ), (426074708859/1250000000000 : ℝ), (8521494981191/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(830851353/2000000000 : ℝ)|^4401 ≤ (7957010839029/25000000000000 : ℝ)^3377
        have hw : |(830851353/2000000000 : ℝ)|=(830851353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4378581097/10000000000 : ℝ)|^4401 ≤ (426074708859/1250000000000 : ℝ)^3377
        have hw : |(4378581097/10000000000 : ℝ)|=(4378581097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2189290707/5000000000 : ℝ)|^4401 ≤ (8521494981191/25000000000000 : ℝ)^3377
        have hw : |(2189290707/5000000000 : ℝ)|=(2189290707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_box_8 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-411210051/2000000000 : ℝ)*x 0 + (5184301357/10000000000 : ℝ)*x 1 + (1349927409/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (411210051/2000000000 : ℝ)^4401 ≤ (6363506837347/50000000000000 : ℝ)^3377 := by
    have hnat : (411210051 : ℕ)^4401*50000000000000^3377 ≤ 6363506837347^3377*2000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411210051 2000000000 6363506837347 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184301357/10000000000 : ℝ)^4401 ≤ (42479208004947/100000000000000 : ℝ)^3377 := by
    have hnat : (5184301357 : ℕ)^4401*100000000000000^3377 ≤ 42479208004947^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184301357 10000000000 42479208004947 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349927409/2500000000 : ℝ)^4401 ≤ (22396889147429/50000000000000 : ℝ)^3377 := by
    have hnat : (1349927409 : ℕ)^4401*50000000000000^3377 ≤ 22396889147429^3377*2500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349927409 2500000000 22396889147429 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-411210051/2000000000 : ℝ), (5184301357/10000000000 : ℝ), (1349927409/2500000000 : ℝ)] ![(6363506837347/50000000000000 : ℝ), (42479208004947/100000000000000 : ℝ), (22396889147429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-411210051/2000000000 : ℝ)|^4401 ≤ (6363506837347/50000000000000 : ℝ)^3377
        have hw : |(-411210051/2000000000 : ℝ)|=(411210051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184301357/10000000000 : ℝ)|^4401 ≤ (42479208004947/100000000000000 : ℝ)^3377
        have hw : |(5184301357/10000000000 : ℝ)|=(5184301357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349927409/2500000000 : ℝ)|^4401 ≤ (22396889147429/50000000000000 : ℝ)^3377
        have hw : |(1349927409/2500000000 : ℝ)|=(1349927409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_box_9 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276371157/10000000000 : ℝ)*x 0 + (-966355893/5000000000 : ℝ)*x 1 + (5399709627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276371157/10000000000 : ℝ)^4401 ≤ (43465003205361/100000000000000 : ℝ)^3377 := by
    have hnat : (5276371157 : ℕ)^4401*100000000000000^3377 ≤ 43465003205361^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276371157 10000000000 43465003205361 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (966355893/5000000000 : ℝ)^4401 ≤ (11741218576969/100000000000000 : ℝ)^3377 := by
    have hnat : (966355893 : ℕ)^4401*100000000000000^3377 ≤ 11741218576969^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966355893 5000000000 11741218576969 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399709627/10000000000 : ℝ)^4401 ≤ (44793778197559/100000000000000 : ℝ)^3377 := by
    have hnat : (5399709627 : ℕ)^4401*100000000000000^3377 ≤ 44793778197559^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399709627 10000000000 44793778197559 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276371157/10000000000 : ℝ), (-966355893/5000000000 : ℝ), (5399709627/10000000000 : ℝ)] ![(43465003205361/100000000000000 : ℝ), (11741218576969/100000000000000 : ℝ), (44793778197559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276371157/10000000000 : ℝ)|^4401 ≤ (43465003205361/100000000000000 : ℝ)^3377
        have hw : |(5276371157/10000000000 : ℝ)|=(5276371157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-966355893/5000000000 : ℝ)|^4401 ≤ (11741218576969/100000000000000 : ℝ)^3377
        have hw : |(-966355893/5000000000 : ℝ)|=(966355893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399709627/10000000000 : ℝ)|^4401 ≤ (44793778197559/100000000000000 : ℝ)^3377
        have hw : |(5399709627/10000000000 : ℝ)|=(5399709627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_box_10 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105527423/200000000 : ℝ)*x 0 + (84370463/156250000 : ℝ)*x 1 + (-1932711789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105527423/200000000 : ℝ)^4401 ≤ (10866250782553/25000000000000 : ℝ)^3377 := by
    have hnat : (105527423 : ℕ)^4401*25000000000000^3377 ≤ 10866250782553^3377*200000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105527423 200000000 10866250782553 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84370463/156250000 : ℝ)^4401 ≤ (22396889125807/50000000000000 : ℝ)^3377 := by
    have hnat : (84370463 : ℕ)^4401*50000000000000^3377 ≤ 22396889125807^3377*156250000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84370463 156250000 22396889125807 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1932711789/10000000000 : ℝ)^4401 ≤ (146765232509/1250000000000 : ℝ)^3377 := by
    have hnat : (1932711789 : ℕ)^4401*1250000000000^3377 ≤ 146765232509^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1932711789 10000000000 146765232509 1250000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105527423/200000000 : ℝ), (84370463/156250000 : ℝ), (-1932711789/10000000000 : ℝ)] ![(10866250782553/25000000000000 : ℝ), (22396889125807/50000000000000 : ℝ), (146765232509/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105527423/200000000 : ℝ)|^4401 ≤ (10866250782553/25000000000000 : ℝ)^3377
        have hw : |(105527423/200000000 : ℝ)|=(105527423/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84370463/156250000 : ℝ)|^4401 ≤ (22396889125807/50000000000000 : ℝ)^3377
        have hw : |(84370463/156250000 : ℝ)|=(84370463/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1932711789/10000000000 : ℝ)|^4401 ≤ (146765232509/1250000000000 : ℝ)^3377
        have hw : |(-1932711789/10000000000 : ℝ)|=(1932711789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_box_11 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (280080359/625000000 : ℝ)*x 0 + (2107415139/5000000000 : ℝ)*x 1 + (2107415133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (280080359/625000000 : ℝ)^4401 ≤ (35131626312057/100000000000000 : ℝ)^3377 := by
    have hnat : (280080359 : ℕ)^4401*100000000000000^3377 ≤ 35131626312057^3377*625000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280080359 625000000 35131626312057 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107415139/5000000000 : ℝ)^4401 ≤ (16217093448919/50000000000000 : ℝ)^3377 := by
    have hnat : (2107415139 : ℕ)^4401*50000000000000^3377 ≤ 16217093448919^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107415139 5000000000 16217093448919 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107415133/5000000000 : ℝ)^4401 ≤ (16217093388747/50000000000000 : ℝ)^3377 := by
    have hnat : (2107415133 : ℕ)^4401*50000000000000^3377 ≤ 16217093388747^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107415133 5000000000 16217093388747 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(280080359/625000000 : ℝ), (2107415139/5000000000 : ℝ), (2107415133/5000000000 : ℝ)] ![(35131626312057/100000000000000 : ℝ), (16217093448919/50000000000000 : ℝ), (16217093388747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(280080359/625000000 : ℝ)|^4401 ≤ (35131626312057/100000000000000 : ℝ)^3377
        have hw : |(280080359/625000000 : ℝ)|=(280080359/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2107415139/5000000000 : ℝ)|^4401 ≤ (16217093448919/50000000000000 : ℝ)^3377
        have hw : |(2107415139/5000000000 : ℝ)|=(2107415139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2107415133/5000000000 : ℝ)|^4401 ≤ (16217093388747/50000000000000 : ℝ)^3377
        have hw : |(2107415133/5000000000 : ℝ)|=(2107415133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_box_12 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-116857167/625000000 : ℝ)*x 0 + (5466138273/10000000000 : ℝ)*x 1 + (656945677/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (116857167/625000000 : ℝ)^4401 ≤ (11244947542239/100000000000000 : ℝ)^3377 := by
    have hnat : (116857167 : ℕ)^4401*100000000000000^3377 ≤ 11244947542239^3377*625000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116857167 625000000 11244947542239 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5466138273/10000000000 : ℝ)^4401 ≤ (22756638427629/50000000000000 : ℝ)^3377 := by
    have hnat : (5466138273 : ℕ)^4401*50000000000000^3377 ≤ 22756638427629^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466138273 10000000000 22756638427629 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656945677/1250000000 : ℝ)^4401 ≤ (43241775590717/100000000000000 : ℝ)^3377 := by
    have hnat : (656945677 : ℕ)^4401*100000000000000^3377 ≤ 43241775590717^3377*1250000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656945677 1250000000 43241775590717 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-116857167/625000000 : ℝ), (5466138273/10000000000 : ℝ), (656945677/1250000000 : ℝ)] ![(11244947542239/100000000000000 : ℝ), (22756638427629/50000000000000 : ℝ), (43241775590717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-116857167/625000000 : ℝ)|^4401 ≤ (11244947542239/100000000000000 : ℝ)^3377
        have hw : |(-116857167/625000000 : ℝ)|=(116857167/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5466138273/10000000000 : ℝ)|^4401 ≤ (22756638427629/50000000000000 : ℝ)^3377
        have hw : |(5466138273/10000000000 : ℝ)|=(5466138273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656945677/1250000000 : ℝ)|^4401 ≤ (43241775590717/100000000000000 : ℝ)^3377
        have hw : |(656945677/1250000000 : ℝ)|=(656945677/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_box_13 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688601737/5000000000 : ℝ)*x 0 + (-497838183/2500000000 : ℝ)*x 1 + (2627782771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688601737/5000000000 : ℝ)^4401 ≤ (22275308557889/50000000000000 : ℝ)^3377 := by
    have hnat : (2688601737 : ℕ)^4401*50000000000000^3377 ≤ 22275308557889^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688601737 5000000000 22275308557889 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (497838183/2500000000 : ℝ)^4401 ≤ (6103802961667/50000000000000 : ℝ)^3377 := by
    have hnat : (497838183 : ℕ)^4401*50000000000000^3377 ≤ 6103802961667^3377*2500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497838183 2500000000 6103802961667 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627782771/5000000000 : ℝ)^4401 ≤ (21620888470889/50000000000000 : ℝ)^3377 := by
    have hnat : (2627782771 : ℕ)^4401*50000000000000^3377 ≤ 21620888470889^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627782771 5000000000 21620888470889 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688601737/5000000000 : ℝ), (-497838183/2500000000 : ℝ), (2627782771/5000000000 : ℝ)] ![(22275308557889/50000000000000 : ℝ), (6103802961667/50000000000000 : ℝ), (21620888470889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688601737/5000000000 : ℝ)|^4401 ≤ (22275308557889/50000000000000 : ℝ)^3377
        have hw : |(2688601737/5000000000 : ℝ)|=(2688601737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-497838183/2500000000 : ℝ)|^4401 ≤ (6103802961667/50000000000000 : ℝ)^3377
        have hw : |(-497838183/2500000000 : ℝ)|=(497838183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627782771/5000000000 : ℝ)|^4401 ≤ (21620888470889/50000000000000 : ℝ)^3377
        have hw : |(2627782771/5000000000 : ℝ)|=(2627782771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_box_14 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215088153/400000000 : ℝ)*x 0 + (21022261/40000000 : ℝ)*x 1 + (-39827053/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215088153/400000000 : ℝ)^4401 ≤ (11137655226413/25000000000000 : ℝ)^3377 := by
    have hnat : (215088153 : ℕ)^4401*25000000000000^3377 ≤ 11137655226413^3377*400000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215088153 400000000 11137655226413 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21022261/40000000 : ℝ)^4401 ≤ (10810443452687/25000000000000 : ℝ)^3377 := by
    have hnat : (21022261 : ℕ)^4401*25000000000000^3377 ≤ 10810443452687^3377*40000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21022261 40000000 10810443452687 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39827053/200000000 : ℝ)^4401 ≤ (610380263411/5000000000000 : ℝ)^3377 := by
    have hnat : (39827053 : ℕ)^4401*5000000000000^3377 ≤ 610380263411^3377*200000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39827053 200000000 610380263411 5000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215088153/400000000 : ℝ), (21022261/40000000 : ℝ), (-39827053/200000000 : ℝ)] ![(11137655226413/25000000000000 : ℝ), (10810443452687/25000000000000 : ℝ), (610380263411/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215088153/400000000 : ℝ)|^4401 ≤ (11137655226413/25000000000000 : ℝ)^3377
        have hw : |(215088153/400000000 : ℝ)|=(215088153/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21022261/40000000 : ℝ)|^4401 ≤ (10810443452687/25000000000000 : ℝ)^3377
        have hw : |(21022261/40000000 : ℝ)|=(21022261/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-39827053/200000000 : ℝ)|^4401 ≤ (610380263411/5000000000000 : ℝ)^3377
        have hw : |(-39827053/200000000 : ℝ)|=(39827053/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_box_15 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (515798891/1250000000 : ℝ)*x 0 + (4392273339/10000000000 : ℝ)*x 1 + (4392273049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (515798891/1250000000 : ℝ)^4401 ≤ (1577504775849/5000000000000 : ℝ)^3377 := by
    have hnat : (515798891 : ℕ)^4401*5000000000000^3377 ≤ 1577504775849^3377*1250000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515798891 1250000000 1577504775849 5000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4392273339/10000000000 : ℝ)^4401 ≤ (17112476853157/50000000000000 : ℝ)^3377 := by
    have hnat : (4392273339 : ℕ)^4401*50000000000000^3377 ≤ 17112476853157^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4392273339 10000000000 17112476853157 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4392273049/10000000000 : ℝ)^4401 ≤ (6844990152281/20000000000000 : ℝ)^3377 := by
    have hnat : (4392273049 : ℕ)^4401*20000000000000^3377 ≤ 6844990152281^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4392273049 10000000000 6844990152281 20000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(515798891/1250000000 : ℝ), (4392273339/10000000000 : ℝ), (4392273049/10000000000 : ℝ)] ![(1577504775849/5000000000000 : ℝ), (17112476853157/50000000000000 : ℝ), (6844990152281/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(515798891/1250000000 : ℝ)|^4401 ≤ (1577504775849/5000000000000 : ℝ)^3377
        have hw : |(515798891/1250000000 : ℝ)|=(515798891/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4392273339/10000000000 : ℝ)|^4401 ≤ (17112476853157/50000000000000 : ℝ)^3377
        have hw : |(4392273339/10000000000 : ℝ)|=(4392273339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4392273049/10000000000 : ℝ)|^4401 ≤ (6844990152281/20000000000000 : ℝ)^3377
        have hw : |(4392273049/10000000000 : ℝ)|=(4392273049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1441_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62907/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59137/100000 : ℝ) ∧ (40257/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (8473/10000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14763/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2273/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14763/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2273/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14763/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2273/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14763/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2273/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14763/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2273/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14763/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2273/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2273/20000 : ℝ) ^ (275/64 : ℝ) ≤ (8747822005978643/100000000000000000000 : ℝ) := by
    have hpowers : (2273/20000 : ℝ)^275 ≤ (8747822005978643/100000000000000000000 : ℝ)^64 := by
      have hnat : (2273 : ℕ)^275*100000000000000000000^64 ≤ 8747822005978643^64*20000^275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2273 20000 8747822005978643 100000000000000000000 275 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2273/20000 : ℝ)) (X := (8747822005978643/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hpowhi : (14763/100000 : ℝ) ^ (275/64 : ℝ) ≤ (2691827305640703/10000000000000000000 : ℝ) := by
    have hpowers : (14763/100000 : ℝ)^275 ≤ (2691827305640703/10000000000000000000 : ℝ)^64 := by
      have hnat : (14763 : ℕ)^275*10000000000000000000^64 ≤ 2691827305640703^64*100000^275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14763 100000 2691827305640703 10000000000000000000 275 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14763/100000 : ℝ)) (X := (2691827305640703/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008747822005978643/50000000000000000000 : ℝ) ≤ (625025446501573/625000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (50008747822005978643/50000000000000000000 : ℝ)^64 ≤ (625025446501573/625000000000000 : ℝ)^275 := by
      have hnat : (50008747822005978643 : ℕ)^64*625000000000000^275 ≤ 625025446501573^275*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008747822005978643 50000000000000000000 625025446501573 625000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625025446501573/625000000000000 : ℝ)) (X := (50008747822005978643/50000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035666095062385673/100000000000000000000 : ℝ) ≤ (10000829933753323/10000000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (100035666095062385673/100000000000000000000 : ℝ)^64 ≤ (10000829933753323/10000000000000000 : ℝ)^275 := by
      have hnat : (100035666095062385673 : ℕ)^64*10000000000000000^275 ≤ 10000829933753323^275*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035666095062385673 100000000000000000000 10000829933753323 10000000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000829933753323/10000000000000000 : ℝ)) (X := (100035666095062385673/100000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002691827305640703/5000000000000000000 : ℝ) ≤ (5000626361740739/5000000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (5002691827305640703/5000000000000000000 : ℝ)^64 ≤ (5000626361740739/5000000000000000 : ℝ)^275 := by
      have hnat : (5002691827305640703 : ℕ)^64*5000000000000000^275 ≤ 5000626361740739^275*5000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002691827305640703 5000000000000000000 5000626361740739 5000000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000626361740739/5000000000000000 : ℝ)) (X := (5002691827305640703/5000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8747822005978643/100000000000000000000 : ℝ) ≤ ((16985886732438278857/16990000000000000000 : ℝ)+2*(84557945631/67960000000000 : ℝ)*(2273/20000 : ℝ))^(275/64 : ℝ) := by
    rw [show (16985886732438278857/16990000000000000000 : ℝ)+2*(84557945631/67960000000000 : ℝ)*(2273/20000 : ℝ)=(625025446501573/625000000000000 : ℝ) by norm_num, show 1+2*(8747822005978643/100000000000000000000 : ℝ)=(50008747822005978643/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2691827305640703/10000000000000000000 : ℝ)+(8747822005978643/100000000000000000000 : ℝ) ≤ ((16985886732438278857/16990000000000000000 : ℝ)+(84557945631/67960000000000 : ℝ)*((14763/100000 : ℝ)+(2273/20000 : ℝ)))^(275/64 : ℝ) := by
    rw [show (16985886732438278857/16990000000000000000 : ℝ)+(84557945631/67960000000000 : ℝ)*((14763/100000 : ℝ)+(2273/20000 : ℝ))=(10000829933753323/10000000000000000 : ℝ) by norm_num, show 1+(2691827305640703/10000000000000000000 : ℝ)+(8747822005978643/100000000000000000000 : ℝ)=(100035666095062385673/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2691827305640703/10000000000000000000 : ℝ) ≤ ((16985886732438278857/16990000000000000000 : ℝ)+2*(84557945631/67960000000000 : ℝ)*(14763/100000 : ℝ))^(275/64 : ℝ) := by
    rw [show (16985886732438278857/16990000000000000000 : ℝ)+2*(84557945631/67960000000000 : ℝ)*(14763/100000 : ℝ)=(5000626361740739/5000000000000000 : ℝ) by norm_num, show 1+2*(2691827305640703/10000000000000000000 : ℝ)=(5002691827305640703/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16985886732438278857/16990000000000000000 : ℝ)*(X 1 0+X 2 0)+(84557945631/67960000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (2273/20000 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (16985886732438278857/16990000000000000000 : ℝ)) (alpha := (84557945631/67960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16985886732438278857/16990000000000000000 : ℝ)*(X 0 1+X 2 1)+(84557945631/67960000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (2273/20000 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (16985886732438278857/16990000000000000000 : ℝ)) (alpha := (84557945631/67960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16985886732438278857/16990000000000000000 : ℝ)*(X 0 2+X 1 2)+(84557945631/67960000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (2273/20000 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (16985886732438278857/16990000000000000000 : ℝ)) (alpha := (84557945631/67960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-360327063/2000000000 : ℝ)*X 0 0+(1346435653/2500000000 : ℝ)*X 0 1+(168304471/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5286145091/10000000000 : ℝ)*X 1 0+(-484629127/2500000000 : ℝ)*X 1 1+(5385742903/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((132153631/250000000 : ℝ)*X 2 0+(5385742459/10000000000 : ℝ)*X 2 1+(-121157307/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2223722447/5000000000 : ℝ)*X 0 0+(4232037859/10000000000 : ℝ)*X 0 1+(4232037629/10000000000 : ℝ)*X 0 2+(2223722447/5000000000 : ℝ)*X 1 0+(4232037859/10000000000 : ℝ)*X 1 1+(4232037629/10000000000 : ℝ)*X 1 2+(2223722447/5000000000 : ℝ)*X 2 0+(4232037859/10000000000 : ℝ)*X 2 1+(4232037629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2123969219/10000000000 : ℝ)*X 0 0+(5266697411/10000000000 : ℝ)*X 0 1+(2633348769/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5369418287/10000000000 : ℝ)*X 1 0+(-1986925039/10000000000 : ℝ)*X 1 1+(2633348737/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5369418153/10000000000 : ℝ)*X 2 0+(5266697501/10000000000 : ℝ)*X 2 1+(-15522853/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((830851353/2000000000 : ℝ)*X 0 0+(4378581097/10000000000 : ℝ)*X 0 1+(2189290707/5000000000 : ℝ)*X 0 2+(830851353/2000000000 : ℝ)*X 1 0+(4378581097/10000000000 : ℝ)*X 1 1+(2189290707/5000000000 : ℝ)*X 1 2+(830851353/2000000000 : ℝ)*X 2 0+(4378581097/10000000000 : ℝ)*X 2 1+(2189290707/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-411210051/2000000000 : ℝ)*X 0 0+(5184301357/10000000000 : ℝ)*X 0 1+(1349927409/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276371157/10000000000 : ℝ)*X 1 0+(-966355893/5000000000 : ℝ)*X 1 1+(5399709627/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((105527423/200000000 : ℝ)*X 2 0+(84370463/156250000 : ℝ)*X 2 1+(-1932711789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((280080359/625000000 : ℝ)*X 0 0+(2107415139/5000000000 : ℝ)*X 0 1+(2107415133/5000000000 : ℝ)*X 0 2+(280080359/625000000 : ℝ)*X 1 0+(2107415139/5000000000 : ℝ)*X 1 1+(2107415133/5000000000 : ℝ)*X 1 2+(280080359/625000000 : ℝ)*X 2 0+(2107415139/5000000000 : ℝ)*X 2 1+(2107415133/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-116857167/625000000 : ℝ)*X 0 0+(5466138273/10000000000 : ℝ)*X 0 1+(656945677/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2688601737/5000000000 : ℝ)*X 1 0+(-497838183/2500000000 : ℝ)*X 1 1+(2627782771/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((215088153/400000000 : ℝ)*X 2 0+(21022261/40000000 : ℝ)*X 2 1+(-39827053/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((515798891/1250000000 : ℝ)*X 0 0+(4392273339/10000000000 : ℝ)*X 0 1+(4392273049/10000000000 : ℝ)*X 0 2+(515798891/1250000000 : ℝ)*X 1 0+(4392273339/10000000000 : ℝ)*X 1 1+(4392273049/10000000000 : ℝ)*X 1 2+(515798891/1250000000 : ℝ)*X 2 0+(4392273339/10000000000 : ℝ)*X 2 1+(4392273049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62907/100000 : ℝ) ≤ (-133593462851677228421531771840289/212375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26309173/100000000000000 : ℝ)*(upper1) + (111569147/100000000000000 : ℝ)*(lower4) + (3669963/6250000000000 : ℝ)*(upper5) + (757452885509341/25000000000000 : ℝ)*(major0) + (757452885509341/25000000000000 : ℝ)*(major1) + (757452885509341/25000000000000 : ℝ)*(major2) + (1614430007/25000000000000 : ℝ)*(sp2) + (202736991/6250000000000 : ℝ)*(sp3) + (2085376085862717/50000000000000 : ℝ)*(sp4) + (2085376258162151/50000000000000 : ℝ)*(sp5) + (2085374253238327/50000000000000 : ℝ)*(sp6) + (1909833047614797/100000000000000 : ℝ)*(sp7) + (174529453/6250000000000 : ℝ)*(sp12) + (122393619/5000000000000 : ℝ)*(sp13) + (954918145703327/50000000000000 : ℝ)*(f.failure) + (2085377482098341/50000000000000 : ℝ)*(f.sum) + (5216413392709/1699000000000000000000000000 : ℝ)*base65 + (1971807812373196763/424750000000000000000000000000000 : ℝ)*base68 + (2219980041960446763/424750000000000000000000000000000 : ℝ)*base70 + (806779656794803237/424750000000000000000000000000000 : ℝ)*base71 + (2254953759517/1699000000000000000000000000 : ℝ)*base73 + (317135618251553237/424750000000000000000000000000000 : ℝ)*base75 + (253909436108196763/424750000000000000000000000000000 : ℝ)*base78 + (3447977348166196763/424750000000000000000000000000000 : ℝ)*base80 + (1657846706037/424750000000000000000000000 : ℝ)*base82 + (32655499/2500000000000000000000 : ℝ)*base89 + (32655499/2500000000000000000000 : ℝ)*base91 + (32655499/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (59137/100000 : ℝ) ≤ (2009569838428519862763774531/3398000000000000000000000000 : ℝ) := by norm_num
    linear_combination (431423/781250000000 : ℝ)*(lower0) + (45227787/50000000000000 : ℝ)*(upper2) + (4382803/6250000000000 : ℝ)*(lower5) + (3101823943100281/100000000000000 : ℝ)*(major0) + (3101823943100281/100000000000000 : ℝ)*(major1) + (3101823943100281/100000000000000 : ℝ)*(major2) + (528586750056719/12500000000000 : ℝ)*(sp0) + (4228698933394613/100000000000000 : ℝ)*(sp1) + (2114301957758623/50000000000000 : ℝ)*(sp2) + (122201530847821/6250000000000 : ℝ)*(sp3) + (6511953129/100000000000000 : ℝ)*(sp5) + (4686169089/100000000000000 : ℝ)*(sp7) + (3172807203/3125000000000 : ℝ)*(sp10) + (11444893989/100000000000000 : ℝ)*(sp12) + (122201823733389/6250000000000 : ℝ)*(f.failure) + (2114352722673871/50000000000000 : ℝ)*(f.sum) + (2264308604727/3398000000000000000000000000 : ℝ)*base66 + (4247778584848808817/1699000000000000000000000000000000 : ℝ)*base67 + (3352933498128808817/1699000000000000000000000000000000 : ℝ)*base69 + (2176823068254191183/1699000000000000000000000000000000 : ℝ)*base72 + (6502210999911/679600000000000000000000000 : ℝ)*base73 + (3288095813654191183/1699000000000000000000000000000000 : ℝ)*base76 + (4130901811420191183/1699000000000000000000000000000000 : ℝ)*base78 + (636954768513808817/1699000000000000000000000000000000 : ℝ)*base79 + (5510209071901/3398000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (4442807/312500000000000000000 : ℝ)*base90 + (4442807/312500000000000000000 : ℝ)*base92 + (4442807/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (40257/50000 : ℝ) ≤ (170997684879508777885713791751579/212375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3958553/100000000000000 : ℝ)*(upper1) + (581719/20000000000000 : ℝ)*(upper2) + (215447/100000000000000 : ℝ)*(lower5) + (852257930725883/25000000000000 : ℝ)*(major0) + (852257930725883/25000000000000 : ℝ)*(major1) + (852257930725883/25000000000000 : ℝ)*(major2) + (2180073877/100000000000000 : ℝ)*(sp1) + (2528970381/100000000000000 : ℝ)*(sp2) + (379695601/50000000000000 : ℝ)*(sp3) + (49084379/20000000000000 : ℝ)*(sp4) + (2321173595870423/50000000000000 : ℝ)*(sp8) + (145073289284027/3125000000000 : ℝ)*(sp9) + (4642344908192359/100000000000000 : ℝ)*(sp10) + (2148876295377581/100000000000000 : ℝ)*(sp11) + (2148877054768783/100000000000000 : ℝ)*(f.failure) + (4642347437162741/100000000000000 : ℝ)*(f.sum) + (5315693602437/1699000000000000000000000000 : ℝ)*base66 + (1149557671824444269/424750000000000000000000000000000 : ℝ)*base68 + (2818373775982694269/424750000000000000000000000000000 : ℝ)*base70 + (1077713504673444269/424750000000000000000000000000000 : ℝ)*base72 + (5824037514281/849500000000000000000000000 : ℝ)*base73 + (301709677484444269/424750000000000000000000000000000 : ℝ)*base76 + (477030285589694269/424750000000000000000000000000000 : ℝ)*base78 + (723476887599444269/424750000000000000000000000000000 : ℝ)*base80 + (2091910360473/1699000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (16544571/5000000000000000000000 : ℝ)*base89 + (16544571/5000000000000000000000 : ℝ)*base91 + (16544571/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-8473/10000 : ℝ) ≤ (-89969690083881654572677524707523/106187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30094377/50000000000000 : ℝ)*(lower2) + (15026031/25000000000000 : ℝ)*(upper3) + (65027799/100000000000000 : ℝ)*(upper4) + (59620591/100000000000000 : ℝ)*(upper5) + (861662421050113/25000000000000 : ℝ)*(major0) + (861662421050113/25000000000000 : ℝ)*(major1) + (861662421050113/25000000000000 : ℝ)*(major2) + (5897686579/100000000000000 : ℝ)*(sp0) + (17302034003/25000000000000 : ℝ)*(sp5) + (12247048429/10000000000000 : ℝ)*(sp6) + (4748946399563189/100000000000000 : ℝ)*(sp12) + (4748883089113757/100000000000000 : ℝ)*(sp13) + (118720745669137/2500000000000 : ℝ)*(sp14) + (33946710460171/1562500000000 : ℝ)*(sp15) + (33946710460171/1562500000000 : ℝ)*(f.failure) + (474895229724977/10000000000000 : ℝ)*(f.sum) + (18840621588949/339800000000000000000000000 : ℝ)*base65 + (303074210156360841/424750000000000000000000000000000 : ℝ)*base67 + (2971144900083110841/424750000000000000000000000000000 : ℝ)*base69 + (6880137190914610841/424750000000000000000000000000000 : ℝ)*base71 + (114131456477/169900000000000000000000000 : ℝ)*base74 + (1287226638500610841/424750000000000000000000000000000 : ℝ)*base75 + (10225623603541610841/424750000000000000000000000000000 : ℝ)*base77 + (1555076363382389159/424750000000000000000000000000000 : ℝ)*base80 + (2762370008151/849500000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (173473/78125000000000000000 : ℝ)*base90 + (173473/78125000000000000000 : ℝ)*base92 + (173473/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1441_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62907/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59137/100000 : ℝ) else (40257/50000 : ℝ) ≤ X j i ∧ X j i ≤ (8473/10000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1441_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1441_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62907/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59137/100000 : ℝ) else (40257/50000 : ℝ) ≤ X j i ∧ X j i ≤ (8473/10000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1441_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1441_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1441_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62907/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59137/100000 : ℝ) else (40257/50000 : ℝ) ≤ X j i ∧ X j i ≤ (8473/10000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1441_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

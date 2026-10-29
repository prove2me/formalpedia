-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1401_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:45:29.196272+00:00
-- url     : https://prove2.me/submissions/4288bfe5-8f3d-43be-a933-db63dd095122

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
theorem support_rectangle_w1401_s3_0 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-996415353/5000000000 : ℝ)*x 0 + (542021163/1000000000 : ℝ)*x 1 + (5236517337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (996415353/5000000000 : ℝ)^4361 ≤ (1518497883613/12500000000000 : ℝ)^3337 := by
    have hnat : (996415353 : ℕ)^4361*12500000000000^3337 ≤ 1518497883613^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996415353 5000000000 1518497883613 12500000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542021163/1000000000 : ℝ)^4361 ≤ (22457728159919/50000000000000 : ℝ)^3337 := by
    have hnat : (542021163 : ℕ)^4361*50000000000000^3337 ≤ 22457728159919^3337*1000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542021163 1000000000 22457728159919 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236517337/10000000000 : ℝ)^4361 ≤ (21468280296543/50000000000000 : ℝ)^3337 := by
    have hnat : (5236517337 : ℕ)^4361*50000000000000^3337 ≤ 21468280296543^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236517337 10000000000 21468280296543 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-996415353/5000000000 : ℝ), (542021163/1000000000 : ℝ), (5236517337/10000000000 : ℝ)] ![(1518497883613/12500000000000 : ℝ), (22457728159919/50000000000000 : ℝ), (21468280296543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-996415353/5000000000 : ℝ)|^4361 ≤ (1518497883613/12500000000000 : ℝ)^3337
        have hw : |(-996415353/5000000000 : ℝ)|=(996415353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542021163/1000000000 : ℝ)|^4361 ≤ (22457728159919/50000000000000 : ℝ)^3337
        have hw : |(542021163/1000000000 : ℝ)|=(542021163/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236517337/10000000000 : ℝ)|^4361 ≤ (21468280296543/50000000000000 : ℝ)^3337
        have hw : |(5236517337/10000000000 : ℝ)|=(5236517337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s3_1 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675307327/5000000000 : ℝ)*x 0 + (-52164627/250000000 : ℝ)*x 1 + (5236516561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675307327/5000000000 : ℝ)^4361 ≤ (44163243348097/100000000000000 : ℝ)^3337 := by
    have hnat : (2675307327 : ℕ)^4361*100000000000000^3337 ≤ 44163243348097^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675307327 5000000000 44163243348097 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52164627/250000000 : ℝ)^4361 ≤ (3225051090319/25000000000000 : ℝ)^3337 := by
    have hnat : (52164627 : ℕ)^4361*25000000000000^3337 ≤ 3225051090319^3337*250000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52164627 250000000 3225051090319 25000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236516561/10000000000 : ℝ)^4361 ≤ (42936552277817/100000000000000 : ℝ)^3337 := by
    have hnat : (5236516561 : ℕ)^4361*100000000000000^3337 ≤ 42936552277817^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236516561 10000000000 42936552277817 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675307327/5000000000 : ℝ), (-52164627/250000000 : ℝ), (5236516561/10000000000 : ℝ)] ![(44163243348097/100000000000000 : ℝ), (3225051090319/25000000000000 : ℝ), (42936552277817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675307327/5000000000 : ℝ)|^4361 ≤ (44163243348097/100000000000000 : ℝ)^3337
        have hw : |(2675307327/5000000000 : ℝ)|=(2675307327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-52164627/250000000 : ℝ)|^4361 ≤ (3225051090319/25000000000000 : ℝ)^3337
        have hw : |(-52164627/250000000 : ℝ)|=(52164627/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236516561/10000000000 : ℝ)|^4361 ≤ (42936552277817/100000000000000 : ℝ)^3337
        have hw : |(5236516561/10000000000 : ℝ)|=(5236516561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s3_2 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675306941/5000000000 : ℝ)*x 0 + (5236517101/10000000000 : ℝ)*x 1 + (-2086585393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675306941/5000000000 : ℝ)^4361 ≤ (44163235020793/100000000000000 : ℝ)^3337 := by
    have hnat : (2675306941 : ℕ)^4361*100000000000000^3337 ≤ 44163235020793^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675306941 5000000000 44163235020793 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5236517101/10000000000 : ℝ)^4361 ≤ (8587311612843/20000000000000 : ℝ)^3337 := by
    have hnat : (5236517101 : ℕ)^4361*20000000000000^3337 ≤ 8587311612843^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236517101 10000000000 8587311612843 20000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086585393/10000000000 : ℝ)^4361 ≤ (6450103445097/50000000000000 : ℝ)^3337 := by
    have hnat : (2086585393 : ℕ)^4361*50000000000000^3337 ≤ 6450103445097^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086585393 10000000000 6450103445097 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675306941/5000000000 : ℝ), (5236517101/10000000000 : ℝ), (-2086585393/10000000000 : ℝ)] ![(44163235020793/100000000000000 : ℝ), (8587311612843/20000000000000 : ℝ), (6450103445097/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675306941/5000000000 : ℝ)|^4361 ≤ (44163235020793/100000000000000 : ℝ)^3337
        have hw : |(2675306941/5000000000 : ℝ)|=(2675306941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5236517101/10000000000 : ℝ)|^4361 ≤ (8587311612843/20000000000000 : ℝ)^3337
        have hw : |(5236517101/10000000000 : ℝ)|=(5236517101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2086585393/10000000000 : ℝ)|^4361 ≤ (6450103445097/50000000000000 : ℝ)^3337
        have hw : |(-2086585393/10000000000 : ℝ)|=(2086585393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s3_3 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4310665299/10000000000 : ℝ)*x 0 + (4118090487/10000000000 : ℝ)*x 1 + (4511408787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310665299/10000000000 : ℝ)^4361 ≤ (33296583414633/100000000000000 : ℝ)^3337 := by
    have hnat : (4310665299 : ℕ)^4361*100000000000000^3337 ≤ 33296583414633^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310665299 10000000000 33296583414633 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4118090487/10000000000 : ℝ)^4361 ≤ (15683049901119/50000000000000 : ℝ)^3337 := by
    have hnat : (4118090487 : ℕ)^4361*50000000000000^3337 ≤ 15683049901119^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4118090487 10000000000 15683049901119 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4511408787/10000000000 : ℝ)^4361 ≤ (17668658384641/50000000000000 : ℝ)^3337 := by
    have hnat : (4511408787 : ℕ)^4361*50000000000000^3337 ≤ 17668658384641^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511408787 10000000000 17668658384641 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310665299/10000000000 : ℝ), (4118090487/10000000000 : ℝ), (4511408787/10000000000 : ℝ)] ![(33296583414633/100000000000000 : ℝ), (15683049901119/50000000000000 : ℝ), (17668658384641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310665299/10000000000 : ℝ)|^4361 ≤ (33296583414633/100000000000000 : ℝ)^3337
        have hw : |(4310665299/10000000000 : ℝ)|=(4310665299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4118090487/10000000000 : ℝ)|^4361 ≤ (15683049901119/50000000000000 : ℝ)^3337
        have hw : |(4118090487/10000000000 : ℝ)|=(4118090487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4511408787/10000000000 : ℝ)|^4361 ≤ (17668658384641/50000000000000 : ℝ)^3337
        have hw : |(4511408787/10000000000 : ℝ)|=(4511408787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s3_4 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-996423979/5000000000 : ℝ)*x 0 + (2618629767/5000000000 : ℝ)*x 1 + (5419464521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (996423979/5000000000 : ℝ)^4361 ≤ (12148120505907/100000000000000 : ℝ)^3337 := by
    have hnat : (996423979 : ℕ)^4361*100000000000000^3337 ≤ 12148120505907^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996423979 5000000000 12148120505907 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2618629767/5000000000 : ℝ)^4361 ≤ (42944513817289/100000000000000 : ℝ)^3337 := by
    have hnat : (2618629767 : ℕ)^4361*100000000000000^3337 ≤ 42944513817289^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618629767 5000000000 42944513817289 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419464521/10000000000 : ℝ)^4361 ≤ (44907365654533/100000000000000 : ℝ)^3337 := by
    have hnat : (5419464521 : ℕ)^4361*100000000000000^3337 ≤ 44907365654533^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419464521 10000000000 44907365654533 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-996423979/5000000000 : ℝ), (2618629767/5000000000 : ℝ), (5419464521/10000000000 : ℝ)] ![(12148120505907/100000000000000 : ℝ), (42944513817289/100000000000000 : ℝ), (44907365654533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-996423979/5000000000 : ℝ)|^4361 ≤ (12148120505907/100000000000000 : ℝ)^3337
        have hw : |(-996423979/5000000000 : ℝ)|=(996423979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2618629767/5000000000 : ℝ)|^4361 ≤ (42944513817289/100000000000000 : ℝ)^3337
        have hw : |(2618629767/5000000000 : ℝ)|=(2618629767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419464521/10000000000 : ℝ)|^4361 ≤ (44907365654533/100000000000000 : ℝ)^3337
        have hw : |(5419464521/10000000000 : ℝ)|=(5419464521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s3_5 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325748273/2500000000 : ℝ)*x 0 + (-475909317/2500000000 : ℝ)*x 1 + (1083892997/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325748273/2500000000 : ℝ)^4361 ≤ (43650268452421/100000000000000 : ℝ)^3337 := by
    have hnat : (1325748273 : ℕ)^4361*100000000000000^3337 ≤ 43650268452421^3337*2500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325748273 2500000000 43650268452421 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (475909317/2500000000 : ℝ)^4361 ≤ (2288472170021/20000000000000 : ℝ)^3337 := by
    have hnat : (475909317 : ℕ)^4361*20000000000000^3337 ≤ 2288472170021^3337*2500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475909317 2500000000 2288472170021 20000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083892997/2000000000 : ℝ)^4361 ≤ (44907370679221/100000000000000 : ℝ)^3337 := by
    have hnat : (1083892997 : ℕ)^4361*100000000000000^3337 ≤ 44907370679221^3337*2000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083892997 2000000000 44907370679221 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325748273/2500000000 : ℝ), (-475909317/2500000000 : ℝ), (1083892997/2000000000 : ℝ)] ![(43650268452421/100000000000000 : ℝ), (2288472170021/20000000000000 : ℝ), (44907370679221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325748273/2500000000 : ℝ)|^4361 ≤ (43650268452421/100000000000000 : ℝ)^3337
        have hw : |(1325748273/2500000000 : ℝ)|=(1325748273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-475909317/2500000000 : ℝ)|^4361 ≤ (2288472170021/20000000000000 : ℝ)^3337
        have hw : |(-475909317/2500000000 : ℝ)|=(475909317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083892997/2000000000 : ℝ)|^4361 ≤ (44907370679221/100000000000000 : ℝ)^3337
        have hw : |(1083892997/2000000000 : ℝ)|=(1083892997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s3_6 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265149703/500000000 : ℝ)*x 0 + (5419464259/10000000000 : ℝ)*x 1 + (-1903636943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265149703/500000000 : ℝ)^4361 ≤ (21825139432653/50000000000000 : ℝ)^3337 := by
    have hnat : (265149703 : ℕ)^4361*50000000000000^3337 ≤ 21825139432653^3337*500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265149703 500000000 21825139432653 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419464259/10000000000 : ℝ)^4361 ≤ (44907362817317/100000000000000 : ℝ)^3337 := by
    have hnat : (5419464259 : ℕ)^4361*100000000000000^3337 ≤ 44907362817317^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419464259 10000000000 44907362817317 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1903636943/10000000000 : ℝ)^4361 ≤ (5721179148571/50000000000000 : ℝ)^3337 := by
    have hnat : (1903636943 : ℕ)^4361*50000000000000^3337 ≤ 5721179148571^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1903636943 10000000000 5721179148571 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265149703/500000000 : ℝ), (5419464259/10000000000 : ℝ), (-1903636943/10000000000 : ℝ)] ![(21825139432653/50000000000000 : ℝ), (44907362817317/100000000000000 : ℝ), (5721179148571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265149703/500000000 : ℝ)|^4361 ≤ (21825139432653/50000000000000 : ℝ)^3337
        have hw : |(265149703/500000000 : ℝ)|=(265149703/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419464259/10000000000 : ℝ)|^4361 ≤ (44907362817317/100000000000000 : ℝ)^3337
        have hw : |(5419464259/10000000000 : ℝ)|=(5419464259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1903636943/10000000000 : ℝ)|^4361 ≤ (5721179148571/50000000000000 : ℝ)^3337
        have hw : |(-1903636943/10000000000 : ℝ)|=(1903636943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s3_7 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4310702591/10000000000 : ℝ)*x 0 + (4509818773/10000000000 : ℝ)*x 1 + (823937527/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310702591/10000000000 : ℝ)^4361 ≤ (6659391971921/20000000000000 : ℝ)^3337 := by
    have hnat : (4310702591 : ℕ)^4361*20000000000000^3337 ≤ 6659391971921^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310702591 10000000000 6659391971921 20000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4509818773/10000000000 : ℝ)^4361 ≤ (17660520739759/50000000000000 : ℝ)^3337 := by
    have hnat : (4509818773 : ℕ)^4361*50000000000000^3337 ≤ 17660520739759^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509818773 10000000000 17660520739759 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (823937527/2000000000 : ℝ)^4361 ≤ (31381998645101/100000000000000 : ℝ)^3337 := by
    have hnat : (823937527 : ℕ)^4361*100000000000000^3337 ≤ 31381998645101^3337*2000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823937527 2000000000 31381998645101 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310702591/10000000000 : ℝ), (4509818773/10000000000 : ℝ), (823937527/2000000000 : ℝ)] ![(6659391971921/20000000000000 : ℝ), (17660520739759/50000000000000 : ℝ), (31381998645101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310702591/10000000000 : ℝ)|^4361 ≤ (6659391971921/20000000000000 : ℝ)^3337
        have hw : |(4310702591/10000000000 : ℝ)|=(4310702591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4509818773/10000000000 : ℝ)|^4361 ≤ (17660520739759/50000000000000 : ℝ)^3337
        have hw : |(4509818773/10000000000 : ℝ)|=(4509818773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(823937527/2000000000 : ℝ)|^4361 ≤ (31381998645101/100000000000000 : ℝ)^3337
        have hw : |(823937527/2000000000 : ℝ)|=(823937527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1401_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15889/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10213/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5537/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14963/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15889/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10213/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15889/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10213/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15889/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10213/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15889/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10213/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15889/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10213/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15889/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10213/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10213/100000 : ℝ) ^ (545/128 : ℝ) ≤ (1510430266875717/25000000000000000000 : ℝ) := by
    have hpowers : (10213/100000 : ℝ)^545 ≤ (1510430266875717/25000000000000000000 : ℝ)^128 := by
      have hnat : (10213 : ℕ)^545*25000000000000000000^128 ≤ 1510430266875717^128*100000^545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10213 100000 1510430266875717 25000000000000000000 545 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10213/100000 : ℝ)) (X := (1510430266875717/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hpowhi : (15889/100000 : ℝ) ^ (545/128 : ℝ) ≤ (9916512804797297/25000000000000000000 : ℝ) := by
    have hpowers : (15889/100000 : ℝ)^545 ≤ (9916512804797297/25000000000000000000 : ℝ)^128 := by
      have hnat : (15889 : ℕ)^545*25000000000000000000^128 ≤ 9916512804797297^128*100000^545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15889 100000 9916512804797297 25000000000000000000 545 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15889/100000 : ℝ)) (X := (9916512804797297/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501510430266875717/12500000000000000000 : ℝ) ≤ (2000056756297219/2000000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (12501510430266875717/12500000000000000000 : ℝ)^128 ≤ (2000056756297219/2000000000000000 : ℝ)^545 := by
      have hnat : (12501510430266875717 : ℕ)^128*2000000000000000^545 ≤ 2000056756297219^545*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501510430266875717 12500000000000000000 2000056756297219 2000000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000056756297219/2000000000000000 : ℝ)) (X := (12501510430266875717/12500000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505713471535836507/12500000000000000000 : ℝ) ≤ (625067082248523/625000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (12505713471535836507/12500000000000000000 : ℝ)^128 ≤ (625067082248523/625000000000000 : ℝ)^545 := by
      have hnat : (12505713471535836507 : ℕ)^128*625000000000000^545 ≤ 625067082248523^545*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505713471535836507 12500000000000000000 625067082248523 625000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625067082248523/625000000000000 : ℝ)) (X := (12505713471535836507/12500000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509916512804797297/12500000000000000000 : ℝ) ≤ (10001862850466641/10000000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (12509916512804797297/12500000000000000000 : ℝ)^128 ≤ (10001862850466641/10000000000000000 : ℝ)^545 := by
      have hnat : (12509916512804797297 : ℕ)^128*10000000000000000^545 ≤ 10001862850466641^545*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509916512804797297 12500000000000000000 10001862850466641 10000000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001862850466641/10000000000000000 : ℝ)) (X := (12509916512804797297/12500000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1510430266875717/25000000000000000000 : ℝ) ≤ ((28372741856108379461/28380000000000000000 : ℝ)+2*(789534490273/567600000000000 : ℝ)*(10213/100000 : ℝ))^(545/128 : ℝ) := by
    rw [show (28372741856108379461/28380000000000000000 : ℝ)+2*(789534490273/567600000000000 : ℝ)*(10213/100000 : ℝ)=(2000056756297219/2000000000000000 : ℝ) by norm_num, show 1+2*(1510430266875717/25000000000000000000 : ℝ)=(12501510430266875717/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9916512804797297/25000000000000000000 : ℝ)+(1510430266875717/25000000000000000000 : ℝ) ≤ ((28372741856108379461/28380000000000000000 : ℝ)+(789534490273/567600000000000 : ℝ)*((15889/100000 : ℝ)+(10213/100000 : ℝ)))^(545/128 : ℝ) := by
    rw [show (28372741856108379461/28380000000000000000 : ℝ)+(789534490273/567600000000000 : ℝ)*((15889/100000 : ℝ)+(10213/100000 : ℝ))=(625067082248523/625000000000000 : ℝ) by norm_num, show 1+(9916512804797297/25000000000000000000 : ℝ)+(1510430266875717/25000000000000000000 : ℝ)=(12505713471535836507/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9916512804797297/25000000000000000000 : ℝ) ≤ ((28372741856108379461/28380000000000000000 : ℝ)+2*(789534490273/567600000000000 : ℝ)*(15889/100000 : ℝ))^(545/128 : ℝ) := by
    rw [show (28372741856108379461/28380000000000000000 : ℝ)+2*(789534490273/567600000000000 : ℝ)*(15889/100000 : ℝ)=(10001862850466641/10000000000000000 : ℝ) by norm_num, show 1+2*(9916512804797297/25000000000000000000 : ℝ)=(12509916512804797297/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28372741856108379461/28380000000000000000 : ℝ)*(X 1 0+X 2 0)+(789534490273/567600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (10213/100000 : ℝ)) (hi := (15889/100000 : ℝ)) (c := (28372741856108379461/28380000000000000000 : ℝ)) (alpha := (789534490273/567600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28372741856108379461/28380000000000000000 : ℝ)*(X 0 1+X 2 1)+(789534490273/567600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (10213/100000 : ℝ)) (hi := (15889/100000 : ℝ)) (c := (28372741856108379461/28380000000000000000 : ℝ)) (alpha := (789534490273/567600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28372741856108379461/28380000000000000000 : ℝ)*(X 0 2+X 1 2)+(789534490273/567600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (10213/100000 : ℝ)) (hi := (15889/100000 : ℝ)) (c := (28372741856108379461/28380000000000000000 : ℝ)) (alpha := (789534490273/567600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-996415353/5000000000 : ℝ)*X 0 0+(542021163/1000000000 : ℝ)*X 0 1+(5236517337/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675307327/5000000000 : ℝ)*X 1 0+(-52164627/250000000 : ℝ)*X 1 1+(5236516561/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675306941/5000000000 : ℝ)*X 2 0+(5236517101/10000000000 : ℝ)*X 2 1+(-2086585393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4310665299/10000000000 : ℝ)*X 0 0+(4118090487/10000000000 : ℝ)*X 0 1+(4511408787/10000000000 : ℝ)*X 0 2+(4310665299/10000000000 : ℝ)*X 1 0+(4118090487/10000000000 : ℝ)*X 1 1+(4511408787/10000000000 : ℝ)*X 1 2+(4310665299/10000000000 : ℝ)*X 2 0+(4118090487/10000000000 : ℝ)*X 2 1+(4511408787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-996423979/5000000000 : ℝ)*X 0 0+(2618629767/5000000000 : ℝ)*X 0 1+(5419464521/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325748273/2500000000 : ℝ)*X 1 0+(-475909317/2500000000 : ℝ)*X 1 1+(1083892997/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265149703/500000000 : ℝ)*X 2 0+(5419464259/10000000000 : ℝ)*X 2 1+(-1903636943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4310702591/10000000000 : ℝ)*X 0 0+(4509818773/10000000000 : ℝ)*X 0 1+(823937527/2000000000 : ℝ)*X 0 2+(4310702591/10000000000 : ℝ)*X 1 0+(4509818773/10000000000 : ℝ)*X 1 1+(823937527/2000000000 : ℝ)*X 1 2+(4310702591/10000000000 : ℝ)*X 2 0+(4509818773/10000000000 : ℝ)*X 2 1+(823937527/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18122853618334235262511/4730000000000000000000000000 : ℝ) := by norm_num
    linear_combination (361773257/100000000000000 : ℝ)*(base19) + (60990101/50000000000000 : ℝ)*(upper2) + (70700079/100000000000000 : ℝ)*(lower3) + (107015643/100000000000000 : ℝ)*(lower4) + (27889767/12500000000000 : ℝ)*(lower5) + (1996578749149597/50000000000000 : ℝ)*(major0) + (1996578749149597/50000000000000 : ℝ)*(major1) + (1996578749149597/50000000000000 : ℝ)*(major2) + (1088768532456699/20000000000000 : ℝ)*(sp0) + (2721916246905417/50000000000000 : ℝ)*(sp1) + (5443832371787979/100000000000000 : ℝ)*(sp2) + (2542472206599213/100000000000000 : ℝ)*(sp3) + (9806699403/100000000000000 : ℝ)*(sp5) + (2058099103/20000000000000 : ℝ)*(sp6) + (2542472206599213/100000000000000 : ℝ)*(f.failure) + (1088768532456699/20000000000000 : ℝ)*(f.sum) + (373615446989249/14190000000000000000000000000 : ℝ)*base66 + (744983446673520253/129000000000000000000000000000000 : ℝ)*base68 + (438828245258520253/129000000000000000000000000000000 : ℝ)*base70 + (408823304604479747/129000000000000000000000000000000 : ℝ)*base71 + (91507842739349/14190000000000000000000000000 : ℝ)*base74 + (134991064064520253/129000000000000000000000000000000 : ℝ)*base76 + (2477224801890479747/129000000000000000000000000000000 : ℝ)*base77 + (420405079920479747/129000000000000000000000000000000 : ℝ)*base79 + (7464509208571/14190000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (15292433/10000000000000000000000 : ℝ)*base90 + (15292433/10000000000000000000000 : ℝ)*base92 + (15292433/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1081605920658314722131884989/236500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (151027269/6250000000000 : ℝ)*(base19) + (376806047/10000000000000 : ℝ)*(base23) + (458945353/100000000000000 : ℝ)*(upper3) + (40018151/50000000000000 : ℝ)*(lower4) + (4157497/1562500000000 : ℝ)*(upper5) + (2012892518362483/50000000000000 : ℝ)*(major0) + (2012892518362483/50000000000000 : ℝ)*(major1) + (2012892518362483/50000000000000 : ℝ)*(major2) + (49334667619/100000000000000 : ℝ)*(sp1) + (14296529747/20000000000000 : ℝ)*(sp2) + (5488323525143839/100000000000000 : ℝ)*(sp4) + (1372067943509979/25000000000000 : ℝ)*(sp5) + (5488248274434633/100000000000000 : ℝ)*(sp6) + (2563246395859869/100000000000000 : ℝ)*(sp7) + (2563246395859869/100000000000000 : ℝ)*(f.failure) + (5488323525143839/100000000000000 : ℝ)*(f.sum) + (8739874124629/14190000000000000000000000000 : ℝ)*base65 + (23309553072171667/129000000000000000000000000000000 : ℝ)*base68 + (1037213971131171667/129000000000000000000000000000000 : ℝ)*base70 + (804564243978171667/129000000000000000000000000000000 : ℝ)*base72 + (17991514143349/14190000000000000000000000000 : ℝ)*base73 + (804503569731171667/129000000000000000000000000000000 : ℝ)*base76 + (850626293586171667/129000000000000000000000000000000 : ℝ)*base78 + (417364325196171667/129000000000000000000000000000000 : ℝ)*base80 + (83918771503931/14190000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (61134271/10000000000000000000000 : ℝ)*base89 + (61134271/10000000000000000000000 : ℝ)*base91 + (61134271/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1401_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15889/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10213/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5537/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14963/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1401_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1401_s4_0 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1993883337/10000000000 : ℝ)*x 0 + (5411344283/10000000000 : ℝ)*x 1 + (1048938431/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1993883337/10000000000 : ℝ)^4361 ≤ (12156369457817/100000000000000 : ℝ)^3337 := by
    have hnat : (1993883337 : ℕ)^4361*100000000000000^3337 ≤ 12156369457817^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993883337 10000000000 12156369457817 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411344283/10000000000 : ℝ)^4361 ≤ (22409725633709/50000000000000 : ℝ)^3337 := by
    have hnat : (5411344283 : ℕ)^4361*50000000000000^3337 ≤ 22409725633709^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411344283 10000000000 22409725633709 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048938431/2000000000 : ℝ)^4361 ≤ (43024179262467/100000000000000 : ℝ)^3337 := by
    have hnat : (1048938431 : ℕ)^4361*100000000000000^3337 ≤ 43024179262467^3337*2000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048938431 2000000000 43024179262467 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1993883337/10000000000 : ℝ), (5411344283/10000000000 : ℝ), (1048938431/2000000000 : ℝ)] ![(12156369457817/100000000000000 : ℝ), (22409725633709/50000000000000 : ℝ), (43024179262467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1993883337/10000000000 : ℝ)|^4361 ≤ (12156369457817/100000000000000 : ℝ)^3337
        have hw : |(-1993883337/10000000000 : ℝ)|=(1993883337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411344283/10000000000 : ℝ)|^4361 ≤ (22409725633709/50000000000000 : ℝ)^3337
        have hw : |(5411344283/10000000000 : ℝ)|=(5411344283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048938431/2000000000 : ℝ)|^4361 ≤ (43024179262467/100000000000000 : ℝ)^3337
        have hw : |(1048938431/2000000000 : ℝ)|=(1048938431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s4_1 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348334083/10000000000 : ℝ)*x 0 + (-207877879/1000000000 : ℝ)*x 1 + (5244692779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348334083/10000000000 : ℝ)^4361 ≤ (11034661300759/25000000000000 : ℝ)^3337 := by
    have hnat : (5348334083 : ℕ)^4361*25000000000000^3337 ≤ 11034661300759^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348334083 10000000000 11034661300759 25000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207877879/1000000000 : ℝ)^4361 ≤ (102697350573/800000000000 : ℝ)^3337 := by
    have hnat : (207877879 : ℕ)^4361*800000000000^3337 ≤ 102697350573^3337*1000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207877879 1000000000 102697350573 800000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244692779/10000000000 : ℝ)^4361 ≤ (21512092976087/50000000000000 : ℝ)^3337 := by
    have hnat : (5244692779 : ℕ)^4361*50000000000000^3337 ≤ 21512092976087^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244692779 10000000000 21512092976087 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348334083/10000000000 : ℝ), (-207877879/1000000000 : ℝ), (5244692779/10000000000 : ℝ)] ![(11034661300759/25000000000000 : ℝ), (102697350573/800000000000 : ℝ), (21512092976087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348334083/10000000000 : ℝ)|^4361 ≤ (11034661300759/25000000000000 : ℝ)^3337
        have hw : |(5348334083/10000000000 : ℝ)|=(5348334083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-207877879/1000000000 : ℝ)|^4361 ≤ (102697350573/800000000000 : ℝ)^3337
        have hw : |(-207877879/1000000000 : ℝ)|=(207877879/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244692779/10000000000 : ℝ)|^4361 ≤ (21512092976087/50000000000000 : ℝ)^3337
        have hw : |(5244692779/10000000000 : ℝ)|=(5244692779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s4_2 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337083547/2500000000 : ℝ)*x 0 + (5244692601/10000000000 : ℝ)*x 1 + (-259847361/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337083547/2500000000 : ℝ)^4361 ≤ (44138646335487/100000000000000 : ℝ)^3337 := by
    have hnat : (1337083547 : ℕ)^4361*100000000000000^3337 ≤ 44138646335487^3337*2500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337083547 2500000000 44138646335487 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244692601/10000000000 : ℝ)^4361 ≤ (10756046010973/25000000000000 : ℝ)^3337 := by
    have hnat : (5244692601 : ℕ)^4361*25000000000000^3337 ≤ 10756046010973^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244692601 10000000000 10756046010973 25000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259847361/1250000000 : ℝ)^4361 ≤ (12837169612517/100000000000000 : ℝ)^3337 := by
    have hnat : (259847361 : ℕ)^4361*100000000000000^3337 ≤ 12837169612517^3337*1250000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259847361 1250000000 12837169612517 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337083547/2500000000 : ℝ), (5244692601/10000000000 : ℝ), (-259847361/1250000000 : ℝ)] ![(44138646335487/100000000000000 : ℝ), (10756046010973/25000000000000 : ℝ), (12837169612517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337083547/2500000000 : ℝ)|^4361 ≤ (44138646335487/100000000000000 : ℝ)^3337
        have hw : |(1337083547/2500000000 : ℝ)|=(1337083547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244692601/10000000000 : ℝ)|^4361 ≤ (10756046010973/25000000000000 : ℝ)^3337
        have hw : |(5244692601/10000000000 : ℝ)|=(5244692601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-259847361/1250000000 : ℝ)|^4361 ≤ (12837169612517/100000000000000 : ℝ)^3337
        have hw : |(-259847361/1250000000 : ℝ)|=(259847361/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s4_3 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1077827469/2500000000 : ℝ)*x 0 + (4136256411/10000000000 : ℝ)*x 1 + (4493085287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077827469/2500000000 : ℝ)^4361 ≤ (33303090252979/100000000000000 : ℝ)^3337 := by
    have hnat : (1077827469 : ℕ)^4361*100000000000000^3337 ≤ 33303090252979^3337*2500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077827469 2500000000 33303090252979 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4136256411/10000000000 : ℝ)^4361 ≤ (246461284143/781250000000 : ℝ)^3337 := by
    have hnat : (4136256411 : ℕ)^4361*781250000000^3337 ≤ 246461284143^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4136256411 10000000000 246461284143 781250000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493085287/10000000000 : ℝ)^4361 ≤ (4393733169417/12500000000000 : ℝ)^3337 := by
    have hnat : (4493085287 : ℕ)^4361*12500000000000^3337 ≤ 4393733169417^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493085287 10000000000 4393733169417 12500000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077827469/2500000000 : ℝ), (4136256411/10000000000 : ℝ), (4493085287/10000000000 : ℝ)] ![(33303090252979/100000000000000 : ℝ), (246461284143/781250000000 : ℝ), (4393733169417/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077827469/2500000000 : ℝ)|^4361 ≤ (33303090252979/100000000000000 : ℝ)^3337
        have hw : |(1077827469/2500000000 : ℝ)|=(1077827469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4136256411/10000000000 : ℝ)|^4361 ≤ (246461284143/781250000000 : ℝ)^3337
        have hw : |(4136256411/10000000000 : ℝ)|=(4136256411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493085287/10000000000 : ℝ)|^4361 ≤ (4393733169417/12500000000000 : ℝ)^3337
        have hw : |(4493085287/10000000000 : ℝ)|=(4493085287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s4_4 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-996947733/5000000000 : ℝ)*x 0 + (5245303657/10000000000 : ℝ)*x 1 + (5410729673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (996947733/5000000000 : ℝ)^4361 ≤ (97251728787/800000000000 : ℝ)^3337 := by
    have hnat : (996947733 : ℕ)^4361*800000000000^3337 ≤ 97251728787^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996947733 5000000000 97251728787 800000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245303657/10000000000 : ℝ)^4361 ≤ (4303073509911/10000000000000 : ℝ)^3337 := by
    have hnat : (5245303657 : ℕ)^4361*10000000000000^3337 ≤ 4303073509911^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245303657 10000000000 4303073509911 10000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410729673/10000000000 : ℝ)^4361 ≤ (22406399395811/50000000000000 : ℝ)^3337 := by
    have hnat : (5410729673 : ℕ)^4361*50000000000000^3337 ≤ 22406399395811^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410729673 10000000000 22406399395811 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-996947733/5000000000 : ℝ), (5245303657/10000000000 : ℝ), (5410729673/10000000000 : ℝ)] ![(97251728787/800000000000 : ℝ), (4303073509911/10000000000000 : ℝ), (22406399395811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-996947733/5000000000 : ℝ)|^4361 ≤ (97251728787/800000000000 : ℝ)^3337
        have hw : |(-996947733/5000000000 : ℝ)|=(996947733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245303657/10000000000 : ℝ)|^4361 ≤ (4303073509911/10000000000000 : ℝ)^3337
        have hw : |(5245303657/10000000000 : ℝ)|=(5245303657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410729673/10000000000 : ℝ)|^4361 ≤ (22406399395811/50000000000000 : ℝ)^3337
        have hw : |(5410729673/10000000000 : ℝ)|=(5410729673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s4_5 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305131291/10000000000 : ℝ)*x 0 + (-1912741399/10000000000 : ℝ)*x 1 + (1082145967/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305131291/10000000000 : ℝ)^4361 ≤ (8734654144769/20000000000000 : ℝ)^3337 := by
    have hnat : (5305131291 : ℕ)^4361*20000000000000^3337 ≤ 8734654144769^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305131291 10000000000 8734654144769 20000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1912741399/10000000000 : ℝ)^4361 ≤ (2878482177457/25000000000000 : ℝ)^3337 := by
    have hnat : (1912741399 : ℕ)^4361*25000000000000^3337 ≤ 2878482177457^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912741399 10000000000 2878482177457 25000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082145967/2000000000 : ℝ)^4361 ≤ (44812800545063/100000000000000 : ℝ)^3337 := by
    have hnat : (1082145967 : ℕ)^4361*100000000000000^3337 ≤ 44812800545063^3337*2000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082145967 2000000000 44812800545063 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305131291/10000000000 : ℝ), (-1912741399/10000000000 : ℝ), (1082145967/2000000000 : ℝ)] ![(8734654144769/20000000000000 : ℝ), (2878482177457/25000000000000 : ℝ), (44812800545063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305131291/10000000000 : ℝ)|^4361 ≤ (8734654144769/20000000000000 : ℝ)^3337
        have hw : |(5305131291/10000000000 : ℝ)|=(5305131291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1912741399/10000000000 : ℝ)|^4361 ≤ (2878482177457/25000000000000 : ℝ)^3337
        have hw : |(-1912741399/10000000000 : ℝ)|=(1912741399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082145967/2000000000 : ℝ)|^4361 ≤ (44812800545063/100000000000000 : ℝ)^3337
        have hw : |(1082145967/2000000000 : ℝ)|=(1082145967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s4_6 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305131253/10000000000 : ℝ)*x 0 + (1082145951/2000000000 : ℝ)*x 1 + (-956370781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305131253/10000000000 : ℝ)^4361 ≤ (2729579394689/6250000000000 : ℝ)^3337 := by
    have hnat : (5305131253 : ℕ)^4361*6250000000000^3337 ≤ 2729579394689^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305131253 10000000000 2729579394689 6250000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082145951/2000000000 : ℝ)^4361 ≤ (44812799679167/100000000000000 : ℝ)^3337 := by
    have hnat : (1082145951 : ℕ)^4361*100000000000000^3337 ≤ 44812799679167^3337*2000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082145951 2000000000 44812799679167 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (956370781/5000000000 : ℝ)^4361 ≤ (5756964996057/50000000000000 : ℝ)^3337 := by
    have hnat : (956370781 : ℕ)^4361*50000000000000^3337 ≤ 5756964996057^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956370781 5000000000 5756964996057 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305131253/10000000000 : ℝ), (1082145951/2000000000 : ℝ), (-956370781/5000000000 : ℝ)] ![(2729579394689/6250000000000 : ℝ), (44812799679167/100000000000000 : ℝ), (5756964996057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305131253/10000000000 : ℝ)|^4361 ≤ (2729579394689/6250000000000 : ℝ)^3337
        have hw : |(5305131253/10000000000 : ℝ)|=(5305131253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082145951/2000000000 : ℝ)|^4361 ≤ (44812799679167/100000000000000 : ℝ)^3337
        have hw : |(1082145951/2000000000 : ℝ)|=(1082145951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-956370781/5000000000 : ℝ)|^4361 ≤ (5756964996057/50000000000000 : ℝ)^3337
        have hw : |(-956370781/5000000000 : ℝ)|=(956370781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s4_7 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4311336041/10000000000 : ℝ)*x 0 + (4491776117/10000000000 : ℝ)*x 1 + (2068786313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311336041/10000000000 : ℝ)^4361 ≤ (16651677194101/50000000000000 : ℝ)^3337 := by
    have hnat : (4311336041 : ℕ)^4361*50000000000000^3337 ≤ 16651677194101^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311336041 10000000000 16651677194101 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4491776117/10000000000 : ℝ)^4361 ≤ (3513648136819/10000000000000 : ℝ)^3337 := by
    have hnat : (4491776117 : ℕ)^4361*10000000000000^3337 ≤ 3513648136819^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491776117 10000000000 3513648136819 10000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2068786313/5000000000 : ℝ)^4361 ≤ (63120328457/200000000000 : ℝ)^3337 := by
    have hnat : (2068786313 : ℕ)^4361*200000000000^3337 ≤ 63120328457^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068786313 5000000000 63120328457 200000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311336041/10000000000 : ℝ), (4491776117/10000000000 : ℝ), (2068786313/5000000000 : ℝ)] ![(16651677194101/50000000000000 : ℝ), (3513648136819/10000000000000 : ℝ), (63120328457/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311336041/10000000000 : ℝ)|^4361 ≤ (16651677194101/50000000000000 : ℝ)^3337
        have hw : |(4311336041/10000000000 : ℝ)|=(4311336041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4491776117/10000000000 : ℝ)|^4361 ≤ (3513648136819/10000000000000 : ℝ)^3337
        have hw : |(4491776117/10000000000 : ℝ)|=(4491776117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2068786313/5000000000 : ℝ)|^4361 ≤ (63120328457/200000000000 : ℝ)^3337
        have hw : |(2068786313/5000000000 : ℝ)|=(2068786313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1401_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14963/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5537/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (703/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14777/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14963/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5537/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14963/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5537/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14963/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5537/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14963/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5537/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14963/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5537/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14963/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5537/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5537/50000 : ℝ) ^ (545/128 : ℝ) ≤ (852761992289833/10000000000000000000 : ℝ) := by
    have hpowers : (5537/50000 : ℝ)^545 ≤ (852761992289833/10000000000000000000 : ℝ)^128 := by
      have hnat : (5537 : ℕ)^545*10000000000000000000^128 ≤ 852761992289833^128*50000^545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5537 50000 852761992289833 10000000000000000000 545 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5537/50000 : ℝ)) (X := (852761992289833/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14963/100000 : ℝ) ^ (545/128 : ℝ) ≤ (30717382531741209/100000000000000000000 : ℝ) := by
    have hpowers : (14963/100000 : ℝ)^545 ≤ (30717382531741209/100000000000000000000 : ℝ)^128 := by
      have hnat : (14963 : ℕ)^545*100000000000000000000^128 ≤ 30717382531741209^128*100000^545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14963 100000 30717382531741209 100000000000000000000 545 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14963/100000 : ℝ)) (X := (30717382531741209/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000852761992289833/5000000000000000000 : ℝ) ≤ (1000040053729789/1000000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (5000852761992289833/5000000000000000000 : ℝ)^128 ≤ (1000040053729789/1000000000000000 : ℝ)^545 := by
      have hnat : (5000852761992289833 : ℕ)^128*1000000000000000^545 ≤ 1000040053729789^545*5000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000852761992289833 5000000000000000000 1000040053729789 1000000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000040053729789/1000000000000000 : ℝ)) (X := (5000852761992289833/5000000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039245002454639539/100000000000000000000 : ℝ) ≤ (250023039478373/250000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (100039245002454639539/100000000000000000000 : ℝ)^128 ≤ (250023039478373/250000000000000 : ℝ)^545 := by
      have hnat : (100039245002454639539 : ℕ)^128*250000000000000^545 ≤ 250023039478373^545*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039245002454639539 100000000000000000000 250023039478373 250000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250023039478373/250000000000000 : ℝ)) (X := (100039245002454639539/100000000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030717382531741209/50000000000000000000 : ℝ) ≤ (200028852419439/200000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (50030717382531741209/50000000000000000000 : ℝ)^128 ≤ (200028852419439/200000000000000 : ℝ)^545 := by
      have hnat : (50030717382531741209 : ℕ)^128*200000000000000^545 ≤ 200028852419439^545*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030717382531741209 50000000000000000000 200028852419439 200000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200028852419439/200000000000000 : ℝ)) (X := (50030717382531741209/50000000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(852761992289833/10000000000000000000 : ℝ) ≤ ((3888001765494495377/3889000000000000000 : ℝ)+2*(52104183703/38890000000000 : ℝ)*(5537/50000 : ℝ))^(545/128 : ℝ) := by
    rw [show (3888001765494495377/3889000000000000000 : ℝ)+2*(52104183703/38890000000000 : ℝ)*(5537/50000 : ℝ)=(1000040053729789/1000000000000000 : ℝ) by norm_num, show 1+2*(852761992289833/10000000000000000000 : ℝ)=(5000852761992289833/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30717382531741209/100000000000000000000 : ℝ)+(852761992289833/10000000000000000000 : ℝ) ≤ ((3888001765494495377/3889000000000000000 : ℝ)+(52104183703/38890000000000 : ℝ)*((14963/100000 : ℝ)+(5537/50000 : ℝ)))^(545/128 : ℝ) := by
    rw [show (3888001765494495377/3889000000000000000 : ℝ)+(52104183703/38890000000000 : ℝ)*((14963/100000 : ℝ)+(5537/50000 : ℝ))=(250023039478373/250000000000000 : ℝ) by norm_num, show 1+(30717382531741209/100000000000000000000 : ℝ)+(852761992289833/10000000000000000000 : ℝ)=(100039245002454639539/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30717382531741209/100000000000000000000 : ℝ) ≤ ((3888001765494495377/3889000000000000000 : ℝ)+2*(52104183703/38890000000000 : ℝ)*(14963/100000 : ℝ))^(545/128 : ℝ) := by
    rw [show (3888001765494495377/3889000000000000000 : ℝ)+2*(52104183703/38890000000000 : ℝ)*(14963/100000 : ℝ)=(200028852419439/200000000000000 : ℝ) by norm_num, show 1+2*(30717382531741209/100000000000000000000 : ℝ)=(50030717382531741209/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3888001765494495377/3889000000000000000 : ℝ)*(X 1 0+X 2 0)+(52104183703/38890000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (5537/50000 : ℝ)) (hi := (14963/100000 : ℝ)) (c := (3888001765494495377/3889000000000000000 : ℝ)) (alpha := (52104183703/38890000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3888001765494495377/3889000000000000000 : ℝ)*(X 0 1+X 2 1)+(52104183703/38890000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (5537/50000 : ℝ)) (hi := (14963/100000 : ℝ)) (c := (3888001765494495377/3889000000000000000 : ℝ)) (alpha := (52104183703/38890000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3888001765494495377/3889000000000000000 : ℝ)*(X 0 2+X 1 2)+(52104183703/38890000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (5537/50000 : ℝ)) (hi := (14963/100000 : ℝ)) (c := (3888001765494495377/3889000000000000000 : ℝ)) (alpha := (52104183703/38890000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1993883337/10000000000 : ℝ)*X 0 0+(5411344283/10000000000 : ℝ)*X 0 1+(1048938431/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348334083/10000000000 : ℝ)*X 1 0+(-207877879/1000000000 : ℝ)*X 1 1+(5244692779/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337083547/2500000000 : ℝ)*X 2 0+(5244692601/10000000000 : ℝ)*X 2 1+(-259847361/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1077827469/2500000000 : ℝ)*X 0 0+(4136256411/10000000000 : ℝ)*X 0 1+(4493085287/10000000000 : ℝ)*X 0 2+(1077827469/2500000000 : ℝ)*X 1 0+(4136256411/10000000000 : ℝ)*X 1 1+(4493085287/10000000000 : ℝ)*X 1 2+(1077827469/2500000000 : ℝ)*X 2 0+(4136256411/10000000000 : ℝ)*X 2 1+(4493085287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-996947733/5000000000 : ℝ)*X 0 0+(5245303657/10000000000 : ℝ)*X 0 1+(5410729673/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305131291/10000000000 : ℝ)*X 1 0+(-1912741399/10000000000 : ℝ)*X 1 1+(1082145967/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305131253/10000000000 : ℝ)*X 2 0+(1082145951/2000000000 : ℝ)*X 2 1+(-956370781/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4311336041/10000000000 : ℝ)*X 0 0+(4491776117/10000000000 : ℝ)*X 0 1+(2068786313/5000000000 : ℝ)*X 0 2+(4311336041/10000000000 : ℝ)*X 1 0+(4491776117/10000000000 : ℝ)*X 1 1+(2068786313/5000000000 : ℝ)*X 1 2+(4311336041/10000000000 : ℝ)*X 2 0+(4491776117/10000000000 : ℝ)*X 2 1+(2068786313/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1772362018691086050885163869/194450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1234140747/100000000000000 : ℝ)*(base19) + (1211314899/100000000000000 : ℝ)*(base23) + (384140881/100000000000000 : ℝ)*(upper3) + (75214287/100000000000000 : ℝ)*(upper4) + (184273141/100000000000000 : ℝ)*(upper5) + (440154750725787/10000000000000 : ℝ)*(major0) + (440154750725787/10000000000000 : ℝ)*(major1) + (4401547507257871/100000000000000 : ℝ)*(major2) + (1500140718955033/25000000000000 : ℝ)*(sp0) + (6000596402994801/100000000000000 : ℝ)*(sp1) + (6000596425820649/100000000000000 : ℝ)*(sp2) + (2802478447231539/100000000000000 : ℝ)*(sp3) + (4345164427/12500000000000 : ℝ)*(sp4) + (18626323833/100000000000000 : ℝ)*(sp7) + (700624268388843/25000000000000 : ℝ)*(f.failure) + (1500149409283887/25000000000000 : ℝ)*(f.sum) + (710448955837/388900000000000000000000000 : ℝ)*base65 + (517673689120303301/38890000000000000000000000000000 : ℝ)*base68 + (3996206351744262367/388900000000000000000000000000000 : ℝ)*base69 + (14235646777316699/38890000000000000000000000000000 : ℝ)*base71 + (9350150316877/3889000000000000000000000000 : ℝ)*base74 + (8886919979260362367/388900000000000000000000000000000 : ℝ)*base75 + (590750546682523301/38890000000000000000000000000000 : ℝ)*base78 + (489164760814423301/38890000000000000000000000000000 : ℝ)*base80 + (26332087855349/3889000000000000000000000000 : ℝ)*base81 + (11164263/2500000000000000000000 : ℝ)*base90 + (11164263/2500000000000000000000 : ℝ)*base92 + (36164263/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (187286058509706467284731987/48612500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (543384541/100000000000000 : ℝ)*(base19) + (4436773/800000000000 : ℝ)*(base23) + (1755831/3125000000000 : ℝ)*(upper2) + (18071881/25000000000000 : ℝ)*(upper3) + (144702253/100000000000000 : ℝ)*(upper5) + (2217058307727023/50000000000000 : ℝ)*(major0) + (2217058307727023/50000000000000 : ℝ)*(major1) + (2217058307727023/50000000000000 : ℝ)*(major2) + (2070436219/12500000000000 : ℝ)*(sp1) + (10251956229/100000000000000 : ℝ)*(sp2) + (1511249760655001/25000000000000 : ℝ)*(sp4) + (6044981935745711/100000000000000 : ℝ)*(sp5) + (120899764721343/2000000000000 : ℝ)*(sp6) + (176452128741689/6250000000000 : ℝ)*(sp7) + (176452128741689/6250000000000 : ℝ)*(f.failure) + (1511249760655001/25000000000000 : ℝ)*(f.sum) + (2011342741999/972250000000000000000000000 : ℝ)*base65 + (954358051911827329/194450000000000000000000000000000 : ℝ)*base68 + (1539668677292172671/194450000000000000000000000000000 : ℝ)*base69 + (1679320997938922671/194450000000000000000000000000000 : ℝ)*base71 + (3750439090199/777800000000000000000000000 : ℝ)*base74 + (3186716606487722671/194450000000000000000000000000000 : ℝ)*base75 + (2491356703990672671/194450000000000000000000000000000 : ℝ)*base77 + (1602143134531222671/194450000000000000000000000000000 : ℝ)*base79 + (660372948629/486125000000000000000000000 : ℝ)*base82 + (778349/625000000000000000000 : ℝ)*base90 + (778349/625000000000000000000 : ℝ)*base92 + (778349/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1401_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14963/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5537/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (703/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14777/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1401_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1401_s5_0 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1994050741/10000000000 : ℝ)*x 0 + (2704947283/5000000000 : ℝ)*x 1 + (1311507831/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1994050741/10000000000 : ℝ)^4361 ≤ (3039425825771/25000000000000 : ℝ)^3337 := by
    have hnat : (1994050741 : ℕ)^4361*25000000000000^3337 ≤ 3039425825771^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994050741 10000000000 3039425825771 25000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704947283/5000000000 : ℝ)^4361 ≤ (22401880025217/50000000000000 : ℝ)^3337 := by
    have hnat : (2704947283 : ℕ)^4361*50000000000000^3337 ≤ 22401880025217^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704947283 5000000000 22401880025217 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311507831/2500000000 : ℝ)^4361 ≤ (2151926831591/5000000000000 : ℝ)^3337 := by
    have hnat : (1311507831 : ℕ)^4361*5000000000000^3337 ≤ 2151926831591^3337*2500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311507831 2500000000 2151926831591 5000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1994050741/10000000000 : ℝ), (2704947283/5000000000 : ℝ), (1311507831/2500000000 : ℝ)] ![(3039425825771/25000000000000 : ℝ), (22401880025217/50000000000000 : ℝ), (2151926831591/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1994050741/10000000000 : ℝ)|^4361 ≤ (3039425825771/25000000000000 : ℝ)^3337
        have hw : |(-1994050741/10000000000 : ℝ)|=(1994050741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704947283/5000000000 : ℝ)|^4361 ≤ (22401880025217/50000000000000 : ℝ)^3337
        have hw : |(2704947283/5000000000 : ℝ)|=(2704947283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311507831/2500000000 : ℝ)|^4361 ≤ (2151926831591/5000000000000 : ℝ)^3337
        have hw : |(1311507831/2500000000 : ℝ)|=(1311507831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s5_1 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347959111/10000000000 : ℝ)*x 0 + (-1038748891/5000000000 : ℝ)*x 1 + (262301709/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347959111/10000000000 : ℝ)^4361 ≤ (22067300539261/50000000000000 : ℝ)^3337 := by
    have hnat : (5347959111 : ℕ)^4361*50000000000000^3337 ≤ 22067300539261^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347959111 10000000000 22067300539261 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1038748891/5000000000 : ℝ)^4361 ≤ (320670791309/2500000000000 : ℝ)^3337 := by
    have hnat : (1038748891 : ℕ)^4361*2500000000000^3337 ≤ 320670791309^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038748891 5000000000 320670791309 2500000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262301709/500000000 : ℝ)^4361 ≤ (21519283626247/50000000000000 : ℝ)^3337 := by
    have hnat : (262301709 : ℕ)^4361*50000000000000^3337 ≤ 21519283626247^3337*500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262301709 500000000 21519283626247 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347959111/10000000000 : ℝ), (-1038748891/5000000000 : ℝ), (262301709/500000000 : ℝ)] ![(22067300539261/50000000000000 : ℝ), (320670791309/2500000000000 : ℝ), (21519283626247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347959111/10000000000 : ℝ)|^4361 ≤ (22067300539261/50000000000000 : ℝ)^3337
        have hw : |(5347959111/10000000000 : ℝ)|=(5347959111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1038748891/5000000000 : ℝ)|^4361 ≤ (320670791309/2500000000000 : ℝ)^3337
        have hw : |(-1038748891/5000000000 : ℝ)|=(1038748891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262301709/500000000 : ℝ)|^4361 ≤ (21519283626247/50000000000000 : ℝ)^3337
        have hw : |(262301709/500000000 : ℝ)|=(262301709/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s5_2 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213918403/400000000 : ℝ)*x 0 + (1311508039/2500000000 : ℝ)*x 1 + (-2077499183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213918403/400000000 : ℝ)^4361 ≤ (44134611475283/100000000000000 : ℝ)^3337 := by
    have hnat : (213918403 : ℕ)^4361*100000000000000^3337 ≤ 44134611475283^3337*400000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213918403 400000000 44134611475283 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311508039/2500000000 : ℝ)^4361 ≤ (168119318563/390625000000 : ℝ)^3337 := by
    have hnat : (1311508039 : ℕ)^4361*390625000000^3337 ≤ 168119318563^3337*2500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311508039 2500000000 168119318563 390625000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2077499183/10000000000 : ℝ)^4361 ≤ (1603355369593/12500000000000 : ℝ)^3337 := by
    have hnat : (2077499183 : ℕ)^4361*12500000000000^3337 ≤ 1603355369593^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077499183 10000000000 1603355369593 12500000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213918403/400000000 : ℝ), (1311508039/2500000000 : ℝ), (-2077499183/10000000000 : ℝ)] ![(44134611475283/100000000000000 : ℝ), (168119318563/390625000000 : ℝ), (1603355369593/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213918403/400000000 : ℝ)|^4361 ≤ (44134611475283/100000000000000 : ℝ)^3337
        have hw : |(213918403/400000000 : ℝ)|=(213918403/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311508039/2500000000 : ℝ)|^4361 ≤ (168119318563/390625000000 : ℝ)^3337
        have hw : |(1311508039/2500000000 : ℝ)|=(1311508039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2077499183/10000000000 : ℝ)|^4361 ≤ (1603355369593/12500000000000 : ℝ)^3337
        have hw : |(-2077499183/10000000000 : ℝ)|=(2077499183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s5_3 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4311409983/10000000000 : ℝ)*x 0 + (517404169/1250000000 : ℝ)*x 1 + (561260439/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311409983/10000000000 : ℝ)^4361 ≤ (33304100834073/100000000000000 : ℝ)^3337 := by
    have hnat : (4311409983 : ℕ)^4361*100000000000000^3337 ≤ 33304100834073^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311409983 10000000000 33304100834073 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517404169/1250000000 : ℝ)^4361 ≤ (31576719954559/100000000000000 : ℝ)^3337 := by
    have hnat : (517404169 : ℕ)^4361*100000000000000^3337 ≤ 31576719954559^3337*1250000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517404169 1250000000 31576719954559 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561260439/1250000000 : ℝ)^4361 ≤ (2194948699939/6250000000000 : ℝ)^3337 := by
    have hnat : (561260439 : ℕ)^4361*6250000000000^3337 ≤ 2194948699939^3337*1250000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561260439 1250000000 2194948699939 6250000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311409983/10000000000 : ℝ), (517404169/1250000000 : ℝ), (561260439/1250000000 : ℝ)] ![(33304100834073/100000000000000 : ℝ), (31576719954559/100000000000000 : ℝ), (2194948699939/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311409983/10000000000 : ℝ)|^4361 ≤ (33304100834073/100000000000000 : ℝ)^3337
        have hw : |(4311409983/10000000000 : ℝ)|=(4311409983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517404169/1250000000 : ℝ)|^4361 ≤ (31576719954559/100000000000000 : ℝ)^3337
        have hw : |(517404169/1250000000 : ℝ)|=(517404169/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561260439/1250000000 : ℝ)|^4361 ≤ (2194948699939/6250000000000 : ℝ)^3337
        have hw : |(561260439/1250000000 : ℝ)|=(561260439/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s5_4 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1994062619/10000000000 : ℝ)*x 0 + (5246623907/10000000000 : ℝ)*x 1 + (1081859757/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1994062619/10000000000 : ℝ)^4361 ≤ (12157797946179/100000000000000 : ℝ)^3337 := by
    have hnat : (1994062619 : ℕ)^4361*100000000000000^3337 ≤ 12157797946179^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994062619 10000000000 12157797946179 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246623907/10000000000 : ℝ)^4361 ≤ (21522445067209/50000000000000 : ℝ)^3337 := by
    have hnat : (5246623907 : ℕ)^4361*50000000000000^3337 ≤ 21522445067209^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246623907 10000000000 21522445067209 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081859757/2000000000 : ℝ)^4361 ≤ (22398655952293/50000000000000 : ℝ)^3337 := by
    have hnat : (1081859757 : ℕ)^4361*50000000000000^3337 ≤ 22398655952293^3337*2000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081859757 2000000000 22398655952293 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1994062619/10000000000 : ℝ), (5246623907/10000000000 : ℝ), (1081859757/2000000000 : ℝ)] ![(12157797946179/100000000000000 : ℝ), (21522445067209/50000000000000 : ℝ), (22398655952293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1994062619/10000000000 : ℝ)|^4361 ≤ (12157797946179/100000000000000 : ℝ)^3337
        have hw : |(-1994062619/10000000000 : ℝ)|=(1994062619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246623907/10000000000 : ℝ)|^4361 ≤ (21522445067209/50000000000000 : ℝ)^3337
        have hw : |(5246623907/10000000000 : ℝ)|=(5246623907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081859757/2000000000 : ℝ)|^4361 ≤ (22398655952293/50000000000000 : ℝ)^3337
        have hw : |(1081859757/2000000000 : ℝ)|=(1081859757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s5_5 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652740183/5000000000 : ℝ)*x 0 + (-382846539/2000000000 : ℝ)*x 1 + (1081859757/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652740183/5000000000 : ℝ)^4361 ≤ (2183851313279/5000000000000 : ℝ)^3337 := by
    have hnat : (2652740183 : ℕ)^4361*5000000000000^3337 ≤ 2183851313279^3337*5000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652740183 5000000000 2183851313279 5000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (382846539/2000000000 : ℝ)^4361 ≤ (11525661814669/100000000000000 : ℝ)^3337 := by
    have hnat : (382846539 : ℕ)^4361*100000000000000^3337 ≤ 11525661814669^3337*2000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382846539 2000000000 11525661814669 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081859757/2000000000 : ℝ)^4361 ≤ (22398655952293/50000000000000 : ℝ)^3337 := by
    have hnat : (1081859757 : ℕ)^4361*50000000000000^3337 ≤ 22398655952293^3337*2000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081859757 2000000000 22398655952293 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652740183/5000000000 : ℝ), (-382846539/2000000000 : ℝ), (1081859757/2000000000 : ℝ)] ![(2183851313279/5000000000000 : ℝ), (11525661814669/100000000000000 : ℝ), (22398655952293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652740183/5000000000 : ℝ)|^4361 ≤ (2183851313279/5000000000000 : ℝ)^3337
        have hw : |(2652740183/5000000000 : ℝ)|=(2652740183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-382846539/2000000000 : ℝ)|^4361 ≤ (11525661814669/100000000000000 : ℝ)^3337
        have hw : |(-382846539/2000000000 : ℝ)|=(382846539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081859757/2000000000 : ℝ)|^4361 ≤ (22398655952293/50000000000000 : ℝ)^3337
        have hw : |(1081859757/2000000000 : ℝ)|=(1081859757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s5_6 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326370091/2500000000 : ℝ)*x 0 + (5409298787/10000000000 : ℝ)*x 1 + (-382846539/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326370091/2500000000 : ℝ)^4361 ≤ (21838513122031/50000000000000 : ℝ)^3337 := by
    have hnat : (1326370091 : ℕ)^4361*50000000000000^3337 ≤ 21838513122031^3337*2500000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326370091 2500000000 21838513122031 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409298787/10000000000 : ℝ)^4361 ≤ (5599663990779/12500000000000 : ℝ)^3337 := by
    have hnat : (5409298787 : ℕ)^4361*12500000000000^3337 ≤ 5599663990779^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409298787 10000000000 5599663990779 12500000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (382846539/2000000000 : ℝ)^4361 ≤ (11525661814669/100000000000000 : ℝ)^3337 := by
    have hnat : (382846539 : ℕ)^4361*100000000000000^3337 ≤ 11525661814669^3337*2000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382846539 2000000000 11525661814669 100000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326370091/2500000000 : ℝ), (5409298787/10000000000 : ℝ), (-382846539/2000000000 : ℝ)] ![(21838513122031/50000000000000 : ℝ), (5599663990779/12500000000000 : ℝ), (11525661814669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326370091/2500000000 : ℝ)|^4361 ≤ (21838513122031/50000000000000 : ℝ)^3337
        have hw : |(1326370091/2500000000 : ℝ)|=(1326370091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409298787/10000000000 : ℝ)|^4361 ≤ (5599663990779/12500000000000 : ℝ)^3337
        have hw : |(5409298787/10000000000 : ℝ)|=(5409298787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-382846539/2000000000 : ℝ)|^4361 ≤ (11525661814669/100000000000000 : ℝ)^3337
        have hw : |(-382846539/2000000000 : ℝ)|=(382846539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1401_s5_7 (p : ℝ) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4311434241/10000000000 : ℝ)*x 0 + (89776373/200000000 : ℝ)*x 1 + (4140505511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311434241/10000000000 : ℝ)^4361 ≤ (8326086429973/25000000000000 : ℝ)^3337 := by
    have hnat : (4311434241 : ℕ)^4361*25000000000000^3337 ≤ 8326086429973^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311434241 10000000000 8326086429973 25000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89776373/200000000 : ℝ)^4361 ≤ (4388281352071/12500000000000 : ℝ)^3337 := by
    have hnat : (89776373 : ℕ)^4361*12500000000000^3337 ≤ 4388281352071^3337*200000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89776373 200000000 4388281352071 12500000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4140505511/10000000000 : ℝ)^4361 ≤ (15794701723539/50000000000000 : ℝ)^3337 := by
    have hnat : (4140505511 : ℕ)^4361*50000000000000^3337 ≤ 15794701723539^3337*10000000000^4361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4140505511 10000000000 15794701723539 50000000000000 4361 3337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4361/1024 : ℝ)) 4361 3337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311434241/10000000000 : ℝ), (89776373/200000000 : ℝ), (4140505511/10000000000 : ℝ)] ![(8326086429973/25000000000000 : ℝ), (4388281352071/12500000000000 : ℝ), (15794701723539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311434241/10000000000 : ℝ)|^4361 ≤ (8326086429973/25000000000000 : ℝ)^3337
        have hw : |(4311434241/10000000000 : ℝ)|=(4311434241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(89776373/200000000 : ℝ)|^4361 ≤ (4388281352071/12500000000000 : ℝ)^3337
        have hw : |(89776373/200000000 : ℝ)|=(89776373/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4140505511/10000000000 : ℝ)|^4361 ≤ (15794701723539/50000000000000 : ℝ)^3337
        have hw : |(4140505511/10000000000 : ℝ)|=(4140505511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1401_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14777/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (703/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (11277/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14747/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14777/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (703/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14777/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (703/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14777/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (703/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14777/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (703/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14777/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (703/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14777/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (703/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (703/6250 : ℝ) ^ (545/128 : ℝ) ≤ (4556449778359957/50000000000000000000 : ℝ) := by
    have hpowers : (703/6250 : ℝ)^545 ≤ (4556449778359957/50000000000000000000 : ℝ)^128 := by
      have hnat : (703 : ℕ)^545*50000000000000000000^128 ≤ 4556449778359957^128*6250^545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        703 6250 4556449778359957 50000000000000000000 545 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (703/6250 : ℝ)) (X := (4556449778359957/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14777/100000 : ℝ) ^ (545/128 : ℝ) ≤ (29124203328036297/100000000000000000000 : ℝ) := by
    have hpowers : (14777/100000 : ℝ)^545 ≤ (29124203328036297/100000000000000000000 : ℝ)^128 := by
      have hnat : (14777 : ℕ)^545*100000000000000000000^128 ≤ 29124203328036297^128*100000^545 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14777 100000 29124203328036297 100000000000000000000 545 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14777/100000 : ℝ)) (X := (29124203328036297/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004556449778359957/25000000000000000000 : ℝ) ≤ (10000428025621927/10000000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (25004556449778359957/25000000000000000000 : ℝ)^128 ≤ (10000428025621927/10000000000000000 : ℝ)^545 := by
      have hnat : (25004556449778359957 : ℕ)^128*10000000000000000^545 ≤ 10000428025621927^545*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004556449778359957 25000000000000000000 10000428025621927 10000000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000428025621927/10000000000000000 : ℝ)) (X := (25004556449778359957/25000000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038237102884756211/100000000000000000000 : ℝ) ≤ (10000897914379649/10000000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (100038237102884756211/100000000000000000000 : ℝ)^128 ≤ (10000897914379649/10000000000000000 : ℝ)^545 := by
      have hnat : (100038237102884756211 : ℕ)^128*10000000000000000^545 ≤ 10000897914379649^545*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038237102884756211 100000000000000000000 10000897914379649 10000000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000897914379649/10000000000000000 : ℝ)) (X := (100038237102884756211/100000000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029124203328036297/50000000000000000000 : ℝ) ≤ (10001367803137371/10000000000000000 : ℝ) ^ (545/128 : ℝ) := by
    have hpowers : (50029124203328036297/50000000000000000000 : ℝ)^128 ≤ (10001367803137371/10000000000000000 : ℝ)^545 := by
      have hnat : (50029124203328036297 : ℕ)^128*10000000000000000^545 ≤ 10001367803137371^545*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029124203328036297 50000000000000000000 10001367803137371 10000000000000000 128 545 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001367803137371/10000000000000000 : ℝ)) (X := (50029124203328036297/50000000000000000000 : ℝ)) (by norm_num) 545 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4556449778359957/50000000000000000000 : ℝ) ≤ ((35280939884926066271/35290000000000000000 : ℝ)+2*(234944378861/176450000000000 : ℝ)*(703/6250 : ℝ))^(545/128 : ℝ) := by
    rw [show (35280939884926066271/35290000000000000000 : ℝ)+2*(234944378861/176450000000000 : ℝ)*(703/6250 : ℝ)=(10000428025621927/10000000000000000 : ℝ) by norm_num, show 1+2*(4556449778359957/50000000000000000000 : ℝ)=(25004556449778359957/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29124203328036297/100000000000000000000 : ℝ)+(4556449778359957/50000000000000000000 : ℝ) ≤ ((35280939884926066271/35290000000000000000 : ℝ)+(234944378861/176450000000000 : ℝ)*((14777/100000 : ℝ)+(703/6250 : ℝ)))^(545/128 : ℝ) := by
    rw [show (35280939884926066271/35290000000000000000 : ℝ)+(234944378861/176450000000000 : ℝ)*((14777/100000 : ℝ)+(703/6250 : ℝ))=(10000897914379649/10000000000000000 : ℝ) by norm_num, show 1+(29124203328036297/100000000000000000000 : ℝ)+(4556449778359957/50000000000000000000 : ℝ)=(100038237102884756211/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29124203328036297/100000000000000000000 : ℝ) ≤ ((35280939884926066271/35290000000000000000 : ℝ)+2*(234944378861/176450000000000 : ℝ)*(14777/100000 : ℝ))^(545/128 : ℝ) := by
    rw [show (35280939884926066271/35290000000000000000 : ℝ)+2*(234944378861/176450000000000 : ℝ)*(14777/100000 : ℝ)=(10001367803137371/10000000000000000 : ℝ) by norm_num, show 1+2*(29124203328036297/100000000000000000000 : ℝ)=(50029124203328036297/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35280939884926066271/35290000000000000000 : ℝ)*(X 1 0+X 2 0)+(234944378861/176450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (703/6250 : ℝ)) (hi := (14777/100000 : ℝ)) (c := (35280939884926066271/35290000000000000000 : ℝ)) (alpha := (234944378861/176450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35280939884926066271/35290000000000000000 : ℝ)*(X 0 1+X 2 1)+(234944378861/176450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (703/6250 : ℝ)) (hi := (14777/100000 : ℝ)) (c := (35280939884926066271/35290000000000000000 : ℝ)) (alpha := (234944378861/176450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35280939884926066271/35290000000000000000 : ℝ)*(X 0 2+X 1 2)+(234944378861/176450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (545/128 : ℝ)) (lo := (703/6250 : ℝ)) (hi := (14777/100000 : ℝ)) (c := (35280939884926066271/35290000000000000000 : ℝ)) (alpha := (234944378861/176450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1994050741/10000000000 : ℝ)*X 0 0+(2704947283/5000000000 : ℝ)*X 0 1+(1311507831/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347959111/10000000000 : ℝ)*X 1 0+(-1038748891/5000000000 : ℝ)*X 1 1+(262301709/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213918403/400000000 : ℝ)*X 2 0+(1311508039/2500000000 : ℝ)*X 2 1+(-2077499183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4311409983/10000000000 : ℝ)*X 0 0+(517404169/1250000000 : ℝ)*X 0 1+(561260439/1250000000 : ℝ)*X 0 2+(4311409983/10000000000 : ℝ)*X 1 0+(517404169/1250000000 : ℝ)*X 1 1+(561260439/1250000000 : ℝ)*X 1 2+(4311409983/10000000000 : ℝ)*X 2 0+(517404169/1250000000 : ℝ)*X 2 1+(561260439/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1994062619/10000000000 : ℝ)*X 0 0+(5246623907/10000000000 : ℝ)*X 0 1+(1081859757/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652740183/5000000000 : ℝ)*X 1 0+(-382846539/2000000000 : ℝ)*X 1 1+(1081859757/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326370091/2500000000 : ℝ)*X 2 0+(5409298787/10000000000 : ℝ)*X 2 1+(-382846539/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4311434241/10000000000 : ℝ)*X 0 0+(89776373/200000000 : ℝ)*X 0 1+(4140505511/10000000000 : ℝ)*X 0 2+(4311434241/10000000000 : ℝ)*X 1 0+(89776373/200000000 : ℝ)*X 1 1+(4140505511/10000000000 : ℝ)*X 1 2+(4311434241/10000000000 : ℝ)*X 2 0+(89776373/200000000 : ℝ)*X 2 1+(4140505511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1401_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8537427834173312390124952227/1764500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15526/1220703125 : ℝ)*(base23) + (72725249/100000000000000 : ℝ)*(lower2) + (152765251/50000000000000 : ℝ)*(upper3) + (292847753/100000000000000 : ℝ)*(lower4) + (13989190020181/312500000000 : ℝ)*(major0) + (13989190020181/312500000000 : ℝ)*(major1) + (4476540806457921/100000000000000 : ℝ)*(major2) + (3051373780544159/50000000000000 : ℝ)*(sp0) + (6102835603086267/100000000000000 : ℝ)*(sp1) + (6102804144031583/100000000000000 : ℝ)*(sp2) + (1425114851669701/50000000000000 : ℝ)*(sp3) + (88041997949/100000000000000 : ℝ)*(sp4) + (30187164763/100000000000000 : ℝ)*(sp6) + (8072604411/50000000000000 : ℝ)*(sp7) + (22267545691783/781250000000 : ℝ)*(f.failure) + (6102835603086267/100000000000000 : ℝ)*(f.sum) + (5135075907127/8822500000000000000000000000 : ℝ)*base66 + (43837367986643699/11028125000000000000000000000000 : ℝ)*base68 + (11242531105915882591/3529000000000000000000000000000000 : ℝ)*base69 + (35531602432950051/11028125000000000000000000000000 : ℝ)*base71 + (24190183109349/17645000000000000000000000000 : ℝ)*base74 + (25662233094588882591/3529000000000000000000000000000000 : ℝ)*base75 + (32103098200012787/5514062500000000000000000000000 : ℝ)*base78 + (135158794598843463/5514062500000000000000000000000 : ℝ)*base79 + (681252441111/176450000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (229197/78125000000000000000 : ℝ)*base89 + (229197/78125000000000000000 : ℝ)*base91 + (552053/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12676970561315564946590618259/1764500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24619737/2000000000000 : ℝ)*(base19) + (1331164589/100000000000000 : ℝ)*(base23) + (18452271/12500000000000 : ℝ)*(upper3) + (23200277/50000000000000 : ℝ)*(lower4) + (73727077/50000000000000 : ℝ)*(upper5) + (4509104700376143/100000000000000 : ℝ)*(major0) + (4509104700376143/100000000000000 : ℝ)*(major1) + (4509104700376143/100000000000000 : ℝ)*(major2) + (3196430063/12500000000000 : ℝ)*(sp1) + (1715558189/6250000000000 : ℝ)*(sp2) + (6147229646378993/100000000000000 : ℝ)*(sp4) + (6147202843951639/100000000000000 : ℝ)*(sp5) + (307360043314169/5000000000000 : ℝ)*(sp6) + (143548975744573/5000000000000 : ℝ)*(sp7) + (143548975744573/5000000000000 : ℝ)*(f.failure) + (6147229646378993/100000000000000 : ℝ)*(f.sum) + (28407633665761/17645000000000000000000000000 : ℝ)*base65 + (14458667301709027247/3529000000000000000000000000000000 : ℝ)*base68 + (18085259296784972753/3529000000000000000000000000000000 : ℝ)*base69 + (37787404752007972753/3529000000000000000000000000000000 : ℝ)*base71 + (95139313912469/17645000000000000000000000000 : ℝ)*base74 + (34064403501285027247/3529000000000000000000000000000000 : ℝ)*base76 + (7035007598750027247/3529000000000000000000000000000000 : ℝ)*base78 + (34594725419646027247/3529000000000000000000000000000000 : ℝ)*base80 + (17838207109443/8822500000000000000000000000 : ℝ)*base81 + (163807/500000000000000000000 : ℝ)*base89 + (163807/500000000000000000000 : ℝ)*base91 + (163807/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1401_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14777/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (703/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11277/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1401_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1401_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15889/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10213/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11277/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1401_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1401_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1401_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (545/128 : ℝ) ≤ p) (hpb : p ≤ (4361/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157058059/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15889/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10213/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11277/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1401_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

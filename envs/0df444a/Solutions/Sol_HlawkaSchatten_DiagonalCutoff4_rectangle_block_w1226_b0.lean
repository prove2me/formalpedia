-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1226_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:13:10.400718+00:00
-- url     : https://prove2.me/submissions/396599c4-6bff-4b79-8c1e-4fbd69e60675

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
theorem support_rectangle_w1226_s0_0 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1865507063/10000000000 : ℝ)*x 0 + (3017559319/5000000000 : ℝ)*x 1 + (299437703/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1865507063/10000000000 : ℝ)^8419 ≤ (2718502621829/25000000000000 : ℝ)^6371 := by
    have hnat : (1865507063 : ℕ)^8419*25000000000000^6371 ≤ 2718502621829^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865507063 10000000000 2718502621829 25000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3017559319/5000000000 : ℝ)^8419 ≤ (51308086536447/100000000000000 : ℝ)^6371 := by
    have hnat : (3017559319 : ℕ)^8419*100000000000000^6371 ≤ 51308086536447^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3017559319 5000000000 51308086536447 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (299437703/625000000 : ℝ)^8419 ≤ (37817902975041/100000000000000 : ℝ)^6371 := by
    have hnat : (299437703 : ℕ)^8419*100000000000000^6371 ≤ 37817902975041^6371*625000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299437703 625000000 37817902975041 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1865507063/10000000000 : ℝ), (3017559319/5000000000 : ℝ), (299437703/625000000 : ℝ)] ![(2718502621829/25000000000000 : ℝ), (51308086536447/100000000000000 : ℝ), (37817902975041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1865507063/10000000000 : ℝ)|^8419 ≤ (2718502621829/25000000000000 : ℝ)^6371
        have hw : |(-1865507063/10000000000 : ℝ)|=(1865507063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3017559319/5000000000 : ℝ)|^8419 ≤ (51308086536447/100000000000000 : ℝ)^6371
        have hw : |(3017559319/5000000000 : ℝ)|=(3017559319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(299437703/625000000 : ℝ)|^8419 ≤ (37817902975041/100000000000000 : ℝ)^6371
        have hw : |(299437703/625000000 : ℝ)|=(299437703/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s0_1 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5512060909/10000000000 : ℝ)*x 0 + (-1288585623/5000000000 : ℝ)*x 1 + (2395501601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5512060909/10000000000 : ℝ)^8419 ≤ (22757664610061/50000000000000 : ℝ)^6371 := by
    have hnat : (5512060909 : ℕ)^8419*50000000000000^6371 ≤ 22757664610061^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512060909 10000000000 22757664610061 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1288585623/5000000000 : ℝ)^8419 ≤ (8333384133259/50000000000000 : ℝ)^6371 := by
    have hnat : (1288585623 : ℕ)^8419*50000000000000^6371 ≤ 8333384133259^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288585623 5000000000 8333384133259 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2395501601/5000000000 : ℝ)^8419 ≤ (37817902495217/100000000000000 : ℝ)^6371 := by
    have hnat : (2395501601 : ℕ)^8419*100000000000000^6371 ≤ 37817902495217^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2395501601 5000000000 37817902495217 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5512060909/10000000000 : ℝ), (-1288585623/5000000000 : ℝ), (2395501601/5000000000 : ℝ)] ![(22757664610061/50000000000000 : ℝ), (8333384133259/50000000000000 : ℝ), (37817902495217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5512060909/10000000000 : ℝ)|^8419 ≤ (22757664610061/50000000000000 : ℝ)^6371
        have hw : |(5512060909/10000000000 : ℝ)|=(5512060909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1288585623/5000000000 : ℝ)|^8419 ≤ (8333384133259/50000000000000 : ℝ)^6371
        have hw : |(-1288585623/5000000000 : ℝ)|=(1288585623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2395501601/5000000000 : ℝ)|^8419 ≤ (37817902495217/100000000000000 : ℝ)^6371
        have hw : |(2395501601/5000000000 : ℝ)|=(2395501601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s0_2 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (86125951/156250000 : ℝ)*x 0 + (598875407/1250000000 : ℝ)*x 1 + (-1288585619/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86125951/156250000 : ℝ)^8419 ≤ (45515328729091/100000000000000 : ℝ)^6371 := by
    have hnat : (86125951 : ℕ)^8419*100000000000000^6371 ≤ 45515328729091^6371*156250000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86125951 156250000 45515328729091 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598875407/1250000000 : ℝ)^8419 ≤ (37817903058489/100000000000000 : ℝ)^6371 := by
    have hnat : (598875407 : ℕ)^8419*100000000000000^6371 ≤ 37817903058489^6371*1250000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598875407 1250000000 37817903058489 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1288585619/5000000000 : ℝ)^8419 ≤ (333335363963/2000000000000 : ℝ)^6371 := by
    have hnat : (1288585619 : ℕ)^8419*2000000000000^6371 ≤ 333335363963^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288585619 5000000000 333335363963 2000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86125951/156250000 : ℝ), (598875407/1250000000 : ℝ), (-1288585619/5000000000 : ℝ)] ![(45515328729091/100000000000000 : ℝ), (37817903058489/100000000000000 : ℝ), (333335363963/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86125951/156250000 : ℝ)|^8419 ≤ (45515328729091/100000000000000 : ℝ)^6371
        have hw : |(86125951/156250000 : ℝ)|=(86125951/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(598875407/1250000000 : ℝ)|^8419 ≤ (37817903058489/100000000000000 : ℝ)^6371
        have hw : |(598875407/1250000000 : ℝ)|=(598875407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1288585619/5000000000 : ℝ)|^8419 ≤ (333335363963/2000000000000 : ℝ)^6371
        have hw : |(-1288585619/5000000000 : ℝ)|=(1288585619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s0_3 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2097140553/5000000000 : ℝ)*x 0 + (623500453/2000000000 : ℝ)*x 1 + (2816741647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097140553/5000000000 : ℝ)^8419 ≤ (31721835439953/100000000000000 : ℝ)^6371 := by
    have hnat : (2097140553 : ℕ)^8419*100000000000000^6371 ≤ 31721835439953^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097140553 5000000000 31721835439953 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623500453/2000000000 : ℝ)^8419 ≤ (10716615024287/50000000000000 : ℝ)^6371 := by
    have hnat : (623500453 : ℕ)^8419*50000000000000^6371 ≤ 10716615024287^6371*2000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623500453 2000000000 10716615024287 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2816741647/5000000000 : ℝ)^8419 ≤ (23422467244733/50000000000000 : ℝ)^6371 := by
    have hnat : (2816741647 : ℕ)^8419*50000000000000^6371 ≤ 23422467244733^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2816741647 5000000000 23422467244733 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2097140553/5000000000 : ℝ), (623500453/2000000000 : ℝ), (2816741647/5000000000 : ℝ)] ![(31721835439953/100000000000000 : ℝ), (10716615024287/50000000000000 : ℝ), (23422467244733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2097140553/5000000000 : ℝ)|^8419 ≤ (31721835439953/100000000000000 : ℝ)^6371
        have hw : |(2097140553/5000000000 : ℝ)|=(2097140553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(623500453/2000000000 : ℝ)|^8419 ≤ (10716615024287/50000000000000 : ℝ)^6371
        have hw : |(623500453/2000000000 : ℝ)|=(623500453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2816741647/5000000000 : ℝ)|^8419 ≤ (23422467244733/50000000000000 : ℝ)^6371
        have hw : |(2816741647/5000000000 : ℝ)|=(2816741647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s0_4 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1870410017/10000000000 : ℝ)*x 0 + (2411525151/5000000000 : ℝ)*x 1 + (1200387869/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1870410017/10000000000 : ℝ)^8419 ≤ (10911792656093/100000000000000 : ℝ)^6371 := by
    have hnat : (1870410017 : ℕ)^8419*100000000000000^6371 ≤ 10911792656093^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870410017 10000000000 10911792656093 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2411525151/5000000000 : ℝ)^8419 ≤ (1526101722209/4000000000000 : ℝ)^6371 := by
    have hnat : (2411525151 : ℕ)^8419*4000000000000^6371 ≤ 1526101722209^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2411525151 5000000000 1526101722209 4000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1200387869/2000000000 : ℝ)^8419 ≤ (25467832137931/50000000000000 : ℝ)^6371 := by
    have hnat : (1200387869 : ℕ)^8419*50000000000000^6371 ≤ 25467832137931^6371*2000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200387869 2000000000 25467832137931 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1870410017/10000000000 : ℝ), (2411525151/5000000000 : ℝ), (1200387869/2000000000 : ℝ)] ![(10911792656093/100000000000000 : ℝ), (1526101722209/4000000000000 : ℝ), (25467832137931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1870410017/10000000000 : ℝ)|^8419 ≤ (10911792656093/100000000000000 : ℝ)^6371
        have hw : |(-1870410017/10000000000 : ℝ)|=(1870410017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2411525151/5000000000 : ℝ)|^8419 ≤ (1526101722209/4000000000000 : ℝ)^6371
        have hw : |(2411525151/5000000000 : ℝ)|=(2411525151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1200387869/2000000000 : ℝ)|^8419 ≤ (25467832137931/50000000000000 : ℝ)^6371
        have hw : |(1200387869/2000000000 : ℝ)|=(1200387869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s0_5 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2586811599/5000000000 : ℝ)*x 0 + (-1366235499/10000000000 : ℝ)*x 1 + (1500484817/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586811599/5000000000 : ℝ)^8419 ≤ (8371865430453/20000000000000 : ℝ)^6371 := by
    have hnat : (2586811599 : ℕ)^8419*20000000000000^6371 ≤ 8371865430453^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586811599 5000000000 8371865430453 20000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366235499/10000000000 : ℝ)^8419 ≤ (7205009416477/100000000000000 : ℝ)^6371 := by
    have hnat : (1366235499 : ℕ)^8419*100000000000000^6371 ≤ 7205009416477^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366235499 10000000000 7205009416477 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1500484817/2500000000 : ℝ)^8419 ≤ (50935663412339/100000000000000 : ℝ)^6371 := by
    have hnat : (1500484817 : ℕ)^8419*100000000000000^6371 ≤ 50935663412339^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1500484817 2500000000 50935663412339 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586811599/5000000000 : ℝ), (-1366235499/10000000000 : ℝ), (1500484817/2500000000 : ℝ)] ![(8371865430453/20000000000000 : ℝ), (7205009416477/100000000000000 : ℝ), (50935663412339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586811599/5000000000 : ℝ)|^8419 ≤ (8371865430453/20000000000000 : ℝ)^6371
        have hw : |(2586811599/5000000000 : ℝ)|=(2586811599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1366235499/10000000000 : ℝ)|^8419 ≤ (7205009416477/100000000000000 : ℝ)^6371
        have hw : |(-1366235499/10000000000 : ℝ)|=(1366235499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1500484817/2500000000 : ℝ)|^8419 ≤ (50935663412339/100000000000000 : ℝ)^6371
        have hw : |(1500484817/2500000000 : ℝ)|=(1500484817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s0_6 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5173623173/10000000000 : ℝ)*x 0 + (6001939347/10000000000 : ℝ)*x 1 + (-1366235411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173623173/10000000000 : ℝ)^8419 ≤ (4185932688497/10000000000000 : ℝ)^6371 := by
    have hnat : (5173623173 : ℕ)^8419*10000000000000^6371 ≤ 4185932688497^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173623173 10000000000 4185932688497 10000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6001939347/10000000000 : ℝ)^8419 ≤ (50935664298291/100000000000000 : ℝ)^6371 := by
    have hnat : (6001939347 : ℕ)^8419*100000000000000^6371 ≤ 50935664298291^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6001939347 10000000000 50935664298291 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1366235411/10000000000 : ℝ)^8419 ≤ (7205008803217/100000000000000 : ℝ)^6371 := by
    have hnat : (1366235411 : ℕ)^8419*100000000000000^6371 ≤ 7205008803217^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366235411 10000000000 7205008803217 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173623173/10000000000 : ℝ), (6001939347/10000000000 : ℝ), (-1366235411/10000000000 : ℝ)] ![(4185932688497/10000000000000 : ℝ), (50935664298291/100000000000000 : ℝ), (7205008803217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173623173/10000000000 : ℝ)|^8419 ≤ (4185932688497/10000000000000 : ℝ)^6371
        have hw : |(5173623173/10000000000 : ℝ)|=(5173623173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6001939347/10000000000 : ℝ)|^8419 ≤ (50935664298291/100000000000000 : ℝ)^6371
        have hw : |(6001939347/10000000000 : ℝ)|=(6001939347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1366235411/10000000000 : ℝ)|^8419 ≤ (7205008803217/100000000000000 : ℝ)^6371
        have hw : |(-1366235411/10000000000 : ℝ)|=(1366235411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s0_7 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2102098043/5000000000 : ℝ)*x 0 + (1392168481/2500000000 : ℝ)*x 1 + (796150343/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102098043/5000000000 : ℝ)^8419 ≤ (31820966650939/100000000000000 : ℝ)^6371 := by
    have hnat : (2102098043 : ℕ)^8419*100000000000000^6371 ≤ 31820966650939^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102098043 5000000000 31820966650939 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1392168481/2500000000 : ℝ)^8419 ≤ (4613409680757/10000000000000 : ℝ)^6371 := by
    have hnat : (1392168481 : ℕ)^8419*10000000000000^6371 ≤ 4613409680757^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1392168481 2500000000 4613409680757 10000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (796150343/2500000000 : ℝ)^8419 ≤ (5511234131611/25000000000000 : ℝ)^6371 := by
    have hnat : (796150343 : ℕ)^8419*25000000000000^6371 ≤ 5511234131611^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796150343 2500000000 5511234131611 25000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2102098043/5000000000 : ℝ), (1392168481/2500000000 : ℝ), (796150343/2500000000 : ℝ)] ![(31820966650939/100000000000000 : ℝ), (4613409680757/10000000000000 : ℝ), (5511234131611/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2102098043/5000000000 : ℝ)|^8419 ≤ (31820966650939/100000000000000 : ℝ)^6371
        have hw : |(2102098043/5000000000 : ℝ)|=(2102098043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1392168481/2500000000 : ℝ)|^8419 ≤ (4613409680757/10000000000000 : ℝ)^6371
        have hw : |(1392168481/2500000000 : ℝ)|=(1392168481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(796150343/2500000000 : ℝ)|^8419 ≤ (5511234131611/25000000000000 : ℝ)^6371
        have hw : |(796150343/2500000000 : ℝ)|=(796150343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1226_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30223053/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (377/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3437/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (4209/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4209 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4209*1^1024 ≤ 0^1024*1^4209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4209 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4209/1024 : ℝ) ≤ (231380451171133517/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4209 ≤ (231380451171133517/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4209*10000000000000000000^1024 ≤ 231380451171133517^1024*5^4209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 231380451171133517 10000000000000000000 4209 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (231380451171133517/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4209/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4209 := by
      have hnat : (1 : ℕ)^1024*1^4209 ≤ 1^4209*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10231380451171133517/10000000000000000000 : ℝ) ≤ (10055805899222061/10000000000000000 : ℝ) ^ (4209/1024 : ℝ) := by
    have hpowers : (10231380451171133517/10000000000000000000 : ℝ)^1024 ≤ (10055805899222061/10000000000000000 : ℝ)^4209 := by
      have hnat : (10231380451171133517 : ℕ)^1024*10000000000000000^4209 ≤ 10055805899222061^4209*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10231380451171133517 10000000000000000000 10055805899222061 10000000000000000 1024 4209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10055805899222061/10000000000000000 : ℝ)) (X := (10231380451171133517/10000000000000000000 : ℝ)) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5231380451171133517/5000000000000000000 : ℝ) ≤ (5055805899222061/5000000000000000 : ℝ) ^ (4209/1024 : ℝ) := by
    have hpowers : (5231380451171133517/5000000000000000000 : ℝ)^1024 ≤ (5055805899222061/5000000000000000 : ℝ)^4209 := by
      have hnat : (5231380451171133517 : ℕ)^1024*5000000000000000^4209 ≤ 5055805899222061^4209*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5231380451171133517 5000000000000000000 5055805899222061 5000000000000000 1024 4209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5055805899222061/5000000000000000 : ℝ)) (X := (5231380451171133517/5000000000000000000 : ℝ)) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(55805899222061/4000000000000000 : ℝ)*(0 : ℝ))^(4209/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(55805899222061/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(231380451171133517/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(55805899222061/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4209/1024 : ℝ) := by
    rw [show (1 : ℝ)+(55805899222061/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10055805899222061/10000000000000000 : ℝ) by norm_num, show 1+(231380451171133517/10000000000000000000 : ℝ)+(0 : ℝ)=(10231380451171133517/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(231380451171133517/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(55805899222061/4000000000000000 : ℝ)*(2/5 : ℝ))^(4209/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(55805899222061/4000000000000000 : ℝ)*(2/5 : ℝ)=(5055805899222061/5000000000000000 : ℝ) by norm_num, show 1+2*(231380451171133517/10000000000000000000 : ℝ)=(5231380451171133517/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(55805899222061/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4209/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55805899222061/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(55805899222061/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4209/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55805899222061/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(55805899222061/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4209/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55805899222061/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1865507063/10000000000 : ℝ)*X 0 0+(3017559319/5000000000 : ℝ)*X 0 1+(299437703/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5512060909/10000000000 : ℝ)*X 1 0+(-1288585623/5000000000 : ℝ)*X 1 1+(2395501601/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((86125951/156250000 : ℝ)*X 2 0+(598875407/1250000000 : ℝ)*X 2 1+(-1288585619/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2097140553/5000000000 : ℝ)*X 0 0+(623500453/2000000000 : ℝ)*X 0 1+(2816741647/5000000000 : ℝ)*X 0 2+(2097140553/5000000000 : ℝ)*X 1 0+(623500453/2000000000 : ℝ)*X 1 1+(2816741647/5000000000 : ℝ)*X 1 2+(2097140553/5000000000 : ℝ)*X 2 0+(623500453/2000000000 : ℝ)*X 2 1+(2816741647/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1870410017/10000000000 : ℝ)*X 0 0+(2411525151/5000000000 : ℝ)*X 0 1+(1200387869/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2586811599/5000000000 : ℝ)*X 1 0+(-1366235499/10000000000 : ℝ)*X 1 1+(1500484817/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5173623173/10000000000 : ℝ)*X 2 0+(6001939347/10000000000 : ℝ)*X 2 1+(-1366235411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2102098043/5000000000 : ℝ)*X 0 0+(1392168481/2500000000 : ℝ)*X 0 1+(796150343/2500000000 : ℝ)*X 0 2+(2102098043/5000000000 : ℝ)*X 1 0+(1392168481/2500000000 : ℝ)*X 1 1+(796150343/2500000000 : ℝ)*X 1 2+(2102098043/5000000000 : ℝ)*X 2 0+(1392168481/2500000000 : ℝ)*X 2 1+(796150343/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (66218385003949121697063/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77700389/100000000000000 : ℝ)*(base1) + (1616907483/100000000000000 : ℝ)*(base19) + (1500399643/100000000000000 : ℝ)*(base23) + (21989151/20000000000000 : ℝ)*(base24) + (36669559/10000000000000 : ℝ)*(upper3) + (120125697795361/20000000000000 : ℝ)*(major0) + (120125697795361/20000000000000 : ℝ)*(major1) + (120125697795361/20000000000000 : ℝ)*(major2) + (803789436260513/100000000000000 : ℝ)*(sp0) + (803791330836843/100000000000000 : ℝ)*(sp1) + (50236958587433/6250000000000 : ℝ)*(sp2) + (7949218448913/2000000000000 : ℝ)*(sp3) + (1794592101/50000000000000 : ℝ)*(sp4) + (280933529/10000000000000 : ℝ)*(sp7) + (397463809481329/100000000000000 : ℝ)*(f.failure) + (401896473872163/50000000000000 : ℝ)*(f.sum) + (8711688820979/40000000000000000000000000000 : ℝ)*base66 + (395174965980979/80000000000000000000000000000 : ℝ)*base68 + (571456356860979/80000000000000000000000000000 : ℝ)*base70 + (340294055500979/80000000000000000000000000000 : ℝ)*base72 + (10678321379021/40000000000000000000000000000 : ℝ)*base73 + (648192146620979/80000000000000000000000000000 : ℝ)*base76 + (502460735900979/80000000000000000000000000000 : ℝ)*base78 + (731130107580979/80000000000000000000000000000 : ℝ)*base80 + (203441569980979/40000000000000000000000000000 : ℝ)*base82 + (8877437/2000000000000000000000 : ℝ)*base89 + (8877437/2000000000000000000000 : ℝ)*base91 + (8877437/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20440344194753665646109/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7606219/25000000000000 : ℝ)*(base1) + (46240383/5000000000000 : ℝ)*(base19) + (45973681/5000000000000 : ℝ)*(base23) + (102027003/100000000000000 : ℝ)*(upper3) + (12848889/10000000000000 : ℝ)*(upper5) + (63385340131677/10000000000000 : ℝ)*(major0) + (63385340131677/10000000000000 : ℝ)*(major1) + (63385340131677/10000000000000 : ℝ)*(major2) + (2006087047/100000000000000 : ℝ)*(sp1) + (1987206511/100000000000000 : ℝ)*(sp2) + (21206410433773/2500000000000 : ℝ)*(sp4) + (848253456031337/100000000000000 : ℝ)*(sp5) + (848253480245913/100000000000000 : ℝ)*(sp6) + (8389004980273/2000000000000 : ℝ)*(sp7) + (209725139719263/50000000000000 : ℝ)*(f.failure) + (212064096731511/25000000000000 : ℝ)*(f.sum) + (39009438126297/20000000000000000000000000000 : ℝ)*base65 + (416535985726297/40000000000000000000000000000 : ℝ)*base67 + (71110595326297/40000000000000000000000000000 : ℝ)*base69 + (320230589366297/40000000000000000000000000000 : ℝ)*base71 + (91222005826297/20000000000000000000000000000 : ℝ)*base73 + (22045858926297/40000000000000000000000000000 : ℝ)*base75 + (269577549206297/40000000000000000000000000000 : ℝ)*base77 + (245733554246297/40000000000000000000000000000 : ℝ)*base79 + (14473835453703/20000000000000000000000000000 : ℝ)*base82 + (9230061/1000000000000000000000 : ℝ)*base90 + (9230061/1000000000000000000000 : ℝ)*base92 + (9230061/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1226_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30223053/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (377/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3437/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1226_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1226_s1_0 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2064083729/10000000000 : ℝ)*x 0 + (1135927519/2000000000 : ℝ)*x 1 + (5019372573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2064083729/10000000000 : ℝ)^8419 ≤ (2485832587303/20000000000000 : ℝ)^6371 := by
    have hnat : (2064083729 : ℕ)^8419*20000000000000^6371 ≤ 2485832587303^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064083729 10000000000 2485832587303 20000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1135927519/2000000000 : ℝ)^8419 ≤ (23676383889171/50000000000000 : ℝ)^6371 := by
    have hnat : (1135927519 : ℕ)^8419*50000000000000^6371 ≤ 23676383889171^6371*2000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135927519 2000000000 23676383889171 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5019372573/10000000000 : ℝ)^8419 ≤ (20109034635439/50000000000000 : ℝ)^6371 := by
    have hnat : (5019372573 : ℕ)^8419*50000000000000^6371 ≤ 20109034635439^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5019372573 10000000000 20109034635439 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2064083729/10000000000 : ℝ), (1135927519/2000000000 : ℝ), (5019372573/10000000000 : ℝ)] ![(2485832587303/20000000000000 : ℝ), (23676383889171/50000000000000 : ℝ), (20109034635439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2064083729/10000000000 : ℝ)|^8419 ≤ (2485832587303/20000000000000 : ℝ)^6371
        have hw : |(-2064083729/10000000000 : ℝ)|=(2064083729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1135927519/2000000000 : ℝ)|^8419 ≤ (23676383889171/50000000000000 : ℝ)^6371
        have hw : |(1135927519/2000000000 : ℝ)|=(1135927519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5019372573/10000000000 : ℝ)|^8419 ≤ (20109034635439/50000000000000 : ℝ)^6371
        have hw : |(5019372573/10000000000 : ℝ)|=(5019372573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s1_1 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1082905411/2000000000 : ℝ)*x 0 + (-2418912319/10000000000 : ℝ)*x 1 + (25096863/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082905411/2000000000 : ℝ)^8419 ≤ (22227048935377/50000000000000 : ℝ)^6371 := by
    have hnat : (1082905411 : ℕ)^8419*50000000000000^6371 ≤ 22227048935377^6371*2000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082905411 2000000000 22227048935377 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2418912319/10000000000 : ℝ)^8419 ≤ (7663916281493/50000000000000 : ℝ)^6371 := by
    have hnat : (2418912319 : ℕ)^8419*50000000000000^6371 ≤ 7663916281493^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2418912319 10000000000 7663916281493 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25096863/50000000 : ℝ)^8419 ≤ (40218069556761/100000000000000 : ℝ)^6371 := by
    have hnat : (25096863 : ℕ)^8419*100000000000000^6371 ≤ 40218069556761^6371*50000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25096863 50000000 40218069556761 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082905411/2000000000 : ℝ), (-2418912319/10000000000 : ℝ), (25096863/50000000 : ℝ)] ![(22227048935377/50000000000000 : ℝ), (7663916281493/50000000000000 : ℝ), (40218069556761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082905411/2000000000 : ℝ)|^8419 ≤ (22227048935377/50000000000000 : ℝ)^6371
        have hw : |(1082905411/2000000000 : ℝ)|=(1082905411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2418912319/10000000000 : ℝ)|^8419 ≤ (7663916281493/50000000000000 : ℝ)^6371
        have hw : |(-2418912319/10000000000 : ℝ)|=(2418912319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(25096863/50000000 : ℝ)|^8419 ≤ (40218069556761/100000000000000 : ℝ)^6371
        have hw : |(25096863/50000000 : ℝ)|=(25096863/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s1_2 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5414527087/10000000000 : ℝ)*x 0 + (5019372589/10000000000 : ℝ)*x 1 + (-241891229/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5414527087/10000000000 : ℝ)^8419 ≤ (22227049108967/50000000000000 : ℝ)^6371 := by
    have hnat : (5414527087 : ℕ)^8419*50000000000000^6371 ≤ 22227049108967^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414527087 10000000000 22227049108967 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5019372589/10000000000 : ℝ)^8419 ≤ (4021806944029/10000000000000 : ℝ)^6371 := by
    have hnat : (5019372589 : ℕ)^8419*10000000000000^6371 ≤ 4021806944029^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5019372589 10000000000 4021806944029 10000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (241891229/1000000000 : ℝ)^8419 ≤ (15327832320151/100000000000000 : ℝ)^6371 := by
    have hnat : (241891229 : ℕ)^8419*100000000000000^6371 ≤ 15327832320151^6371*1000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241891229 1000000000 15327832320151 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5414527087/10000000000 : ℝ), (5019372589/10000000000 : ℝ), (-241891229/1000000000 : ℝ)] ![(22227049108967/50000000000000 : ℝ), (4021806944029/10000000000000 : ℝ), (15327832320151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5414527087/10000000000 : ℝ)|^8419 ≤ (22227049108967/50000000000000 : ℝ)^6371
        have hw : |(5414527087/10000000000 : ℝ)|=(5414527087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5019372589/10000000000 : ℝ)|^8419 ≤ (4021806944029/10000000000000 : ℝ)^6371
        have hw : |(5019372589/10000000000 : ℝ)|=(5019372589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-241891229/1000000000 : ℝ)|^8419 ≤ (15327832320151/100000000000000 : ℝ)^6371
        have hw : |(-241891229/1000000000 : ℝ)|=(241891229/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s1_3 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4310243239/10000000000 : ℝ)*x 0 + (1846278569/5000000000 : ℝ)*x 1 + (628476877/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310243239/10000000000 : ℝ)^8419 ≤ (32885917570279/100000000000000 : ℝ)^6371 := by
    have hnat : (4310243239 : ℕ)^8419*100000000000000^6371 ≤ 32885917570279^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310243239 10000000000 32885917570279 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1846278569/5000000000 : ℝ)^8419 ≤ (13403299097269/50000000000000 : ℝ)^6371 := by
    have hnat : (1846278569 : ℕ)^8419*50000000000000^6371 ≤ 13403299097269^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846278569 5000000000 13403299097269 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (628476877/1250000000 : ℝ)^8419 ≤ (10076871057019/25000000000000 : ℝ)^6371 := by
    have hnat : (628476877 : ℕ)^8419*25000000000000^6371 ≤ 10076871057019^6371*1250000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628476877 1250000000 10076871057019 25000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310243239/10000000000 : ℝ), (1846278569/5000000000 : ℝ), (628476877/1250000000 : ℝ)] ![(32885917570279/100000000000000 : ℝ), (13403299097269/50000000000000 : ℝ), (10076871057019/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310243239/10000000000 : ℝ)|^8419 ≤ (32885917570279/100000000000000 : ℝ)^6371
        have hw : |(4310243239/10000000000 : ℝ)|=(4310243239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1846278569/5000000000 : ℝ)|^8419 ≤ (13403299097269/50000000000000 : ℝ)^6371
        have hw : |(1846278569/5000000000 : ℝ)|=(1846278569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(628476877/1250000000 : ℝ)|^8419 ≤ (10076871057019/25000000000000 : ℝ)^6371
        have hw : |(628476877/1250000000 : ℝ)|=(628476877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s1_4 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2064780057/10000000000 : ℝ)*x 0 + (2514050193/5000000000 : ℝ)*x 1 + (2835371087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2064780057/10000000000 : ℝ)^8419 ≤ (12434704149973/100000000000000 : ℝ)^6371 := by
    have hnat : (2064780057 : ℕ)^8419*100000000000000^6371 ≤ 12434704149973^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064780057 10000000000 12434704149973 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2514050193/5000000000 : ℝ)^8419 ≤ (40310507460827/100000000000000 : ℝ)^6371 := by
    have hnat : (2514050193 : ℕ)^8419*100000000000000^6371 ≤ 40310507460827^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2514050193 5000000000 40310507460827 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2835371087/5000000000 : ℝ)^8419 ≤ (11813697094527/25000000000000 : ℝ)^6371 := by
    have hnat : (2835371087 : ℕ)^8419*25000000000000^6371 ≤ 11813697094527^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2835371087 5000000000 11813697094527 25000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2064780057/10000000000 : ℝ), (2514050193/5000000000 : ℝ), (2835371087/5000000000 : ℝ)] ![(12434704149973/100000000000000 : ℝ), (40310507460827/100000000000000 : ℝ), (11813697094527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2064780057/10000000000 : ℝ)|^8419 ≤ (12434704149973/100000000000000 : ℝ)^6371
        have hw : |(-2064780057/10000000000 : ℝ)|=(2064780057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2514050193/5000000000 : ℝ)|^8419 ≤ (40310507460827/100000000000000 : ℝ)^6371
        have hw : |(2514050193/5000000000 : ℝ)|=(2514050193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2835371087/5000000000 : ℝ)|^8419 ≤ (11813697094527/25000000000000 : ℝ)^6371
        have hw : |(2835371087/5000000000 : ℝ)|=(2835371087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s1_5 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5244552117/10000000000 : ℝ)*x 0 + (-70701681/400000000 : ℝ)*x 1 + (2835371297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5244552117/10000000000 : ℝ)^8419 ≤ (42619350058487/100000000000000 : ℝ)^6371 := by
    have hnat : (5244552117 : ℕ)^8419*100000000000000^6371 ≤ 42619350058487^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244552117 10000000000 42619350058487 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70701681/400000000 : ℝ)^8419 ≤ (10125856919993/100000000000000 : ℝ)^6371 := by
    have hnat : (70701681 : ℕ)^8419*100000000000000^6371 ≤ 10125856919993^6371*400000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70701681 400000000 10125856919993 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2835371297/5000000000 : ℝ)^8419 ≤ (4725479300307/10000000000000 : ℝ)^6371 := by
    have hnat : (2835371297 : ℕ)^8419*10000000000000^6371 ≤ 4725479300307^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2835371297 5000000000 4725479300307 10000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5244552117/10000000000 : ℝ), (-70701681/400000000 : ℝ), (2835371297/5000000000 : ℝ)] ![(42619350058487/100000000000000 : ℝ), (10125856919993/100000000000000 : ℝ), (4725479300307/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5244552117/10000000000 : ℝ)|^8419 ≤ (42619350058487/100000000000000 : ℝ)^6371
        have hw : |(5244552117/10000000000 : ℝ)|=(5244552117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-70701681/400000000 : ℝ)|^8419 ≤ (10125856919993/100000000000000 : ℝ)^6371
        have hw : |(-70701681/400000000 : ℝ)|=(70701681/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2835371297/5000000000 : ℝ)|^8419 ≤ (4725479300307/10000000000000 : ℝ)^6371
        have hw : |(2835371297/5000000000 : ℝ)|=(2835371297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s1_6 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5244552393/10000000000 : ℝ)*x 0 + (5670743331/10000000000 : ℝ)*x 1 + (-1767540561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5244552393/10000000000 : ℝ)^8419 ≤ (21309676511183/50000000000000 : ℝ)^6371 := by
    have hnat : (5244552393 : ℕ)^8419*50000000000000^6371 ≤ 21309676511183^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244552393 10000000000 21309676511183 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5670743331/10000000000 : ℝ)^8419 ≤ (5906850139847/12500000000000 : ℝ)^6371 := by
    have hnat : (5670743331 : ℕ)^8419*12500000000000^6371 ≤ 5906850139847^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5670743331 10000000000 5906850139847 12500000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1767540561/10000000000 : ℝ)^8419 ≤ (2531461459257/25000000000000 : ℝ)^6371 := by
    have hnat : (1767540561 : ℕ)^8419*25000000000000^6371 ≤ 2531461459257^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1767540561 10000000000 2531461459257 25000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5244552393/10000000000 : ℝ), (5670743331/10000000000 : ℝ), (-1767540561/10000000000 : ℝ)] ![(21309676511183/50000000000000 : ℝ), (5906850139847/12500000000000 : ℝ), (2531461459257/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5244552393/10000000000 : ℝ)|^8419 ≤ (21309676511183/50000000000000 : ℝ)^6371
        have hw : |(5244552393/10000000000 : ℝ)|=(5244552393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5670743331/10000000000 : ℝ)|^8419 ≤ (5906850139847/12500000000000 : ℝ)^6371
        have hw : |(5670743331/10000000000 : ℝ)|=(5670743331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1767540561/10000000000 : ℝ)|^8419 ≤ (2531461459257/25000000000000 : ℝ)^6371
        have hw : |(-1767540561/10000000000 : ℝ)|=(1767540561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s1_7 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2155824797/5000000000 : ℝ)*x 0 + (5010165519/10000000000 : ℝ)*x 1 + (1855272247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155824797/5000000000 : ℝ)^8419 ≤ (6580019530989/20000000000000 : ℝ)^6371 := by
    have hnat : (2155824797 : ℕ)^8419*20000000000000^6371 ≤ 6580019530989^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155824797 5000000000 6580019530989 20000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5010165519/10000000000 : ℝ)^8419 ≤ (40120611322067/100000000000000 : ℝ)^6371 := by
    have hnat : (5010165519 : ℕ)^8419*100000000000000^6371 ≤ 40120611322067^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5010165519 10000000000 40120611322067 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1855272247/5000000000 : ℝ)^8419 ≤ (13489645498659/50000000000000 : ℝ)^6371 := by
    have hnat : (1855272247 : ℕ)^8419*50000000000000^6371 ≤ 13489645498659^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1855272247 5000000000 13489645498659 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155824797/5000000000 : ℝ), (5010165519/10000000000 : ℝ), (1855272247/5000000000 : ℝ)] ![(6580019530989/20000000000000 : ℝ), (40120611322067/100000000000000 : ℝ), (13489645498659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155824797/5000000000 : ℝ)|^8419 ≤ (6580019530989/20000000000000 : ℝ)^6371
        have hw : |(2155824797/5000000000 : ℝ)|=(2155824797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5010165519/10000000000 : ℝ)|^8419 ≤ (40120611322067/100000000000000 : ℝ)^6371
        have hw : |(5010165519/10000000000 : ℝ)|=(5010165519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1855272247/5000000000 : ℝ)|^8419 ≤ (13489645498659/50000000000000 : ℝ)^6371
        have hw : |(1855272247/5000000000 : ℝ)|=(1855272247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1226_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30223053/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3437/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (377/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (6107/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20067/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3437/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (377/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3437/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (377/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3437/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (377/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3437/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (377/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3437/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (377/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3437/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (377/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
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
  have hpowlo : (377/50000 : ℝ) ^ (4209/1024 : ℝ) ≤ (5889792797/3125000000000000000 : ℝ) := by
    have hpowers : (377/50000 : ℝ)^4209 ≤ (5889792797/3125000000000000000 : ℝ)^1024 := by
      have hnat : (377 : ℕ)^4209*3125000000000000000^1024 ≤ 5889792797^1024*50000^4209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        377 50000 5889792797 3125000000000000000 4209 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (377/50000 : ℝ)) (X := (5889792797/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3437/12500 : ℝ) ^ (4209/1024 : ℝ) ≤ (99135816410677729/20000000000000000000 : ℝ) := by
    have hpowers : (3437/12500 : ℝ)^4209 ≤ (99135816410677729/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3437 : ℕ)^4209*20000000000000000000^1024 ≤ 99135816410677729^1024*12500^4209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3437 12500 99135816410677729 20000000000000000000 4209 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3437/12500 : ℝ)) (X := (99135816410677729/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562500005889792797/1562500000000000000 : ℝ) ≤ (1000000000917067/1000000000000000 : ℝ) ^ (4209/1024 : ℝ) := by
    have hpowers : (1562500005889792797/1562500000000000000 : ℝ)^1024 ≤ (1000000000917067/1000000000000000 : ℝ)^4209 := by
      have hnat : (1562500005889792797 : ℕ)^1024*1000000000000000^4209 ≤ 1000000000917067^4209*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562500005889792797 1562500000000000000 1000000000917067 1000000000000000 1024 4209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000000917067/1000000000000000 : ℝ)) (X := (1562500005889792797/1562500000000000000 : ℝ)) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100495679270526758149/100000000000000000000 : ℝ) ≤ (1251504592549477/1250000000000000 : ℝ) ^ (4209/1024 : ℝ) := by
    have hpowers : (100495679270526758149/100000000000000000000 : ℝ)^1024 ≤ (1251504592549477/1250000000000000 : ℝ)^4209 := by
      have hnat : (100495679270526758149 : ℕ)^1024*1250000000000000^4209 ≤ 1251504592549477^4209*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100495679270526758149 100000000000000000000 1251504592549477 1250000000000000 1024 4209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251504592549477/1250000000000000 : ℝ)) (X := (100495679270526758149/100000000000000000000 : ℝ)) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10099135816410677729/10000000000000000000 : ℝ) ≤ (5012036735810481/5000000000000000 : ℝ) ^ (4209/1024 : ℝ) := by
    have hpowers : (10099135816410677729/10000000000000000000 : ℝ)^1024 ≤ (5012036735810481/5000000000000000 : ℝ)^4209 := by
      have hnat : (10099135816410677729 : ℕ)^1024*5000000000000000^4209 ≤ 5012036735810481^4209*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10099135816410677729 10000000000000000000 5012036735810481 5000000000000000 1024 4209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5012036735810481/5000000000000000 : ℝ)) (X := (10099135816410677729/10000000000000000000 : ℝ)) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5889792797/3125000000000000000 : ℝ) ≤ ((66850462213638634243/66855000000000000000 : ℝ)+2*(6018365612573/1337100000000000 : ℝ)*(377/50000 : ℝ))^(4209/1024 : ℝ) := by
    rw [show (66850462213638634243/66855000000000000000 : ℝ)+2*(6018365612573/1337100000000000 : ℝ)*(377/50000 : ℝ)=(1000000000917067/1000000000000000 : ℝ) by norm_num, show 1+2*(5889792797/3125000000000000000 : ℝ)=(1562500005889792797/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(99135816410677729/20000000000000000000 : ℝ)+(5889792797/3125000000000000000 : ℝ) ≤ ((66850462213638634243/66855000000000000000 : ℝ)+(6018365612573/1337100000000000 : ℝ)*((3437/12500 : ℝ)+(377/50000 : ℝ)))^(4209/1024 : ℝ) := by
    rw [show (66850462213638634243/66855000000000000000 : ℝ)+(6018365612573/1337100000000000 : ℝ)*((3437/12500 : ℝ)+(377/50000 : ℝ))=(1251504592549477/1250000000000000 : ℝ) by norm_num, show 1+(99135816410677729/20000000000000000000 : ℝ)+(5889792797/3125000000000000000 : ℝ)=(100495679270526758149/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(99135816410677729/20000000000000000000 : ℝ) ≤ ((66850462213638634243/66855000000000000000 : ℝ)+2*(6018365612573/1337100000000000 : ℝ)*(3437/12500 : ℝ))^(4209/1024 : ℝ) := by
    rw [show (66850462213638634243/66855000000000000000 : ℝ)+2*(6018365612573/1337100000000000 : ℝ)*(3437/12500 : ℝ)=(5012036735810481/5000000000000000 : ℝ) by norm_num, show 1+2*(99135816410677729/20000000000000000000 : ℝ)=(10099135816410677729/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (66850462213638634243/66855000000000000000 : ℝ)*(X 1 0+X 2 0)+(6018365612573/1337100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4209/1024 : ℝ)) (lo := (377/50000 : ℝ)) (hi := (3437/12500 : ℝ)) (c := (66850462213638634243/66855000000000000000 : ℝ)) (alpha := (6018365612573/1337100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (66850462213638634243/66855000000000000000 : ℝ)*(X 0 1+X 2 1)+(6018365612573/1337100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4209/1024 : ℝ)) (lo := (377/50000 : ℝ)) (hi := (3437/12500 : ℝ)) (c := (66850462213638634243/66855000000000000000 : ℝ)) (alpha := (6018365612573/1337100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (66850462213638634243/66855000000000000000 : ℝ)*(X 0 2+X 1 2)+(6018365612573/1337100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4209/1024 : ℝ)) (lo := (377/50000 : ℝ)) (hi := (3437/12500 : ℝ)) (c := (66850462213638634243/66855000000000000000 : ℝ)) (alpha := (6018365612573/1337100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2064083729/10000000000 : ℝ)*X 0 0+(1135927519/2000000000 : ℝ)*X 0 1+(5019372573/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1082905411/2000000000 : ℝ)*X 1 0+(-2418912319/10000000000 : ℝ)*X 1 1+(25096863/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5414527087/10000000000 : ℝ)*X 2 0+(5019372589/10000000000 : ℝ)*X 2 1+(-241891229/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4310243239/10000000000 : ℝ)*X 0 0+(1846278569/5000000000 : ℝ)*X 0 1+(628476877/1250000000 : ℝ)*X 0 2+(4310243239/10000000000 : ℝ)*X 1 0+(1846278569/5000000000 : ℝ)*X 1 1+(628476877/1250000000 : ℝ)*X 1 2+(4310243239/10000000000 : ℝ)*X 2 0+(1846278569/5000000000 : ℝ)*X 2 1+(628476877/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2064780057/10000000000 : ℝ)*X 0 0+(2514050193/5000000000 : ℝ)*X 0 1+(2835371087/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5244552117/10000000000 : ℝ)*X 1 0+(-70701681/400000000 : ℝ)*X 1 1+(2835371297/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5244552393/10000000000 : ℝ)*X 2 0+(5670743331/10000000000 : ℝ)*X 2 1+(-1767540561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2155824797/5000000000 : ℝ)*X 0 0+(5010165519/10000000000 : ℝ)*X 0 1+(1855272247/5000000000 : ℝ)*X 0 2+(2155824797/5000000000 : ℝ)*X 1 0+(5010165519/10000000000 : ℝ)*X 1 1+(1855272247/5000000000 : ℝ)*X 1 2+(2155824797/5000000000 : ℝ)*X 2 0+(5010165519/10000000000 : ℝ)*X 2 1+(1855272247/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2241137461174557146108346921/557125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47895123/100000000000000 : ℝ)*(base1) + (891121469/100000000000000 : ℝ)*(base19) + (900072513/100000000000000 : ℝ)*(base23) + (24373587/25000000000000 : ℝ)*(upper3) + (110389573/100000000000000 : ℝ)*(upper5) + (565869318020849/50000000000000 : ℝ)*(major0) + (565869318020849/50000000000000 : ℝ)*(major1) + (565869318020849/50000000000000 : ℝ)*(major2) + (15145480766147/1000000000000 : ℝ)*(sp0) + (1514552148409161/100000000000000 : ℝ)*(sp1) + (757276069729059/50000000000000 : ℝ)*(sp2) + (149784303436357/20000000000000 : ℝ)*(sp3) + (1252702763/25000000000000 : ℝ)*(sp4) + (2533386407/100000000000000 : ℝ)*(sp7) + (374462049231657/50000000000000 : ℝ)*(f.failure) + (151455303953063/10000000000000 : ℝ)*(f.sum) + (210544573938241/66855000000000000000000000000 : ℝ)*base66 + (267741522388067693/3342750000000000000000000000000000 : ℝ)*base68 + (8087645957163317693/3342750000000000000000000000000000 : ℝ)*base70 + (11426098725013817693/3342750000000000000000000000000000 : ℝ)*base72 + (92730726702233/33427500000000000000000000000 : ℝ)*base74 + (7827106847586317693/3342750000000000000000000000000000 : ℝ)*base76 + (24692441939134067693/3342750000000000000000000000000000 : ℝ)*base78 + (25735535129645567693/3342750000000000000000000000000000 : ℝ)*base80 + (40045428021167/8356875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (1211179/1000000000000000000000 : ℝ)*base90 + (1211179/1000000000000000000000 : ℝ)*base92 + (1211179/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2715064389155635151319903987/557125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (860253861/50000000000000 : ℝ)*(base19) + (136324461/6250000000000 : ℝ)*(base23) + (104561597/100000000000000 : ℝ)*(upper2) + (296976921/100000000000000 : ℝ)*(upper3) + (122371033/100000000000000 : ℝ)*(upper5) + (581382758224797/50000000000000 : ℝ)*(major0) + (581382758224797/50000000000000 : ℝ)*(major1) + (581382758224797/50000000000000 : ℝ)*(major2) + (7879243857/100000000000000 : ℝ)*(sp1) + (13415299287/100000000000000 : ℝ)*(sp2) + (1556074842004947/100000000000000 : ℝ)*(sp4) + (1556065242253367/100000000000000 : ℝ)*(sp5) + (389014811378571/25000000000000 : ℝ)*(sp6) + (96182003556159/12500000000000 : ℝ)*(sp7) + (96182003556159/12500000000000 : ℝ)*(f.failure) + (1556074842004947/100000000000000 : ℝ)*(f.sum) + (124738525817589/22285000000000000000000000000 : ℝ)*base65 + (6523521034595824557/1114250000000000000000000000000000 : ℝ)*base67 + (5003927569532824557/1114250000000000000000000000000000 : ℝ)*base69 + (9932220225114824557/1114250000000000000000000000000000 : ℝ)*base71 + (13580228702599/5571250000000000000000000000 : ℝ)*base74 + (14295215494297824557/1114250000000000000000000000000000 : ℝ)*base75 + (7790754841940074557/1114250000000000000000000000000000 : ℝ)*base77 + (7601363467399574557/1114250000000000000000000000000000 : ℝ)*base79 + (3494223157933/2785625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3066573/250000000000000000000 : ℝ)*base90 + (3066573/250000000000000000000 : ℝ)*base92 + (3066573/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1226_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30223053/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3437/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (377/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6107/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20067/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1226_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1226_s2_0 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-422585767/2000000000 : ℝ)*x 0 + (549554061/1000000000 : ℝ)*x 1 + (5172333637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422585767/2000000000 : ℝ)^8419 ≤ (6409655082427/50000000000000 : ℝ)^6371 := by
    have hnat : (422585767 : ℕ)^8419*50000000000000^6371 ≤ 6409655082427^6371*2000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422585767 2000000000 6409655082427 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549554061/1000000000 : ℝ)^8419 ≤ (11333787460187/25000000000000 : ℝ)^6371 := by
    have hnat : (549554061 : ℕ)^8419*25000000000000^6371 ≤ 11333787460187^6371*1000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549554061 1000000000 11333787460187 25000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5172333637/10000000000 : ℝ)^8419 ≤ (20922769995707/50000000000000 : ℝ)^6371 := by
    have hnat : (5172333637 : ℕ)^8419*50000000000000^6371 ≤ 20922769995707^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172333637 10000000000 20922769995707 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-422585767/2000000000 : ℝ), (549554061/1000000000 : ℝ), (5172333637/10000000000 : ℝ)] ![(6409655082427/50000000000000 : ℝ), (11333787460187/25000000000000 : ℝ), (20922769995707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-422585767/2000000000 : ℝ)|^8419 ≤ (6409655082427/50000000000000 : ℝ)^6371
        have hw : |(-422585767/2000000000 : ℝ)|=(422585767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(549554061/1000000000 : ℝ)|^8419 ≤ (11333787460187/25000000000000 : ℝ)^6371
        have hw : |(549554061/1000000000 : ℝ)|=(549554061/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5172333637/10000000000 : ℝ)|^8419 ≤ (20922769995707/50000000000000 : ℝ)^6371
        have hw : |(5172333637/10000000000 : ℝ)|=(5172333637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s2_1 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2685169619/5000000000 : ℝ)*x 0 + (-570110453/2500000000 : ℝ)*x 1 + (2586166787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685169619/5000000000 : ℝ)^8419 ≤ (43975318279043/100000000000000 : ℝ)^6371 := by
    have hnat : (2685169619 : ℕ)^8419*100000000000000^6371 ≤ 43975318279043^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685169619 5000000000 43975318279043 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (570110453/2500000000 : ℝ)^8419 ≤ (567165695857/4000000000000 : ℝ)^6371 := by
    have hnat : (570110453 : ℕ)^8419*4000000000000^6371 ≤ 567165695857^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570110453 2500000000 567165695857 4000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2586166787/5000000000 : ℝ)^8419 ≤ (20922769658943/50000000000000 : ℝ)^6371 := by
    have hnat : (2586166787 : ℕ)^8419*50000000000000^6371 ≤ 20922769658943^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586166787 5000000000 20922769658943 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685169619/5000000000 : ℝ), (-570110453/2500000000 : ℝ), (2586166787/5000000000 : ℝ)] ![(43975318279043/100000000000000 : ℝ), (567165695857/4000000000000 : ℝ), (20922769658943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685169619/5000000000 : ℝ)|^8419 ≤ (43975318279043/100000000000000 : ℝ)^6371
        have hw : |(2685169619/5000000000 : ℝ)|=(2685169619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-570110453/2500000000 : ℝ)|^8419 ≤ (567165695857/4000000000000 : ℝ)^6371
        have hw : |(-570110453/2500000000 : ℝ)|=(570110453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2586166787/5000000000 : ℝ)|^8419 ≤ (20922769658943/50000000000000 : ℝ)^6371
        have hw : |(2586166787/5000000000 : ℝ)|=(2586166787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s2_2 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5370339047/10000000000 : ℝ)*x 0 + (5172333743/10000000000 : ℝ)*x 1 + (-570110461/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370339047/10000000000 : ℝ)^8419 ≤ (21987658106133/50000000000000 : ℝ)^6371 := by
    have hnat : (5370339047 : ℕ)^8419*50000000000000^6371 ≤ 21987658106133^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370339047 10000000000 21987658106133 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5172333743/10000000000 : ℝ)^8419 ≤ (41845541124653/100000000000000 : ℝ)^6371 := by
    have hnat : (5172333743 : ℕ)^8419*100000000000000^6371 ≤ 41845541124653^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172333743 10000000000 41845541124653 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (570110461/2500000000 : ℝ)^8419 ≤ (14179142659351/100000000000000 : ℝ)^6371 := by
    have hnat : (570110461 : ℕ)^8419*100000000000000^6371 ≤ 14179142659351^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570110461 2500000000 14179142659351 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370339047/10000000000 : ℝ), (5172333743/10000000000 : ℝ), (-570110461/2500000000 : ℝ)] ![(21987658106133/50000000000000 : ℝ), (41845541124653/100000000000000 : ℝ), (14179142659351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370339047/10000000000 : ℝ)|^8419 ≤ (21987658106133/50000000000000 : ℝ)^6371
        have hw : |(5370339047/10000000000 : ℝ)|=(5370339047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5172333743/10000000000 : ℝ)|^8419 ≤ (41845541124653/100000000000000 : ℝ)^6371
        have hw : |(5172333743/10000000000 : ℝ)|=(5172333743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-570110461/2500000000 : ℝ)|^8419 ≤ (14179142659351/100000000000000 : ℝ)^6371
        have hw : |(-570110461/2500000000 : ℝ)|=(570110461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s2_3 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1085987233/2500000000 : ℝ)*x 0 + (805817557/2000000000 : ℝ)*x 1 + (4682711209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085987233/2500000000 : ℝ)^8419 ≤ (6645235201351/20000000000000 : ℝ)^6371 := by
    have hnat : (1085987233 : ℕ)^8419*20000000000000^6371 ≤ 6645235201351^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085987233 2500000000 6645235201351 20000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (805817557/2000000000 : ℝ)^8419 ≤ (15040692476833/50000000000000 : ℝ)^6371 := by
    have hnat : (805817557 : ℕ)^8419*50000000000000^6371 ≤ 15040692476833^6371*2000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805817557 2000000000 15040692476833 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4682711209/10000000000 : ℝ)^8419 ≤ (36692439031851/100000000000000 : ℝ)^6371 := by
    have hnat : (4682711209 : ℕ)^8419*100000000000000^6371 ≤ 36692439031851^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4682711209 10000000000 36692439031851 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085987233/2500000000 : ℝ), (805817557/2000000000 : ℝ), (4682711209/10000000000 : ℝ)] ![(6645235201351/20000000000000 : ℝ), (15040692476833/50000000000000 : ℝ), (36692439031851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085987233/2500000000 : ℝ)|^8419 ≤ (6645235201351/20000000000000 : ℝ)^6371
        have hw : |(1085987233/2500000000 : ℝ)|=(1085987233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(805817557/2000000000 : ℝ)|^8419 ≤ (15040692476833/50000000000000 : ℝ)^6371
        have hw : |(805817557/2000000000 : ℝ)|=(805817557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4682711209/10000000000 : ℝ)|^8419 ≤ (36692439031851/100000000000000 : ℝ)^6371
        have hw : |(4682711209/10000000000 : ℝ)|=(4682711209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s2_4 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-528252663/2500000000 : ℝ)*x 0 + (517443457/1000000000 : ℝ)*x 1 + (5493419777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528252663/2500000000 : ℝ)^8419 ≤ (51279864509/400000000000 : ℝ)^6371 := by
    have hnat : (528252663 : ℕ)^8419*400000000000^6371 ≤ 51279864509^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528252663 2500000000 51279864509 400000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517443457/1000000000 : ℝ)^8419 ≤ (4186800238861/10000000000000 : ℝ)^6371 := by
    have hnat : (517443457 : ℕ)^8419*10000000000000^6371 ≤ 4186800238861^6371*1000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517443457 1000000000 4186800238861 10000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5493419777/10000000000 : ℝ)^8419 ≤ (45312031478253/100000000000000 : ℝ)^6371 := by
    have hnat : (5493419777 : ℕ)^8419*100000000000000^6371 ≤ 45312031478253^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493419777 10000000000 45312031478253 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528252663/2500000000 : ℝ), (517443457/1000000000 : ℝ), (5493419777/10000000000 : ℝ)] ![(51279864509/400000000000 : ℝ), (4186800238861/10000000000000 : ℝ), (45312031478253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528252663/2500000000 : ℝ)|^8419 ≤ (51279864509/400000000000 : ℝ)^6371
        have hw : |(-528252663/2500000000 : ℝ)|=(528252663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517443457/1000000000 : ℝ)|^8419 ≤ (4186800238861/10000000000000 : ℝ)^6371
        have hw : |(517443457/1000000000 : ℝ)|=(517443457/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5493419777/10000000000 : ℝ)|^8419 ≤ (45312031478253/100000000000000 : ℝ)^6371
        have hw : |(5493419777/10000000000 : ℝ)|=(5493419777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s2_5 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2643941657/5000000000 : ℝ)*x 0 + (-489838859/2500000000 : ℝ)*x 1 + (1098683963/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643941657/5000000000 : ℝ)^8419 ≤ (21542643571447/50000000000000 : ℝ)^6371 := by
    have hnat : (2643941657 : ℕ)^8419*50000000000000^6371 ≤ 21542643571447^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643941657 5000000000 21542643571447 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (489838859/2500000000 : ℝ)^8419 ≤ (11602680957329/100000000000000 : ℝ)^6371 := by
    have hnat : (489838859 : ℕ)^8419*100000000000000^6371 ≤ 11602680957329^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489838859 2500000000 11602680957329 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098683963/2000000000 : ℝ)^8419 ≤ (45312031892451/100000000000000 : ℝ)^6371 := by
    have hnat : (1098683963 : ℕ)^8419*100000000000000^6371 ≤ 45312031892451^6371*2000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098683963 2000000000 45312031892451 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643941657/5000000000 : ℝ), (-489838859/2500000000 : ℝ), (1098683963/2000000000 : ℝ)] ![(21542643571447/50000000000000 : ℝ), (11602680957329/100000000000000 : ℝ), (45312031892451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643941657/5000000000 : ℝ)|^8419 ≤ (21542643571447/50000000000000 : ℝ)^6371
        have hw : |(2643941657/5000000000 : ℝ)|=(2643941657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-489838859/2500000000 : ℝ)|^8419 ≤ (11602680957329/100000000000000 : ℝ)^6371
        have hw : |(-489838859/2500000000 : ℝ)|=(489838859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1098683963/2000000000 : ℝ)|^8419 ≤ (45312031892451/100000000000000 : ℝ)^6371
        have hw : |(1098683963/2000000000 : ℝ)|=(1098683963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s2_6 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2643941747/5000000000 : ℝ)*x 0 + (549341987/1000000000 : ℝ)*x 1 + (-1959355111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643941747/5000000000 : ℝ)^8419 ≤ (21542644540489/50000000000000 : ℝ)^6371 := by
    have hnat : (2643941747 : ℕ)^8419*50000000000000^6371 ≤ 21542644540489^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643941747 5000000000 21542644540489 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549341987/1000000000 : ℝ)^8419 ≤ (45312032491947/100000000000000 : ℝ)^6371 := by
    have hnat : (549341987 : ℕ)^8419*100000000000000^6371 ≤ 45312032491947^6371*1000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549341987 1000000000 45312032491947 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1959355111/10000000000 : ℝ)^8419 ≤ (2900669603531/25000000000000 : ℝ)^6371 := by
    have hnat : (1959355111 : ℕ)^8419*25000000000000^6371 ≤ 2900669603531^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959355111 10000000000 2900669603531 25000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643941747/5000000000 : ℝ), (549341987/1000000000 : ℝ), (-1959355111/10000000000 : ℝ)] ![(21542644540489/50000000000000 : ℝ), (45312032491947/100000000000000 : ℝ), (2900669603531/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643941747/5000000000 : ℝ)|^8419 ≤ (21542644540489/50000000000000 : ℝ)^6371
        have hw : |(2643941747/5000000000 : ℝ)|=(2643941747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(549341987/1000000000 : ℝ)|^8419 ≤ (45312032491947/100000000000000 : ℝ)^6371
        have hw : |(549341987/1000000000 : ℝ)|=(549341987/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1959355111/10000000000 : ℝ)|^8419 ≤ (2900669603531/25000000000000 : ℝ)^6371
        have hw : |(-1959355111/10000000000 : ℝ)|=(1959355111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s2_7 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4344113853/10000000000 : ℝ)*x 0 + (4678462621/10000000000 : ℝ)*x 1 + (504172049/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4344113853/10000000000 : ℝ)^8419 ≤ (4153480371797/12500000000000 : ℝ)^6371 := by
    have hnat : (4344113853 : ℕ)^8419*12500000000000^6371 ≤ 4153480371797^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4344113853 10000000000 4153480371797 12500000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4678462621/10000000000 : ℝ)^8419 ≤ (36648453142317/100000000000000 : ℝ)^6371 := by
    have hnat : (4678462621 : ℕ)^8419*100000000000000^6371 ≤ 36648453142317^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4678462621 10000000000 36648453142317 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (504172049/1250000000 : ℝ)^8419 ≤ (30123703868959/100000000000000 : ℝ)^6371 := by
    have hnat : (504172049 : ℕ)^8419*100000000000000^6371 ≤ 30123703868959^6371*1250000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504172049 1250000000 30123703868959 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4344113853/10000000000 : ℝ), (4678462621/10000000000 : ℝ), (504172049/1250000000 : ℝ)] ![(4153480371797/12500000000000 : ℝ), (36648453142317/100000000000000 : ℝ), (30123703868959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4344113853/10000000000 : ℝ)|^8419 ≤ (4153480371797/12500000000000 : ℝ)^6371
        have hw : |(4344113853/10000000000 : ℝ)|=(4344113853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4678462621/10000000000 : ℝ)|^8419 ≤ (36648453142317/100000000000000 : ℝ)^6371
        have hw : |(4678462621/10000000000 : ℝ)|=(4678462621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(504172049/1250000000 : ℝ)|^8419 ≤ (30123703868959/100000000000000 : ℝ)^6371
        have hw : |(504172049/1250000000 : ℝ)|=(504172049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1226_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30223053/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20067/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6107/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4717/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3253/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20067/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6107/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20067/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6107/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20067/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6107/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20067/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6107/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20067/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6107/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20067/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6107/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6107/100000 : ℝ) ^ (4209/1024 : ℝ) ≤ (510852941203391/50000000000000000000 : ℝ) := by
    have hpowers : (6107/100000 : ℝ)^4209 ≤ (510852941203391/50000000000000000000 : ℝ)^1024 := by
      have hnat : (6107 : ℕ)^4209*50000000000000000000^1024 ≤ 510852941203391^1024*100000^4209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6107 100000 510852941203391 50000000000000000000 4209 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6107/100000 : ℝ)) (X := (510852941203391/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20067/100000 : ℝ) ^ (4209/1024 : ℝ) ≤ (135818100172567749/100000000000000000000 : ℝ) := by
    have hpowers : (20067/100000 : ℝ)^4209 ≤ (135818100172567749/100000000000000000000 : ℝ)^1024 := by
      have hnat : (20067 : ℕ)^4209*100000000000000000000^1024 ≤ 135818100172567749^1024*100000^4209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20067 100000 135818100172567749 100000000000000000000 4209 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20067/100000 : ℝ)) (X := (135818100172567749/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000510852941203391/25000000000000000000 : ℝ) ≤ (500002485670551/500000000000000 : ℝ) ^ (4209/1024 : ℝ) := by
    have hpowers : (25000510852941203391/25000000000000000000 : ℝ)^1024 ≤ (500002485670551/500000000000000 : ℝ)^4209 := by
      have hnat : (25000510852941203391 : ℕ)^1024*500000000000000^4209 ≤ 500002485670551^4209*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000510852941203391 25000000000000000000 500002485670551 500000000000000 1024 4209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500002485670551/500000000000000 : ℝ)) (X := (25000510852941203391/25000000000000000000 : ℝ)) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100136839806054974531/100000000000000000000 : ℝ) ≤ (10003327428640767/10000000000000000 : ℝ) ^ (4209/1024 : ℝ) := by
    have hpowers : (100136839806054974531/100000000000000000000 : ℝ)^1024 ≤ (10003327428640767/10000000000000000 : ℝ)^4209 := by
      have hnat : (100136839806054974531 : ℕ)^1024*10000000000000000^4209 ≤ 10003327428640767^4209*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100136839806054974531 100000000000000000000 10003327428640767 10000000000000000 1024 4209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003327428640767/10000000000000000 : ℝ)) (X := (100136839806054974531/100000000000000000000 : ℝ)) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50135818100172567749/50000000000000000000 : ℝ) ≤ (5003302571935257/5000000000000000 : ℝ) ^ (4209/1024 : ℝ) := by
    have hpowers : (50135818100172567749/50000000000000000000 : ℝ)^1024 ≤ (5003302571935257/5000000000000000 : ℝ)^4209 := by
      have hnat : (50135818100172567749 : ℕ)^1024*5000000000000000^4209 ≤ 5003302571935257^4209*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50135818100172567749 50000000000000000000 5003302571935257 5000000000000000 1024 4209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003302571935257/5000000000000000 : ℝ)) (X := (50135818100172567749/50000000000000000000 : ℝ)) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(510852941203391/50000000000000000000 : ℝ) ≤ ((69780329992700854671/69800000000000000000 : ℝ)+2*(3277715229747/1396000000000000 : ℝ)*(6107/100000 : ℝ))^(4209/1024 : ℝ) := by
    rw [show (69780329992700854671/69800000000000000000 : ℝ)+2*(3277715229747/1396000000000000 : ℝ)*(6107/100000 : ℝ)=(500002485670551/500000000000000 : ℝ) by norm_num, show 1+2*(510852941203391/50000000000000000000 : ℝ)=(25000510852941203391/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(135818100172567749/100000000000000000000 : ℝ)+(510852941203391/50000000000000000000 : ℝ) ≤ ((69780329992700854671/69800000000000000000 : ℝ)+(3277715229747/1396000000000000 : ℝ)*((20067/100000 : ℝ)+(6107/100000 : ℝ)))^(4209/1024 : ℝ) := by
    rw [show (69780329992700854671/69800000000000000000 : ℝ)+(3277715229747/1396000000000000 : ℝ)*((20067/100000 : ℝ)+(6107/100000 : ℝ))=(10003327428640767/10000000000000000 : ℝ) by norm_num, show 1+(135818100172567749/100000000000000000000 : ℝ)+(510852941203391/50000000000000000000 : ℝ)=(100136839806054974531/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(135818100172567749/100000000000000000000 : ℝ) ≤ ((69780329992700854671/69800000000000000000 : ℝ)+2*(3277715229747/1396000000000000 : ℝ)*(20067/100000 : ℝ))^(4209/1024 : ℝ) := by
    rw [show (69780329992700854671/69800000000000000000 : ℝ)+2*(3277715229747/1396000000000000 : ℝ)*(20067/100000 : ℝ)=(5003302571935257/5000000000000000 : ℝ) by norm_num, show 1+2*(135818100172567749/100000000000000000000 : ℝ)=(50135818100172567749/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (69780329992700854671/69800000000000000000 : ℝ)*(X 1 0+X 2 0)+(3277715229747/1396000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4209/1024 : ℝ)) (lo := (6107/100000 : ℝ)) (hi := (20067/100000 : ℝ)) (c := (69780329992700854671/69800000000000000000 : ℝ)) (alpha := (3277715229747/1396000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (69780329992700854671/69800000000000000000 : ℝ)*(X 0 1+X 2 1)+(3277715229747/1396000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4209/1024 : ℝ)) (lo := (6107/100000 : ℝ)) (hi := (20067/100000 : ℝ)) (c := (69780329992700854671/69800000000000000000 : ℝ)) (alpha := (3277715229747/1396000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (69780329992700854671/69800000000000000000 : ℝ)*(X 0 2+X 1 2)+(3277715229747/1396000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4209/1024 : ℝ)) (lo := (6107/100000 : ℝ)) (hi := (20067/100000 : ℝ)) (c := (69780329992700854671/69800000000000000000 : ℝ)) (alpha := (3277715229747/1396000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-422585767/2000000000 : ℝ)*X 0 0+(549554061/1000000000 : ℝ)*X 0 1+(5172333637/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2685169619/5000000000 : ℝ)*X 1 0+(-570110453/2500000000 : ℝ)*X 1 1+(2586166787/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5370339047/10000000000 : ℝ)*X 2 0+(5172333743/10000000000 : ℝ)*X 2 1+(-570110461/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1085987233/2500000000 : ℝ)*X 0 0+(805817557/2000000000 : ℝ)*X 0 1+(4682711209/10000000000 : ℝ)*X 0 2+(1085987233/2500000000 : ℝ)*X 1 0+(805817557/2000000000 : ℝ)*X 1 1+(4682711209/10000000000 : ℝ)*X 1 2+(1085987233/2500000000 : ℝ)*X 2 0+(805817557/2000000000 : ℝ)*X 2 1+(4682711209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-528252663/2500000000 : ℝ)*X 0 0+(517443457/1000000000 : ℝ)*X 0 1+(5493419777/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643941657/5000000000 : ℝ)*X 1 0+(-489838859/2500000000 : ℝ)*X 1 1+(1098683963/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2643941747/5000000000 : ℝ)*X 2 0+(549341987/1000000000 : ℝ)*X 2 1+(-1959355111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4344113853/10000000000 : ℝ)*X 0 0+(4678462621/10000000000 : ℝ)*X 0 1+(504172049/1250000000 : ℝ)*X 0 2+(4344113853/10000000000 : ℝ)*X 1 0+(4678462621/10000000000 : ℝ)*X 1 1+(504172049/1250000000 : ℝ)*X 1 2+(4344113853/10000000000 : ℝ)*X 2 0+(4678462621/10000000000 : ℝ)*X 2 1+(504172049/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6677579124469202108392472577/1745000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (745623727/100000000000000 : ℝ)*(base19) + (288340701/50000000000000 : ℝ)*(base23) + (15816117/50000000000000 : ℝ)*(lower2) + (69534753/50000000000000 : ℝ)*(upper3) + (5535271/12500000000000 : ℝ)*(upper5) + (1155987003250857/50000000000000 : ℝ)*(major0) + (1155987003250857/50000000000000 : ℝ)*(major1) + (1155987003250857/50000000000000 : ℝ)*(major2) + (1547000435523357/50000000000000 : ℝ)*(sp0) + (3094006397899067/100000000000000 : ℝ)*(sp1) + (193375410427587/6250000000000 : ℝ)*(sp2) + (305987290632591/20000000000000 : ℝ)*(sp3) + (6272476079/100000000000000 : ℝ)*(sp4) + (107219031/2500000000000 : ℝ)*(sp7) + (305988148384839/20000000000000 : ℝ)*(f.failure) + (1547003571761397/50000000000000 : ℝ)*(f.sum) + (517114781379/34900000000000000000000000000 : ℝ)*base65 + (34356522996822153047/3490000000000000000000000000000000 : ℝ)*base67 + (15392838134232153047/3490000000000000000000000000000000 : ℝ)*base69 + (24097872367732153047/3490000000000000000000000000000000 : ℝ)*base71 + (128373653710721/34900000000000000000000000000 : ℝ)*base74 + (29531378657302153047/3490000000000000000000000000000000 : ℝ)*base75 + (14885171119512153047/3490000000000000000000000000000000 : ℝ)*base77 + (20044089932682153047/3490000000000000000000000000000000 : ℝ)*base79 + (93427464119121/34900000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2506533/400000000000000000000 : ℝ)*base90 + (2506533/400000000000000000000 : ℝ)*base92 + (2506533/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (80829491577494698921251/34900000000000000000000000000 : ℝ) := by norm_num
    linear_combination (824944119/100000000000000 : ℝ)*(base19) + (285656049/25000000000000 : ℝ)*(base23) + (15589261/25000000000000 : ℝ)*(upper2) + (66763207/50000000000000 : ℝ)*(upper3) + (44514659/100000000000000 : ℝ)*(upper5) + (1171280297307863/50000000000000 : ℝ)*(major0) + (1171280297307863/50000000000000 : ℝ)*(major1) + (1171280297307863/50000000000000 : ℝ)*(major2) + (19477169/250000000000 : ℝ)*(sp1) + (3439425653/25000000000000 : ℝ)*(sp2) + (195933737625711/6250000000000 : ℝ)*(sp4) + (391866398274957/12500000000000 : ℝ)*(sp5) + (391865612710571/12500000000000 : ℝ)*(sp6) + (387545327504757/25000000000000 : ℝ)*(sp7) + (387545327504757/25000000000000 : ℝ)*(f.failure) + (195933737625711/6250000000000 : ℝ)*(f.sum) + (19477535753861/34900000000000000000000000000 : ℝ)*base65 + (1173336960378371927/3490000000000000000000000000000000 : ℝ)*base68 + (8335687436178371927/3490000000000000000000000000000000 : ℝ)*base70 + (12889956709221628073/3490000000000000000000000000000000 : ℝ)*base71 + (172321616697861/34900000000000000000000000000 : ℝ)*base73 + (7062182484701628073/3490000000000000000000000000000000 : ℝ)*base75 + (42187068467058371927/3490000000000000000000000000000000 : ℝ)*base78 + (2237319439181628073/3490000000000000000000000000000000 : ℝ)*base79 + (111709661940661/34900000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1436879/500000000000000000000 : ℝ)*base90 + (1436879/500000000000000000000 : ℝ)*base92 + (1436879/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1226_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30223053/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20067/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6107/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4717/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3253/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1226_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1226_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30223053/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4717/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3253/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1226_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1226_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1226_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30223053/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4717/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3253/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1226_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

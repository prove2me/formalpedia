-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1645_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:11:56.132388+00:00
-- url     : https://prove2.me/submissions/dea3ffa5-e355-4b88-aa94-db2b09db3db0

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
theorem support_rectangle_w1645_box_0 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1360222303/10000000000 : ℝ)*x 0 + (270464851/500000000 : ℝ)*x 1 + (540929621/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1360222303/10000000000 : ℝ)^4899 ≤ (1605792088923/20000000000000 : ℝ)^3875 := by
    have hnat : (1360222303 : ℕ)^4899*20000000000000^3875 ≤ 1605792088923^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360222303 10000000000 1605792088923 20000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270464851/500000000 : ℝ)^4899 ≤ (45985524126097/100000000000000 : ℝ)^3875 := by
    have hnat : (270464851 : ℕ)^4899*100000000000000^3875 ≤ 45985524126097^3875*500000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270464851 500000000 45985524126097 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540929621/1000000000 : ℝ)^4899 ≤ (919710308409/2000000000000 : ℝ)^3875 := by
    have hnat : (540929621 : ℕ)^4899*2000000000000^3875 ≤ 919710308409^3875*1000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540929621 1000000000 919710308409 2000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1360222303/10000000000 : ℝ), (270464851/500000000 : ℝ), (540929621/1000000000 : ℝ)] ![(1605792088923/20000000000000 : ℝ), (45985524126097/100000000000000 : ℝ), (919710308409/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1360222303/10000000000 : ℝ)|^4899 ≤ (1605792088923/20000000000000 : ℝ)^3875
        have hw : |(-1360222303/10000000000 : ℝ)|=(1360222303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270464851/500000000 : ℝ)|^4899 ≤ (45985524126097/100000000000000 : ℝ)^3875
        have hw : |(270464851/500000000 : ℝ)|=(270464851/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540929621/1000000000 : ℝ)|^4899 ≤ (919710308409/2000000000000 : ℝ)^3875
        have hw : |(540929621/1000000000 : ℝ)|=(540929621/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_box_1 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625573411/5000000000 : ℝ)*x 0 + (-197811091/1250000000 : ℝ)*x 1 + (2704648241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625573411/5000000000 : ℝ)^4899 ≤ (2768274070081/6250000000000 : ℝ)^3875 := by
    have hnat : (2625573411 : ℕ)^4899*6250000000000^3875 ≤ 2768274070081^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625573411 5000000000 2768274070081 6250000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (197811091/1250000000 : ℝ)^4899 ≤ (9722096523051/100000000000000 : ℝ)^3875 := by
    have hnat : (197811091 : ℕ)^4899*100000000000000^3875 ≤ 9722096523051^3875*1250000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197811091 1250000000 9722096523051 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704648241/5000000000 : ℝ)^4899 ≤ (11496379585957/25000000000000 : ℝ)^3875 := by
    have hnat : (2704648241 : ℕ)^4899*25000000000000^3875 ≤ 11496379585957^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704648241 5000000000 11496379585957 25000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625573411/5000000000 : ℝ), (-197811091/1250000000 : ℝ), (2704648241/5000000000 : ℝ)] ![(2768274070081/6250000000000 : ℝ), (9722096523051/100000000000000 : ℝ), (11496379585957/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625573411/5000000000 : ℝ)|^4899 ≤ (2768274070081/6250000000000 : ℝ)^3875
        have hw : |(2625573411/5000000000 : ℝ)|=(2625573411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-197811091/1250000000 : ℝ)|^4899 ≤ (9722096523051/100000000000000 : ℝ)^3875
        have hw : |(-197811091/1250000000 : ℝ)|=(197811091/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704648241/5000000000 : ℝ)|^4899 ≤ (11496379585957/25000000000000 : ℝ)^3875
        have hw : |(2704648241/5000000000 : ℝ)|=(2704648241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_box_2 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251146991/10000000000 : ℝ)*x 0 + (540929657/1000000000 : ℝ)*x 1 + (-1582488373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251146991/10000000000 : ℝ)^4899 ≤ (44292386923473/100000000000000 : ℝ)^3875 := by
    have hnat : (5251146991 : ℕ)^4899*100000000000000^3875 ≤ 44292386923473^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251146991 10000000000 44292386923473 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540929657/1000000000 : ℝ)^4899 ≤ (45985519289627/100000000000000 : ℝ)^3875 := by
    have hnat : (540929657 : ℕ)^4899*100000000000000^3875 ≤ 45985519289627^3875*1000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540929657 1000000000 45985519289627 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1582488373/10000000000 : ℝ)^4899 ≤ (1944418753151/20000000000000 : ℝ)^3875 := by
    have hnat : (1582488373 : ℕ)^4899*20000000000000^3875 ≤ 1944418753151^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1582488373 10000000000 1944418753151 20000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251146991/10000000000 : ℝ), (540929657/1000000000 : ℝ), (-1582488373/10000000000 : ℝ)] ![(44292386923473/100000000000000 : ℝ), (45985519289627/100000000000000 : ℝ), (1944418753151/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251146991/10000000000 : ℝ)|^4899 ≤ (44292386923473/100000000000000 : ℝ)^3875
        have hw : |(5251146991/10000000000 : ℝ)|=(5251146991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540929657/1000000000 : ℝ)|^4899 ≤ (45985519289627/100000000000000 : ℝ)^3875
        have hw : |(540929657/1000000000 : ℝ)|=(540929657/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1582488373/10000000000 : ℝ)|^4899 ≤ (1944418753151/20000000000000 : ℝ)^3875
        have hw : |(-1582488373/10000000000 : ℝ)|=(1582488373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_box_3 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (892347233/2000000000 : ℝ)*x 0 + (4058133457/10000000000 : ℝ)*x 1 + (2029066817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (892347233/2000000000 : ℝ)^4899 ≤ (36048106782313/100000000000000 : ℝ)^3875 := by
    have hnat : (892347233 : ℕ)^4899*100000000000000^3875 ≤ 36048106782313^3875*2000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892347233 2000000000 36048106782313 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4058133457/10000000000 : ℝ)^4899 ≤ (3996993215361/12500000000000 : ℝ)^3875 := by
    have hnat : (4058133457 : ℕ)^4899*12500000000000^3875 ≤ 3996993215361^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4058133457 10000000000 3996993215361 12500000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2029066817/5000000000 : ℝ)^4899 ≤ (31975947486107/100000000000000 : ℝ)^3875 := by
    have hnat : (2029066817 : ℕ)^4899*100000000000000^3875 ≤ 31975947486107^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029066817 5000000000 31975947486107 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(892347233/2000000000 : ℝ), (4058133457/10000000000 : ℝ), (2029066817/5000000000 : ℝ)] ![(36048106782313/100000000000000 : ℝ), (3996993215361/12500000000000 : ℝ), (31975947486107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(892347233/2000000000 : ℝ)|^4899 ≤ (36048106782313/100000000000000 : ℝ)^3875
        have hw : |(892347233/2000000000 : ℝ)|=(892347233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4058133457/10000000000 : ℝ)|^4899 ≤ (3996993215361/12500000000000 : ℝ)^3875
        have hw : |(4058133457/10000000000 : ℝ)|=(4058133457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2029066817/5000000000 : ℝ)|^4899 ≤ (31975947486107/100000000000000 : ℝ)^3875
        have hw : |(2029066817/5000000000 : ℝ)|=(2029066817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_box_4 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1890416681/10000000000 : ℝ)*x 0 + (1043121057/2000000000 : ℝ)*x 1 + (651950671/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1890416681/10000000000 : ℝ)^4899 ≤ (1217256316413/10000000000000 : ℝ)^3875 := by
    have hnat : (1890416681 : ℕ)^4899*10000000000000^3875 ≤ 1217256316413^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1890416681 10000000000 1217256316413 10000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043121057/2000000000 : ℝ)^4899 ≤ (137230368647/312500000000 : ℝ)^3875 := by
    have hnat : (1043121057 : ℕ)^4899*312500000000^3875 ≤ 137230368647^3875*2000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043121057 2000000000 137230368647 312500000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (651950671/1250000000 : ℝ)^4899 ≤ (8782743770109/20000000000000 : ℝ)^3875 := by
    have hnat : (651950671 : ℕ)^4899*20000000000000^3875 ≤ 8782743770109^3875*1250000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651950671 1250000000 8782743770109 20000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1890416681/10000000000 : ℝ), (1043121057/2000000000 : ℝ), (651950671/1250000000 : ℝ)] ![(1217256316413/10000000000000 : ℝ), (137230368647/312500000000 : ℝ), (8782743770109/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1890416681/10000000000 : ℝ)|^4899 ≤ (1217256316413/10000000000000 : ℝ)^3875
        have hw : |(-1890416681/10000000000 : ℝ)|=(1890416681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043121057/2000000000 : ℝ)|^4899 ≤ (137230368647/312500000000 : ℝ)^3875
        have hw : |(1043121057/2000000000 : ℝ)|=(1043121057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(651950671/1250000000 : ℝ)|^4899 ≤ (8782743770109/20000000000000 : ℝ)^3875
        have hw : |(651950671/1250000000 : ℝ)|=(651950671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_box_5 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5384181541/10000000000 : ℝ)*x 0 + (-832703279/5000000000 : ℝ)*x 1 + (5215605427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5384181541/10000000000 : ℝ)^4899 ≤ (22857877981747/50000000000000 : ℝ)^3875 := by
    have hnat : (5384181541 : ℕ)^4899*50000000000000^3875 ≤ 22857877981747^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384181541 10000000000 22857877981747 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (832703279/5000000000 : ℝ)^4899 ≤ (10370524549089/100000000000000 : ℝ)^3875 := by
    have hnat : (832703279 : ℕ)^4899*100000000000000^3875 ≤ 10370524549089^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832703279 5000000000 10370524549089 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215605427/10000000000 : ℝ)^4899 ≤ (43913719478579/100000000000000 : ℝ)^3875 := by
    have hnat : (5215605427 : ℕ)^4899*100000000000000^3875 ≤ 43913719478579^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215605427 10000000000 43913719478579 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5384181541/10000000000 : ℝ), (-832703279/5000000000 : ℝ), (5215605427/10000000000 : ℝ)] ![(22857877981747/50000000000000 : ℝ), (10370524549089/100000000000000 : ℝ), (43913719478579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5384181541/10000000000 : ℝ)|^4899 ≤ (22857877981747/50000000000000 : ℝ)^3875
        have hw : |(5384181541/10000000000 : ℝ)|=(5384181541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-832703279/5000000000 : ℝ)|^4899 ≤ (10370524549089/100000000000000 : ℝ)^3875
        have hw : |(-832703279/5000000000 : ℝ)|=(832703279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215605427/10000000000 : ℝ)|^4899 ≤ (43913719478579/100000000000000 : ℝ)^3875
        have hw : |(5215605427/10000000000 : ℝ)|=(5215605427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_box_6 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5384181533/10000000000 : ℝ)*x 0 + (5215605619/10000000000 : ℝ)*x 1 + (-416351577/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5384181533/10000000000 : ℝ)^4899 ≤ (22857877938809/50000000000000 : ℝ)^3875 := by
    have hnat : (5384181533 : ℕ)^4899*50000000000000^3875 ≤ 22857877938809^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384181533 10000000000 22857877938809 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215605619/10000000000 : ℝ)^4899 ≤ (43913721522351/100000000000000 : ℝ)^3875 := by
    have hnat : (5215605619 : ℕ)^4899*100000000000000^3875 ≤ 43913721522351^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215605619 10000000000 43913721522351 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416351577/2500000000 : ℝ)^4899 ≤ (2592630645237/25000000000000 : ℝ)^3875 := by
    have hnat : (416351577 : ℕ)^4899*25000000000000^3875 ≤ 2592630645237^3875*2500000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416351577 2500000000 2592630645237 25000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5384181533/10000000000 : ℝ), (5215605619/10000000000 : ℝ), (-416351577/2500000000 : ℝ)] ![(22857877938809/50000000000000 : ℝ), (43913721522351/100000000000000 : ℝ), (2592630645237/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5384181533/10000000000 : ℝ)|^4899 ≤ (22857877938809/50000000000000 : ℝ)^3875
        have hw : |(5384181533/10000000000 : ℝ)|=(5384181533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215605619/10000000000 : ℝ)|^4899 ≤ (43913721522351/100000000000000 : ℝ)^3875
        have hw : |(5215605619/10000000000 : ℝ)|=(5215605619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-416351577/2500000000 : ℝ)|^4899 ≤ (2592630645237/25000000000000 : ℝ)^3875
        have hw : |(-416351577/2500000000 : ℝ)|=(416351577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_box_7 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3901027201/10000000000 : ℝ)*x 0 + (4338160959/10000000000 : ℝ)*x 1 + (4338161001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3901027201/10000000000 : ℝ)^4899 ≤ (30418985559433/100000000000000 : ℝ)^3875 := by
    have hnat : (3901027201 : ℕ)^4899*100000000000000^3875 ≤ 30418985559433^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3901027201 10000000000 30418985559433 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4338160959/10000000000 : ℝ)^4899 ≤ (34790507001259/100000000000000 : ℝ)^3875 := by
    have hnat : (4338160959 : ℕ)^4899*100000000000000^3875 ≤ 34790507001259^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338160959 10000000000 34790507001259 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4338161001/10000000000 : ℝ)^4899 ≤ (34790507427093/100000000000000 : ℝ)^3875 := by
    have hnat : (4338161001 : ℕ)^4899*100000000000000^3875 ≤ 34790507427093^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338161001 10000000000 34790507427093 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3901027201/10000000000 : ℝ), (4338160959/10000000000 : ℝ), (4338161001/10000000000 : ℝ)] ![(30418985559433/100000000000000 : ℝ), (34790507001259/100000000000000 : ℝ), (34790507427093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3901027201/10000000000 : ℝ)|^4899 ≤ (30418985559433/100000000000000 : ℝ)^3875
        have hw : |(3901027201/10000000000 : ℝ)|=(3901027201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4338160959/10000000000 : ℝ)|^4899 ≤ (34790507001259/100000000000000 : ℝ)^3875
        have hw : |(4338160959/10000000000 : ℝ)|=(4338160959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4338161001/10000000000 : ℝ)|^4899 ≤ (34790507427093/100000000000000 : ℝ)^3875
        have hw : |(4338161001/10000000000 : ℝ)|=(4338161001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_box_8 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-888681097/5000000000 : ℝ)*x 0 + (2538210581/5000000000 : ℝ)*x 1 + (2719406579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (888681097/5000000000 : ℝ)^4899 ≤ (703725351947/6250000000000 : ℝ)^3875 := by
    have hnat : (888681097 : ℕ)^4899*6250000000000^3875 ≤ 703725351947^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888681097 5000000000 703725351947 6250000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2538210581/5000000000 : ℝ)^4899 ≤ (265233817801/625000000000 : ℝ)^3875 := by
    have hnat : (2538210581 : ℕ)^4899*625000000000^3875 ≤ 265233817801^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538210581 5000000000 265233817801 625000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719406579/5000000000 : ℝ)^4899 ≤ (46302983502863/100000000000000 : ℝ)^3875 := by
    have hnat : (2719406579 : ℕ)^4899*100000000000000^3875 ≤ 46302983502863^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719406579 5000000000 46302983502863 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-888681097/5000000000 : ℝ), (2538210581/5000000000 : ℝ), (2719406579/5000000000 : ℝ)] ![(703725351947/6250000000000 : ℝ), (265233817801/625000000000 : ℝ), (46302983502863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-888681097/5000000000 : ℝ)|^4899 ≤ (703725351947/6250000000000 : ℝ)^3875
        have hw : |(-888681097/5000000000 : ℝ)|=(888681097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2538210581/5000000000 : ℝ)|^4899 ≤ (265233817801/625000000000 : ℝ)^3875
        have hw : |(2538210581/5000000000 : ℝ)|=(2538210581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719406579/5000000000 : ℝ)|^4899 ≤ (46302983502863/100000000000000 : ℝ)^3875
        have hw : |(2719406579/5000000000 : ℝ)|=(2719406579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_box_9 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2615436327/5000000000 : ℝ)*x 0 + (-1569419897/10000000000 : ℝ)*x 1 + (2719407437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615436327/5000000000 : ℝ)^4899 ≤ (11019074129423/25000000000000 : ℝ)^3875 := by
    have hnat : (2615436327 : ℕ)^4899*25000000000000^3875 ≤ 11019074129423^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615436327 5000000000 11019074129423 25000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1569419897/10000000000 : ℝ)^4899 ≤ (9620701494107/100000000000000 : ℝ)^3875 := by
    have hnat : (1569419897 : ℕ)^4899*100000000000000^3875 ≤ 9620701494107^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1569419897 10000000000 9620701494107 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719407437/5000000000 : ℝ)^4899 ≤ (46303001972479/100000000000000 : ℝ)^3875 := by
    have hnat : (2719407437 : ℕ)^4899*100000000000000^3875 ≤ 46303001972479^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719407437 5000000000 46303001972479 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2615436327/5000000000 : ℝ), (-1569419897/10000000000 : ℝ), (2719407437/5000000000 : ℝ)] ![(11019074129423/25000000000000 : ℝ), (9620701494107/100000000000000 : ℝ), (46303001972479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2615436327/5000000000 : ℝ)|^4899 ≤ (11019074129423/25000000000000 : ℝ)^3875
        have hw : |(2615436327/5000000000 : ℝ)|=(2615436327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1569419897/10000000000 : ℝ)|^4899 ≤ (9620701494107/100000000000000 : ℝ)^3875
        have hw : |(-1569419897/10000000000 : ℝ)|=(1569419897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719407437/5000000000 : ℝ)|^4899 ≤ (46303001972479/100000000000000 : ℝ)^3875
        have hw : |(2719407437/5000000000 : ℝ)|=(2719407437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_box_10 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1046174441/2000000000 : ℝ)*x 0 + (2719407453/5000000000 : ℝ)*x 1 + (-156942047/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046174441/2000000000 : ℝ)^4899 ≤ (44076291734553/100000000000000 : ℝ)^3875 := by
    have hnat : (1046174441 : ℕ)^4899*100000000000000^3875 ≤ 44076291734553^3875*2000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046174441 2000000000 44076291734553 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719407453/5000000000 : ℝ)^4899 ≤ (46303002316901/100000000000000 : ℝ)^3875 := by
    have hnat : (2719407453 : ℕ)^4899*100000000000000^3875 ≤ 46303002316901^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719407453 5000000000 46303002316901 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (156942047/1000000000 : ℝ)^4899 ≤ (4810352967437/50000000000000 : ℝ)^3875 := by
    have hnat : (156942047 : ℕ)^4899*50000000000000^3875 ≤ 4810352967437^3875*1000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156942047 1000000000 4810352967437 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046174441/2000000000 : ℝ), (2719407453/5000000000 : ℝ), (-156942047/1000000000 : ℝ)] ![(44076291734553/100000000000000 : ℝ), (46303002316901/100000000000000 : ℝ), (4810352967437/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046174441/2000000000 : ℝ)|^4899 ≤ (44076291734553/100000000000000 : ℝ)^3875
        have hw : |(1046174441/2000000000 : ℝ)|=(1046174441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719407453/5000000000 : ℝ)|^4899 ≤ (46303002316901/100000000000000 : ℝ)^3875
        have hw : |(2719407453/5000000000 : ℝ)|=(2719407453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-156942047/1000000000 : ℝ)|^4899 ≤ (4810352967437/50000000000000 : ℝ)^3875
        have hw : |(-156942047/1000000000 : ℝ)|=(156942047/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_box_11 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2272401741/5000000000 : ℝ)*x 0 + (4015383151/10000000000 : ℝ)*x 1 + (501922641/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2272401741/5000000000 : ℝ)^4899 ≤ (1475946807269/4000000000000 : ℝ)^3875 := by
    have hnat : (2272401741 : ℕ)^4899*4000000000000^3875 ≤ 1475946807269^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272401741 5000000000 1475946807269 4000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4015383151/10000000000 : ℝ)^4899 ≤ (31550674944539/100000000000000 : ℝ)^3875 := by
    have hnat : (4015383151 : ℕ)^4899*100000000000000^3875 ≤ 31550674944539^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4015383151 10000000000 31550674944539 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501922641/1250000000 : ℝ)^4899 ≤ (7887663712093/25000000000000 : ℝ)^3875 := by
    have hnat : (501922641 : ℕ)^4899*25000000000000^3875 ≤ 7887663712093^3875*1250000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501922641 1250000000 7887663712093 25000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2272401741/5000000000 : ℝ), (4015383151/10000000000 : ℝ), (501922641/1250000000 : ℝ)] ![(1475946807269/4000000000000 : ℝ), (31550674944539/100000000000000 : ℝ), (7887663712093/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2272401741/5000000000 : ℝ)|^4899 ≤ (1475946807269/4000000000000 : ℝ)^3875
        have hw : |(2272401741/5000000000 : ℝ)|=(2272401741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4015383151/10000000000 : ℝ)|^4899 ≤ (31550674944539/100000000000000 : ℝ)^3875
        have hw : |(4015383151/10000000000 : ℝ)|=(4015383151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(501922641/1250000000 : ℝ)|^4899 ≤ (7887663712093/25000000000000 : ℝ)^3875
        have hw : |(501922641/1250000000 : ℝ)|=(501922641/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_box_12 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1471574889/10000000000 : ℝ)*x 0 + (5543122177/10000000000 : ℝ)*x 1 + (1039155109/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1471574889/10000000000 : ℝ)^4899 ≤ (8868744588941/100000000000000 : ℝ)^3875 := by
    have hnat : (1471574889 : ℕ)^4899*100000000000000^3875 ≤ 8868744588941^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1471574889 10000000000 8868744588941 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5543122177/10000000000 : ℝ)^4899 ≤ (47428511863341/100000000000000 : ℝ)^3875 := by
    have hnat : (5543122177 : ℕ)^4899*100000000000000^3875 ≤ 47428511863341^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5543122177 10000000000 47428511863341 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039155109/2000000000 : ℝ)^4899 ≤ (1748109741611/4000000000000 : ℝ)^3875 := by
    have hnat : (1039155109 : ℕ)^4899*4000000000000^3875 ≤ 1748109741611^3875*2000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039155109 2000000000 1748109741611 4000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1471574889/10000000000 : ℝ), (5543122177/10000000000 : ℝ), (1039155109/2000000000 : ℝ)] ![(8868744588941/100000000000000 : ℝ), (47428511863341/100000000000000 : ℝ), (1748109741611/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1471574889/10000000000 : ℝ)|^4899 ≤ (8868744588941/100000000000000 : ℝ)^3875
        have hw : |(-1471574889/10000000000 : ℝ)|=(1471574889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5543122177/10000000000 : ℝ)|^4899 ≤ (47428511863341/100000000000000 : ℝ)^3875
        have hw : |(5543122177/10000000000 : ℝ)|=(5543122177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1039155109/2000000000 : ℝ)|^4899 ≤ (1748109741611/4000000000000 : ℝ)^3875
        have hw : |(1039155109/2000000000 : ℝ)|=(1039155109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_box_13 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5397810847/10000000000 : ℝ)*x 0 + (-418402511/2500000000 : ℝ)*x 1 + (1298943857/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5397810847/10000000000 : ℝ)^4899 ≤ (22931054346807/50000000000000 : ℝ)^3875 := by
    have hnat : (5397810847 : ℕ)^4899*50000000000000^3875 ≤ 22931054346807^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397810847 10000000000 22931054346807 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (418402511/2500000000 : ℝ)^4899 ≤ (1304393624747/12500000000000 : ℝ)^3875 := by
    have hnat : (418402511 : ℕ)^4899*12500000000000^3875 ≤ 1304393624747^3875*2500000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418402511 2500000000 1304393624747 12500000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1298943857/2500000000 : ℝ)^4899 ≤ (5462842787013/12500000000000 : ℝ)^3875 := by
    have hnat : (1298943857 : ℕ)^4899*12500000000000^3875 ≤ 5462842787013^3875*2500000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298943857 2500000000 5462842787013 12500000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5397810847/10000000000 : ℝ), (-418402511/2500000000 : ℝ), (1298943857/2500000000 : ℝ)] ![(22931054346807/50000000000000 : ℝ), (1304393624747/12500000000000 : ℝ), (5462842787013/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5397810847/10000000000 : ℝ)|^4899 ≤ (22931054346807/50000000000000 : ℝ)^3875
        have hw : |(5397810847/10000000000 : ℝ)|=(5397810847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-418402511/2500000000 : ℝ)|^4899 ≤ (1304393624747/12500000000000 : ℝ)^3875
        have hw : |(-418402511/2500000000 : ℝ)|=(418402511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1298943857/2500000000 : ℝ)|^4899 ≤ (5462842787013/12500000000000 : ℝ)^3875
        have hw : |(1298943857/2500000000 : ℝ)|=(1298943857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_box_14 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5397810841/10000000000 : ℝ)*x 0 + (2597887641/5000000000 : ℝ)*x 1 + (-6694441/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5397810841/10000000000 : ℝ)^4899 ≤ (11465527157291/25000000000000 : ℝ)^3875 := by
    have hnat : (5397810841 : ℕ)^4899*25000000000000^3875 ≤ 11465527157291^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397810841 10000000000 11465527157291 25000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2597887641/5000000000 : ℝ)^4899 ≤ (43702740743549/100000000000000 : ℝ)^3875 := by
    have hnat : (2597887641 : ℕ)^4899*100000000000000^3875 ≤ 43702740743549^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597887641 5000000000 43702740743549 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6694441/40000000 : ℝ)^4899 ≤ (10435150621831/100000000000000 : ℝ)^3875 := by
    have hnat : (6694441 : ℕ)^4899*100000000000000^3875 ≤ 10435150621831^3875*40000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6694441 40000000 10435150621831 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5397810841/10000000000 : ℝ), (2597887641/5000000000 : ℝ), (-6694441/40000000 : ℝ)] ![(11465527157291/25000000000000 : ℝ), (43702740743549/100000000000000 : ℝ), (10435150621831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5397810841/10000000000 : ℝ)|^4899 ≤ (11465527157291/25000000000000 : ℝ)^3875
        have hw : |(5397810841/10000000000 : ℝ)|=(5397810841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2597887641/5000000000 : ℝ)|^4899 ≤ (43702740743549/100000000000000 : ℝ)^3875
        have hw : |(2597887641/5000000000 : ℝ)|=(2597887641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6694441/40000000 : ℝ)|^4899 ≤ (10435150621831/100000000000000 : ℝ)^3875
        have hw : |(-6694441/40000000 : ℝ)|=(6694441/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_box_15 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (480249263/1250000000 : ℝ)*x 0 + (4366778737/10000000000 : ℝ)*x 1 + (4366777471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (480249263/1250000000 : ℝ)^4899 ≤ (29838188284457/100000000000000 : ℝ)^3875 := by
    have hnat : (480249263 : ℕ)^4899*100000000000000^3875 ≤ 29838188284457^3875*1250000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480249263 1250000000 29838188284457 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4366778737/10000000000 : ℝ)^4899 ≤ (35080912279097/100000000000000 : ℝ)^3875 := by
    have hnat : (4366778737 : ℕ)^4899*100000000000000^3875 ≤ 35080912279097^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366778737 10000000000 35080912279097 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4366777471/10000000000 : ℝ)^4899 ≤ (137034763363/390625000000 : ℝ)^3875 := by
    have hnat : (4366777471 : ℕ)^4899*390625000000^3875 ≤ 137034763363^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366777471 10000000000 137034763363 390625000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(480249263/1250000000 : ℝ), (4366778737/10000000000 : ℝ), (4366777471/10000000000 : ℝ)] ![(29838188284457/100000000000000 : ℝ), (35080912279097/100000000000000 : ℝ), (137034763363/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(480249263/1250000000 : ℝ)|^4899 ≤ (29838188284457/100000000000000 : ℝ)^3875
        have hw : |(480249263/1250000000 : ℝ)|=(480249263/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4366778737/10000000000 : ℝ)|^4899 ≤ (35080912279097/100000000000000 : ℝ)^3875
        have hw : |(4366778737/10000000000 : ℝ)|=(4366778737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4366777471/10000000000 : ℝ)|^4899 ≤ (137034763363/390625000000 : ℝ)^3875
        have hw : |(4366777471/10000000000 : ℝ)|=(4366777471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1645_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35709611/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(65047/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14643/25000 : ℝ) ∧ (16221/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (3527/4000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16277/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2661/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16277/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2661/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16277/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2661/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16277/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2661/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16277/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2661/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16277/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2661/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2661/25000 : ℝ) ^ (4895/1024 : ℝ) ≤ (2235091118876023/100000000000000000000 : ℝ) := by
    have hpowers : (2661/25000 : ℝ)^4895 ≤ (2235091118876023/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2661 : ℕ)^4895*100000000000000000000^1024 ≤ 2235091118876023^1024*25000^4895 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2661 25000 2235091118876023 100000000000000000000 4895 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2661/25000 : ℝ)) (X := (2235091118876023/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16277/100000 : ℝ) ^ (4895/1024 : ℝ) ≤ (8512945962745767/50000000000000000000 : ℝ) := by
    have hpowers : (16277/100000 : ℝ)^4895 ≤ (8512945962745767/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16277 : ℕ)^4895*50000000000000000000^1024 ≤ 8512945962745767^1024*100000^4895 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16277 100000 8512945962745767 50000000000000000000 4895 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16277/100000 : ℝ)) (X := (8512945962745767/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002235091118876023/50000000000000000000 : ℝ) ≤ (10000093511454663/10000000000000000 : ℝ) ^ (4895/1024 : ℝ) := by
    have hpowers : (50002235091118876023/50000000000000000000 : ℝ)^1024 ≤ (10000093511454663/10000000000000000 : ℝ)^4895 := by
      have hnat : (50002235091118876023 : ℕ)^1024*10000000000000000^4895 ≤ 10000093511454663^4895*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002235091118876023 50000000000000000000 10000093511454663 10000000000000000 1024 4895 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000093511454663/10000000000000000 : ℝ)) (X := (50002235091118876023/50000000000000000000 : ℝ)) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100019260983044367557/100000000000000000000 : ℝ) ≤ (10000402895704093/10000000000000000 : ℝ) ^ (4895/1024 : ℝ) := by
    have hpowers : (100019260983044367557/100000000000000000000 : ℝ)^1024 ≤ (10000402895704093/10000000000000000 : ℝ)^4895 := by
      have hnat : (100019260983044367557 : ℕ)^1024*10000000000000000^4895 ≤ 10000402895704093^4895*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019260983044367557 100000000000000000000 10000402895704093 10000000000000000 1024 4895 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000402895704093/10000000000000000 : ℝ)) (X := (100019260983044367557/100000000000000000000 : ℝ)) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25008512945962745767/25000000000000000000 : ℝ) ≤ (10000712279953523/10000000000000000 : ℝ) ^ (4895/1024 : ℝ) := by
    have hpowers : (25008512945962745767/25000000000000000000 : ℝ)^1024 ≤ (10000712279953523/10000000000000000 : ℝ)^4895 := by
      have hnat : (25008512945962745767 : ℕ)^1024*10000000000000000^4895 ≤ 10000712279953523^4895*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008512945962745767 25000000000000000000 10000712279953523 10000000000000000 1024 4895 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000712279953523/10000000000000000 : ℝ)) (X := (25008512945962745767/25000000000000000000 : ℝ)) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2235091118876023/100000000000000000000 : ℝ) ≤ ((56323940578122250839/56330000000000000000 : ℝ)+2*(30938424943/56330000000000 : ℝ)*(2661/25000 : ℝ))^(4895/1024 : ℝ) := by
    rw [show (56323940578122250839/56330000000000000000 : ℝ)+2*(30938424943/56330000000000 : ℝ)*(2661/25000 : ℝ)=(10000093511454663/10000000000000000 : ℝ) by norm_num, show 1+2*(2235091118876023/100000000000000000000 : ℝ)=(50002235091118876023/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8512945962745767/50000000000000000000 : ℝ)+(2235091118876023/100000000000000000000 : ℝ) ≤ ((56323940578122250839/56330000000000000000 : ℝ)+(30938424943/56330000000000 : ℝ)*((16277/100000 : ℝ)+(2661/25000 : ℝ)))^(4895/1024 : ℝ) := by
    rw [show (56323940578122250839/56330000000000000000 : ℝ)+(30938424943/56330000000000 : ℝ)*((16277/100000 : ℝ)+(2661/25000 : ℝ))=(10000402895704093/10000000000000000 : ℝ) by norm_num, show 1+(8512945962745767/50000000000000000000 : ℝ)+(2235091118876023/100000000000000000000 : ℝ)=(100019260983044367557/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8512945962745767/50000000000000000000 : ℝ) ≤ ((56323940578122250839/56330000000000000000 : ℝ)+2*(30938424943/56330000000000 : ℝ)*(16277/100000 : ℝ))^(4895/1024 : ℝ) := by
    rw [show (56323940578122250839/56330000000000000000 : ℝ)+2*(30938424943/56330000000000 : ℝ)*(16277/100000 : ℝ)=(10000712279953523/10000000000000000 : ℝ) by norm_num, show 1+2*(8512945962745767/50000000000000000000 : ℝ)=(25008512945962745767/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (56323940578122250839/56330000000000000000 : ℝ)*(X 1 0+X 2 0)+(30938424943/56330000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4895/1024 : ℝ)) (lo := (2661/25000 : ℝ)) (hi := (16277/100000 : ℝ)) (c := (56323940578122250839/56330000000000000000 : ℝ)) (alpha := (30938424943/56330000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (56323940578122250839/56330000000000000000 : ℝ)*(X 0 1+X 2 1)+(30938424943/56330000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4895/1024 : ℝ)) (lo := (2661/25000 : ℝ)) (hi := (16277/100000 : ℝ)) (c := (56323940578122250839/56330000000000000000 : ℝ)) (alpha := (30938424943/56330000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (56323940578122250839/56330000000000000000 : ℝ)*(X 0 2+X 1 2)+(30938424943/56330000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4895/1024 : ℝ)) (lo := (2661/25000 : ℝ)) (hi := (16277/100000 : ℝ)) (c := (56323940578122250839/56330000000000000000 : ℝ)) (alpha := (30938424943/56330000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1360222303/10000000000 : ℝ)*X 0 0+(270464851/500000000 : ℝ)*X 0 1+(540929621/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2625573411/5000000000 : ℝ)*X 1 0+(-197811091/1250000000 : ℝ)*X 1 1+(2704648241/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5251146991/10000000000 : ℝ)*X 2 0+(540929657/1000000000 : ℝ)*X 2 1+(-1582488373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((892347233/2000000000 : ℝ)*X 0 0+(4058133457/10000000000 : ℝ)*X 0 1+(2029066817/5000000000 : ℝ)*X 0 2+(892347233/2000000000 : ℝ)*X 1 0+(4058133457/10000000000 : ℝ)*X 1 1+(2029066817/5000000000 : ℝ)*X 1 2+(892347233/2000000000 : ℝ)*X 2 0+(4058133457/10000000000 : ℝ)*X 2 1+(2029066817/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1890416681/10000000000 : ℝ)*X 0 0+(1043121057/2000000000 : ℝ)*X 0 1+(651950671/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5384181541/10000000000 : ℝ)*X 1 0+(-832703279/5000000000 : ℝ)*X 1 1+(5215605427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5384181533/10000000000 : ℝ)*X 2 0+(5215605619/10000000000 : ℝ)*X 2 1+(-416351577/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3901027201/10000000000 : ℝ)*X 0 0+(4338160959/10000000000 : ℝ)*X 0 1+(4338161001/10000000000 : ℝ)*X 0 2+(3901027201/10000000000 : ℝ)*X 1 0+(4338160959/10000000000 : ℝ)*X 1 1+(4338161001/10000000000 : ℝ)*X 1 2+(3901027201/10000000000 : ℝ)*X 2 0+(4338160959/10000000000 : ℝ)*X 2 1+(4338161001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-888681097/5000000000 : ℝ)*X 0 0+(2538210581/5000000000 : ℝ)*X 0 1+(2719406579/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2615436327/5000000000 : ℝ)*X 1 0+(-1569419897/10000000000 : ℝ)*X 1 1+(2719407437/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1046174441/2000000000 : ℝ)*X 2 0+(2719407453/5000000000 : ℝ)*X 2 1+(-156942047/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2272401741/5000000000 : ℝ)*X 0 0+(4015383151/10000000000 : ℝ)*X 0 1+(501922641/1250000000 : ℝ)*X 0 2+(2272401741/5000000000 : ℝ)*X 1 0+(4015383151/10000000000 : ℝ)*X 1 1+(501922641/1250000000 : ℝ)*X 1 2+(2272401741/5000000000 : ℝ)*X 2 0+(4015383151/10000000000 : ℝ)*X 2 1+(501922641/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1471574889/10000000000 : ℝ)*X 0 0+(5543122177/10000000000 : ℝ)*X 0 1+(1039155109/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5397810847/10000000000 : ℝ)*X 1 0+(-418402511/2500000000 : ℝ)*X 1 1+(1298943857/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5397810841/10000000000 : ℝ)*X 2 0+(2597887641/5000000000 : ℝ)*X 2 1+(-6694441/40000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((480249263/1250000000 : ℝ)*X 0 0+(4366778737/10000000000 : ℝ)*X 0 1+(4366777471/10000000000 : ℝ)*X 0 2+(480249263/1250000000 : ℝ)*X 1 0+(4366778737/10000000000 : ℝ)*X 1 1+(4366777471/10000000000 : ℝ)*X 1 2+(480249263/1250000000 : ℝ)*X 2 0+(4366778737/10000000000 : ℝ)*X 2 1+(4366777471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-65047/100000 : ℝ) ≤ (-732790531532541496863514647/1126600000000000000000000000 : ℝ) := by norm_num
    linear_combination (9969583/50000000000000 : ℝ)*(upper0) + (47337841/100000000000000 : ℝ)*(lower2) + (130901/1000000000000 : ℝ)*(lower3) + (152687/3125000000000 : ℝ)*(upper5) + (27334889825833/1562500000000 : ℝ)*(major0) + (27334889825833/1562500000000 : ℝ)*(major1) + (27334889825833/1562500000000 : ℝ)*(major2) + (488309377/100000000000000 : ℝ)*(sp3) + (635184168283679/25000000000000 : ℝ)*(sp4) + (158795157034107/6250000000000 : ℝ)*(sp5) + (317585786102853/12500000000000 : ℝ)*(sp6) + (979810212430719/100000000000000 : ℝ)*(sp7) + (3540147251/25000000000000 : ℝ)*(sp13) + (12596077973/25000000000000 : ℝ)*(sp14) + (1913692774883/195312500000 : ℝ)*(f.failure) + (635184168283679/25000000000000 : ℝ)*(f.sum) + (55815024449/704125000000000000000000000 : ℝ)*base66 + (183326237640844863/88015625000000000000000000000000 : ℝ)*base68 + (208980525247883369/44007812500000000000000000000000 : ℝ)*base70 + (312031382675998887/88015625000000000000000000000000 : ℝ)*base71 + (3627792375761/2816500000000000000000000000 : ℝ)*base74 + (117717882732133369/44007812500000000000000000000000 : ℝ)*base76 + (216683899093623887/88015625000000000000000000000000 : ℝ)*base77 + (1181309596221342637/88015625000000000000000000000000 : ℝ)*base79 + (34354362664753/5633000000000000000000000000 : ℝ)*base82 + (513/3906250000000000000 : ℝ)*base89 + (513/3906250000000000000 : ℝ)*base91 + (513/3906250000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (14643/25000 : ℝ) ≤ (206218325030132486178652541606787/352062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (178818669/100000000000000 : ℝ)*(lower1) + (172343797/100000000000000 : ℝ)*(lower2) + (148626867/100000000000000 : ℝ)*(lower5) + (1839140967978489/100000000000000 : ℝ)*(major0) + (1839140967978489/100000000000000 : ℝ)*(major1) + (183914096797849/10000000000000 : ℝ)*(major2) + (657175510886323/25000000000000 : ℝ)*(sp0) + (65716642182897/2500000000000 : ℝ)*(sp1) + (2628699513870163/100000000000000 : ℝ)*(sp2) + (128756170188201/12500000000000 : ℝ)*(sp3) + (967625801/25000000000000 : ℝ)*(sp6) + (4406360129/100000000000000 : ℝ)*(sp7) + (53633123/4000000000000 : ℝ)*(sp8) + (37697057487/100000000000000 : ℝ)*(sp9) + (515026883932869/50000000000000 : ℝ)*(f.failure) + (1314351692186683/50000000000000 : ℝ)*(f.sum) + (19921652758519/2816500000000000000000000000 : ℝ)*base65 + (47327548916096797729/5633000000000000000000000000000000 : ℝ)*base68 + (1526303900462045311/563300000000000000000000000000000 : ℝ)*base69 + (30505679050246797729/5633000000000000000000000000000000 : ℝ)*base72 + (12808192631507/5633000000000000000000000000 : ℝ)*base74 + (2579313471409645311/563300000000000000000000000000000 : ℝ)*base75 + (28339000578820797729/5633000000000000000000000000000000 : ℝ)*base78 + (27624912148107797729/5633000000000000000000000000000000 : ℝ)*base80 + (1120991728061/1408250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (12103959/1000000000000000000000 : ℝ)*base89 + (12103959/1000000000000000000000 : ℝ)*base91 + (2103959/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (16221/20000 : ℝ) ≤ (13281353697908261111470130451357/16375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14743673/100000000000000 : ℝ)*(upper2) + (339372309/100000000000000 : ℝ)*(upper3) + (2166983/2000000000000 : ℝ)*(lower5) + (483788107610801/25000000000000 : ℝ)*(major0) + (483788107610801/25000000000000 : ℝ)*(major1) + (483788107610801/25000000000000 : ℝ)*(major2) + (3585170737/50000000000000 : ℝ)*(sp0) + (13153880781/25000000000000 : ℝ)*(sp1) + (5322592793/5000000000000 : ℝ)*(sp2) + (654028637/20000000000000 : ℝ)*(sp3) + (275943463068399/10000000000000 : ℝ)*(sp8) + (137969459275117/5000000000000 : ℝ)*(sp9) + (689833837292401/25000000000000 : ℝ)*(sp10) + (67738997201137/6250000000000 : ℝ)*(sp11) + (33869600792543/3125000000000 : ℝ)*(f.failure) + (344930225128183/12500000000000 : ℝ)*(f.sum) + (651359460889/131000000000000000000000000 : ℝ)*base66 + (3345123878477627/32750000000000000000000000000000 : ℝ)*base68 + (415179368178227627/32750000000000000000000000000000 : ℝ)*base70 + (273824916318477627/32750000000000000000000000000000 : ℝ)*base72 + (402043385473/131000000000000000000000000 : ℝ)*base73 + (419459824880227627/32750000000000000000000000000000 : ℝ)*base76 + (371421612506477627/32750000000000000000000000000000 : ℝ)*base78 + (53403943099477627/32750000000000000000000000000000 : ℝ)*base80 + (359464225589/65500000000000000000000000 : ℝ)*base82 + (269227/62500000000000000000 : ℝ)*base90 + (269227/62500000000000000000 : ℝ)*base92 + (269227/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-3527/4000 : ℝ) ≤ (-2483369963651847102295000827804147/2816500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30845189/50000000000000 : ℝ)*(upper1) + (7922539/100000000000000 : ℝ)*(lower2) + (189884521/100000000000000 : ℝ)*(upper3) + (23074899/50000000000000 : ℝ)*(upper5) + (494743673098701/25000000000000 : ℝ)*(major0) + (494743673098701/25000000000000 : ℝ)*(major1) + (395794938478961/20000000000000 : ℝ)*(major2) + (10204115831/12500000000000 : ℝ)*(sp5) + (74552643119/100000000000000 : ℝ)*(sp6) + (3021674451/6250000000000 : ℝ)*(sp7) + (1439484606456679/50000000000000 : ℝ)*(sp12) + (287888757998671/10000000000000 : ℝ)*(sp13) + (17993091626689/625000000000 : ℝ)*(sp14) + (1108322557834323/100000000000000 : ℝ)*(sp15) + (1108370904625539/100000000000000 : ℝ)*(f.failure) + (1439484606456679/50000000000000 : ℝ)*(f.sum) + (4934475974931/5633000000000000000000000000 : ℝ)*base66 + (4737365581677560139/1408250000000000000000000000000000 : ℝ)*base67 + (1459991377908901721/1126600000000000000000000000000000 : ℝ)*base70 + (6388906987248689861/1408250000000000000000000000000000 : ℝ)*base72 + (2040014805389/1408250000000000000000000000 : ℝ)*base74 + (30623215832904501721/1126600000000000000000000000000000 : ℝ)*base76 + (8929443053048689861/1408250000000000000000000000000000 : ℝ)*base78 + (14536571051601939861/1408250000000000000000000000000000 : ℝ)*base80 + (75856262850857/5633000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (18355329/2000000000000000000000 : ℝ)*base89 + (18355329/2000000000000000000000 : ℝ)*base91 + (1644671/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1645_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35709611/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65047/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14643/25000 : ℝ) else (16221/20000 : ℝ) ≤ X j i ∧ X j i ≤ (3527/4000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1645_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1645_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35709611/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65047/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14643/25000 : ℝ) else (16221/20000 : ℝ) ≤ X j i ∧ X j i ≤ (3527/4000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1645_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35709611/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65047/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14643/25000 : ℝ) else (16221/20000 : ℝ) ≤ X j i ∧ X j i ≤ (3527/4000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1645_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1147_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:34:22.816906+00:00
-- url     : https://prove2.me/submissions/0e18aac3-a56c-4248-a74e-cf06298b9031

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
theorem support_rectangle_w1147_s9_0 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-432900721/2000000000 : ℝ)*x 0 + (2696443853/5000000000 : ℝ)*x 1 + (2632935727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432900721/2000000000 : ℝ)^2085 ≤ (3288230946443/25000000000000 : ℝ)^1573 := by
    have hnat : (432900721 : ℕ)^2085*25000000000000^1573 ≤ 3288230946443^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432900721 2000000000 3288230946443 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696443853/5000000000 : ℝ)^2085 ≤ (22054702327797/50000000000000 : ℝ)^1573 := by
    have hnat : (2696443853 : ℕ)^2085*50000000000000^1573 ≤ 22054702327797^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696443853 5000000000 22054702327797 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632935727/5000000000 : ℝ)^2085 ≤ (42737671542919/100000000000000 : ℝ)^1573 := by
    have hnat : (2632935727 : ℕ)^2085*100000000000000^1573 ≤ 42737671542919^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632935727 5000000000 42737671542919 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-432900721/2000000000 : ℝ), (2696443853/5000000000 : ℝ), (2632935727/5000000000 : ℝ)] ![(3288230946443/25000000000000 : ℝ), (22054702327797/50000000000000 : ℝ), (42737671542919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-432900721/2000000000 : ℝ)|^2085 ≤ (3288230946443/25000000000000 : ℝ)^1573
        have hw : |(-432900721/2000000000 : ℝ)|=(432900721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696443853/5000000000 : ℝ)|^2085 ≤ (22054702327797/50000000000000 : ℝ)^1573
        have hw : |(2696443853/5000000000 : ℝ)|=(2696443853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632935727/5000000000 : ℝ)|^2085 ≤ (42737671542919/100000000000000 : ℝ)^1573
        have hw : |(2632935727/5000000000 : ℝ)|=(2632935727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s9_1 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344724929/10000000000 : ℝ)*x 0 + (-445785283/2000000000 : ℝ)*x 1 + (5265871451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344724929/10000000000 : ℝ)^2085 ≤ (21794005516423/50000000000000 : ℝ)^1573 := by
    have hnat : (5344724929 : ℕ)^2085*50000000000000^1573 ≤ 21794005516423^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344724929 10000000000 21794005516423 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (445785283/2000000000 : ℝ)^2085 ≤ (427322419989/3125000000000 : ℝ)^1573 := by
    have hnat : (445785283 : ℕ)^2085*3125000000000^1573 ≤ 427322419989^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445785283 2000000000 427322419989 3125000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265871451/10000000000 : ℝ)^2085 ≤ (21368835755323/50000000000000 : ℝ)^1573 := by
    have hnat : (5265871451 : ℕ)^2085*50000000000000^1573 ≤ 21368835755323^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265871451 10000000000 21368835755323 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344724929/10000000000 : ℝ), (-445785283/2000000000 : ℝ), (5265871451/10000000000 : ℝ)] ![(21794005516423/50000000000000 : ℝ), (427322419989/3125000000000 : ℝ), (21368835755323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344724929/10000000000 : ℝ)|^2085 ≤ (21794005516423/50000000000000 : ℝ)^1573
        have hw : |(5344724929/10000000000 : ℝ)|=(5344724929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-445785283/2000000000 : ℝ)|^2085 ≤ (427322419989/3125000000000 : ℝ)^1573
        have hw : |(-445785283/2000000000 : ℝ)|=(445785283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265871451/10000000000 : ℝ)|^2085 ≤ (21368835755323/50000000000000 : ℝ)^1573
        have hw : |(5265871451/10000000000 : ℝ)|=(5265871451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s9_2 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672362467/5000000000 : ℝ)*x 0 + (5265871423/10000000000 : ℝ)*x 1 + (-445785289/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672362467/5000000000 : ℝ)^2085 ≤ (8717602217379/20000000000000 : ℝ)^1573 := by
    have hnat : (2672362467 : ℕ)^2085*20000000000000^1573 ≤ 8717602217379^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672362467 5000000000 8717602217379 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265871423/10000000000 : ℝ)^2085 ≤ (5342208901179/12500000000000 : ℝ)^1573 := by
    have hnat : (5265871423 : ℕ)^2085*12500000000000^1573 ≤ 5342208901179^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265871423 10000000000 5342208901179 12500000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (445785289/2000000000 : ℝ)^2085 ≤ (6837158841801/50000000000000 : ℝ)^1573 := by
    have hnat : (445785289 : ℕ)^2085*50000000000000^1573 ≤ 6837158841801^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445785289 2000000000 6837158841801 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672362467/5000000000 : ℝ), (5265871423/10000000000 : ℝ), (-445785289/2000000000 : ℝ)] ![(8717602217379/20000000000000 : ℝ), (5342208901179/12500000000000 : ℝ), (6837158841801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672362467/5000000000 : ℝ)|^2085 ≤ (8717602217379/20000000000000 : ℝ)^1573
        have hw : |(2672362467/5000000000 : ℝ)|=(2672362467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265871423/10000000000 : ℝ)|^2085 ≤ (5342208901179/12500000000000 : ℝ)^1573
        have hw : |(5265871423/10000000000 : ℝ)|=(5265871423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-445785289/2000000000 : ℝ)|^2085 ≤ (6837158841801/50000000000000 : ℝ)^1573
        have hw : |(-445785289/2000000000 : ℝ)|=(445785289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s9_3 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2181985961/5000000000 : ℝ)*x 0 + (2119660853/5000000000 : ℝ)*x 1 + (140383287/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181985961/5000000000 : ℝ)^2085 ≤ (33317020372669/100000000000000 : ℝ)^1573 := by
    have hnat : (2181985961 : ℕ)^2085*100000000000000^1573 ≤ 33317020372669^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181985961 5000000000 33317020372669 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119660853/5000000000 : ℝ)^2085 ≤ (32061517168217/100000000000000 : ℝ)^1573 := by
    have hnat : (2119660853 : ℕ)^2085*100000000000000^1573 ≤ 32061517168217^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119660853 5000000000 32061517168217 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140383287/312500000 : ℝ)^2085 ≤ (34621462446937/100000000000000 : ℝ)^1573 := by
    have hnat : (140383287 : ℕ)^2085*100000000000000^1573 ≤ 34621462446937^1573*312500000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140383287 312500000 34621462446937 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181985961/5000000000 : ℝ), (2119660853/5000000000 : ℝ), (140383287/312500000 : ℝ)] ![(33317020372669/100000000000000 : ℝ), (32061517168217/100000000000000 : ℝ), (34621462446937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181985961/5000000000 : ℝ)|^2085 ≤ (33317020372669/100000000000000 : ℝ)^1573
        have hw : |(2181985961/5000000000 : ℝ)|=(2181985961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2119660853/5000000000 : ℝ)|^2085 ≤ (32061517168217/100000000000000 : ℝ)^1573
        have hw : |(2119660853/5000000000 : ℝ)|=(2119660853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140383287/312500000 : ℝ)|^2085 ≤ (34621462446937/100000000000000 : ℝ)^1573
        have hw : |(140383287/312500000 : ℝ)|=(140383287/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s9_4 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-270563549/1250000000 : ℝ)*x 0 + (2633095097/5000000000 : ℝ)*x 1 + (2696283933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270563549/1250000000 : ℝ)^2085 ≤ (13152962342921/100000000000000 : ℝ)^1573 := by
    have hnat : (270563549 : ℕ)^2085*100000000000000^1573 ≤ 13152962342921^1573*1250000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270563549 1250000000 13152962342921 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633095097/5000000000 : ℝ)^2085 ≤ (21370550237121/50000000000000 : ℝ)^1573 := by
    have hnat : (2633095097 : ℕ)^2085*50000000000000^1573 ≤ 21370550237121^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633095097 5000000000 21370550237121 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696283933/5000000000 : ℝ)^2085 ≤ (44105937161417/100000000000000 : ℝ)^1573 := by
    have hnat : (2696283933 : ℕ)^2085*100000000000000^1573 ≤ 44105937161417^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696283933 5000000000 44105937161417 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-270563549/1250000000 : ℝ), (2633095097/5000000000 : ℝ), (2696283933/5000000000 : ℝ)] ![(13152962342921/100000000000000 : ℝ), (21370550237121/50000000000000 : ℝ), (44105937161417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-270563549/1250000000 : ℝ)|^2085 ≤ (13152962342921/100000000000000 : ℝ)^1573
        have hw : |(-270563549/1250000000 : ℝ)|=(270563549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633095097/5000000000 : ℝ)|^2085 ≤ (21370550237121/50000000000000 : ℝ)^1573
        have hw : |(2633095097/5000000000 : ℝ)|=(2633095097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696283933/5000000000 : ℝ)|^2085 ≤ (44105937161417/100000000000000 : ℝ)^1573
        have hw : |(2696283933/5000000000 : ℝ)|=(2696283933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s9_5 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4363981719/10000000000 : ℝ)*x 0 + (1122907493/2500000000 : ℝ)*x 1 + (4239959093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363981719/10000000000 : ℝ)^2085 ≤ (6663423902803/20000000000000 : ℝ)^1573 := by
    have hnat : (4363981719 : ℕ)^2085*20000000000000^1573 ≤ 6663423902803^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363981719 10000000000 6663423902803 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122907493/2500000000 : ℝ)^2085 ≤ (34614973621967/100000000000000 : ℝ)^1573 := by
    have hnat : (1122907493 : ℕ)^2085*100000000000000^1573 ≤ 34614973621967^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122907493 2500000000 34614973621967 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4239959093/10000000000 : ℝ)^2085 ≤ (250530522223/781250000000 : ℝ)^1573 := by
    have hnat : (4239959093 : ℕ)^2085*781250000000^1573 ≤ 250530522223^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239959093 10000000000 250530522223 781250000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363981719/10000000000 : ℝ), (1122907493/2500000000 : ℝ), (4239959093/10000000000 : ℝ)] ![(6663423902803/20000000000000 : ℝ), (34614973621967/100000000000000 : ℝ), (250530522223/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363981719/10000000000 : ℝ)|^2085 ≤ (6663423902803/20000000000000 : ℝ)^1573
        have hw : |(4363981719/10000000000 : ℝ)|=(4363981719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122907493/2500000000 : ℝ)|^2085 ≤ (34614973621967/100000000000000 : ℝ)^1573
        have hw : |(1122907493/2500000000 : ℝ)|=(1122907493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4239959093/10000000000 : ℝ)|^2085 ≤ (250530522223/781250000000 : ℝ)^1573
        have hw : |(4239959093/10000000000 : ℝ)|=(4239959093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1147_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (71/625 : ℝ)*pair X i i ≤ pair X i h) :
    (11361/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14051/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (71/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (71/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (71/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (71/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (71/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (71/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (71/625 : ℝ) ^ (8339/2048 : ℝ) ≤ (14246588860950631/100000000000000000000 : ℝ) := by
    have hpowers : (71/625 : ℝ)^8339 ≤ (14246588860950631/100000000000000000000 : ℝ)^2048 := by
      have hnat : (71 : ℕ)^8339*100000000000000000000^2048 ≤ 14246588860950631^2048*625^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71 625 14246588860950631 100000000000000000000 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71/625 : ℝ)) (X := (14246588860950631/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14051/100000 : ℝ) ^ (8339/2048 : ℝ) ≤ (33857401546922563/100000000000000000000 : ℝ) := by
    have hpowers : (14051/100000 : ℝ)^8339 ≤ (33857401546922563/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14051 : ℕ)^8339*100000000000000000000^2048 ≤ 33857401546922563^2048*100000^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14051 100000 33857401546922563 100000000000000000000 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14051/100000 : ℝ)) (X := (33857401546922563/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014246588860950631/50000000000000000000 : ℝ) ≤ (10000699697293297/10000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (50014246588860950631/50000000000000000000 : ℝ)^2048 ≤ (10000699697293297/10000000000000000 : ℝ)^8339 := by
      have hnat : (50014246588860950631 : ℕ)^2048*10000000000000000^8339 ≤ 10000699697293297^8339*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014246588860950631 50000000000000000000 10000699697293297 10000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000699697293297/10000000000000000 : ℝ)) (X := (50014246588860950631/50000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024051995203936597/50000000000000000000 : ℝ) ≤ (10001181186011321/10000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (50024051995203936597/50000000000000000000 : ℝ)^2048 ≤ (10001181186011321/10000000000000000 : ℝ)^8339 := by
      have hnat : (50024051995203936597 : ℕ)^2048*10000000000000000^8339 ≤ 10001181186011321^8339*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024051995203936597 50000000000000000000 10001181186011321 10000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001181186011321/10000000000000000 : ℝ)) (X := (50024051995203936597/50000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033857401546922563/50000000000000000000 : ℝ) ≤ (2000332534945869/2000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (50033857401546922563/50000000000000000000 : ℝ)^2048 ≤ (2000332534945869/2000000000000000 : ℝ)^8339 := by
      have hnat : (50033857401546922563 : ℕ)^2048*2000000000000000^8339 ≤ 2000332534945869^8339*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033857401546922563 50000000000000000000 2000332534945869 2000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000332534945869/2000000000000000 : ℝ)) (X := (50033857401546922563/50000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14246588860950631/100000000000000000000 : ℝ) ≤ ((1169606237467076389/1170000000000000000 : ℝ)+2*(2616786511/1462500000000 : ℝ)*(71/625 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (1169606237467076389/1170000000000000000 : ℝ)+2*(2616786511/1462500000000 : ℝ)*(71/625 : ℝ)=(10000699697293297/10000000000000000 : ℝ) by norm_num, show 1+2*(14246588860950631/100000000000000000000 : ℝ)=(50014246588860950631/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33857401546922563/100000000000000000000 : ℝ)+(14246588860950631/100000000000000000000 : ℝ) ≤ ((1169606237467076389/1170000000000000000 : ℝ)+(2616786511/1462500000000 : ℝ)*((14051/100000 : ℝ)+(71/625 : ℝ)))^(8339/2048 : ℝ) := by
    rw [show (1169606237467076389/1170000000000000000 : ℝ)+(2616786511/1462500000000 : ℝ)*((14051/100000 : ℝ)+(71/625 : ℝ))=(10001181186011321/10000000000000000 : ℝ) by norm_num, show 1+(33857401546922563/100000000000000000000 : ℝ)+(14246588860950631/100000000000000000000 : ℝ)=(50024051995203936597/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33857401546922563/100000000000000000000 : ℝ) ≤ ((1169606237467076389/1170000000000000000 : ℝ)+2*(2616786511/1462500000000 : ℝ)*(14051/100000 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (1169606237467076389/1170000000000000000 : ℝ)+2*(2616786511/1462500000000 : ℝ)*(14051/100000 : ℝ)=(2000332534945869/2000000000000000 : ℝ) by norm_num, show 1+2*(33857401546922563/100000000000000000000 : ℝ)=(50033857401546922563/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1169606237467076389/1170000000000000000 : ℝ)*(X 1 0+X 2 0)+(2616786511/1462500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (71/625 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (1169606237467076389/1170000000000000000 : ℝ)) (alpha := (2616786511/1462500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1169606237467076389/1170000000000000000 : ℝ)*(X 0 1+X 2 1)+(2616786511/1462500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (71/625 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (1169606237467076389/1170000000000000000 : ℝ)) (alpha := (2616786511/1462500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1169606237467076389/1170000000000000000 : ℝ)*(X 0 2+X 1 2)+(2616786511/1462500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (71/625 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (1169606237467076389/1170000000000000000 : ℝ)) (alpha := (2616786511/1462500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-432900721/2000000000 : ℝ)*X 0 0+(2696443853/5000000000 : ℝ)*X 0 1+(2632935727/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344724929/10000000000 : ℝ)*X 1 0+(-445785283/2000000000 : ℝ)*X 1 1+(5265871451/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672362467/5000000000 : ℝ)*X 2 0+(5265871423/10000000000 : ℝ)*X 2 1+(-445785289/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2181985961/5000000000 : ℝ)*X 0 0+(2119660853/5000000000 : ℝ)*X 0 1+(140383287/312500000 : ℝ)*X 0 2+(2181985961/5000000000 : ℝ)*X 1 0+(2119660853/5000000000 : ℝ)*X 1 1+(140383287/312500000 : ℝ)*X 1 2+(2181985961/5000000000 : ℝ)*X 2 0+(2119660853/5000000000 : ℝ)*X 2 1+(140383287/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-270563549/1250000000 : ℝ)*X 0 0+(2633095097/5000000000 : ℝ)*X 0 1+(2696283933/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4363981719/10000000000 : ℝ)*X 0 0+(1122907493/2500000000 : ℝ)*X 0 1+(4239959093/10000000000 : ℝ)*X 0 2+(4363981719/10000000000 : ℝ)*X 1 0+(1122907493/2500000000 : ℝ)*X 1 1+(4239959093/10000000000 : ℝ)*X 1 2+(4363981719/10000000000 : ℝ)*X 2 0+(1122907493/2500000000 : ℝ)*X 2 1+(4239959093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10033556128102947608985647/3900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (255097333/50000000000000 : ℝ)*(base19) + (57958207/12500000000000 : ℝ)*(base23) + (15748599/50000000000000 : ℝ)*(lower2) + (87016441/100000000000000 : ℝ)*(upper3) + (1346103/50000000000000 : ℝ)*(lower4) + (1182650305668323/20000000000000 : ℝ)*(major0) + (1182650305668323/20000000000000 : ℝ)*(major1) + (369578220521351/6250000000000 : ℝ)*(major2) + (7873023580957631/100000000000000 : ℝ)*(sp0) + (1968258770032287/25000000000000 : ℝ)*(sp1) + (3936517563329079/50000000000000 : ℝ)*(sp2) + (494182352532243/12500000000000 : ℝ)*(sp3) + (6004683091/50000000000000 : ℝ)*(sp4) + (4280172287/50000000000000 : ℝ)*(sp5) + (1976733690301259/50000000000000 : ℝ)*(f.failure) + (7873035590323813/100000000000000 : ℝ)*(f.sum) + (954172805737/195000000000000000000000000 : ℝ)*base66 + (73046095329714353/23400000000000000000000000000000 : ℝ)*base68 + (39287985511481539/7312500000000000000000000000000 : ℝ)*base69 + (58180791578285647/23400000000000000000000000000000 : ℝ)*base71 + (15539805161/6093750000000000000000000 : ℝ)*base74 + (82826966829393461/7312500000000000000000000000000 : ℝ)*base76 + (100101417178491451/7800000000000000000000000000000 : ℝ)*base78 + (117866857702491451/7800000000000000000000000000000 : ℝ)*base80 + (43194948821/14625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1216983/2500000000000000000000 : ℝ)*base89 + (1216983/2500000000000000000000 : ℝ)*base91 + (23783017/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1147_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (71/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1147_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1147_box_0 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2037779539/10000000000 : ℝ)*x 0 + (5376235177/10000000000 : ℝ)*x 1 + (1344059/2500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037779539/10000000000 : ℝ)^2085 ≤ (12142075125563/100000000000000 : ℝ)^1573 := by
    have hnat : (2037779539 : ℕ)^2085*100000000000000^1573 ≤ 12142075125563^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037779539 10000000000 12142075125563 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376235177/10000000000 : ℝ)^2085 ≤ (43928957974951/100000000000000 : ℝ)^1573 := by
    have hnat : (5376235177 : ℕ)^2085*100000000000000^1573 ≤ 43928957974951^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376235177 10000000000 43928957974951 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344059/2500000 : ℝ)^2085 ≤ (43928966888483/100000000000000 : ℝ)^1573 := by
    have hnat : (1344059 : ℕ)^2085*100000000000000^1573 ≤ 43928966888483^1573*2500000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344059 2500000 43928966888483 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2037779539/10000000000 : ℝ), (5376235177/10000000000 : ℝ), (1344059/2500000 : ℝ)] ![(12142075125563/100000000000000 : ℝ), (43928957974951/100000000000000 : ℝ), (43928966888483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2037779539/10000000000 : ℝ)|^2085 ≤ (12142075125563/100000000000000 : ℝ)^1573
        have hw : |(-2037779539/10000000000 : ℝ)|=(2037779539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376235177/10000000000 : ℝ)|^2085 ≤ (43928957974951/100000000000000 : ℝ)^1573
        have hw : |(5376235177/10000000000 : ℝ)|=(5376235177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344059/2500000 : ℝ)|^2085 ≤ (43928966888483/100000000000000 : ℝ)^1573
        have hw : |(1344059/2500000 : ℝ)|=(1344059/2500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_box_1 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2648016189/5000000000 : ℝ)*x 0 + (-536639977/2500000000 : ℝ)*x 1 + (672029589/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648016189/5000000000 : ℝ)^2085 ≤ (5382804332583/12500000000000 : ℝ)^1573 := by
    have hnat : (2648016189 : ℕ)^2085*12500000000000^1573 ≤ 5382804332583^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648016189 5000000000 5382804332583 12500000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (536639977/2500000000 : ℝ)^2085 ≤ (6504295361711/50000000000000 : ℝ)^1573 := by
    have hnat : (536639977 : ℕ)^2085*50000000000000^1573 ≤ 6504295361711^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536639977 2500000000 6504295361711 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672029589/1250000000 : ℝ)^2085 ≤ (21964487299913/50000000000000 : ℝ)^1573 := by
    have hnat : (672029589 : ℕ)^2085*50000000000000^1573 ≤ 21964487299913^1573*1250000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672029589 1250000000 21964487299913 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648016189/5000000000 : ℝ), (-536639977/2500000000 : ℝ), (672029589/1250000000 : ℝ)] ![(5382804332583/12500000000000 : ℝ), (6504295361711/50000000000000 : ℝ), (21964487299913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648016189/5000000000 : ℝ)|^2085 ≤ (5382804332583/12500000000000 : ℝ)^1573
        have hw : |(2648016189/5000000000 : ℝ)|=(2648016189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-536639977/2500000000 : ℝ)|^2085 ≤ (6504295361711/50000000000000 : ℝ)^1573
        have hw : |(-536639977/2500000000 : ℝ)|=(536639977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672029589/1250000000 : ℝ)|^2085 ≤ (21964487299913/50000000000000 : ℝ)^1573
        have hw : |(672029589/1250000000 : ℝ)|=(672029589/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_box_2 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (662004263/1250000000 : ℝ)*x 0 + (5376235509/10000000000 : ℝ)*x 1 + (-1073279607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662004263/1250000000 : ℝ)^2085 ≤ (2153122663147/5000000000000 : ℝ)^1573 := by
    have hnat : (662004263 : ℕ)^2085*5000000000000^1573 ≤ 2153122663147^1573*1250000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662004263 1250000000 2153122663147 5000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376235509/10000000000 : ℝ)^2085 ≤ (4392896157069/10000000000000 : ℝ)^1573 := by
    have hnat : (5376235509 : ℕ)^2085*10000000000000^1573 ≤ 4392896157069^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376235509 10000000000 4392896157069 10000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1073279607/5000000000 : ℝ)^2085 ≤ (1300858514869/10000000000000 : ℝ)^1573 := by
    have hnat : (1073279607 : ℕ)^2085*10000000000000^1573 ≤ 1300858514869^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073279607 5000000000 1300858514869 10000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662004263/1250000000 : ℝ), (5376235509/10000000000 : ℝ), (-1073279607/5000000000 : ℝ)] ![(2153122663147/5000000000000 : ℝ), (4392896157069/10000000000000 : ℝ), (1300858514869/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662004263/1250000000 : ℝ)|^2085 ≤ (2153122663147/5000000000000 : ℝ)^1573
        have hw : |(662004263/1250000000 : ℝ)|=(662004263/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376235509/10000000000 : ℝ)|^2085 ≤ (4392896157069/10000000000000 : ℝ)^1573
        have hw : |(5376235509/10000000000 : ℝ)|=(5376235509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1073279607/5000000000 : ℝ)|^2085 ≤ (1300858514869/10000000000000 : ℝ)^1573
        have hw : |(-1073279607/5000000000 : ℝ)|=(1073279607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_box_3 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4471456397/10000000000 : ℝ)*x 0 + (862466777/2000000000 : ℝ)*x 1 + (1078083413/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4471456397/10000000000 : ℝ)^2085 ≤ (17204525905033/50000000000000 : ℝ)^1573 := by
    have hnat : (4471456397 : ℕ)^2085*50000000000000^1573 ≤ 17204525905033^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4471456397 10000000000 17204525905033 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (862466777/2000000000 : ℝ)^2085 ≤ (2049717203743/6250000000000 : ℝ)^1573 := by
    have hnat : (862466777 : ℕ)^2085*6250000000000^1573 ≤ 2049717203743^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862466777 2000000000 2049717203743 6250000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078083413/2500000000 : ℝ)^2085 ≤ (32795472911149/100000000000000 : ℝ)^1573 := by
    have hnat : (1078083413 : ℕ)^2085*100000000000000^1573 ≤ 32795472911149^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078083413 2500000000 32795472911149 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4471456397/10000000000 : ℝ), (862466777/2000000000 : ℝ), (1078083413/2500000000 : ℝ)] ![(17204525905033/50000000000000 : ℝ), (2049717203743/6250000000000 : ℝ), (32795472911149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4471456397/10000000000 : ℝ)|^2085 ≤ (17204525905033/50000000000000 : ℝ)^1573
        have hw : |(4471456397/10000000000 : ℝ)|=(4471456397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(862466777/2000000000 : ℝ)|^2085 ≤ (2049717203743/6250000000000 : ℝ)^1573
        have hw : |(862466777/2000000000 : ℝ)|=(862466777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078083413/2500000000 : ℝ)|^2085 ≤ (32795472911149/100000000000000 : ℝ)^1573
        have hw : |(1078083413/2500000000 : ℝ)|=(1078083413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_box_4 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-458521013/2000000000 : ℝ)*x 0 + (5281207693/10000000000 : ℝ)*x 1 + (660151007/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (458521013/2000000000 : ℝ)^2085 ≤ (3548633130419/25000000000000 : ℝ)^1573 := by
    have hnat : (458521013 : ℕ)^2085*25000000000000^1573 ≤ 3548633130419^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458521013 2000000000 3548633130419 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281207693/10000000000 : ℝ)^2085 ≤ (21451365891391/50000000000000 : ℝ)^1573 := by
    have hnat : (5281207693 : ℕ)^2085*50000000000000^1573 ≤ 21451365891391^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281207693 10000000000 21451365891391 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660151007/1250000000 : ℝ)^2085 ≤ (5362841961439/12500000000000 : ℝ)^1573 := by
    have hnat : (660151007 : ℕ)^2085*12500000000000^1573 ≤ 5362841961439^1573*1250000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660151007 1250000000 5362841961439 12500000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-458521013/2000000000 : ℝ), (5281207693/10000000000 : ℝ), (660151007/1250000000 : ℝ)] ![(3548633130419/25000000000000 : ℝ), (21451365891391/50000000000000 : ℝ), (5362841961439/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-458521013/2000000000 : ℝ)|^2085 ≤ (3548633130419/25000000000000 : ℝ)^1573
        have hw : |(-458521013/2000000000 : ℝ)|=(458521013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281207693/10000000000 : ℝ)|^2085 ≤ (21451365891391/50000000000000 : ℝ)^1573
        have hw : |(5281207693/10000000000 : ℝ)|=(5281207693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(660151007/1250000000 : ℝ)|^2085 ≤ (5362841961439/12500000000000 : ℝ)^1573
        have hw : |(660151007/1250000000 : ℝ)|=(660151007/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_box_5 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5363163187/10000000000 : ℝ)*x 0 + (-436791171/2000000000 : ℝ)*x 1 + (5281207621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363163187/10000000000 : ℝ)^2085 ≤ (2189371868029/5000000000000 : ℝ)^1573 := by
    have hnat : (5363163187 : ℕ)^2085*5000000000000^1573 ≤ 2189371868029^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363163187 10000000000 2189371868029 5000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (436791171/2000000000 : ℝ)^2085 ≤ (13309831618381/100000000000000 : ℝ)^1573 := by
    have hnat : (436791171 : ℕ)^2085*100000000000000^1573 ≤ 13309831618381^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436791171 2000000000 13309831618381 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281207621/10000000000 : ℝ)^2085 ≤ (42902731007497/100000000000000 : ℝ)^1573 := by
    have hnat : (5281207621 : ℕ)^2085*100000000000000^1573 ≤ 42902731007497^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281207621 10000000000 42902731007497 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363163187/10000000000 : ℝ), (-436791171/2000000000 : ℝ), (5281207621/10000000000 : ℝ)] ![(2189371868029/5000000000000 : ℝ), (13309831618381/100000000000000 : ℝ), (42902731007497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363163187/10000000000 : ℝ)|^2085 ≤ (2189371868029/5000000000000 : ℝ)^1573
        have hw : |(5363163187/10000000000 : ℝ)|=(5363163187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-436791171/2000000000 : ℝ)|^2085 ≤ (13309831618381/100000000000000 : ℝ)^1573
        have hw : |(-436791171/2000000000 : ℝ)|=(436791171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281207621/10000000000 : ℝ)|^2085 ≤ (42902731007497/100000000000000 : ℝ)^1573
        have hw : |(5281207621/10000000000 : ℝ)|=(5281207621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_box_6 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5363162973/10000000000 : ℝ)*x 0 + (2640603831/5000000000 : ℝ)*x 1 + (-2183956087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363162973/10000000000 : ℝ)^2085 ≤ (1094685876117/2500000000000 : ℝ)^1573 := by
    have hnat : (5363162973 : ℕ)^2085*2500000000000^1573 ≤ 1094685876117^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363162973 10000000000 1094685876117 2500000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640603831/5000000000 : ℝ)^2085 ≤ (42902731448979/100000000000000 : ℝ)^1573 := by
    have hnat : (2640603831 : ℕ)^2085*100000000000000^1573 ≤ 42902731448979^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640603831 5000000000 42902731448979 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2183956087/10000000000 : ℝ)^2085 ≤ (6654916746243/50000000000000 : ℝ)^1573 := by
    have hnat : (2183956087 : ℕ)^2085*50000000000000^1573 ≤ 6654916746243^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183956087 10000000000 6654916746243 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363162973/10000000000 : ℝ), (2640603831/5000000000 : ℝ), (-2183956087/10000000000 : ℝ)] ![(1094685876117/2500000000000 : ℝ), (42902731448979/100000000000000 : ℝ), (6654916746243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363162973/10000000000 : ℝ)|^2085 ≤ (1094685876117/2500000000000 : ℝ)^1573
        have hw : |(5363162973/10000000000 : ℝ)|=(5363162973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640603831/5000000000 : ℝ)|^2085 ≤ (42902731448979/100000000000000 : ℝ)^1573
        have hw : |(2640603831/5000000000 : ℝ)|=(2640603831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2183956087/10000000000 : ℝ)|^2085 ≤ (6654916746243/50000000000000 : ℝ)^1573
        have hw : |(-2183956087/10000000000 : ℝ)|=(2183956087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_box_7 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4256123933/10000000000 : ℝ)*x 0 + (4419979141/10000000000 : ℝ)*x 1 + (1104994817/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4256123933/10000000000 : ℝ)^2085 ≤ (16115030269241/50000000000000 : ℝ)^1573 := by
    have hnat : (4256123933 : ℕ)^2085*50000000000000^1573 ≤ 16115030269241^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4256123933 10000000000 16115030269241 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4419979141/10000000000 : ℝ)^2085 ≤ (6776993815377/20000000000000 : ℝ)^1573 := by
    have hnat : (4419979141 : ℕ)^2085*20000000000000^1573 ≤ 6776993815377^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4419979141 10000000000 6776993815377 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1104994817/2500000000 : ℝ)^2085 ≤ (16942485183707/50000000000000 : ℝ)^1573 := by
    have hnat : (1104994817 : ℕ)^2085*50000000000000^1573 ≤ 16942485183707^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104994817 2500000000 16942485183707 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4256123933/10000000000 : ℝ), (4419979141/10000000000 : ℝ), (1104994817/2500000000 : ℝ)] ![(16115030269241/50000000000000 : ℝ), (6776993815377/20000000000000 : ℝ), (16942485183707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4256123933/10000000000 : ℝ)|^2085 ≤ (16115030269241/50000000000000 : ℝ)^1573
        have hw : |(4256123933/10000000000 : ℝ)|=(4256123933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4419979141/10000000000 : ℝ)|^2085 ≤ (6776993815377/20000000000000 : ℝ)^1573
        have hw : |(4419979141/10000000000 : ℝ)|=(4419979141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1104994817/2500000000 : ℝ)|^2085 ≤ (16942485183707/50000000000000 : ℝ)^1573
        have hw : |(1104994817/2500000000 : ℝ)|=(1104994817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_box_8 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2239311217/10000000000 : ℝ)*x 0 + (104331401/200000000 : ℝ)*x 1 + (1346461021/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2239311217/10000000000 : ℝ)^2085 ≤ (13758828649619/100000000000000 : ℝ)^1573 := by
    have hnat : (2239311217 : ℕ)^2085*100000000000000^1573 ≤ 13758828649619^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239311217 10000000000 13758828649619 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104331401/200000000 : ℝ)^2085 ≤ (42208113477799/100000000000000 : ℝ)^1573 := by
    have hnat : (104331401 : ℕ)^2085*100000000000000^1573 ≤ 42208113477799^1573*200000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104331401 200000000 42208113477799 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346461021/2500000000 : ℝ)^2085 ≤ (8806611570887/20000000000000 : ℝ)^1573 := by
    have hnat : (1346461021 : ℕ)^2085*20000000000000^1573 ≤ 8806611570887^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346461021 2500000000 8806611570887 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2239311217/10000000000 : ℝ), (104331401/200000000 : ℝ), (1346461021/2500000000 : ℝ)] ![(13758828649619/100000000000000 : ℝ), (42208113477799/100000000000000 : ℝ), (8806611570887/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2239311217/10000000000 : ℝ)|^2085 ≤ (13758828649619/100000000000000 : ℝ)^1573
        have hw : |(-2239311217/10000000000 : ℝ)|=(2239311217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104331401/200000000 : ℝ)|^2085 ≤ (42208113477799/100000000000000 : ℝ)^1573
        have hw : |(104331401/200000000 : ℝ)|=(104331401/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346461021/2500000000 : ℝ)|^2085 ≤ (8806611570887/20000000000000 : ℝ)^1573
        have hw : |(1346461021/2500000000 : ℝ)|=(1346461021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_box_9 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (132231059/250000000 : ℝ)*x 0 + (-214270959/1000000000 : ℝ)*x 1 + (1077168849/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132231059/250000000 : ℝ)^2085 ≤ (42989269293371/100000000000000 : ℝ)^1573 := by
    have hnat : (132231059 : ℕ)^2085*100000000000000^1573 ≤ 42989269293371^1573*250000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132231059 250000000 42989269293371 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (214270959/1000000000 : ℝ)^2085 ≤ (12977671090911/100000000000000 : ℝ)^1573 := by
    have hnat : (214270959 : ℕ)^2085*100000000000000^1573 ≤ 12977671090911^1573*1000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214270959 1000000000 12977671090911 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077168849/2000000000 : ℝ)^2085 ≤ (8806611919833/20000000000000 : ℝ)^1573 := by
    have hnat : (1077168849 : ℕ)^2085*20000000000000^1573 ≤ 8806611919833^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077168849 2000000000 8806611919833 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132231059/250000000 : ℝ), (-214270959/1000000000 : ℝ), (1077168849/2000000000 : ℝ)] ![(42989269293371/100000000000000 : ℝ), (12977671090911/100000000000000 : ℝ), (8806611919833/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132231059/250000000 : ℝ)|^2085 ≤ (42989269293371/100000000000000 : ℝ)^1573
        have hw : |(132231059/250000000 : ℝ)|=(132231059/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-214270959/1000000000 : ℝ)|^2085 ≤ (12977671090911/100000000000000 : ℝ)^1573
        have hw : |(-214270959/1000000000 : ℝ)|=(214270959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077168849/2000000000 : ℝ)|^2085 ≤ (8806611919833/20000000000000 : ℝ)^1573
        have hw : |(1077168849/2000000000 : ℝ)|=(1077168849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_box_10 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5289242333/10000000000 : ℝ)*x 0 + (5385844359/10000000000 : ℝ)*x 1 + (-2142709473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289242333/10000000000 : ℝ)^2085 ≤ (8597853800499/20000000000000 : ℝ)^1573 := by
    have hnat : (5289242333 : ℕ)^2085*20000000000000^1573 ≤ 8597853800499^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289242333 10000000000 8597853800499 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385844359/10000000000 : ℝ)^2085 ≤ (11008265208641/25000000000000 : ℝ)^1573 := by
    have hnat : (5385844359 : ℕ)^2085*25000000000000^1573 ≤ 11008265208641^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385844359 10000000000 11008265208641 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2142709473/10000000000 : ℝ)^2085 ≤ (12977670151627/100000000000000 : ℝ)^1573 := by
    have hnat : (2142709473 : ℕ)^2085*100000000000000^1573 ≤ 12977670151627^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142709473 10000000000 12977670151627 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289242333/10000000000 : ℝ), (5385844359/10000000000 : ℝ), (-2142709473/10000000000 : ℝ)] ![(8597853800499/20000000000000 : ℝ), (11008265208641/25000000000000 : ℝ), (12977670151627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289242333/10000000000 : ℝ)|^2085 ≤ (8597853800499/20000000000000 : ℝ)^1573
        have hw : |(5289242333/10000000000 : ℝ)|=(5289242333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385844359/10000000000 : ℝ)|^2085 ≤ (11008265208641/25000000000000 : ℝ)^1573
        have hw : |(5385844359/10000000000 : ℝ)|=(5385844359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2142709473/10000000000 : ℝ)|^2085 ≤ (12977670151627/100000000000000 : ℝ)^1573
        have hw : |(-2142709473/10000000000 : ℝ)|=(2142709473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_box_11 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4492955909/10000000000 : ℝ)*x 0 + (4301443333/10000000000 : ℝ)*x 1 + (215072183/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4492955909/10000000000 : ℝ)^2085 ≤ (8657129671973/25000000000000 : ℝ)^1573 := by
    have hnat : (4492955909 : ℕ)^2085*25000000000000^1573 ≤ 8657129671973^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492955909 10000000000 8657129671973 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4301443333/10000000000 : ℝ)^2085 ≤ (32685739002679/100000000000000 : ℝ)^1573 := by
    have hnat : (4301443333 : ℕ)^2085*100000000000000^1573 ≤ 32685739002679^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301443333 10000000000 32685739002679 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215072183/500000000 : ℝ)^2085 ≤ (32685742296267/100000000000000 : ℝ)^1573 := by
    have hnat : (215072183 : ℕ)^2085*100000000000000^1573 ≤ 32685742296267^1573*500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215072183 500000000 32685742296267 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4492955909/10000000000 : ℝ), (4301443333/10000000000 : ℝ), (215072183/500000000 : ℝ)] ![(8657129671973/25000000000000 : ℝ), (32685739002679/100000000000000 : ℝ), (32685742296267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4492955909/10000000000 : ℝ)|^2085 ≤ (8657129671973/25000000000000 : ℝ)^1573
        have hw : |(4492955909/10000000000 : ℝ)|=(4492955909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4301443333/10000000000 : ℝ)|^2085 ≤ (32685739002679/100000000000000 : ℝ)^1573
        have hw : |(4301443333/10000000000 : ℝ)|=(4301443333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215072183/500000000 : ℝ)|^2085 ≤ (32685742296267/100000000000000 : ℝ)^1573
        have hw : |(215072183/500000000 : ℝ)|=(215072183/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_box_12 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1045694393/5000000000 : ℝ)*x 0 + (2719799843/5000000000 : ℝ)*x 1 + (5273167563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045694393/5000000000 : ℝ)^2085 ≤ (2513455833217/20000000000000 : ℝ)^1573 := by
    have hnat : (1045694393 : ℕ)^2085*20000000000000^1573 ≤ 2513455833217^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045694393 5000000000 2513455833217 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719799843/5000000000 : ℝ)^2085 ≤ (44616542508203/100000000000000 : ℝ)^1573 := by
    have hnat : (2719799843 : ℕ)^2085*100000000000000^1573 ≤ 44616542508203^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719799843 5000000000 44616542508203 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273167563/10000000000 : ℝ)^2085 ≤ (5352022289861/12500000000000 : ℝ)^1573 := by
    have hnat : (5273167563 : ℕ)^2085*12500000000000^1573 ≤ 5352022289861^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273167563 10000000000 5352022289861 12500000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1045694393/5000000000 : ℝ), (2719799843/5000000000 : ℝ), (5273167563/10000000000 : ℝ)] ![(2513455833217/20000000000000 : ℝ), (44616542508203/100000000000000 : ℝ), (5352022289861/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1045694393/5000000000 : ℝ)|^2085 ≤ (2513455833217/20000000000000 : ℝ)^1573
        have hw : |(-1045694393/5000000000 : ℝ)|=(1045694393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719799843/5000000000 : ℝ)|^2085 ≤ (44616542508203/100000000000000 : ℝ)^1573
        have hw : |(2719799843/5000000000 : ℝ)|=(2719799843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273167563/10000000000 : ℝ)|^2085 ≤ (5352022289861/12500000000000 : ℝ)^1573
        have hw : |(5273167563/10000000000 : ℝ)|=(5273167563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_box_13 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (167776253/312500000 : ℝ)*x 0 + (-218706257/1000000000 : ℝ)*x 1 + (2636584007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167776253/312500000 : ℝ)^2085 ≤ (548111040169/1250000000000 : ℝ)^1573 := by
    have hnat : (167776253 : ℕ)^2085*1250000000000^1573 ≤ 548111040169^1573*312500000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167776253 312500000 548111040169 1250000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218706257/1000000000 : ℝ)^2085 ≤ (3333733399263/25000000000000 : ℝ)^1573 := by
    have hnat : (218706257 : ℕ)^2085*25000000000000^1573 ≤ 3333733399263^1573*1000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218706257 1000000000 3333733399263 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636584007/5000000000 : ℝ)^2085 ≤ (42816183172781/100000000000000 : ℝ)^1573 := by
    have hnat : (2636584007 : ℕ)^2085*100000000000000^1573 ≤ 42816183172781^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636584007 5000000000 42816183172781 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167776253/312500000 : ℝ), (-218706257/1000000000 : ℝ), (2636584007/5000000000 : ℝ)] ![(548111040169/1250000000000 : ℝ), (3333733399263/25000000000000 : ℝ), (42816183172781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167776253/312500000 : ℝ)|^2085 ≤ (548111040169/1250000000000 : ℝ)^1573
        have hw : |(167776253/312500000 : ℝ)|=(167776253/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-218706257/1000000000 : ℝ)|^2085 ≤ (3333733399263/25000000000000 : ℝ)^1573
        have hw : |(-218706257/1000000000 : ℝ)|=(218706257/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636584007/5000000000 : ℝ)|^2085 ≤ (42816183172781/100000000000000 : ℝ)^1573
        have hw : |(2636584007/5000000000 : ℝ)|=(2636584007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_box_14 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1073768049/2000000000 : ℝ)*x 0 + (105463363/200000000 : ℝ)*x 1 + (-2187062189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073768049/2000000000 : ℝ)^2085 ≤ (43848884826547/100000000000000 : ℝ)^1573 := by
    have hnat : (1073768049 : ℕ)^2085*100000000000000^1573 ≤ 43848884826547^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073768049 2000000000 43848884826547 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105463363/200000000 : ℝ)^2085 ≤ (42816184636483/100000000000000 : ℝ)^1573 := by
    have hnat : (105463363 : ℕ)^2085*100000000000000^1573 ≤ 42816184636483^1573*200000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105463363 200000000 42816184636483 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2187062189/10000000000 : ℝ)^2085 ≤ (6667465258947/50000000000000 : ℝ)^1573 := by
    have hnat : (2187062189 : ℕ)^2085*50000000000000^1573 ≤ 6667465258947^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187062189 10000000000 6667465258947 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073768049/2000000000 : ℝ), (105463363/200000000 : ℝ), (-2187062189/10000000000 : ℝ)] ![(43848884826547/100000000000000 : ℝ), (42816184636483/100000000000000 : ℝ), (6667465258947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073768049/2000000000 : ℝ)|^2085 ≤ (43848884826547/100000000000000 : ℝ)^1573
        have hw : |(1073768049/2000000000 : ℝ)|=(1073768049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105463363/200000000 : ℝ)|^2085 ≤ (42816184636483/100000000000000 : ℝ)^1573
        have hw : |(105463363/200000000 : ℝ)|=(105463363/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2187062189/10000000000 : ℝ)|^2085 ≤ (6667465258947/50000000000000 : ℝ)^1573
        have hw : |(-2187062189/10000000000 : ℝ)|=(2187062189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_box_15 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4237672823/10000000000 : ℝ)*x 0 + (2214541409/5000000000 : ℝ)*x 1 + (553635281/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4237672823/10000000000 : ℝ)^2085 ≤ (4005623612377/12500000000000 : ℝ)^1573 := by
    have hnat : (4237672823 : ℕ)^2085*12500000000000^1573 ≤ 4005623612377^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237672823 10000000000 4005623612377 12500000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2214541409/5000000000 : ℝ)^2085 ≤ (33977508446361/100000000000000 : ℝ)^1573 := by
    have hnat : (2214541409 : ℕ)^2085*100000000000000^1573 ≤ 33977508446361^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214541409 5000000000 33977508446361 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553635281/1250000000 : ℝ)^2085 ≤ (33977502650341/100000000000000 : ℝ)^1573 := by
    have hnat : (553635281 : ℕ)^2085*100000000000000^1573 ≤ 33977502650341^1573*1250000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553635281 1250000000 33977502650341 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4237672823/10000000000 : ℝ), (2214541409/5000000000 : ℝ), (553635281/1250000000 : ℝ)] ![(4005623612377/12500000000000 : ℝ), (33977508446361/100000000000000 : ℝ), (33977502650341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4237672823/10000000000 : ℝ)|^2085 ≤ (4005623612377/12500000000000 : ℝ)^1573
        have hw : |(4237672823/10000000000 : ℝ)|=(4237672823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2214541409/5000000000 : ℝ)|^2085 ≤ (33977508446361/100000000000000 : ℝ)^1573
        have hw : |(2214541409/5000000000 : ℝ)|=(2214541409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(553635281/1250000000 : ℝ)|^2085 ≤ (33977502650341/100000000000000 : ℝ)^1573
        have hw : |(553635281/1250000000 : ℝ)|=(553635281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1147_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(7779/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29651/50000 : ℝ) ∧ (4989/6250 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (2598/3125 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11361/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11361/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11361/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11361/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11361/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14051/100000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (11361/100000 : ℝ) ^ (8339/2048 : ℝ) ≤ (178146199649559/1250000000000000000 : ℝ) := by
    have hpowers : (11361/100000 : ℝ)^8339 ≤ (178146199649559/1250000000000000000 : ℝ)^2048 := by
      have hnat : (11361 : ℕ)^8339*1250000000000000000^2048 ≤ 178146199649559^2048*100000^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11361 100000 178146199649559 1250000000000000000 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11361/100000 : ℝ)) (X := (178146199649559/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14051/100000 : ℝ) ^ (8339/2048 : ℝ) ≤ (33857401546922563/100000000000000000000 : ℝ) := by
    have hpowers : (14051/100000 : ℝ)^8339 ≤ (33857401546922563/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14051 : ℕ)^8339*100000000000000000000^2048 ≤ 33857401546922563^2048*100000^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14051 100000 33857401546922563 100000000000000000000 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14051/100000 : ℝ)) (X := (33857401546922563/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (625178146199649559/625000000000000000 : ℝ) ≤ (10000699948093519/10000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (625178146199649559/625000000000000000 : ℝ)^2048 ≤ (10000699948093519/10000000000000000 : ℝ)^8339 := by
      have hnat : (625178146199649559 : ℕ)^2048*10000000000000000^8339 ≤ 10000699948093519^8339*625000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625178146199649559 625000000000000000 10000699948093519 10000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000699948093519/10000000000000000 : ℝ)) (X := (625178146199649559/625000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048109097518887283/100000000000000000000 : ℝ) ≤ (1000118131139289/1000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (100048109097518887283/100000000000000000000 : ℝ)^2048 ≤ (1000118131139289/1000000000000000 : ℝ)^8339 := by
      have hnat : (100048109097518887283 : ℕ)^2048*1000000000000000^8339 ≤ 1000118131139289^8339*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048109097518887283 100000000000000000000 1000118131139289 1000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000118131139289/1000000000000000 : ℝ)) (X := (100048109097518887283/100000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033857401546922563/50000000000000000000 : ℝ) ≤ (10001662674692261/10000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (50033857401546922563/50000000000000000000 : ℝ)^2048 ≤ (10001662674692261/10000000000000000 : ℝ)^8339 := by
      have hnat : (50033857401546922563 : ℕ)^2048*10000000000000000^8339 ≤ 10001662674692261^8339*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033857401546922563 50000000000000000000 10001662674692261 10000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001662674692261/10000000000000000 : ℝ)) (X := (50033857401546922563/50000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(178146199649559/1250000000000000000 : ℝ) ≤ ((3361368165435407281/3362500000000000000 : ℝ)+2*(481363299371/269000000000000 : ℝ)*(11361/100000 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (3361368165435407281/3362500000000000000 : ℝ)+2*(481363299371/269000000000000 : ℝ)*(11361/100000 : ℝ)=(10000699948093519/10000000000000000 : ℝ) by norm_num, show 1+2*(178146199649559/1250000000000000000 : ℝ)=(625178146199649559/625000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33857401546922563/100000000000000000000 : ℝ)+(178146199649559/1250000000000000000 : ℝ) ≤ ((3361368165435407281/3362500000000000000 : ℝ)+(481363299371/269000000000000 : ℝ)*((14051/100000 : ℝ)+(11361/100000 : ℝ)))^(8339/2048 : ℝ) := by
    rw [show (3361368165435407281/3362500000000000000 : ℝ)+(481363299371/269000000000000 : ℝ)*((14051/100000 : ℝ)+(11361/100000 : ℝ))=(1000118131139289/1000000000000000 : ℝ) by norm_num, show 1+(33857401546922563/100000000000000000000 : ℝ)+(178146199649559/1250000000000000000 : ℝ)=(100048109097518887283/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33857401546922563/100000000000000000000 : ℝ) ≤ ((3361368165435407281/3362500000000000000 : ℝ)+2*(481363299371/269000000000000 : ℝ)*(14051/100000 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (3361368165435407281/3362500000000000000 : ℝ)+2*(481363299371/269000000000000 : ℝ)*(14051/100000 : ℝ)=(10001662674692261/10000000000000000 : ℝ) by norm_num, show 1+2*(33857401546922563/100000000000000000000 : ℝ)=(50033857401546922563/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3361368165435407281/3362500000000000000 : ℝ)*(X 1 0+X 2 0)+(481363299371/269000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (11361/100000 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (3361368165435407281/3362500000000000000 : ℝ)) (alpha := (481363299371/269000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3361368165435407281/3362500000000000000 : ℝ)*(X 0 1+X 2 1)+(481363299371/269000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (11361/100000 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (3361368165435407281/3362500000000000000 : ℝ)) (alpha := (481363299371/269000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3361368165435407281/3362500000000000000 : ℝ)*(X 0 2+X 1 2)+(481363299371/269000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (11361/100000 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (3361368165435407281/3362500000000000000 : ℝ)) (alpha := (481363299371/269000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2037779539/10000000000 : ℝ)*X 0 0+(5376235177/10000000000 : ℝ)*X 0 1+(1344059/2500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2648016189/5000000000 : ℝ)*X 1 0+(-536639977/2500000000 : ℝ)*X 1 1+(672029589/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((662004263/1250000000 : ℝ)*X 2 0+(5376235509/10000000000 : ℝ)*X 2 1+(-1073279607/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4471456397/10000000000 : ℝ)*X 0 0+(862466777/2000000000 : ℝ)*X 0 1+(1078083413/2500000000 : ℝ)*X 0 2+(4471456397/10000000000 : ℝ)*X 1 0+(862466777/2000000000 : ℝ)*X 1 1+(1078083413/2500000000 : ℝ)*X 1 2+(4471456397/10000000000 : ℝ)*X 2 0+(862466777/2000000000 : ℝ)*X 2 1+(1078083413/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-458521013/2000000000 : ℝ)*X 0 0+(5281207693/10000000000 : ℝ)*X 0 1+(660151007/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363163187/10000000000 : ℝ)*X 1 0+(-436791171/2000000000 : ℝ)*X 1 1+(5281207621/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5363162973/10000000000 : ℝ)*X 2 0+(2640603831/5000000000 : ℝ)*X 2 1+(-2183956087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4256123933/10000000000 : ℝ)*X 0 0+(4419979141/10000000000 : ℝ)*X 0 1+(1104994817/2500000000 : ℝ)*X 0 2+(4256123933/10000000000 : ℝ)*X 1 0+(4419979141/10000000000 : ℝ)*X 1 1+(1104994817/2500000000 : ℝ)*X 1 2+(4256123933/10000000000 : ℝ)*X 2 0+(4419979141/10000000000 : ℝ)*X 2 1+(1104994817/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2239311217/10000000000 : ℝ)*X 0 0+(104331401/200000000 : ℝ)*X 0 1+(1346461021/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((132231059/250000000 : ℝ)*X 1 0+(-214270959/1000000000 : ℝ)*X 1 1+(1077168849/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289242333/10000000000 : ℝ)*X 2 0+(5385844359/10000000000 : ℝ)*X 2 1+(-2142709473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4492955909/10000000000 : ℝ)*X 0 0+(4301443333/10000000000 : ℝ)*X 0 1+(215072183/500000000 : ℝ)*X 0 2+(4492955909/10000000000 : ℝ)*X 1 0+(4301443333/10000000000 : ℝ)*X 1 1+(215072183/500000000 : ℝ)*X 1 2+(4492955909/10000000000 : ℝ)*X 2 0+(4301443333/10000000000 : ℝ)*X 2 1+(215072183/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1045694393/5000000000 : ℝ)*X 0 0+(2719799843/5000000000 : ℝ)*X 0 1+(5273167563/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((167776253/312500000 : ℝ)*X 1 0+(-218706257/1000000000 : ℝ)*X 1 1+(2636584007/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1073768049/2000000000 : ℝ)*X 2 0+(105463363/200000000 : ℝ)*X 2 1+(-2187062189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4237672823/10000000000 : ℝ)*X 0 0+(2214541409/5000000000 : ℝ)*X 0 1+(553635281/1250000000 : ℝ)*X 0 2+(4237672823/10000000000 : ℝ)*X 1 0+(2214541409/5000000000 : ℝ)*X 1 1+(553635281/1250000000 : ℝ)*X 1 2+(4237672823/10000000000 : ℝ)*X 2 0+(2214541409/5000000000 : ℝ)*X 2 1+(553635281/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-7779/12500 : ℝ) ≤ (-104622645620001687961404069572373/168125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4954869/5000000000000 : ℝ)*(upper1) + (200780541/100000000000000 : ℝ)*(lower4) + (30006639/50000000000000 : ℝ)*(upper5) + (15331758691641/390625000000 : ℝ)*(major0) + (15331758691641/390625000000 : ℝ)*(major1) + (3924930225060097/100000000000000 : ℝ)*(major2) + (12682287709/100000000000000 : ℝ)*(sp1) + (5173423217/20000000000000 : ℝ)*(sp2) + (229186651/2500000000000 : ℝ)*(sp3) + (2623236216797771/50000000000000 : ℝ)*(sp4) + (1049294090928607/20000000000000 : ℝ)*(sp5) + (262322863490733/5000000000000 : ℝ)*(sp6) + (1312055586677809/50000000000000 : ℝ)*(sp7) + (10703335203/100000000000000 : ℝ)*(sp12) + (1312060170410829/50000000000000 : ℝ)*(f.failure) + (1049296627386149/20000000000000 : ℝ)*(f.sum) + (158264750745203/26900000000000000000000000000 : ℝ)*base65 + (635733742368550881/84062500000000000000000000000000 : ℝ)*base68 + (2915968211114683743/336250000000000000000000000000000 : ℝ)*base70 + (8381829715738381/84062500000000000000000000000000 : ℝ)*base72 + (160795256475703/26900000000000000000000000000 : ℝ)*base73 + (1139571533162183743/336250000000000000000000000000000 : ℝ)*base76 + (115331191535979407/10507812500000000000000000000000 : ℝ)*base78 + (114368349915786939/21015625000000000000000000000000 : ℝ)*base80 + (10718136778671/3362500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1536927/2500000000000000000000 : ℝ)*base90 + (1536927/2500000000000000000000 : ℝ)*base92 + (26536927/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29651/50000 : ℝ) ≤ (3115822814028566126531358023007/5253906250000000000000000000000 : ℝ) := by norm_num
    linear_combination (83728461/50000000000000 : ℝ)*(lower1) + (147134987/100000000000000 : ℝ)*(lower2) + (49748823/20000000000000 : ℝ)*(lower3) + (113341161/20000000000000 : ℝ)*(upper4) + (31165322817081/781250000000 : ℝ)*(major0) + (31165322817081/781250000000 : ℝ)*(major1) + (31165322817081/781250000000 : ℝ)*(major2) + (2645745268338293/50000000000000 : ℝ)*(sp0) + (264572116828027/5000000000000 : ℝ)*(sp1) + (1058294409945737/20000000000000 : ℝ)*(sp2) + (1333522331157489/50000000000000 : ℝ)*(sp3) + (48200116047/100000000000000 : ℝ)*(sp5) + (18486947901/100000000000000 : ℝ)*(sp6) + (19148738987/100000000000000 : ℝ)*(sp7) + (533412762210793/20000000000000 : ℝ)*(f.failure) + (2645745268338293/50000000000000 : ℝ)*(f.sum) + (15823005784089/6725000000000000000000000000 : ℝ)*base65 + (23370887665037787/21015625000000000000000000000000 : ℝ)*base68 + (73447842649794603/5253906250000000000000000000000 : ℝ)*base70 + (723632303936542331/10507812500000000000000000000000 : ℝ)*base72 + (414508950123/210156250000000000000000000 : ℝ)*base74 + (54037342102149713/21015625000000000000000000000000 : ℝ)*base75 + (739740126763613919/10507812500000000000000000000000 : ℝ)*base77 + (3487936201452557/1313476562500000000000000000000 : ℝ)*base80 + (231468478424111/6725000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2780141/1000000000000000000000 : ℝ)*base89 + (2780141/1000000000000000000000 : ℝ)*base91 + (2780141/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (4989/6250 : ℝ) ≤ (134207613018472619911336138040259/168125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33559989/100000000000000 : ℝ)*(upper0) + (35536047/100000000000000 : ℝ)*(lower1) + (38611283/50000000000000 : ℝ)*(lower3) + (9898261/50000000000000 : ℝ)*(upper4) + (2228514664972943/50000000000000 : ℝ)*(major0) + (2228514664972943/50000000000000 : ℝ)*(major1) + (4457029329945887/100000000000000 : ℝ)*(major2) + (17798346217/12500000000000 : ℝ)*(sp1) + (97491406449/50000000000000 : ℝ)*(sp2) + (17246800433/50000000000000 : ℝ)*(sp3) + (5907580092149173/100000000000000 : ℝ)*(sp8) + (5907437705379437/100000000000000 : ℝ)*(sp9) + (1476846277334069/25000000000000 : ℝ)*(sp10) + (372479422204061/12500000000000 : ℝ)*(sp11) + (1489934935616677/50000000000000 : ℝ)*(f.failure) + (5907580092149173/100000000000000 : ℝ)*(f.sum) + (296297939270917/26900000000000000000000000000 : ℝ)*base66 + (92167542959429233/168125000000000000000000000000000 : ℝ)*base67 + (2387863287712128247/336250000000000000000000000000000 : ℝ)*base69 + (724744688395679233/168125000000000000000000000000000 : ℝ)*base71 + (276947799337617/26900000000000000000000000000 : ℝ)*base74 + (3788682278980878247/336250000000000000000000000000000 : ℝ)*base75 + (534322642642889517/168125000000000000000000000000000 : ℝ)*base78 + (121904012539139517/168125000000000000000000000000000 : ℝ)*base80 + (25531690927347/6725000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (27268249/2500000000000000000000 : ℝ)*base89 + (27268249/2500000000000000000000 : ℝ)*base91 + (2268249/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-2598/3125 : ℝ) ≤ (-139767475800359687999820888659343/168125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (157749381/50000000000000 : ℝ)*(lower0) + (8952621/10000000000000 : ℝ)*(lower2) + (12631663/25000000000000 : ℝ)*(upper3) + (423781721/100000000000000 : ℝ)*(upper5) + (898401500265183/20000000000000 : ℝ)*(major0) + (898401500265183/20000000000000 : ℝ)*(major1) + (1123001875331479/25000000000000 : ℝ)*(major2) + (2820314681/20000000000000 : ℝ)*(sp4) + (34329704603/12500000000000 : ℝ)*(sp7) + (9279529001/50000000000000 : ℝ)*(sp8) + (6008437873411167/100000000000000 : ℝ)*(sp12) + (3004235267021287/50000000000000 : ℝ)*(sp13) + (3004235267021287/50000000000000 : ℝ)*(sp14) + (3002980854675099/100000000000000 : ℝ)*(sp15) + (3003255492311923/100000000000000 : ℝ)*(f.failure) + (3004235267021287/50000000000000 : ℝ)*(f.sum) + (110208089127101/26900000000000000000000000000 : ℝ)*base65 + (1355352250798162577/67250000000000000000000000000000 : ℝ)*base68 + (22637420893007139/5253906250000000000000000000000 : ℝ)*base69 + (301343773521837423/67250000000000000000000000000000 : ℝ)*base71 + (5591481125099/26900000000000000000000000000 : ℝ)*base74 + (92677701234294181/21015625000000000000000000000000 : ℝ)*base75 + (343599736850090077/67250000000000000000000000000000 : ℝ)*base78 + (742057423780840077/67250000000000000000000000000000 : ℝ)*base80 + (12075283004273/2690000000000000000000000000 : ℝ)*base81 + (14249951/5000000000000000000000 : ℝ)*base89 + (14249951/5000000000000000000000 : ℝ)*base91 + (35750049/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1147_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7779/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(29651/50000 : ℝ) else (4989/6250 : ℝ) ≤ X j i ∧ X j i ≤ (2598/3125 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1147_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1147_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (71/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7779/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(29651/50000 : ℝ) else (4989/6250 : ℝ) ≤ X j i ∧ X j i ≤ (2598/3125 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1147_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1147_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (71/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7779/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(29651/50000 : ℝ) else (4989/6250 : ℝ) ≤ X j i ∧ X j i ≤ (2598/3125 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1147_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

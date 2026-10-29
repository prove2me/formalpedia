-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1551_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:10:06.140959+00:00
-- url     : https://prove2.me/submissions/1701686a-6437-4bf5-bdab-7241db80c6ae

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
theorem support_rectangle_w1551_s0_0 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1645240351/10000000000 : ℝ)*x 0 + (588342569/1000000000 : ℝ)*x 1 + (4871648231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1645240351/10000000000 : ℝ)^4599 ≤ (1962280672319/20000000000000 : ℝ)^3575 := by
    have hnat : (1645240351 : ℕ)^4599*20000000000000^3575 ≤ 1962280672319^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1645240351 10000000000 1962280672319 20000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (588342569/1000000000 : ℝ)^4599 ≤ (3158818459037/6250000000000 : ℝ)^3575 := by
    have hnat : (588342569 : ℕ)^4599*6250000000000^3575 ≤ 3158818459037^3575*1000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      588342569 1000000000 3158818459037 6250000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4871648231/10000000000 : ℝ)^4599 ≤ (9911875319763/25000000000000 : ℝ)^3575 := by
    have hnat : (4871648231 : ℕ)^4599*25000000000000^3575 ≤ 9911875319763^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4871648231 10000000000 9911875319763 25000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1645240351/10000000000 : ℝ), (588342569/1000000000 : ℝ), (4871648231/10000000000 : ℝ)] ![(1962280672319/20000000000000 : ℝ), (3158818459037/6250000000000 : ℝ), (9911875319763/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1645240351/10000000000 : ℝ)|^4599 ≤ (1962280672319/20000000000000 : ℝ)^3575
        have hw : |(-1645240351/10000000000 : ℝ)|=(1645240351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(588342569/1000000000 : ℝ)|^4599 ≤ (3158818459037/6250000000000 : ℝ)^3575
        have hw : |(588342569/1000000000 : ℝ)|=(588342569/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4871648231/10000000000 : ℝ)|^4599 ≤ (9911875319763/25000000000000 : ℝ)^3575
        have hw : |(4871648231/10000000000 : ℝ)|=(4871648231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s0_1 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2734773001/5000000000 : ℝ)*x 0 + (-110479013/500000000 : ℝ)*x 1 + (1217912057/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2734773001/5000000000 : ℝ)^4599 ≤ (23007092260293/50000000000000 : ℝ)^3575 := by
    have hnat : (2734773001 : ℕ)^4599*50000000000000^3575 ≤ 23007092260293^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734773001 5000000000 23007092260293 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110479013/500000000 : ℝ)^4599 ≤ (14338314218143/100000000000000 : ℝ)^3575 := by
    have hnat : (110479013 : ℕ)^4599*100000000000000^3575 ≤ 14338314218143^3575*500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110479013 500000000 14338314218143 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1217912057/2500000000 : ℝ)^4599 ≤ (9911875311911/25000000000000 : ℝ)^3575 := by
    have hnat : (1217912057 : ℕ)^4599*25000000000000^3575 ≤ 9911875311911^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217912057 2500000000 9911875311911 25000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2734773001/5000000000 : ℝ), (-110479013/500000000 : ℝ), (1217912057/2500000000 : ℝ)] ![(23007092260293/50000000000000 : ℝ), (14338314218143/100000000000000 : ℝ), (9911875311911/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2734773001/5000000000 : ℝ)|^4599 ≤ (23007092260293/50000000000000 : ℝ)^3575
        have hw : |(2734773001/5000000000 : ℝ)|=(2734773001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-110479013/500000000 : ℝ)|^4599 ≤ (14338314218143/100000000000000 : ℝ)^3575
        have hw : |(-110479013/500000000 : ℝ)|=(110479013/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1217912057/2500000000 : ℝ)|^4599 ≤ (9911875311911/25000000000000 : ℝ)^3575
        have hw : |(1217912057/2500000000 : ℝ)|=(1217912057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s0_2 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5469546037/10000000000 : ℝ)*x 0 + (1217912047/2500000000 : ℝ)*x 1 + (-441916053/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5469546037/10000000000 : ℝ)^4599 ≤ (23007092449687/50000000000000 : ℝ)^3575 := by
    have hnat : (5469546037 : ℕ)^4599*50000000000000^3575 ≤ 23007092449687^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469546037 10000000000 23007092449687 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1217912047/2500000000 : ℝ)^4599 ≤ (39647500828863/100000000000000 : ℝ)^3575 := by
    have hnat : (1217912047 : ℕ)^4599*100000000000000^3575 ≤ 39647500828863^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217912047 2500000000 39647500828863 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441916053/2000000000 : ℝ)^4599 ≤ (7169157129941/50000000000000 : ℝ)^3575 := by
    have hnat : (441916053 : ℕ)^4599*50000000000000^3575 ≤ 7169157129941^3575*2000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441916053 2000000000 7169157129941 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5469546037/10000000000 : ℝ), (1217912047/2500000000 : ℝ), (-441916053/2000000000 : ℝ)] ![(23007092449687/50000000000000 : ℝ), (39647500828863/100000000000000 : ℝ), (7169157129941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5469546037/10000000000 : ℝ)|^4599 ≤ (23007092449687/50000000000000 : ℝ)^3575
        have hw : |(5469546037/10000000000 : ℝ)|=(5469546037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1217912047/2500000000 : ℝ)|^4599 ≤ (39647500828863/100000000000000 : ℝ)^3575
        have hw : |(1217912047/2500000000 : ℝ)|=(1217912047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-441916053/2000000000 : ℝ)|^4599 ≤ (7169157129941/50000000000000 : ℝ)^3575
        have hw : |(-441916053/2000000000 : ℝ)|=(441916053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s0_3 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (258424193/625000000 : ℝ)*x 0 + (3092240129/10000000000 : ℝ)*x 1 + (1362430273/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258424193/625000000 : ℝ)^4599 ≤ (32106462659713/100000000000000 : ℝ)^3575 := by
    have hnat : (258424193 : ℕ)^4599*100000000000000^3575 ≤ 32106462659713^3575*625000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258424193 625000000 32106462659713 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3092240129/10000000000 : ℝ)^4599 ≤ (22093796524849/100000000000000 : ℝ)^3575 := by
    have hnat : (3092240129 : ℕ)^4599*100000000000000^3575 ≤ 22093796524849^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3092240129 10000000000 22093796524849 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1362430273/2500000000 : ℝ)^4599 ≤ (45799740796261/100000000000000 : ℝ)^3575 := by
    have hnat : (1362430273 : ℕ)^4599*100000000000000^3575 ≤ 45799740796261^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362430273 2500000000 45799740796261 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(258424193/625000000 : ℝ), (3092240129/10000000000 : ℝ), (1362430273/2500000000 : ℝ)] ![(32106462659713/100000000000000 : ℝ), (22093796524849/100000000000000 : ℝ), (45799740796261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(258424193/625000000 : ℝ)|^4599 ≤ (32106462659713/100000000000000 : ℝ)^3575
        have hw : |(258424193/625000000 : ℝ)|=(258424193/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3092240129/10000000000 : ℝ)|^4599 ≤ (22093796524849/100000000000000 : ℝ)^3575
        have hw : |(3092240129/10000000000 : ℝ)|=(3092240129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1362430273/2500000000 : ℝ)|^4599 ≤ (45799740796261/100000000000000 : ℝ)^3575
        have hw : |(1362430273/2500000000 : ℝ)|=(1362430273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s0_4 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-412110381/2500000000 : ℝ)*x 0 + (1224313233/2500000000 : ℝ)*x 1 + (5856909979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412110381/2500000000 : ℝ)^4599 ≤ (9835968501067/100000000000000 : ℝ)^3575 := by
    have hnat : (412110381 : ℕ)^4599*100000000000000^3575 ≤ 9835968501067^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412110381 2500000000 9835968501067 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1224313233/2500000000 : ℝ)^4599 ≤ (4989471505481/12500000000000 : ℝ)^3575 := by
    have hnat : (1224313233 : ℕ)^4599*12500000000000^3575 ≤ 4989471505481^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1224313233 2500000000 4989471505481 12500000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5856909979/10000000000 : ℝ)^4599 ≤ (25124129725631/50000000000000 : ℝ)^3575 := by
    have hnat : (5856909979 : ℕ)^4599*50000000000000^3575 ≤ 25124129725631^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5856909979 10000000000 25124129725631 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-412110381/2500000000 : ℝ), (1224313233/2500000000 : ℝ), (5856909979/10000000000 : ℝ)] ![(9835968501067/100000000000000 : ℝ), (4989471505481/12500000000000 : ℝ), (25124129725631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-412110381/2500000000 : ℝ)|^4599 ≤ (9835968501067/100000000000000 : ℝ)^3575
        have hw : |(-412110381/2500000000 : ℝ)|=(412110381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1224313233/2500000000 : ℝ)|^4599 ≤ (4989471505481/12500000000000 : ℝ)^3575
        have hw : |(1224313233/2500000000 : ℝ)|=(1224313233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5856909979/10000000000 : ℝ)|^4599 ≤ (25124129725631/50000000000000 : ℝ)^3575
        have hw : |(5856909979/10000000000 : ℝ)|=(5856909979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s0_5 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (324561699/625000000 : ℝ)*x 0 + (-15303987/125000000 : ℝ)*x 1 + (146422741/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324561699/625000000 : ℝ)^4599 ≤ (21521532999707/50000000000000 : ℝ)^3575 := by
    have hnat : (324561699 : ℕ)^4599*50000000000000^3575 ≤ 21521532999707^3575*625000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324561699 625000000 21521532999707 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15303987/125000000 : ℝ)^4599 ≤ (3354339138789/50000000000000 : ℝ)^3575 := by
    have hnat : (15303987 : ℕ)^4599*50000000000000^3575 ≤ 3354339138789^3575*125000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15303987 125000000 3354339138789 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (146422741/250000000 : ℝ)^4599 ≤ (10049651141963/20000000000000 : ℝ)^3575 := by
    have hnat : (146422741 : ℕ)^4599*20000000000000^3575 ≤ 10049651141963^3575*250000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146422741 250000000 10049651141963 20000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(324561699/625000000 : ℝ), (-15303987/125000000 : ℝ), (146422741/250000000 : ℝ)] ![(21521532999707/50000000000000 : ℝ), (3354339138789/50000000000000 : ℝ), (10049651141963/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(324561699/625000000 : ℝ)|^4599 ≤ (21521532999707/50000000000000 : ℝ)^3575
        have hw : |(324561699/625000000 : ℝ)|=(324561699/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15303987/125000000 : ℝ)|^4599 ≤ (3354339138789/50000000000000 : ℝ)^3575
        have hw : |(-15303987/125000000 : ℝ)|=(15303987/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(146422741/250000000 : ℝ)|^4599 ≤ (10049651141963/20000000000000 : ℝ)^3575
        have hw : |(146422741/250000000 : ℝ)|=(146422741/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s0_6 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5192986629/10000000000 : ℝ)*x 0 + (5856910593/10000000000 : ℝ)*x 1 + (-1224318307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5192986629/10000000000 : ℝ)^4599 ≤ (10760765020383/25000000000000 : ℝ)^3575 := by
    have hnat : (5192986629 : ℕ)^4599*25000000000000^3575 ≤ 10760765020383^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192986629 10000000000 10760765020383 25000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5856910593/10000000000 : ℝ)^4599 ≤ (10049653245561/20000000000000 : ℝ)^3575 := by
    have hnat : (5856910593 : ℕ)^4599*20000000000000^3575 ≤ 10049653245561^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5856910593 10000000000 10049653245561 20000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1224318307/10000000000 : ℝ)^4599 ≤ (3354336837279/50000000000000 : ℝ)^3575 := by
    have hnat : (1224318307 : ℕ)^4599*50000000000000^3575 ≤ 3354336837279^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1224318307 10000000000 3354336837279 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5192986629/10000000000 : ℝ), (5856910593/10000000000 : ℝ), (-1224318307/10000000000 : ℝ)] ![(10760765020383/25000000000000 : ℝ), (10049653245561/20000000000000 : ℝ), (3354336837279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5192986629/10000000000 : ℝ)|^4599 ≤ (10760765020383/25000000000000 : ℝ)^3575
        have hw : |(5192986629/10000000000 : ℝ)|=(5192986629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5856910593/10000000000 : ℝ)|^4599 ≤ (10049653245561/20000000000000 : ℝ)^3575
        have hw : |(5856910593/10000000000 : ℝ)|=(5856910593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1224318307/10000000000 : ℝ)|^4599 ≤ (3354336837279/50000000000000 : ℝ)^3575
        have hw : |(-1224318307/10000000000 : ℝ)|=(1224318307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s0_7 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1035561059/2500000000 : ℝ)*x 0 + (2695030101/5000000000 : ℝ)*x 1 + (3154022307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035561059/2500000000 : ℝ)^4599 ≤ (16090486071111/50000000000000 : ℝ)^3575 := by
    have hnat : (1035561059 : ℕ)^4599*50000000000000^3575 ≤ 16090486071111^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035561059 2500000000 16090486071111 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695030101/5000000000 : ℝ)^4599 ≤ (45155745641083/100000000000000 : ℝ)^3575 := by
    have hnat : (2695030101 : ℕ)^4599*100000000000000^3575 ≤ 45155745641083^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695030101 5000000000 45155745641083 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154022307/10000000000 : ℝ)^4599 ≤ (11331641102351/50000000000000 : ℝ)^3575 := by
    have hnat : (3154022307 : ℕ)^4599*50000000000000^3575 ≤ 11331641102351^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154022307 10000000000 11331641102351 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1035561059/2500000000 : ℝ), (2695030101/5000000000 : ℝ), (3154022307/10000000000 : ℝ)] ![(16090486071111/50000000000000 : ℝ), (45155745641083/100000000000000 : ℝ), (11331641102351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1035561059/2500000000 : ℝ)|^4599 ≤ (16090486071111/50000000000000 : ℝ)^3575
        have hw : |(1035561059/2500000000 : ℝ)|=(1035561059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695030101/5000000000 : ℝ)|^4599 ≤ (45155745641083/100000000000000 : ℝ)^3575
        have hw : |(2695030101/5000000000 : ℝ)|=(2695030101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154022307/10000000000 : ℝ)|^4599 ≤ (11331641102351/50000000000000 : ℝ)^3575
        have hw : |(3154022307/10000000000 : ℝ)|=(3154022307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1551_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2601593/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (829/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24989/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4597/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4597 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4597*1^1024 ≤ 0^1024*1^4597 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4597 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4597/1024 : ℝ) ≤ (817550731578645013/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4597 ≤ (817550731578645013/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4597*50000000000000000000^1024 ≤ 817550731578645013^1024*5^4597 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 817550731578645013 50000000000000000000 4597 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (817550731578645013/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4597/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4597 := by
      have hnat : (1 : ℕ)^1024*1^4597 ≤ 1^4597*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4597 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50817550731578645013/50000000000000000000 : ℝ) ≤ (10036193308328171/10000000000000000 : ℝ) ^ (4597/1024 : ℝ) := by
    have hpowers : (50817550731578645013/50000000000000000000 : ℝ)^1024 ≤ (10036193308328171/10000000000000000 : ℝ)^4597 := by
      have hnat : (50817550731578645013 : ℕ)^1024*10000000000000000^4597 ≤ 10036193308328171^4597*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50817550731578645013 50000000000000000000 10036193308328171 10000000000000000 1024 4597 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10036193308328171/10000000000000000 : ℝ)) (X := (50817550731578645013/50000000000000000000 : ℝ)) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25817550731578645013/25000000000000000000 : ℝ) ≤ (5036193308328171/5000000000000000 : ℝ) ^ (4597/1024 : ℝ) := by
    have hpowers : (25817550731578645013/25000000000000000000 : ℝ)^1024 ≤ (5036193308328171/5000000000000000 : ℝ)^4597 := by
      have hnat : (25817550731578645013 : ℕ)^1024*5000000000000000^4597 ≤ 5036193308328171^4597*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25817550731578645013 25000000000000000000 5036193308328171 5000000000000000 1024 4597 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5036193308328171/5000000000000000 : ℝ)) (X := (25817550731578645013/25000000000000000000 : ℝ)) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(36193308328171/4000000000000000 : ℝ)*(0 : ℝ))^(4597/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(36193308328171/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(817550731578645013/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(36193308328171/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4597/1024 : ℝ) := by
    rw [show (1 : ℝ)+(36193308328171/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10036193308328171/10000000000000000 : ℝ) by norm_num, show 1+(817550731578645013/50000000000000000000 : ℝ)+(0 : ℝ)=(50817550731578645013/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(817550731578645013/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(36193308328171/4000000000000000 : ℝ)*(2/5 : ℝ))^(4597/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(36193308328171/4000000000000000 : ℝ)*(2/5 : ℝ)=(5036193308328171/5000000000000000 : ℝ) by norm_num, show 1+2*(817550731578645013/50000000000000000000 : ℝ)=(25817550731578645013/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(36193308328171/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4597/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (36193308328171/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(36193308328171/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4597/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (36193308328171/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(36193308328171/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4597/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (36193308328171/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1645240351/10000000000 : ℝ)*X 0 0+(588342569/1000000000 : ℝ)*X 0 1+(4871648231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2734773001/5000000000 : ℝ)*X 1 0+(-110479013/500000000 : ℝ)*X 1 1+(1217912057/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5469546037/10000000000 : ℝ)*X 2 0+(1217912047/2500000000 : ℝ)*X 2 1+(-441916053/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((258424193/625000000 : ℝ)*X 0 0+(3092240129/10000000000 : ℝ)*X 0 1+(1362430273/2500000000 : ℝ)*X 0 2+(258424193/625000000 : ℝ)*X 1 0+(3092240129/10000000000 : ℝ)*X 1 1+(1362430273/2500000000 : ℝ)*X 1 2+(258424193/625000000 : ℝ)*X 2 0+(3092240129/10000000000 : ℝ)*X 2 1+(1362430273/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-412110381/2500000000 : ℝ)*X 0 0+(1224313233/2500000000 : ℝ)*X 0 1+(5856909979/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((324561699/625000000 : ℝ)*X 1 0+(-15303987/125000000 : ℝ)*X 1 1+(146422741/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5192986629/10000000000 : ℝ)*X 2 0+(5856910593/10000000000 : ℝ)*X 2 1+(-1224318307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1035561059/2500000000 : ℝ)*X 0 0+(2695030101/5000000000 : ℝ)*X 0 1+(3154022307/10000000000 : ℝ)*X 0 2+(1035561059/2500000000 : ℝ)*X 1 0+(2695030101/5000000000 : ℝ)*X 1 1+(3154022307/10000000000 : ℝ)*X 1 2+(1035561059/2500000000 : ℝ)*X 2 0+(2695030101/5000000000 : ℝ)*X 2 1+(3154022307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (273899868562104348466311/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26562417/50000000000000 : ℝ)*(base1) + (1159124071/100000000000000 : ℝ)*(base19) + (1165448697/100000000000000 : ℝ)*(base23) + (5991373/4000000000000 : ℝ)*(upper3) + (150106521/100000000000000 : ℝ)*(upper5) + (353138302601149/50000000000000 : ℝ)*(major0) + (353138302601149/50000000000000 : ℝ)*(major1) + (353138302601149/50000000000000 : ℝ)*(major2) + (988363653303611/100000000000000 : ℝ)*(sp0) + (247091672108953/25000000000000 : ℝ)*(sp1) + (494183341055593/50000000000000 : ℝ)*(sp2) + (106045826367469/25000000000000 : ℝ)*(sp3) + (849476221/20000000000000 : ℝ)*(sp4) + (455412521/25000000000000 : ℝ)*(sp7) + (424185180244793/100000000000000 : ℝ)*(f.failure) + (988367847559883/100000000000000 : ℝ)*(f.sum) + (314132729431521/100000000000000000000000000000 : ℝ)*base66 + (386391670731521/200000000000000000000000000000 : ℝ)*base68 + (1866557649531521/200000000000000000000000000000 : ℝ)*base70 + (1397966293531521/200000000000000000000000000000 : ℝ)*base72 + (166580171531521/100000000000000000000000000000 : ℝ)*base74 + (1725944089531521/200000000000000000000000000000 : ℝ)*base76 + (1602255545131521/200000000000000000000000000000 : ℝ)*base78 + (1022714574331521/200000000000000000000000000000 : ℝ)*base80 + (420276595331521/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1130249/156250000000000000000 : ℝ)*base89 + (1130249/156250000000000000000 : ℝ)*base91 + (1130249/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1282119017982186997693701/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (145577929/10000000000000 : ℝ)*(base19) + (788865257/50000000000000 : ℝ)*(base23) + (233194483/100000000000000 : ℝ)*(base39) + (35489549/20000000000000 : ℝ)*(upper3) + (327513127/100000000000000 : ℝ)*(upper5) + (74462859828299/10000000000000 : ℝ)*(major0) + (74462859828299/10000000000000 : ℝ)*(major1) + (744628365088507/100000000000000 : ℝ)*(major2) + (1981046297/50000000000000 : ℝ)*(sp1) + (4040712833/100000000000000 : ℝ)*(sp2) + (208407521881097/20000000000000 : ℝ)*(sp4) + (521016095766801/50000000000000 : ℝ)*(sp5) + (521016112078311/50000000000000 : ℝ)*(sp6) + (447219140279503/100000000000000 : ℝ)*(sp7) + (447219140279503/100000000000000 : ℝ)*(f.failure) + (1042037842599969/100000000000000 : ℝ)*(f.sum) + (665065563658013/400000000000000000000000000000 : ℝ)*base66 + (371598033969303/400000000000000000000000000000 : ℝ)*base68 + (37232524728871/40000000000000000000000000000 : ℝ)*base70 + (2699113649169303/400000000000000000000000000000 : ℝ)*base72 + (305728165141987/400000000000000000000000000000 : ℝ)*base73 + (249869000608871/40000000000000000000000000000 : ℝ)*base76 + (114751985968871/40000000000000000000000000000 : ℝ)*base78 + (406897517528871/40000000000000000000000000000 : ℝ)*base80 + (43963269728871/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1173279/156250000000000000000 : ℝ)*base89 + (1173279/156250000000000000000 : ℝ)*base91 + (1173279/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1551_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2601593/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (829/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24989/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1551_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1551_s1_0 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1788692373/10000000000 : ℝ)*x 0 + (173309621/312500000 : ℝ)*x 1 + (255839763/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1788692373/10000000000 : ℝ)^4599 ≤ (10925385680587/100000000000000 : ℝ)^3575 := by
    have hnat : (1788692373 : ℕ)^4599*100000000000000^3575 ≤ 10925385680587^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788692373 10000000000 10925385680587 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (173309621/312500000 : ℝ)^4599 ≤ (11710564563273/25000000000000 : ℝ)^3575 := by
    have hnat : (173309621 : ℕ)^4599*25000000000000^3575 ≤ 11710564563273^3575*312500000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173309621 312500000 11710564563273 25000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (255839763/500000000 : ℝ)^4599 ≤ (42232356050779/100000000000000 : ℝ)^3575 := by
    have hnat : (255839763 : ℕ)^4599*100000000000000^3575 ≤ 42232356050779^3575*500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255839763 500000000 42232356050779 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1788692373/10000000000 : ℝ), (173309621/312500000 : ℝ), (255839763/500000000 : ℝ)] ![(10925385680587/100000000000000 : ℝ), (11710564563273/25000000000000 : ℝ), (42232356050779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1788692373/10000000000 : ℝ)|^4599 ≤ (10925385680587/100000000000000 : ℝ)^3575
        have hw : |(-1788692373/10000000000 : ℝ)|=(1788692373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(173309621/312500000 : ℝ)|^4599 ≤ (11710564563273/25000000000000 : ℝ)^3575
        have hw : |(173309621/312500000 : ℝ)|=(173309621/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(255839763/500000000 : ℝ)|^4599 ≤ (42232356050779/100000000000000 : ℝ)^3575
        have hw : |(255839763/500000000 : ℝ)|=(255839763/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s1_1 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379690659/10000000000 : ℝ)*x 0 + (-2013611099/10000000000 : ℝ)*x 1 + (319799691/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379690659/10000000000 : ℝ)^4599 ≤ (45044021595727/100000000000000 : ℝ)^3575 := by
    have hnat : (5379690659 : ℕ)^4599*100000000000000^3575 ≤ 45044021595727^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379690659 10000000000 45044021595727 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2013611099/10000000000 : ℝ)^4599 ≤ (12723624511861/100000000000000 : ℝ)^3575 := by
    have hnat : (2013611099 : ℕ)^4599*100000000000000^3575 ≤ 12723624511861^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013611099 10000000000 12723624511861 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319799691/625000000 : ℝ)^4599 ≤ (42232353884747/100000000000000 : ℝ)^3575 := by
    have hnat : (319799691 : ℕ)^4599*100000000000000^3575 ≤ 42232353884747^3575*625000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319799691 625000000 42232353884747 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379690659/10000000000 : ℝ), (-2013611099/10000000000 : ℝ), (319799691/625000000 : ℝ)] ![(45044021595727/100000000000000 : ℝ), (12723624511861/100000000000000 : ℝ), (42232353884747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379690659/10000000000 : ℝ)|^4599 ≤ (45044021595727/100000000000000 : ℝ)^3575
        have hw : |(5379690659/10000000000 : ℝ)|=(5379690659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2013611099/10000000000 : ℝ)|^4599 ≤ (12723624511861/100000000000000 : ℝ)^3575
        have hw : |(-2013611099/10000000000 : ℝ)|=(2013611099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(319799691/625000000 : ℝ)|^4599 ≤ (42232353884747/100000000000000 : ℝ)^3575
        have hw : |(319799691/625000000 : ℝ)|=(319799691/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s1_2 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537969051/1000000000 : ℝ)*x 0 + (1023358843/2000000000 : ℝ)*x 1 + (-1006806197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537969051/1000000000 : ℝ)^4599 ≤ (45044019990807/100000000000000 : ℝ)^3575 := by
    have hnat : (537969051 : ℕ)^4599*100000000000000^3575 ≤ 45044019990807^3575*1000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537969051 1000000000 45044019990807 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1023358843/2000000000 : ℝ)^4599 ≤ (5279043119397/12500000000000 : ℝ)^3575 := by
    have hnat : (1023358843 : ℕ)^4599*12500000000000^3575 ≤ 5279043119397^3575*2000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023358843 2000000000 5279043119397 12500000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1006806197/5000000000 : ℝ)^4599 ≤ (6361817519283/50000000000000 : ℝ)^3575 := by
    have hnat : (1006806197 : ℕ)^4599*50000000000000^3575 ≤ 6361817519283^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006806197 5000000000 6361817519283 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537969051/1000000000 : ℝ), (1023358843/2000000000 : ℝ), (-1006806197/5000000000 : ℝ)] ![(45044019990807/100000000000000 : ℝ), (5279043119397/12500000000000 : ℝ), (6361817519283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537969051/1000000000 : ℝ)|^4599 ≤ (45044019990807/100000000000000 : ℝ)^3575
        have hw : |(537969051/1000000000 : ℝ)|=(537969051/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1023358843/2000000000 : ℝ)|^4599 ≤ (5279043119397/12500000000000 : ℝ)^3575
        have hw : |(1023358843/2000000000 : ℝ)|=(1023358843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1006806197/5000000000 : ℝ)|^4599 ≤ (6361817519283/50000000000000 : ℝ)^3575
        have hw : |(-1006806197/5000000000 : ℝ)|=(1006806197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s1_3 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058845193/2500000000 : ℝ)*x 0 + (3759600463/10000000000 : ℝ)*x 1 + (190377999/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058845193/2500000000 : ℝ)^4599 ≤ (33114784831253/100000000000000 : ℝ)^3575 := by
    have hnat : (1058845193 : ℕ)^4599*100000000000000^3575 ≤ 33114784831253^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058845193 2500000000 33114784831253 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3759600463/10000000000 : ℝ)^4599 ≤ (28408481135717/100000000000000 : ℝ)^3575 := by
    have hnat : (3759600463 : ℕ)^4599*100000000000000^3575 ≤ 28408481135717^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3759600463 10000000000 28408481135717 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190377999/400000000 : ℝ)^4599 ≤ (38476734013621/100000000000000 : ℝ)^3575 := by
    have hnat : (190377999 : ℕ)^4599*100000000000000^3575 ≤ 38476734013621^3575*400000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190377999 400000000 38476734013621 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058845193/2500000000 : ℝ), (3759600463/10000000000 : ℝ), (190377999/400000000 : ℝ)] ![(33114784831253/100000000000000 : ℝ), (28408481135717/100000000000000 : ℝ), (38476734013621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058845193/2500000000 : ℝ)|^4599 ≤ (33114784831253/100000000000000 : ℝ)^3575
        have hw : |(1058845193/2500000000 : ℝ)|=(1058845193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3759600463/10000000000 : ℝ)|^4599 ≤ (28408481135717/100000000000000 : ℝ)^3575
        have hw : |(3759600463/10000000000 : ℝ)|=(3759600463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(190377999/400000000 : ℝ)|^4599 ≤ (38476734013621/100000000000000 : ℝ)^3575
        have hw : |(190377999/400000000 : ℝ)|=(190377999/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s1_4 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-223616331/1250000000 : ℝ)*x 0 + (5121338221/10000000000 : ℝ)*x 1 + (1385323769/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223616331/1250000000 : ℝ)^4599 ≤ (437090319191/4000000000000 : ℝ)^3575 := by
    have hnat : (223616331 : ℕ)^4599*4000000000000^3575 ≤ 437090319191^3575*1250000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223616331 1250000000 437090319191 4000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5121338221/10000000000 : ℝ)^4599 ≤ (42280598444681/100000000000000 : ℝ)^3575 := by
    have hnat : (5121338221 : ℕ)^4599*100000000000000^3575 ≤ 42280598444681^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5121338221 10000000000 42280598444681 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1385323769/2500000000 : ℝ)^4599 ≤ (23396071782103/50000000000000 : ℝ)^3575 := by
    have hnat : (1385323769 : ℕ)^4599*50000000000000^3575 ≤ 23396071782103^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385323769 2500000000 23396071782103 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-223616331/1250000000 : ℝ), (5121338221/10000000000 : ℝ), (1385323769/2500000000 : ℝ)] ![(437090319191/4000000000000 : ℝ), (42280598444681/100000000000000 : ℝ), (23396071782103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-223616331/1250000000 : ℝ)|^4599 ≤ (437090319191/4000000000000 : ℝ)^3575
        have hw : |(-223616331/1250000000 : ℝ)|=(223616331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5121338221/10000000000 : ℝ)|^4599 ≤ (42280598444681/100000000000000 : ℝ)^3575
        have hw : |(5121338221/10000000000 : ℝ)|=(5121338221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1385323769/2500000000 : ℝ)|^4599 ≤ (23396071782103/50000000000000 : ℝ)^3575
        have hw : |(1385323769/2500000000 : ℝ)|=(1385323769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s1_5 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526616539/1000000000 : ℝ)*x 0 + (-794556533/5000000000 : ℝ)*x 1 + (138532371/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526616539/1000000000 : ℝ)^4599 ≤ (21912461882341/50000000000000 : ℝ)^3575 := by
    have hnat : (526616539 : ℕ)^4599*50000000000000^3575 ≤ 21912461882341^3575*1000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526616539 1000000000 21912461882341 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (794556533/5000000000 : ℝ)^4599 ≤ (9382935230383/100000000000000 : ℝ)^3575 := by
    have hnat : (794556533 : ℕ)^4599*100000000000000^3575 ≤ 9382935230383^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      794556533 5000000000 9382935230383 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138532371/250000000 : ℝ)^4599 ≤ (23396070500271/50000000000000 : ℝ)^3575 := by
    have hnat : (138532371 : ℕ)^4599*50000000000000^3575 ≤ 23396070500271^3575*250000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138532371 250000000 23396070500271 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526616539/1000000000 : ℝ), (-794556533/5000000000 : ℝ), (138532371/250000000 : ℝ)] ![(21912461882341/50000000000000 : ℝ), (9382935230383/100000000000000 : ℝ), (23396070500271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526616539/1000000000 : ℝ)|^4599 ≤ (21912461882341/50000000000000 : ℝ)^3575
        have hw : |(526616539/1000000000 : ℝ)|=(526616539/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-794556533/5000000000 : ℝ)|^4599 ≤ (9382935230383/100000000000000 : ℝ)^3575
        have hw : |(-794556533/5000000000 : ℝ)|=(794556533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(138532371/250000000 : ℝ)|^4599 ≤ (23396070500271/50000000000000 : ℝ)^3575
        have hw : |(138532371/250000000 : ℝ)|=(138532371/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s1_6 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266166991/10000000000 : ℝ)*x 0 + (1385323647/2500000000 : ℝ)*x 1 + (-12414931/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266166991/10000000000 : ℝ)^4599 ≤ (10956235226117/25000000000000 : ℝ)^3575 := by
    have hnat : (5266166991 : ℕ)^4599*25000000000000^3575 ≤ 10956235226117^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266166991 10000000000 10956235226117 25000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1385323647/2500000000 : ℝ)^4599 ≤ (46792138263071/100000000000000 : ℝ)^3575 := by
    have hnat : (1385323647 : ℕ)^4599*100000000000000^3575 ≤ 46792138263071^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385323647 2500000000 46792138263071 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12414931/78125000 : ℝ)^4599 ≤ (9382920813631/100000000000000 : ℝ)^3575 := by
    have hnat : (12414931 : ℕ)^4599*100000000000000^3575 ≤ 9382920813631^3575*78125000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12414931 78125000 9382920813631 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266166991/10000000000 : ℝ), (1385323647/2500000000 : ℝ), (-12414931/78125000 : ℝ)] ![(10956235226117/25000000000000 : ℝ), (46792138263071/100000000000000 : ℝ), (9382920813631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266166991/10000000000 : ℝ)|^4599 ≤ (10956235226117/25000000000000 : ℝ)^3575
        have hw : |(5266166991/10000000000 : ℝ)|=(5266166991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1385323647/2500000000 : ℝ)|^4599 ≤ (46792138263071/100000000000000 : ℝ)^3575
        have hw : |(1385323647/2500000000 : ℝ)|=(1385323647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12414931/78125000 : ℝ)|^4599 ≤ (9382920813631/100000000000000 : ℝ)^3575
        have hw : |(-12414931/78125000 : ℝ)|=(12414931/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s1_7 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4235933911/10000000000 : ℝ)*x 0 + (2374430923/5000000000 : ℝ)*x 1 + (3770348129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4235933911/10000000000 : ℝ)^4599 ≤ (16560174237051/50000000000000 : ℝ)^3575 := by
    have hnat : (4235933911 : ℕ)^4599*50000000000000^3575 ≤ 16560174237051^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235933911 10000000000 16560174237051 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2374430923/5000000000 : ℝ)^4599 ≤ (7673330745131/20000000000000 : ℝ)^3575 := by
    have hnat : (2374430923 : ℕ)^4599*20000000000000^3575 ≤ 7673330745131^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2374430923 5000000000 7673330745131 20000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3770348129/10000000000 : ℝ)^4599 ≤ (1782062361831/6250000000000 : ℝ)^3575 := by
    have hnat : (3770348129 : ℕ)^4599*6250000000000^3575 ≤ 1782062361831^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3770348129 10000000000 1782062361831 6250000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4235933911/10000000000 : ℝ), (2374430923/5000000000 : ℝ), (3770348129/10000000000 : ℝ)] ![(16560174237051/50000000000000 : ℝ), (7673330745131/20000000000000 : ℝ), (1782062361831/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4235933911/10000000000 : ℝ)|^4599 ≤ (16560174237051/50000000000000 : ℝ)^3575
        have hw : |(4235933911/10000000000 : ℝ)|=(4235933911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2374430923/5000000000 : ℝ)|^4599 ≤ (7673330745131/20000000000000 : ℝ)^3575
        have hw : |(2374430923/5000000000 : ℝ)|=(2374430923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3770348129/10000000000 : ℝ)|^4599 ≤ (1782062361831/6250000000000 : ℝ)^3575
        have hw : |(3770348129/10000000000 : ℝ)|=(3770348129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1551_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2601593/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (829/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (8849/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17933/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24989/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (829/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24989/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (829/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24989/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (829/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24989/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (829/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24989/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (829/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24989/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (829/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (829/25000 : ℝ) ^ (4597/1024 : ℝ) ≤ (1141897675743/5000000000000000000 : ℝ) := by
    have hpowers : (829/25000 : ℝ)^4597 ≤ (1141897675743/5000000000000000000 : ℝ)^1024 := by
      have hnat : (829 : ℕ)^4597*5000000000000000000^1024 ≤ 1141897675743^1024*25000^4597 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        829 25000 1141897675743 5000000000000000000 4597 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (829/25000 : ℝ)) (X := (1141897675743/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24989/100000 : ℝ) ^ (4597/1024 : ℝ) ≤ (98925771413377451/50000000000000000000 : ℝ) := by
    have hpowers : (24989/100000 : ℝ)^4597 ≤ (98925771413377451/50000000000000000000 : ℝ)^1024 := by
      have hnat : (24989 : ℕ)^4597*50000000000000000000^1024 ≤ 98925771413377451^1024*100000^4597 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24989 100000 98925771413377451 50000000000000000000 4597 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24989/100000 : ℝ)) (X := (98925771413377451/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500001141897675743/2500000000000000000 : ℝ) ≤ (5000000508724391/5000000000000000 : ℝ) ^ (4597/1024 : ℝ) := by
    have hpowers : (2500001141897675743/2500000000000000000 : ℝ)^1024 ≤ (5000000508724391/5000000000000000 : ℝ)^4597 := by
      have hnat : (2500001141897675743 : ℕ)^1024*5000000000000000^4597 ≤ 5000000508724391^4597*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500001141897675743 2500000000000000000 5000000508724391 5000000000000000 1024 4597 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000508724391/5000000000000000 : ℝ)) (X := (2500001141897675743/2500000000000000000 : ℝ)) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50098937190390134881/50000000000000000000 : ℝ) ≤ (10004404344875203/10000000000000000 : ℝ) ^ (4597/1024 : ℝ) := by
    have hpowers : (50098937190390134881/50000000000000000000 : ℝ)^1024 ≤ (10004404344875203/10000000000000000 : ℝ)^4597 := by
      have hnat : (50098937190390134881 : ℕ)^1024*10000000000000000^4597 ≤ 10004404344875203^4597*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50098937190390134881 50000000000000000000 10004404344875203 10000000000000000 1024 4597 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004404344875203/10000000000000000 : ℝ)) (X := (50098937190390134881/50000000000000000000 : ℝ)) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25098925771413377451/25000000000000000000 : ℝ) ≤ (1251100959037703/1250000000000000 : ℝ) ^ (4597/1024 : ℝ) := by
    have hpowers : (25098925771413377451/25000000000000000000 : ℝ)^1024 ≤ (1251100959037703/1250000000000000 : ℝ)^4597 := by
      have hnat : (25098925771413377451 : ℕ)^1024*1250000000000000^4597 ≤ 1251100959037703^4597*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25098925771413377451 25000000000000000000 1251100959037703 1250000000000000 1024 4597 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251100959037703/1250000000000000 : ℝ)) (X := (25098925771413377451/25000000000000000000 : ℝ)) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1141897675743/5000000000000000000 : ℝ) ≤ ((108350409591837714107/108365000000000000000 : ℝ)+2*(4403327426421/2167300000000000 : ℝ)*(829/25000 : ℝ))^(4597/1024 : ℝ) := by
    rw [show (108350409591837714107/108365000000000000000 : ℝ)+2*(4403327426421/2167300000000000 : ℝ)*(829/25000 : ℝ)=(5000000508724391/5000000000000000 : ℝ) by norm_num, show 1+2*(1141897675743/5000000000000000000 : ℝ)=(2500001141897675743/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(98925771413377451/50000000000000000000 : ℝ)+(1141897675743/5000000000000000000 : ℝ) ≤ ((108350409591837714107/108365000000000000000 : ℝ)+(4403327426421/2167300000000000 : ℝ)*((24989/100000 : ℝ)+(829/25000 : ℝ)))^(4597/1024 : ℝ) := by
    rw [show (108350409591837714107/108365000000000000000 : ℝ)+(4403327426421/2167300000000000 : ℝ)*((24989/100000 : ℝ)+(829/25000 : ℝ))=(10004404344875203/10000000000000000 : ℝ) by norm_num, show 1+(98925771413377451/50000000000000000000 : ℝ)+(1141897675743/5000000000000000000 : ℝ)=(50098937190390134881/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(98925771413377451/50000000000000000000 : ℝ) ≤ ((108350409591837714107/108365000000000000000 : ℝ)+2*(4403327426421/2167300000000000 : ℝ)*(24989/100000 : ℝ))^(4597/1024 : ℝ) := by
    rw [show (108350409591837714107/108365000000000000000 : ℝ)+2*(4403327426421/2167300000000000 : ℝ)*(24989/100000 : ℝ)=(1251100959037703/1250000000000000 : ℝ) by norm_num, show 1+2*(98925771413377451/50000000000000000000 : ℝ)=(25098925771413377451/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (108350409591837714107/108365000000000000000 : ℝ)*(X 1 0+X 2 0)+(4403327426421/2167300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4597/1024 : ℝ)) (lo := (829/25000 : ℝ)) (hi := (24989/100000 : ℝ)) (c := (108350409591837714107/108365000000000000000 : ℝ)) (alpha := (4403327426421/2167300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (108350409591837714107/108365000000000000000 : ℝ)*(X 0 1+X 2 1)+(4403327426421/2167300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4597/1024 : ℝ)) (lo := (829/25000 : ℝ)) (hi := (24989/100000 : ℝ)) (c := (108350409591837714107/108365000000000000000 : ℝ)) (alpha := (4403327426421/2167300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (108350409591837714107/108365000000000000000 : ℝ)*(X 0 2+X 1 2)+(4403327426421/2167300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4597/1024 : ℝ)) (lo := (829/25000 : ℝ)) (hi := (24989/100000 : ℝ)) (c := (108350409591837714107/108365000000000000000 : ℝ)) (alpha := (4403327426421/2167300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1788692373/10000000000 : ℝ)*X 0 0+(173309621/312500000 : ℝ)*X 0 1+(255839763/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5379690659/10000000000 : ℝ)*X 1 0+(-2013611099/10000000000 : ℝ)*X 1 1+(319799691/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((537969051/1000000000 : ℝ)*X 2 0+(1023358843/2000000000 : ℝ)*X 2 1+(-1006806197/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1058845193/2500000000 : ℝ)*X 0 0+(3759600463/10000000000 : ℝ)*X 0 1+(190377999/400000000 : ℝ)*X 0 2+(1058845193/2500000000 : ℝ)*X 1 0+(3759600463/10000000000 : ℝ)*X 1 1+(190377999/400000000 : ℝ)*X 1 2+(1058845193/2500000000 : ℝ)*X 2 0+(3759600463/10000000000 : ℝ)*X 2 1+(190377999/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-223616331/1250000000 : ℝ)*X 0 0+(5121338221/10000000000 : ℝ)*X 0 1+(1385323769/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((526616539/1000000000 : ℝ)*X 1 0+(-794556533/5000000000 : ℝ)*X 1 1+(138532371/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5266166991/10000000000 : ℝ)*X 2 0+(1385323647/2500000000 : ℝ)*X 2 1+(-12414931/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4235933911/10000000000 : ℝ)*X 0 0+(2374430923/5000000000 : ℝ)*X 0 1+(3770348129/10000000000 : ℝ)*X 0 2+(4235933911/10000000000 : ℝ)*X 1 0+(2374430923/5000000000 : ℝ)*X 1 1+(3770348129/10000000000 : ℝ)*X 1 2+(4235933911/10000000000 : ℝ)*X 2 0+(2374430923/5000000000 : ℝ)*X 2 1+(3770348129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2643882502258280907311882619/216730000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (277016873/100000000000000 : ℝ)*(base1) + (104733543/6250000000000 : ℝ)*(base19) + (303485249/20000000000000 : ℝ)*(base23) + (61248057/20000000000000 : ℝ)*(upper3) + (66611411140139/4000000000000 : ℝ)*(major0) + (66611411140139/4000000000000 : ℝ)*(major1) + (66611411140139/4000000000000 : ℝ)*(major2) + (72825100342529/3125000000000 : ℝ)*(sp0) + (2330408861792419/100000000000000 : ℝ)*(sp1) + (29130057208801/1250000000000 : ℝ)*(sp2) + (100015406084877/10000000000000 : ℝ)*(sp3) + (7603585053/100000000000000 : ℝ)*(sp4) + (4443398781/100000000000000 : ℝ)*(sp6) + (2637489951/50000000000000 : ℝ)*(sp7) + (200031922569109/20000000000000 : ℝ)*(f.failure) + (1165205268764553/50000000000000 : ℝ)*(f.sum) + (24596243154993/21673000000000000000000000000 : ℝ)*base65 + (2517302084247069127/433460000000000000000000000000000 : ℝ)*base68 + (3778388451939169127/433460000000000000000000000000000 : ℝ)*base70 + (410030118308989127/433460000000000000000000000000000 : ℝ)*base72 + (5853454226419/10836500000000000000000000000 : ℝ)*base74 + (2159753518358929127/433460000000000000000000000000000 : ℝ)*base76 + (1274046658102010873/433460000000000000000000000000000 : ℝ)*base77 + (968081072776390873/433460000000000000000000000000000 : ℝ)*base79 + (28320326772629/4334600000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (53137/31250000000000000000 : ℝ)*base89 + (53137/31250000000000000000 : ℝ)*base91 + (53137/31250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3359250429682130498127869367/2709125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (80208247/100000000000000 : ℝ)*(base19) + (374163791/50000000000000 : ℝ)*(base23) + (53097641/50000000000000 : ℝ)*(upper4) + (330803871/100000000000000 : ℝ)*(upper5) + (1701583606562727/100000000000000 : ℝ)*(major0) + (1701583606562727/100000000000000 : ℝ)*(major1) + (1701583606562727/100000000000000 : ℝ)*(major2) + (481366359/100000000000000 : ℝ)*(sp0) + (33828607/500000000000 : ℝ)*(sp2) + (132869507/10000000000000 : ℝ)*(sp3) + (297650816941419/12500000000000 : ℝ)*(sp4) + (297650867086183/12500000000000 : ℝ)*(sp5) + (238119950284873/10000000000000 : ℝ)*(sp6) + (15968106659377/1562500000000 : ℝ)*(sp7) + (1021960154895197/100000000000000 : ℝ)*(f.failure) + (2381207016897711/100000000000000 : ℝ)*(f.sum) + (158277325127679/54182500000000000000000000000 : ℝ)*base66 + (53056073542345360211/10836500000000000000000000000000000 : ℝ)*base68 + (13717934818679360211/10836500000000000000000000000000000 : ℝ)*base70 + (4609612730599639789/10836500000000000000000000000000000 : ℝ)*base71 + (757948965313943/108365000000000000000000000000 : ℝ)*base74 + (9488282723461360211/10836500000000000000000000000000000 : ℝ)*base76 + (47207652853555360211/10836500000000000000000000000000000 : ℝ)*base78 + (60835503698445360211/10836500000000000000000000000000000 : ℝ)*base80 + (224732312731463/108365000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (688679/156250000000000000000 : ℝ)*base90 + (688679/156250000000000000000 : ℝ)*base92 + (688679/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1551_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2601593/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (829/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8849/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17933/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1551_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1551_s2_0 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1809074841/10000000000 : ℝ)*x 0 + (5446417213/10000000000 : ℝ)*x 1 + (650378649/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1809074841/10000000000 : ℝ)^4599 ≤ (11085803101017/100000000000000 : ℝ)^3575 := by
    have hnat : (1809074841 : ℕ)^4599*100000000000000^3575 ≤ 11085803101017^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1809074841 10000000000 11085803101017 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5446417213/10000000000 : ℝ)^4599 ≤ (45764024819961/100000000000000 : ℝ)^3575 := by
    have hnat : (5446417213 : ℕ)^4599*100000000000000^3575 ≤ 45764024819961^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446417213 10000000000 45764024819961 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (650378649/1250000000 : ℝ)^4599 ≤ (539377150853/1250000000000 : ℝ)^3575 := by
    have hnat : (650378649 : ℕ)^4599*1250000000000^3575 ≤ 539377150853^3575*1250000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650378649 1250000000 539377150853 1250000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1809074841/10000000000 : ℝ), (5446417213/10000000000 : ℝ), (650378649/1250000000 : ℝ)] ![(11085803101017/100000000000000 : ℝ), (45764024819961/100000000000000 : ℝ), (539377150853/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1809074841/10000000000 : ℝ)|^4599 ≤ (11085803101017/100000000000000 : ℝ)^3575
        have hw : |(-1809074841/10000000000 : ℝ)|=(1809074841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5446417213/10000000000 : ℝ)|^4599 ≤ (45764024819961/100000000000000 : ℝ)^3575
        have hw : |(5446417213/10000000000 : ℝ)|=(5446417213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(650378649/1250000000 : ℝ)|^4599 ≤ (539377150853/1250000000000 : ℝ)^3575
        have hw : |(650378649/1250000000 : ℝ)|=(650378649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s2_1 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53541221/100000000 : ℝ)*x 0 + (-1934104129/10000000000 : ℝ)*x 1 + (5203029297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53541221/100000000 : ℝ)^4599 ≤ (44768803225271/100000000000000 : ℝ)^3575 := by
    have hnat : (53541221 : ℕ)^4599*100000000000000^3575 ≤ 44768803225271^3575*100000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53541221 100000000 44768803225271 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1934104129/10000000000 : ℝ)^4599 ≤ (1510127945401/12500000000000 : ℝ)^3575 := by
    have hnat : (1934104129 : ℕ)^4599*12500000000000^3575 ≤ 1510127945401^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934104129 10000000000 1510127945401 12500000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5203029297/10000000000 : ℝ)^4599 ≤ (43150173188459/100000000000000 : ℝ)^3575 := by
    have hnat : (5203029297 : ℕ)^4599*100000000000000^3575 ≤ 43150173188459^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203029297 10000000000 43150173188459 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53541221/100000000 : ℝ), (-1934104129/10000000000 : ℝ), (5203029297/10000000000 : ℝ)] ![(44768803225271/100000000000000 : ℝ), (1510127945401/12500000000000 : ℝ), (43150173188459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53541221/100000000 : ℝ)|^4599 ≤ (44768803225271/100000000000000 : ℝ)^3575
        have hw : |(53541221/100000000 : ℝ)|=(53541221/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1934104129/10000000000 : ℝ)|^4599 ≤ (1510127945401/12500000000000 : ℝ)^3575
        have hw : |(-1934104129/10000000000 : ℝ)|=(1934104129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5203029297/10000000000 : ℝ)|^4599 ≤ (43150173188459/100000000000000 : ℝ)^3575
        have hw : |(5203029297/10000000000 : ℝ)|=(5203029297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s2_2 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677061387/5000000000 : ℝ)*x 0 + (5203028657/10000000000 : ℝ)*x 1 + (-1934104077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677061387/5000000000 : ℝ)^4599 ≤ (44768810475213/100000000000000 : ℝ)^3575 := by
    have hnat : (2677061387 : ℕ)^4599*100000000000000^3575 ≤ 44768810475213^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677061387 5000000000 44768810475213 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5203028657/10000000000 : ℝ)^4599 ≤ (21575083180229/50000000000000 : ℝ)^3575 := by
    have hnat : (5203028657 : ℕ)^4599*50000000000000^3575 ≤ 21575083180229^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203028657 10000000000 21575083180229 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1934104077/10000000000 : ℝ)^4599 ≤ (3020255786341/25000000000000 : ℝ)^3575 := by
    have hnat : (1934104077 : ℕ)^4599*25000000000000^3575 ≤ 3020255786341^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934104077 10000000000 3020255786341 25000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677061387/5000000000 : ℝ), (5203028657/10000000000 : ℝ), (-1934104077/10000000000 : ℝ)] ![(44768810475213/100000000000000 : ℝ), (21575083180229/50000000000000 : ℝ), (3020255786341/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677061387/5000000000 : ℝ)|^4599 ≤ (44768810475213/100000000000000 : ℝ)^3575
        have hw : |(2677061387/5000000000 : ℝ)|=(2677061387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5203028657/10000000000 : ℝ)|^4599 ≤ (21575083180229/50000000000000 : ℝ)^3575
        have hw : |(5203028657/10000000000 : ℝ)|=(5203028657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1934104077/10000000000 : ℝ)|^4599 ≤ (3020255786341/25000000000000 : ℝ)^3575
        have hw : |(-1934104077/10000000000 : ℝ)|=(1934104077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s2_3 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2125053759/5000000000 : ℝ)*x 0 + (1987163371/5000000000 : ℝ)*x 1 + (4541432781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125053759/5000000000 : ℝ)^4599 ≤ (8315745480019/25000000000000 : ℝ)^3575 := by
    have hnat : (2125053759 : ℕ)^4599*25000000000000^3575 ≤ 8315745480019^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125053759 5000000000 8315745480019 25000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1987163371/5000000000 : ℝ)^4599 ≤ (30512599161913/100000000000000 : ℝ)^3575 := by
    have hnat : (1987163371 : ℕ)^4599*100000000000000^3575 ≤ 30512599161913^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987163371 5000000000 30512599161913 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4541432781/10000000000 : ℝ)^4599 ≤ (3622441890689/10000000000000 : ℝ)^3575 := by
    have hnat : (4541432781 : ℕ)^4599*10000000000000^3575 ≤ 3622441890689^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4541432781 10000000000 3622441890689 10000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2125053759/5000000000 : ℝ), (1987163371/5000000000 : ℝ), (4541432781/10000000000 : ℝ)] ![(8315745480019/25000000000000 : ℝ), (30512599161913/100000000000000 : ℝ), (3622441890689/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2125053759/5000000000 : ℝ)|^4599 ≤ (8315745480019/25000000000000 : ℝ)^3575
        have hw : |(2125053759/5000000000 : ℝ)|=(2125053759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1987163371/5000000000 : ℝ)|^4599 ≤ (30512599161913/100000000000000 : ℝ)^3575
        have hw : |(1987163371/5000000000 : ℝ)|=(1987163371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4541432781/10000000000 : ℝ)|^4599 ≤ (3622441890689/10000000000000 : ℝ)^3575
        have hw : |(4541432781/10000000000 : ℝ)|=(4541432781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s2_4 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1809117267/10000000000 : ℝ)*x 0 + (2602249371/5000000000 : ℝ)*x 1 + (1361233931/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1809117267/10000000000 : ℝ)^4599 ≤ (2771534387819/25000000000000 : ℝ)^3575 := by
    have hnat : (1809117267 : ℕ)^4599*25000000000000^3575 ≤ 2771534387819^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1809117267 10000000000 2771534387819 25000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2602249371/5000000000 : ℝ)^4599 ≤ (8633170193471/20000000000000 : ℝ)^3575 := by
    have hnat : (2602249371 : ℕ)^4599*20000000000000^3575 ≤ 8633170193471^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602249371 5000000000 8633170193471 20000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1361233931/2500000000 : ℝ)^4599 ≤ (45748011470537/100000000000000 : ℝ)^3575 := by
    have hnat : (1361233931 : ℕ)^4599*100000000000000^3575 ≤ 45748011470537^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361233931 2500000000 45748011470537 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1809117267/10000000000 : ℝ), (2602249371/5000000000 : ℝ), (1361233931/2500000000 : ℝ)] ![(2771534387819/25000000000000 : ℝ), (8633170193471/20000000000000 : ℝ), (45748011470537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1809117267/10000000000 : ℝ)|^4599 ≤ (2771534387819/25000000000000 : ℝ)^3575
        have hw : |(-1809117267/10000000000 : ℝ)|=(1809117267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2602249371/5000000000 : ℝ)|^4599 ≤ (8633170193471/20000000000000 : ℝ)^3575
        have hw : |(2602249371/5000000000 : ℝ)|=(2602249371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1361233931/2500000000 : ℝ)|^4599 ≤ (45748011470537/100000000000000 : ℝ)^3575
        have hw : |(1361233931/2500000000 : ℝ)|=(1361233931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s2_5 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644936069/5000000000 : ℝ)*x 0 + (-846098747/5000000000 : ℝ)*x 1 + (1063464/1953125 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644936069/5000000000 : ℝ)^4599 ≤ (44078883947301/100000000000000 : ℝ)^3575 := by
    have hnat : (2644936069 : ℕ)^4599*100000000000000^3575 ≤ 44078883947301^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644936069 5000000000 44078883947301 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846098747/5000000000 : ℝ)^4599 ≤ (5086552528323/50000000000000 : ℝ)^3575 := by
    have hnat : (846098747 : ℕ)^4599*50000000000000^3575 ≤ 5086552528323^3575*5000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846098747 5000000000 5086552528323 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063464/1953125 : ℝ)^4599 ≤ (22874005497481/50000000000000 : ℝ)^3575 := by
    have hnat : (1063464 : ℕ)^4599*50000000000000^3575 ≤ 22874005497481^3575*1953125^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063464 1953125 22874005497481 50000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644936069/5000000000 : ℝ), (-846098747/5000000000 : ℝ), (1063464/1953125 : ℝ)] ![(44078883947301/100000000000000 : ℝ), (5086552528323/50000000000000 : ℝ), (22874005497481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644936069/5000000000 : ℝ)|^4599 ≤ (44078883947301/100000000000000 : ℝ)^3575
        have hw : |(2644936069/5000000000 : ℝ)|=(2644936069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-846098747/5000000000 : ℝ)|^4599 ≤ (5086552528323/50000000000000 : ℝ)^3575
        have hw : |(-846098747/5000000000 : ℝ)|=(846098747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1063464/1953125 : ℝ)|^4599 ≤ (22874005497481/50000000000000 : ℝ)^3575
        have hw : |(1063464/1953125 : ℝ)|=(1063464/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s2_6 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661233929/1250000000 : ℝ)*x 0 + (5444936087/10000000000 : ℝ)*x 1 + (-1692197901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661233929/1250000000 : ℝ)^4599 ≤ (8815775275873/20000000000000 : ℝ)^3575 := by
    have hnat : (661233929 : ℕ)^4599*20000000000000^3575 ≤ 8815775275873^3575*1250000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661233929 1250000000 8815775275873 20000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5444936087/10000000000 : ℝ)^4599 ≤ (9149603078807/20000000000000 : ℝ)^3575 := by
    have hnat : (5444936087 : ℕ)^4599*20000000000000^3575 ≤ 9149603078807^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444936087 10000000000 9149603078807 20000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1692197901/10000000000 : ℝ)^4599 ≤ (254327705107/2500000000000 : ℝ)^3575 := by
    have hnat : (1692197901 : ℕ)^4599*2500000000000^3575 ≤ 254327705107^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1692197901 10000000000 254327705107 2500000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661233929/1250000000 : ℝ), (5444936087/10000000000 : ℝ), (-1692197901/10000000000 : ℝ)] ![(8815775275873/20000000000000 : ℝ), (9149603078807/20000000000000 : ℝ), (254327705107/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661233929/1250000000 : ℝ)|^4599 ≤ (8815775275873/20000000000000 : ℝ)^3575
        have hw : |(661233929/1250000000 : ℝ)|=(661233929/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5444936087/10000000000 : ℝ)|^4599 ≤ (9149603078807/20000000000000 : ℝ)^3575
        have hw : |(5444936087/10000000000 : ℝ)|=(5444936087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1692197901/10000000000 : ℝ)|^4599 ≤ (254327705107/2500000000000 : ℝ)^3575
        have hw : |(-1692197901/10000000000 : ℝ)|=(1692197901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1551_s2_7 (p : ℝ) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4250206849/10000000000 : ℝ)*x 0 + (1134501897/2500000000 : ℝ)*x 1 + (3977783257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4250206849/10000000000 : ℝ)^4599 ≤ (33263982000411/100000000000000 : ℝ)^3575 := by
    have hnat : (4250206849 : ℕ)^4599*100000000000000^3575 ≤ 33263982000411^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250206849 10000000000 33263982000411 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134501897/2500000000 : ℝ)^4599 ≤ (4523659536971/12500000000000 : ℝ)^3575 := by
    have hnat : (1134501897 : ℕ)^4599*12500000000000^3575 ≤ 4523659536971^3575*2500000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134501897 2500000000 4523659536971 12500000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3977783257/10000000000 : ℝ)^4599 ≤ (30546741678113/100000000000000 : ℝ)^3575 := by
    have hnat : (3977783257 : ℕ)^4599*100000000000000^3575 ≤ 30546741678113^3575*10000000000^4599 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3977783257 10000000000 30546741678113 100000000000000 4599 3575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4599/1024 : ℝ)) 4599 3575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4250206849/10000000000 : ℝ), (1134501897/2500000000 : ℝ), (3977783257/10000000000 : ℝ)] ![(33263982000411/100000000000000 : ℝ), (4523659536971/12500000000000 : ℝ), (30546741678113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4250206849/10000000000 : ℝ)|^4599 ≤ (33263982000411/100000000000000 : ℝ)^3575
        have hw : |(4250206849/10000000000 : ℝ)|=(4250206849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1134501897/2500000000 : ℝ)|^4599 ≤ (4523659536971/12500000000000 : ℝ)^3575
        have hw : |(1134501897/2500000000 : ℝ)|=(1134501897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3977783257/10000000000 : ℝ)|^4599 ≤ (30546741678113/100000000000000 : ℝ)^3575
        have hw : |(3977783257/10000000000 : ℝ)|=(3977783257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1551_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2601593/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17933/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8849/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2677/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3173/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17933/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8849/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17933/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8849/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17933/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8849/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17933/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8849/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17933/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8849/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17933/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8849/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8849/100000 : ℝ) ^ (4597/1024 : ℝ) ≤ (468033076863467/25000000000000000000 : ℝ) := by
    have hpowers : (8849/100000 : ℝ)^4597 ≤ (468033076863467/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8849 : ℕ)^4597*25000000000000000000^1024 ≤ 468033076863467^1024*100000^4597 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8849 100000 468033076863467 25000000000000000000 4597 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8849/100000 : ℝ)) (X := (468033076863467/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17933/100000 : ℝ) ^ (4597/1024 : ℝ) ≤ (22306204142980599/50000000000000000000 : ℝ) := by
    have hpowers : (17933/100000 : ℝ)^4597 ≤ (22306204142980599/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17933 : ℕ)^4597*50000000000000000000^1024 ≤ 22306204142980599^1024*100000^4597 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17933 100000 22306204142980599 50000000000000000000 4597 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17933/100000 : ℝ)) (X := (22306204142980599/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500468033076863467/12500000000000000000 : ℝ) ≤ (5000041701883579/5000000000000000 : ℝ) ^ (4597/1024 : ℝ) := by
    have hpowers : (12500468033076863467/12500000000000000000 : ℝ)^1024 ≤ (5000041701883579/5000000000000000 : ℝ)^4597 := by
      have hnat : (12500468033076863467 : ℕ)^1024*5000000000000000^4597 ≤ 5000041701883579^4597*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500468033076863467 12500000000000000000 5000041701883579 5000000000000000 1024 4597 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000041701883579/5000000000000000 : ℝ)) (X := (12500468033076863467/12500000000000000000 : ℝ)) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023242270296707533/50000000000000000000 : ℝ) ≤ (5000517637295869/5000000000000000 : ℝ) ^ (4597/1024 : ℝ) := by
    have hpowers : (50023242270296707533/50000000000000000000 : ℝ)^1024 ≤ (5000517637295869/5000000000000000 : ℝ)^4597 := by
      have hnat : (50023242270296707533 : ℕ)^1024*5000000000000000^4597 ≤ 5000517637295869^4597*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023242270296707533 50000000000000000000 5000517637295869 5000000000000000 1024 4597 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000517637295869/5000000000000000 : ℝ)) (X := (50023242270296707533/50000000000000000000 : ℝ)) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25022306204142980599/25000000000000000000 : ℝ) ≤ (5000993572708159/5000000000000000 : ℝ) ^ (4597/1024 : ℝ) := by
    have hpowers : (25022306204142980599/25000000000000000000 : ℝ)^1024 ≤ (5000993572708159/5000000000000000 : ℝ)^4597 := by
      have hnat : (25022306204142980599 : ℕ)^1024*5000000000000000^4597 ≤ 5000993572708159^4597*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25022306204142980599 25000000000000000000 5000993572708159 5000000000000000 1024 4597 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000993572708159/5000000000000000 : ℝ)) (X := (25022306204142980599/25000000000000000000 : ℝ)) (by norm_num) 4597 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(468033076863467/25000000000000000000 : ℝ) ≤ ((946082410728827567/946250000000000000 : ℝ)+2*(15864513743/15140000000000 : ℝ)*(8849/100000 : ℝ))^(4597/1024 : ℝ) := by
    rw [show (946082410728827567/946250000000000000 : ℝ)+2*(15864513743/15140000000000 : ℝ)*(8849/100000 : ℝ)=(5000041701883579/5000000000000000 : ℝ) by norm_num, show 1+2*(468033076863467/25000000000000000000 : ℝ)=(12500468033076863467/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22306204142980599/50000000000000000000 : ℝ)+(468033076863467/25000000000000000000 : ℝ) ≤ ((946082410728827567/946250000000000000 : ℝ)+(15864513743/15140000000000 : ℝ)*((17933/100000 : ℝ)+(8849/100000 : ℝ)))^(4597/1024 : ℝ) := by
    rw [show (946082410728827567/946250000000000000 : ℝ)+(15864513743/15140000000000 : ℝ)*((17933/100000 : ℝ)+(8849/100000 : ℝ))=(5000517637295869/5000000000000000 : ℝ) by norm_num, show 1+(22306204142980599/50000000000000000000 : ℝ)+(468033076863467/25000000000000000000 : ℝ)=(50023242270296707533/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22306204142980599/50000000000000000000 : ℝ) ≤ ((946082410728827567/946250000000000000 : ℝ)+2*(15864513743/15140000000000 : ℝ)*(17933/100000 : ℝ))^(4597/1024 : ℝ) := by
    rw [show (946082410728827567/946250000000000000 : ℝ)+2*(15864513743/15140000000000 : ℝ)*(17933/100000 : ℝ)=(5000993572708159/5000000000000000 : ℝ) by norm_num, show 1+2*(22306204142980599/50000000000000000000 : ℝ)=(25022306204142980599/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (946082410728827567/946250000000000000 : ℝ)*(X 1 0+X 2 0)+(15864513743/15140000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4597/1024 : ℝ)) (lo := (8849/100000 : ℝ)) (hi := (17933/100000 : ℝ)) (c := (946082410728827567/946250000000000000 : ℝ)) (alpha := (15864513743/15140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (946082410728827567/946250000000000000 : ℝ)*(X 0 1+X 2 1)+(15864513743/15140000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4597/1024 : ℝ)) (lo := (8849/100000 : ℝ)) (hi := (17933/100000 : ℝ)) (c := (946082410728827567/946250000000000000 : ℝ)) (alpha := (15864513743/15140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (946082410728827567/946250000000000000 : ℝ)*(X 0 2+X 1 2)+(15864513743/15140000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4597/1024 : ℝ)) (lo := (8849/100000 : ℝ)) (hi := (17933/100000 : ℝ)) (c := (946082410728827567/946250000000000000 : ℝ)) (alpha := (15864513743/15140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1809074841/10000000000 : ℝ)*X 0 0+(5446417213/10000000000 : ℝ)*X 0 1+(650378649/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((53541221/100000000 : ℝ)*X 1 0+(-1934104129/10000000000 : ℝ)*X 1 1+(5203029297/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677061387/5000000000 : ℝ)*X 2 0+(5203028657/10000000000 : ℝ)*X 2 1+(-1934104077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2125053759/5000000000 : ℝ)*X 0 0+(1987163371/5000000000 : ℝ)*X 0 1+(4541432781/10000000000 : ℝ)*X 0 2+(2125053759/5000000000 : ℝ)*X 1 0+(1987163371/5000000000 : ℝ)*X 1 1+(4541432781/10000000000 : ℝ)*X 1 2+(2125053759/5000000000 : ℝ)*X 2 0+(1987163371/5000000000 : ℝ)*X 2 1+(4541432781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1809117267/10000000000 : ℝ)*X 0 0+(2602249371/5000000000 : ℝ)*X 0 1+(1361233931/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644936069/5000000000 : ℝ)*X 1 0+(-846098747/5000000000 : ℝ)*X 1 1+(1063464/1953125 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661233929/1250000000 : ℝ)*X 2 0+(5444936087/10000000000 : ℝ)*X 2 1+(-1692197901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4250206849/10000000000 : ℝ)*X 0 0+(1134501897/2500000000 : ℝ)*X 0 1+(3977783257/10000000000 : ℝ)*X 0 2+(4250206849/10000000000 : ℝ)*X 1 0+(1134501897/2500000000 : ℝ)*X 1 1+(3977783257/10000000000 : ℝ)*X 1 2+(4250206849/10000000000 : ℝ)*X 2 0+(1134501897/2500000000 : ℝ)*X 2 1+(3977783257/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1551_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36348803986420319918420613/23656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (657246423/50000000000000 : ℝ)*(base19) + (1373448039/100000000000000 : ℝ)*(base23) + (140473183/50000000000000 : ℝ)*(upper3) + (2453607/1000000000000 : ℝ)*(upper4) + (22133353/25000000000000 : ℝ)*(upper5) + (1468013907201763/50000000000000 : ℝ)*(major0) + (1468013907201763/50000000000000 : ℝ)*(major1) + (1468013907201763/50000000000000 : ℝ)*(major2) + (1027169986567527/25000000000000 : ℝ)*(sp0) + (410869486752371/10000000000000 : ℝ)*(sp1) + (1027173702142129/25000000000000 : ℝ)*(sp2) + (881673482233069/50000000000000 : ℝ)*(sp3) + (16235746447/100000000000000 : ℝ)*(sp4) + (1243110631/10000000000000 : ℝ)*(sp7) + (55104981111639/3125000000000 : ℝ)*(f.failure) + (1027174045504139/25000000000000 : ℝ)*(f.sum) + (2757999591411/757000000000000000000000000 : ℝ)*base66 + (36420469951088121/47312500000000000000000000000000 : ℝ)*base67 + (180067594530536879/47312500000000000000000000000000 : ℝ)*base70 + (403091474188911879/47312500000000000000000000000000 : ℝ)*base72 + (218795146179/189250000000000000000000000 : ℝ)*base73 + (106958734845661879/47312500000000000000000000000000 : ℝ)*base76 + (113065488856911879/47312500000000000000000000000000 : ℝ)*base78 + (145479362398713121/47312500000000000000000000000000 : ℝ)*base79 + (829679800597/378500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (291833/19531250000000000000 : ℝ)*base89 + (291833/19531250000000000000 : ℝ)*base91 + (291833/19531250000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (91735401333150999434227047/9462500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (597024357/100000000000000 : ℝ)*(base19) + (86335713/50000000000000 : ℝ)*(base23) + (285489/250000000000 : ℝ)*(upper2) + (11758259/20000000000000 : ℝ)*(lower3) + (594410938095147/20000000000000 : ℝ)*(major0) + (594410938095147/20000000000000 : ℝ)*(major1) + (594410938095147/20000000000000 : ℝ)*(major2) + (2166684721/20000000000000 : ℝ)*(sp0) + (23749155417/100000000000000 : ℝ)*(sp1) + (836937107/5000000000000 : ℝ)*(sp2) + (129971916220833/3125000000000 : ℝ)*(sp4) + (519885975788811/12500000000000 : ℝ)*(sp5) + (519886905134587/12500000000000 : ℝ)*(sp6) + (1784996905306993/100000000000000 : ℝ)*(sp7) + (1784996905306993/100000000000000 : ℝ)*(f.failure) + (2079556076245131/50000000000000 : ℝ)*(f.sum) + (274802783519/151400000000000000000000000 : ℝ)*base66 + (43783031847404849/18925000000000000000000000000000 : ℝ)*base67 + (119837122306704849/18925000000000000000000000000000 : ℝ)*base69 + (7529675682595151/18925000000000000000000000000000 : ℝ)*base72 + (244139029361/378500000000000000000000000 : ℝ)*base73 + (168166699239420151/18925000000000000000000000000000 : ℝ)*base76 + (34706846005495151/18925000000000000000000000000000 : ℝ)*base78 + (213217993418970151/18925000000000000000000000000000 : ℝ)*base80 + (42231610101/9462500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (97651/156250000000000000000 : ℝ)*base90 + (97651/156250000000000000000 : ℝ)*base92 + (97651/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1551_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2601593/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17933/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8849/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2677/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3173/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1551_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1551_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2601593/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2677/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3173/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1551_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1551_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1551_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4597/1024 : ℝ) ≤ p) (hpb : p ≤ (4599/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2601593/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2677/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3173/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1551_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

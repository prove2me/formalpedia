-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1588_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:36:17.411763+00:00
-- url     : https://prove2.me/submissions/b19143ac-356d-4aa1-ad9f-3b64db5041b3

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
theorem support_rectangle_w1588_s3_0 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-880556969/5000000000 : ℝ)*x 0 + (5424868639/10000000000 : ℝ)*x 1 + (104388257/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (880556969/5000000000 : ℝ)^4673 ≤ (5408871850941/50000000000000 : ℝ)^3649 := by
    have hnat : (880556969 : ℕ)^4673*50000000000000^3649 ≤ 5408871850941^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880556969 5000000000 5408871850941 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424868639/10000000000 : ℝ)^4673 ≤ (22846635496973/50000000000000 : ℝ)^3649 := by
    have hnat : (5424868639 : ℕ)^4673*50000000000000^3649 ≤ 22846635496973^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424868639 10000000000 22846635496973 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104388257/200000000 : ℝ)^4673 ≤ (21744492639601/50000000000000 : ℝ)^3649 := by
    have hnat : (104388257 : ℕ)^4673*50000000000000^3649 ≤ 21744492639601^3649*200000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104388257 200000000 21744492639601 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-880556969/5000000000 : ℝ), (5424868639/10000000000 : ℝ), (104388257/200000000 : ℝ)] ![(5408871850941/50000000000000 : ℝ), (22846635496973/50000000000000 : ℝ), (21744492639601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-880556969/5000000000 : ℝ)|^4673 ≤ (5408871850941/50000000000000 : ℝ)^3649
        have hw : |(-880556969/5000000000 : ℝ)|=(880556969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424868639/10000000000 : ℝ)|^4673 ≤ (22846635496973/50000000000000 : ℝ)^3649
        have hw : |(5424868639/10000000000 : ℝ)|=(5424868639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104388257/200000000 : ℝ)|^4673 ≤ (21744492639601/50000000000000 : ℝ)^3649
        have hw : |(104388257/200000000 : ℝ)|=(104388257/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s3_1 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668428867/1250000000 : ℝ)*x 0 + (-933109117/5000000000 : ℝ)*x 1 + (5219412993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668428867/1250000000 : ℝ)^4673 ≤ (44859659528369/100000000000000 : ℝ)^3649 := by
    have hnat : (668428867 : ℕ)^4673*100000000000000^3649 ≤ 44859659528369^3649*1250000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668428867 1250000000 44859659528369 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (933109117/5000000000 : ℝ)^4673 ≤ (2912838414443/25000000000000 : ℝ)^3649 := by
    have hnat : (933109117 : ℕ)^4673*25000000000000^3649 ≤ 2912838414443^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933109117 5000000000 2912838414443 25000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219412993/10000000000 : ℝ)^4673 ≤ (8697797361013/20000000000000 : ℝ)^3649 := by
    have hnat : (5219412993 : ℕ)^4673*20000000000000^3649 ≤ 8697797361013^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219412993 10000000000 8697797361013 20000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668428867/1250000000 : ℝ), (-933109117/5000000000 : ℝ), (5219412993/10000000000 : ℝ)] ![(44859659528369/100000000000000 : ℝ), (2912838414443/25000000000000 : ℝ), (8697797361013/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668428867/1250000000 : ℝ)|^4673 ≤ (44859659528369/100000000000000 : ℝ)^3649
        have hw : |(668428867/1250000000 : ℝ)|=(668428867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-933109117/5000000000 : ℝ)|^4673 ≤ (2912838414443/25000000000000 : ℝ)^3649
        have hw : |(-933109117/5000000000 : ℝ)|=(933109117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219412993/10000000000 : ℝ)|^4673 ≤ (8697797361013/20000000000000 : ℝ)^3649
        have hw : |(5219412993/10000000000 : ℝ)|=(5219412993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s3_2 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347430749/10000000000 : ℝ)*x 0 + (2609706527/5000000000 : ℝ)*x 1 + (-466554601/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347430749/10000000000 : ℝ)^4673 ≤ (8971931503879/20000000000000 : ℝ)^3649 := by
    have hnat : (5347430749 : ℕ)^4673*20000000000000^3649 ≤ 8971931503879^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347430749 10000000000 8971931503879 20000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609706527/5000000000 : ℝ)^4673 ≤ (21744493727979/50000000000000 : ℝ)^3649 := by
    have hnat : (2609706527 : ℕ)^4673*50000000000000^3649 ≤ 21744493727979^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609706527 5000000000 21744493727979 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (466554601/2500000000 : ℝ)^4673 ≤ (11651355016977/100000000000000 : ℝ)^3649 := by
    have hnat : (466554601 : ℕ)^4673*100000000000000^3649 ≤ 11651355016977^3649*2500000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466554601 2500000000 11651355016977 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347430749/10000000000 : ℝ), (2609706527/5000000000 : ℝ), (-466554601/2500000000 : ℝ)] ![(8971931503879/20000000000000 : ℝ), (21744493727979/50000000000000 : ℝ), (11651355016977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347430749/10000000000 : ℝ)|^4673 ≤ (8971931503879/20000000000000 : ℝ)^3649
        have hw : |(5347430749/10000000000 : ℝ)|=(5347430749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609706527/5000000000 : ℝ)|^4673 ≤ (21744493727979/50000000000000 : ℝ)^3649
        have hw : |(2609706527/5000000000 : ℝ)|=(2609706527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-466554601/2500000000 : ℝ)|^4673 ≤ (11651355016977/100000000000000 : ℝ)^3649
        have hw : |(-466554601/2500000000 : ℝ)|=(466554601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s3_3 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2117759697/5000000000 : ℝ)*x 0 + (998931519/2500000000 : ℝ)*x 1 + (4486670011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117759697/5000000000 : ℝ)^4673 ≤ (16640923667903/50000000000000 : ℝ)^3649 := by
    have hnat : (2117759697 : ℕ)^4673*50000000000000^3649 ≤ 16640923667903^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117759697 5000000000 16640923667903 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (998931519/2500000000 : ℝ)^4673 ≤ (15444134527547/50000000000000 : ℝ)^3649 := by
    have hnat : (998931519 : ℕ)^4673*50000000000000^3649 ≤ 15444134527547^3649*2500000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998931519 2500000000 15444134527547 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486670011/10000000000 : ℝ)^4673 ≤ (17914941795619/50000000000000 : ℝ)^3649 := by
    have hnat : (4486670011 : ℕ)^4673*50000000000000^3649 ≤ 17914941795619^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486670011 10000000000 17914941795619 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2117759697/5000000000 : ℝ), (998931519/2500000000 : ℝ), (4486670011/10000000000 : ℝ)] ![(16640923667903/50000000000000 : ℝ), (15444134527547/50000000000000 : ℝ), (17914941795619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2117759697/5000000000 : ℝ)|^4673 ≤ (16640923667903/50000000000000 : ℝ)^3649
        have hw : |(2117759697/5000000000 : ℝ)|=(2117759697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(998931519/2500000000 : ℝ)|^4673 ≤ (15444134527547/50000000000000 : ℝ)^3649
        have hw : |(998931519/2500000000 : ℝ)|=(998931519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486670011/10000000000 : ℝ)|^4673 ≤ (17914941795619/50000000000000 : ℝ)^3649
        have hw : |(4486670011/10000000000 : ℝ)|=(4486670011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s3_4 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1761140387/10000000000 : ℝ)*x 0 + (208820053/400000000 : ℝ)*x 1 + (5423772543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1761140387/10000000000 : ℝ)^4673 ≤ (10817951758399/100000000000000 : ℝ)^3649 := by
    have hnat : (1761140387 : ℕ)^4673*100000000000000^3649 ≤ 10817951758399^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1761140387 10000000000 10817951758399 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208820053/400000000 : ℝ)^4673 ≤ (43500600051699/100000000000000 : ℝ)^3649 := by
    have hnat : (208820053 : ℕ)^4673*100000000000000^3649 ≤ 43500600051699^3649*400000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208820053 400000000 43500600051699 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423772543/10000000000 : ℝ)^4673 ≤ (285509051063/625000000000 : ℝ)^3649 := by
    have hnat : (5423772543 : ℕ)^4673*625000000000^3649 ≤ 285509051063^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423772543 10000000000 285509051063 625000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1761140387/10000000000 : ℝ), (208820053/400000000 : ℝ), (5423772543/10000000000 : ℝ)] ![(10817951758399/100000000000000 : ℝ), (43500600051699/100000000000000 : ℝ), (285509051063/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1761140387/10000000000 : ℝ)|^4673 ≤ (10817951758399/100000000000000 : ℝ)^3649
        have hw : |(-1761140387/10000000000 : ℝ)|=(1761140387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208820053/400000000 : ℝ)|^4673 ≤ (43500600051699/100000000000000 : ℝ)^3649
        have hw : |(208820053/400000000 : ℝ)|=(208820053/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423772543/10000000000 : ℝ)|^4673 ≤ (285509051063/625000000000 : ℝ)^3649
        have hw : |(5423772543/10000000000 : ℝ)|=(5423772543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s3_5 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646480199/5000000000 : ℝ)*x 0 + (-66474327/400000000 : ℝ)*x 1 + (5423773807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646480199/5000000000 : ℝ)^4673 ≤ (44275311368681/100000000000000 : ℝ)^3649 := by
    have hnat : (2646480199 : ℕ)^4673*100000000000000^3649 ≤ 44275311368681^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646480199 5000000000 44275311368681 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66474327/400000000 : ℝ)^4673 ≤ (2510806702941/25000000000000 : ℝ)^3649 := by
    have hnat : (66474327 : ℕ)^4673*25000000000000^3649 ≤ 2510806702941^3649*400000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66474327 400000000 2510806702941 25000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423773807/10000000000 : ℝ)^4673 ≤ (45681461803581/100000000000000 : ℝ)^3649 := by
    have hnat : (5423773807 : ℕ)^4673*100000000000000^3649 ≤ 45681461803581^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423773807 10000000000 45681461803581 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646480199/5000000000 : ℝ), (-66474327/400000000 : ℝ), (5423773807/10000000000 : ℝ)] ![(44275311368681/100000000000000 : ℝ), (2510806702941/25000000000000 : ℝ), (45681461803581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646480199/5000000000 : ℝ)|^4673 ≤ (44275311368681/100000000000000 : ℝ)^3649
        have hw : |(2646480199/5000000000 : ℝ)|=(2646480199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-66474327/400000000 : ℝ)|^4673 ≤ (2510806702941/25000000000000 : ℝ)^3649
        have hw : |(-66474327/400000000 : ℝ)|=(66474327/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423773807/10000000000 : ℝ)|^4673 ≤ (45681461803581/100000000000000 : ℝ)^3649
        have hw : |(5423773807/10000000000 : ℝ)|=(5423773807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s3_6 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5292960767/10000000000 : ℝ)*x 0 + (5423772331/10000000000 : ℝ)*x 1 + (-1661859721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5292960767/10000000000 : ℝ)^4673 ≤ (44275315321539/100000000000000 : ℝ)^3649 := by
    have hnat : (5292960767 : ℕ)^4673*100000000000000^3649 ≤ 44275315321539^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292960767 10000000000 44275315321539 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423772331/10000000000 : ℝ)^4673 ≤ (45681445883449/100000000000000 : ℝ)^3649 := by
    have hnat : (5423772331 : ℕ)^4673*100000000000000^3649 ≤ 45681445883449^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423772331 10000000000 45681445883449 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1661859721/10000000000 : ℝ)^4673 ≤ (10043238776711/100000000000000 : ℝ)^3649 := by
    have hnat : (1661859721 : ℕ)^4673*100000000000000^3649 ≤ 10043238776711^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1661859721 10000000000 10043238776711 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5292960767/10000000000 : ℝ), (5423772331/10000000000 : ℝ), (-1661859721/10000000000 : ℝ)] ![(44275315321539/100000000000000 : ℝ), (45681445883449/100000000000000 : ℝ), (10043238776711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5292960767/10000000000 : ℝ)|^4673 ≤ (44275315321539/100000000000000 : ℝ)^3649
        have hw : |(5292960767/10000000000 : ℝ)|=(5292960767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423772331/10000000000 : ℝ)|^4673 ≤ (45681445883449/100000000000000 : ℝ)^3649
        have hw : |(5423772331/10000000000 : ℝ)|=(5423772331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1661859721/10000000000 : ℝ)|^4673 ≤ (10043238776711/100000000000000 : ℝ)^3649
        have hw : |(-1661859721/10000000000 : ℝ)|=(1661859721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s3_7 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (84711703/200000000 : ℝ)*x 0 + (280254449/625000000 : ℝ)*x 1 + (999585877/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84711703/200000000 : ℝ)^4673 ≤ (16641254516277/50000000000000 : ℝ)^3649 := by
    have hnat : (84711703 : ℕ)^4673*50000000000000^3649 ≤ 16641254516277^3649*200000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84711703 200000000 16641254516277 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280254449/625000000 : ℝ)^4673 ≤ (7160661571633/20000000000000 : ℝ)^3649 := by
    have hnat : (280254449 : ℕ)^4673*20000000000000^3649 ≤ 7160661571633^3649*625000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280254449 625000000 7160661571633 20000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (999585877/2500000000 : ℝ)^4673 ≤ (30914183093507/100000000000000 : ℝ)^3649 := by
    have hnat : (999585877 : ℕ)^4673*100000000000000^3649 ≤ 30914183093507^3649*2500000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999585877 2500000000 30914183093507 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84711703/200000000 : ℝ), (280254449/625000000 : ℝ), (999585877/2500000000 : ℝ)] ![(16641254516277/50000000000000 : ℝ), (7160661571633/20000000000000 : ℝ), (30914183093507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84711703/200000000 : ℝ)|^4673 ≤ (16641254516277/50000000000000 : ℝ)^3649
        have hw : |(84711703/200000000 : ℝ)|=(84711703/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280254449/625000000 : ℝ)|^4673 ≤ (7160661571633/20000000000000 : ℝ)^3649
        have hw : |(280254449/625000000 : ℝ)|=(280254449/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(999585877/2500000000 : ℝ)|^4673 ≤ (30914183093507/100000000000000 : ℝ)^3649
        have hw : |(999585877/2500000000 : ℝ)|=(999585877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1588_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21184593/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7883/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10917/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (697/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15511/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7883/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10917/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7883/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10917/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7883/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10917/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7883/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10917/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7883/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10917/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7883/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10917/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
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
  have hpowlo : (10917/100000 : ℝ) ^ (4671/1024 : ℝ) ≤ (1023824962587529/25000000000000000000 : ℝ) := by
    have hpowers : (10917/100000 : ℝ)^4671 ≤ (1023824962587529/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10917 : ℕ)^4671*25000000000000000000^1024 ≤ 1023824962587529^1024*100000^4671 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10917 100000 1023824962587529 25000000000000000000 4671 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10917/100000 : ℝ)) (X := (1023824962587529/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7883/50000 : ℝ) ^ (4671/1024 : ℝ) ≤ (21897166479739043/100000000000000000000 : ℝ) := by
    have hpowers : (7883/50000 : ℝ)^4671 ≤ (21897166479739043/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7883 : ℕ)^4671*100000000000000000000^1024 ≤ 21897166479739043^1024*50000^4671 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7883 50000 21897166479739043 100000000000000000000 4671 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7883/50000 : ℝ)) (X := (21897166479739043/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501023824962587529/12500000000000000000 : ℝ) ≤ (10000179552685207/10000000000000000 : ℝ) ^ (4671/1024 : ℝ) := by
    have hpowers : (12501023824962587529/12500000000000000000 : ℝ)^1024 ≤ (10000179552685207/10000000000000000 : ℝ)^4671 := by
      have hnat : (12501023824962587529 : ℕ)^1024*10000000000000000^4671 ≤ 10000179552685207^4671*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501023824962587529 12500000000000000000 10000179552685207 10000000000000000 1024 4671 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000179552685207/10000000000000000 : ℝ)) (X := (12501023824962587529/12500000000000000000 : ℝ)) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025992466330089159/100000000000000000000 : ℝ) ≤ (10000569762045569/10000000000000000 : ℝ) ^ (4671/1024 : ℝ) := by
    have hpowers : (100025992466330089159/100000000000000000000 : ℝ)^1024 ≤ (10000569762045569/10000000000000000 : ℝ)^4671 := by
      have hnat : (100025992466330089159 : ℕ)^1024*10000000000000000^4671 ≤ 10000569762045569^4671*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025992466330089159 100000000000000000000 10000569762045569 10000000000000000 1024 4671 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000569762045569/10000000000000000 : ℝ)) (X := (100025992466330089159/100000000000000000000 : ℝ)) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021897166479739043/50000000000000000000 : ℝ) ≤ (10000959971405931/10000000000000000 : ℝ) ^ (4671/1024 : ℝ) := by
    have hpowers : (50021897166479739043/50000000000000000000 : ℝ)^1024 ≤ (10000959971405931/10000000000000000 : ℝ)^4671 := by
      have hnat : (50021897166479739043 : ℕ)^1024*10000000000000000^4671 ≤ 10000959971405931^4671*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021897166479739043 50000000000000000000 10000959971405931 10000000000000000 1024 4671 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000959971405931/10000000000000000 : ℝ)) (X := (50021897166479739043/50000000000000000000 : ℝ)) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1023824962587529/25000000000000000000 : ℝ) ≤ ((9696470163959284967/9698000000000000000 : ℝ)+2*(195104680181/242450000000000 : ℝ)*(10917/100000 : ℝ))^(4671/1024 : ℝ) := by
    rw [show (9696470163959284967/9698000000000000000 : ℝ)+2*(195104680181/242450000000000 : ℝ)*(10917/100000 : ℝ)=(10000179552685207/10000000000000000 : ℝ) by norm_num, show 1+2*(1023824962587529/25000000000000000000 : ℝ)=(12501023824962587529/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21897166479739043/100000000000000000000 : ℝ)+(1023824962587529/25000000000000000000 : ℝ) ≤ ((9696470163959284967/9698000000000000000 : ℝ)+(195104680181/242450000000000 : ℝ)*((7883/50000 : ℝ)+(10917/100000 : ℝ)))^(4671/1024 : ℝ) := by
    rw [show (9696470163959284967/9698000000000000000 : ℝ)+(195104680181/242450000000000 : ℝ)*((7883/50000 : ℝ)+(10917/100000 : ℝ))=(10000569762045569/10000000000000000 : ℝ) by norm_num, show 1+(21897166479739043/100000000000000000000 : ℝ)+(1023824962587529/25000000000000000000 : ℝ)=(100025992466330089159/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21897166479739043/100000000000000000000 : ℝ) ≤ ((9696470163959284967/9698000000000000000 : ℝ)+2*(195104680181/242450000000000 : ℝ)*(7883/50000 : ℝ))^(4671/1024 : ℝ) := by
    rw [show (9696470163959284967/9698000000000000000 : ℝ)+2*(195104680181/242450000000000 : ℝ)*(7883/50000 : ℝ)=(10000959971405931/10000000000000000 : ℝ) by norm_num, show 1+2*(21897166479739043/100000000000000000000 : ℝ)=(50021897166479739043/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9696470163959284967/9698000000000000000 : ℝ)*(X 1 0+X 2 0)+(195104680181/242450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4671/1024 : ℝ)) (lo := (10917/100000 : ℝ)) (hi := (7883/50000 : ℝ)) (c := (9696470163959284967/9698000000000000000 : ℝ)) (alpha := (195104680181/242450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9696470163959284967/9698000000000000000 : ℝ)*(X 0 1+X 2 1)+(195104680181/242450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4671/1024 : ℝ)) (lo := (10917/100000 : ℝ)) (hi := (7883/50000 : ℝ)) (c := (9696470163959284967/9698000000000000000 : ℝ)) (alpha := (195104680181/242450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9696470163959284967/9698000000000000000 : ℝ)*(X 0 2+X 1 2)+(195104680181/242450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4671/1024 : ℝ)) (lo := (10917/100000 : ℝ)) (hi := (7883/50000 : ℝ)) (c := (9696470163959284967/9698000000000000000 : ℝ)) (alpha := (195104680181/242450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-880556969/5000000000 : ℝ)*X 0 0+(5424868639/10000000000 : ℝ)*X 0 1+(104388257/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668428867/1250000000 : ℝ)*X 1 0+(-933109117/5000000000 : ℝ)*X 1 1+(5219412993/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347430749/10000000000 : ℝ)*X 2 0+(2609706527/5000000000 : ℝ)*X 2 1+(-466554601/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2117759697/5000000000 : ℝ)*X 0 0+(998931519/2500000000 : ℝ)*X 0 1+(4486670011/10000000000 : ℝ)*X 0 2+(2117759697/5000000000 : ℝ)*X 1 0+(998931519/2500000000 : ℝ)*X 1 1+(4486670011/10000000000 : ℝ)*X 1 2+(2117759697/5000000000 : ℝ)*X 2 0+(998931519/2500000000 : ℝ)*X 2 1+(4486670011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1761140387/10000000000 : ℝ)*X 0 0+(208820053/400000000 : ℝ)*X 0 1+(5423772543/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646480199/5000000000 : ℝ)*X 1 0+(-66474327/400000000 : ℝ)*X 1 1+(5423773807/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5292960767/10000000000 : ℝ)*X 2 0+(5423772331/10000000000 : ℝ)*X 2 1+(-1661859721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((84711703/200000000 : ℝ)*X 0 0+(280254449/625000000 : ℝ)*X 0 1+(999585877/2500000000 : ℝ)*X 0 2+(84711703/200000000 : ℝ)*X 1 0+(280254449/625000000 : ℝ)*X 1 1+(999585877/2500000000 : ℝ)*X 1 2+(84711703/200000000 : ℝ)*X 2 0+(280254449/625000000 : ℝ)*X 2 1+(999585877/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17148298371988048962063/2424500000000000000000000000 : ℝ) := by norm_num
    linear_combination (526828479/50000000000000 : ℝ)*(base19) + (2634417/312500000000 : ℝ)*(base23) + (5405593/25000000000000 : ℝ)*(lower2) + (71914687/25000000000000 : ℝ)*(upper3) + (61261711/100000000000000 : ℝ)*(upper5) + (690417081302671/20000000000000 : ℝ)*(major0) + (690417081302671/20000000000000 : ℝ)*(major1) + (690417081302671/20000000000000 : ℝ)*(major2) + (4867248569904569/100000000000000 : ℝ)*(sp0) + (973452298839761/20000000000000 : ℝ)*(sp1) + (4867261704842323/100000000000000 : ℝ)*(sp2) + (1018449567651269/50000000000000 : ℝ)*(sp3) + (13977951193/100000000000000 : ℝ)*(sp4) + (8894104349/100000000000000 : ℝ)*(sp7) + (2036908029406887/100000000000000 : ℝ)*(f.failure) + (4867262547855763/100000000000000 : ℝ)*(f.sum) + (5838884643161/4849000000000000000000000000 : ℝ)*base65 + (679948428777913143/193960000000000000000000000000000 : ℝ)*base68 + (2390669719145646857/193960000000000000000000000000000 : ℝ)*base69 + (406505247849366857/193960000000000000000000000000000 : ℝ)*base71 + (39726283329/303062500000000000000000000 : ℝ)*base74 + (1147600565841713143/193960000000000000000000000000000 : ℝ)*base76 + (721480468530753143/193960000000000000000000000000000 : ℝ)*base78 + (1987943804463126857/193960000000000000000000000000000 : ℝ)*base79 + (241096838579/60612500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (5008009/1250000000000000000000 : ℝ)*base90 + (5008009/1250000000000000000000 : ℝ)*base92 + (5008009/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (447571414520127429075764457/121225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (101325197/25000000000000 : ℝ)*(base8) + (122618651/100000000000000 : ℝ)*(lower2) + (300289357/50000000000000 : ℝ)*(upper3) + (71048417/100000000000000 : ℝ)*(lower4) + (1744582323470157/50000000000000 : ℝ)*(major0) + (1744582323470157/50000000000000 : ℝ)*(major1) + (1744582323470157/50000000000000 : ℝ)*(major2) + (2412468747/20000000000000 : ℝ)*(sp0) + (4771786349/20000000000000 : ℝ)*(sp1) + (6550808737/100000000000000 : ℝ)*(sp3) + (4919530013861557/100000000000000 : ℝ)*(sp4) + (19216869619431/390625000000 : ℝ)*(sp5) + (4919542481506081/100000000000000 : ℝ)*(sp6) + (1029390069248369/50000000000000 : ℝ)*(sp7) + (1029393344652737/50000000000000 : ℝ)*(f.failure) + (4919542481506081/100000000000000 : ℝ)*(f.sum) + (315658019449137/24245000000000000000000000000 : ℝ)*base66 + (3130425055020690181/484900000000000000000000000000000 : ℝ)*base68 + (4312889450878890181/484900000000000000000000000000000 : ℝ)*base70 + (3875561978377490181/484900000000000000000000000000000 : ℝ)*base72 + (47836519233731/12122500000000000000000000000 : ℝ)*base74 + (3161036527265290181/484900000000000000000000000000000 : ℝ)*base76 + (2224327239815409819/484900000000000000000000000000000 : ℝ)*base77 + (129551153193590181/484900000000000000000000000000000 : ℝ)*base80 + (81411127805391/12122500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2818959/625000000000000000000 : ℝ)*base90 + (2818959/625000000000000000000 : ℝ)*base92 + (2818959/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1588_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21184593/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7883/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10917/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (697/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15511/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1588_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1588_s4_0 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-880648359/5000000000 : ℝ)*x 0 + (1084727539/2000000000 : ℝ)*x 1 + (2610261191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (880648359/5000000000 : ℝ)^4673 ≤ (1352397690909/12500000000000 : ℝ)^3649 := by
    have hnat : (880648359 : ℕ)^4673*12500000000000^3649 ≤ 1352397690909^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880648359 5000000000 1352397690909 12500000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084727539/2000000000 : ℝ)^4673 ≤ (11419998426243/25000000000000 : ℝ)^3649 := by
    have hnat : (1084727539 : ℕ)^4673*25000000000000^3649 ≤ 11419998426243^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084727539 2000000000 11419998426243 25000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2610261191/5000000000 : ℝ)^4673 ≤ (10875206187747/25000000000000 : ℝ)^3649 := by
    have hnat : (2610261191 : ℕ)^4673*25000000000000^3649 ≤ 10875206187747^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610261191 5000000000 10875206187747 25000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-880648359/5000000000 : ℝ), (1084727539/2000000000 : ℝ), (2610261191/5000000000 : ℝ)] ![(1352397690909/12500000000000 : ℝ), (11419998426243/25000000000000 : ℝ), (10875206187747/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-880648359/5000000000 : ℝ)|^4673 ≤ (1352397690909/12500000000000 : ℝ)^3649
        have hw : |(-880648359/5000000000 : ℝ)|=(880648359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084727539/2000000000 : ℝ)|^4673 ≤ (11419998426243/25000000000000 : ℝ)^3649
        have hw : |(1084727539/2000000000 : ℝ)|=(1084727539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2610261191/5000000000 : ℝ)|^4673 ≤ (10875206187747/25000000000000 : ℝ)^3649
        have hw : |(2610261191/5000000000 : ℝ)|=(2610261191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s4_1 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069420757/2000000000 : ℝ)*x 0 + (-1865177351/10000000000 : ℝ)*x 1 + (5220522213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069420757/2000000000 : ℝ)^4673 ≤ (44856144917639/100000000000000 : ℝ)^3649 := by
    have hnat : (1069420757 : ℕ)^4673*100000000000000^3649 ≤ 44856144917639^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069420757 2000000000 44856144917639 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1865177351/10000000000 : ℝ)^4673 ≤ (11643032116027/100000000000000 : ℝ)^3649 := by
    have hnat : (1865177351 : ℕ)^4673*100000000000000^3649 ≤ 11643032116027^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865177351 10000000000 11643032116027 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220522213/10000000000 : ℝ)^4673 ≤ (43500822947587/100000000000000 : ℝ)^3649 := by
    have hnat : (5220522213 : ℕ)^4673*100000000000000^3649 ≤ 43500822947587^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220522213 10000000000 43500822947587 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069420757/2000000000 : ℝ), (-1865177351/10000000000 : ℝ), (5220522213/10000000000 : ℝ)] ![(44856144917639/100000000000000 : ℝ), (11643032116027/100000000000000 : ℝ), (43500822947587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069420757/2000000000 : ℝ)|^4673 ≤ (44856144917639/100000000000000 : ℝ)^3649
        have hw : |(1069420757/2000000000 : ℝ)|=(1069420757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1865177351/10000000000 : ℝ)|^4673 ≤ (11643032116027/100000000000000 : ℝ)^3649
        have hw : |(-1865177351/10000000000 : ℝ)|=(1865177351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220522213/10000000000 : ℝ)|^4673 ≤ (43500822947587/100000000000000 : ℝ)^3649
        have hw : |(5220522213/10000000000 : ℝ)|=(5220522213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s4_2 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347103757/10000000000 : ℝ)*x 0 + (5220522197/10000000000 : ℝ)*x 1 + (-1865177411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347103757/10000000000 : ℝ)^4673 ≤ (11214036154209/25000000000000 : ℝ)^3649 := by
    have hnat : (5347103757 : ℕ)^4673*25000000000000^3649 ≤ 11214036154209^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347103757 10000000000 11214036154209 25000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220522197/10000000000 : ℝ)^4673 ≤ (43500822776851/100000000000000 : ℝ)^3649 := by
    have hnat : (5220522197 : ℕ)^4673*100000000000000^3649 ≤ 43500822776851^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220522197 10000000000 43500822776851 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1865177411/10000000000 : ℝ)^4673 ≤ (11643032595671/100000000000000 : ℝ)^3649 := by
    have hnat : (1865177411 : ℕ)^4673*100000000000000^3649 ≤ 11643032595671^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865177411 10000000000 11643032595671 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347103757/10000000000 : ℝ), (5220522197/10000000000 : ℝ), (-1865177411/10000000000 : ℝ)] ![(11214036154209/25000000000000 : ℝ), (43500822776851/100000000000000 : ℝ), (11643032595671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347103757/10000000000 : ℝ)|^4673 ≤ (11214036154209/25000000000000 : ℝ)^3649
        have hw : |(5347103757/10000000000 : ℝ)|=(5347103757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220522197/10000000000 : ℝ)|^4673 ≤ (43500822776851/100000000000000 : ℝ)^3649
        have hw : |(5220522197/10000000000 : ℝ)|=(5220522197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1865177411/10000000000 : ℝ)|^4673 ≤ (11643032595671/100000000000000 : ℝ)^3649
        have hw : |(-1865177411/10000000000 : ℝ)|=(1865177411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s4_3 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058908767/2500000000 : ℝ)*x 0 + (3998509303/10000000000 : ℝ)*x 1 + (448386151/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058908767/2500000000 : ℝ)^4673 ≤ (1040094104839/3125000000000 : ℝ)^3649 := by
    have hnat : (1058908767 : ℕ)^4673*3125000000000^3649 ≤ 1040094104839^3649*2500000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058908767 2500000000 1040094104839 3125000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3998509303/10000000000 : ℝ)^4673 ≤ (618316494339/2000000000000 : ℝ)^3649 := by
    have hnat : (3998509303 : ℕ)^4673*2000000000000^3649 ≤ 618316494339^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3998509303 10000000000 618316494339 2000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448386151/1000000000 : ℝ)^4673 ≤ (35801163909891/100000000000000 : ℝ)^3649 := by
    have hnat : (448386151 : ℕ)^4673*100000000000000^3649 ≤ 35801163909891^3649*1000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448386151 1000000000 35801163909891 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058908767/2500000000 : ℝ), (3998509303/10000000000 : ℝ), (448386151/1000000000 : ℝ)] ![(1040094104839/3125000000000 : ℝ), (618316494339/2000000000000 : ℝ), (35801163909891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058908767/2500000000 : ℝ)|^4673 ≤ (1040094104839/3125000000000 : ℝ)^3649
        have hw : |(1058908767/2500000000 : ℝ)|=(1058908767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3998509303/10000000000 : ℝ)|^4673 ≤ (618316494339/2000000000000 : ℝ)^3649
        have hw : |(3998509303/10000000000 : ℝ)|=(3998509303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(448386151/1000000000 : ℝ)|^4673 ≤ (35801163909891/100000000000000 : ℝ)^3649
        have hw : |(448386151/1000000000 : ℝ)|=(448386151/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s4_4 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-880661527/5000000000 : ℝ)*x 0 + (1305396341/2500000000 : ℝ)*x 1 + (5422566771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (880661527/5000000000 : ℝ)^4673 ≤ (432775548037/4000000000000 : ℝ)^3649 := by
    have hnat : (880661527 : ℕ)^4673*4000000000000^3649 ≤ 432775548037^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880661527 5000000000 432775548037 4000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305396341/2500000000 : ℝ)^4673 ≤ (43512168164497/100000000000000 : ℝ)^3649 := by
    have hnat : (1305396341 : ℕ)^4673*100000000000000^3649 ≤ 43512168164497^3649*2500000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305396341 2500000000 43512168164497 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422566771/10000000000 : ℝ)^4673 ≤ (11417110780521/25000000000000 : ℝ)^3649 := by
    have hnat : (5422566771 : ℕ)^4673*25000000000000^3649 ≤ 11417110780521^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422566771 10000000000 11417110780521 25000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-880661527/5000000000 : ℝ), (1305396341/2500000000 : ℝ), (5422566771/10000000000 : ℝ)] ![(432775548037/4000000000000 : ℝ), (43512168164497/100000000000000 : ℝ), (11417110780521/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-880661527/5000000000 : ℝ)|^4673 ≤ (432775548037/4000000000000 : ℝ)^3649
        have hw : |(-880661527/5000000000 : ℝ)|=(880661527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305396341/2500000000 : ℝ)|^4673 ≤ (43512168164497/100000000000000 : ℝ)^3649
        have hw : |(1305396341/2500000000 : ℝ)|=(1305396341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422566771/10000000000 : ℝ)|^4673 ≤ (11417110780521/25000000000000 : ℝ)^3649
        have hw : |(5422566771/10000000000 : ℝ)|=(5422566771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s4_5 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529325471/1000000000 : ℝ)*x 0 + (-831566403/5000000000 : ℝ)*x 1 + (5422566779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529325471/1000000000 : ℝ)^4673 ≤ (2767404010467/6250000000000 : ℝ)^3649 := by
    have hnat : (529325471 : ℕ)^4673*6250000000000^3649 ≤ 2767404010467^3649*1000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529325471 1000000000 2767404010467 6250000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (831566403/5000000000 : ℝ)^4673 ≤ (10053092614649/100000000000000 : ℝ)^3649 := by
    have hnat : (831566403 : ℕ)^4673*100000000000000^3649 ≤ 10053092614649^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831566403 5000000000 10053092614649 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422566779/10000000000 : ℝ)^4673 ≤ (22834221604183/50000000000000 : ℝ)^3649 := by
    have hnat : (5422566779 : ℕ)^4673*50000000000000^3649 ≤ 22834221604183^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422566779 10000000000 22834221604183 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529325471/1000000000 : ℝ), (-831566403/5000000000 : ℝ), (5422566779/10000000000 : ℝ)] ![(2767404010467/6250000000000 : ℝ), (10053092614649/100000000000000 : ℝ), (22834221604183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529325471/1000000000 : ℝ)|^4673 ≤ (2767404010467/6250000000000 : ℝ)^3649
        have hw : |(529325471/1000000000 : ℝ)|=(529325471/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-831566403/5000000000 : ℝ)|^4673 ≤ (10053092614649/100000000000000 : ℝ)^3649
        have hw : |(-831566403/5000000000 : ℝ)|=(831566403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422566779/10000000000 : ℝ)|^4673 ≤ (22834221604183/50000000000000 : ℝ)^3649
        have hw : |(5422566779/10000000000 : ℝ)|=(5422566779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s4_6 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293254727/10000000000 : ℝ)*x 0 + (5422566773/10000000000 : ℝ)*x 1 + (-1663132791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293254727/10000000000 : ℝ)^4673 ≤ (8855692869917/20000000000000 : ℝ)^3649 := by
    have hnat : (5293254727 : ℕ)^4673*20000000000000^3649 ≤ 8855692869917^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293254727 10000000000 8855692869917 20000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422566773/10000000000 : ℝ)^4673 ≤ (22834221571827/50000000000000 : ℝ)^3649 := by
    have hnat : (5422566773 : ℕ)^4673*50000000000000^3649 ≤ 22834221571827^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422566773 10000000000 22834221571827 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1663132791/10000000000 : ℝ)^4673 ≤ (2010618499707/20000000000000 : ℝ)^3649 := by
    have hnat : (1663132791 : ℕ)^4673*20000000000000^3649 ≤ 2010618499707^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1663132791 10000000000 2010618499707 20000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293254727/10000000000 : ℝ), (5422566773/10000000000 : ℝ), (-1663132791/10000000000 : ℝ)] ![(8855692869917/20000000000000 : ℝ), (22834221571827/50000000000000 : ℝ), (2010618499707/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293254727/10000000000 : ℝ)|^4673 ≤ (8855692869917/20000000000000 : ℝ)^3649
        have hw : |(5293254727/10000000000 : ℝ)|=(5293254727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422566773/10000000000 : ℝ)|^4673 ≤ (22834221571827/50000000000000 : ℝ)^3649
        have hw : |(5422566773/10000000000 : ℝ)|=(5422566773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1663132791/10000000000 : ℝ)|^4673 ≤ (2010618499707/20000000000000 : ℝ)^3649
        have hw : |(-1663132791/10000000000 : ℝ)|=(1663132791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s4_7 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2117848909/5000000000 : ℝ)*x 0 + (2240660427/5000000000 : ℝ)*x 1 + (800213751/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117848909/5000000000 : ℝ)^4673 ≤ (33283642807263/100000000000000 : ℝ)^3649 := by
    have hnat : (2117848909 : ℕ)^4673*100000000000000^3649 ≤ 33283642807263^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117848909 5000000000 33283642807263 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2240660427/5000000000 : ℝ)^4673 ≤ (35775187555219/100000000000000 : ℝ)^3649 := by
    have hnat : (2240660427 : ℕ)^4673*100000000000000^3649 ≤ 35775187555219^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240660427 5000000000 35775187555219 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (800213751/2000000000 : ℝ)^4673 ≤ (30941169619777/100000000000000 : ℝ)^3649 := by
    have hnat : (800213751 : ℕ)^4673*100000000000000^3649 ≤ 30941169619777^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800213751 2000000000 30941169619777 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2117848909/5000000000 : ℝ), (2240660427/5000000000 : ℝ), (800213751/2000000000 : ℝ)] ![(33283642807263/100000000000000 : ℝ), (35775187555219/100000000000000 : ℝ), (30941169619777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2117848909/5000000000 : ℝ)|^4673 ≤ (33283642807263/100000000000000 : ℝ)^3649
        have hw : |(2117848909/5000000000 : ℝ)|=(2117848909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2240660427/5000000000 : ℝ)|^4673 ≤ (35775187555219/100000000000000 : ℝ)^3649
        have hw : |(2240660427/5000000000 : ℝ)|=(2240660427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(800213751/2000000000 : ℝ)|^4673 ≤ (30941169619777/100000000000000 : ℝ)^3649
        have hw : |(800213751/2000000000 : ℝ)|=(800213751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1588_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21184593/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15511/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (697/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (1397/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7743/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15511/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (697/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15511/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (697/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15511/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (697/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15511/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (697/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15511/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (697/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15511/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (697/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (697/6250 : ℝ) ^ (4671/1024 : ℝ) ≤ (4513124253559747/100000000000000000000 : ℝ) := by
    have hpowers : (697/6250 : ℝ)^4671 ≤ (4513124253559747/100000000000000000000 : ℝ)^1024 := by
      have hnat : (697 : ℕ)^4671*100000000000000000000^1024 ≤ 4513124253559747^1024*6250^4671 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        697 6250 4513124253559747 100000000000000000000 4671 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (697/6250 : ℝ)) (X := (4513124253559747/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15511/100000 : ℝ) ^ (4671/1024 : ℝ) ≤ (10163761672255077/50000000000000000000 : ℝ) := by
    have hpowers : (15511/100000 : ℝ)^4671 ≤ (10163761672255077/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15511 : ℕ)^4671*50000000000000000000^1024 ≤ 10163761672255077^1024*100000^4671 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15511 100000 10163761672255077 50000000000000000000 4671 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15511/100000 : ℝ)) (X := (10163761672255077/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004513124253559747/50000000000000000000 : ℝ) ≤ (10000197870965409/10000000000000000 : ℝ) ^ (4671/1024 : ℝ) := by
    have hpowers : (50004513124253559747/50000000000000000000 : ℝ)^1024 ≤ (10000197870965409/10000000000000000 : ℝ)^4671 := by
      have hnat : (50004513124253559747 : ℕ)^1024*10000000000000000^4671 ≤ 10000197870965409^4671*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004513124253559747 50000000000000000000 10000197870965409 10000000000000000 1024 4671 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000197870965409/10000000000000000 : ℝ)) (X := (50004513124253559747/50000000000000000000 : ℝ)) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100024840647598069901/100000000000000000000 : ℝ) ≤ (10000544516308579/10000000000000000 : ℝ) ^ (4671/1024 : ℝ) := by
    have hpowers : (100024840647598069901/100000000000000000000 : ℝ)^1024 ≤ (10000544516308579/10000000000000000 : ℝ)^4671 := by
      have hnat : (100024840647598069901 : ℕ)^1024*10000000000000000^4671 ≤ 10000544516308579^4671*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100024840647598069901 100000000000000000000 10000544516308579 10000000000000000 1024 4671 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000544516308579/10000000000000000 : ℝ)) (X := (100024840647598069901/100000000000000000000 : ℝ)) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010163761672255077/25000000000000000000 : ℝ) ≤ (10000891161651749/10000000000000000 : ℝ) ^ (4671/1024 : ℝ) := by
    have hpowers : (25010163761672255077/25000000000000000000 : ℝ)^1024 ≤ (10000891161651749/10000000000000000 : ℝ)^4671 := by
      have hnat : (25010163761672255077 : ℕ)^1024*10000000000000000^4671 ≤ 10000891161651749^4671*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010163761672255077 25000000000000000000 10000891161651749 10000000000000000 1024 4671 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000891161651749/10000000000000000 : ℝ)) (X := (25010163761672255077/25000000000000000000 : ℝ)) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4513124253559747/100000000000000000000 : ℝ) ≤ ((43583130941804154151/43590000000000000000 : ℝ)+2*(34664534317/43590000000000 : ℝ)*(697/6250 : ℝ))^(4671/1024 : ℝ) := by
    rw [show (43583130941804154151/43590000000000000000 : ℝ)+2*(34664534317/43590000000000 : ℝ)*(697/6250 : ℝ)=(10000197870965409/10000000000000000 : ℝ) by norm_num, show 1+2*(4513124253559747/100000000000000000000 : ℝ)=(50004513124253559747/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10163761672255077/50000000000000000000 : ℝ)+(4513124253559747/100000000000000000000 : ℝ) ≤ ((43583130941804154151/43590000000000000000 : ℝ)+(34664534317/43590000000000 : ℝ)*((15511/100000 : ℝ)+(697/6250 : ℝ)))^(4671/1024 : ℝ) := by
    rw [show (43583130941804154151/43590000000000000000 : ℝ)+(34664534317/43590000000000 : ℝ)*((15511/100000 : ℝ)+(697/6250 : ℝ))=(10000544516308579/10000000000000000 : ℝ) by norm_num, show 1+(10163761672255077/50000000000000000000 : ℝ)+(4513124253559747/100000000000000000000 : ℝ)=(100024840647598069901/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10163761672255077/50000000000000000000 : ℝ) ≤ ((43583130941804154151/43590000000000000000 : ℝ)+2*(34664534317/43590000000000 : ℝ)*(15511/100000 : ℝ))^(4671/1024 : ℝ) := by
    rw [show (43583130941804154151/43590000000000000000 : ℝ)+2*(34664534317/43590000000000 : ℝ)*(15511/100000 : ℝ)=(10000891161651749/10000000000000000 : ℝ) by norm_num, show 1+2*(10163761672255077/50000000000000000000 : ℝ)=(25010163761672255077/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43583130941804154151/43590000000000000000 : ℝ)*(X 1 0+X 2 0)+(34664534317/43590000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4671/1024 : ℝ)) (lo := (697/6250 : ℝ)) (hi := (15511/100000 : ℝ)) (c := (43583130941804154151/43590000000000000000 : ℝ)) (alpha := (34664534317/43590000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43583130941804154151/43590000000000000000 : ℝ)*(X 0 1+X 2 1)+(34664534317/43590000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4671/1024 : ℝ)) (lo := (697/6250 : ℝ)) (hi := (15511/100000 : ℝ)) (c := (43583130941804154151/43590000000000000000 : ℝ)) (alpha := (34664534317/43590000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43583130941804154151/43590000000000000000 : ℝ)*(X 0 2+X 1 2)+(34664534317/43590000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4671/1024 : ℝ)) (lo := (697/6250 : ℝ)) (hi := (15511/100000 : ℝ)) (c := (43583130941804154151/43590000000000000000 : ℝ)) (alpha := (34664534317/43590000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-880648359/5000000000 : ℝ)*X 0 0+(1084727539/2000000000 : ℝ)*X 0 1+(2610261191/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069420757/2000000000 : ℝ)*X 1 0+(-1865177351/10000000000 : ℝ)*X 1 1+(5220522213/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347103757/10000000000 : ℝ)*X 2 0+(5220522197/10000000000 : ℝ)*X 2 1+(-1865177411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1058908767/2500000000 : ℝ)*X 0 0+(3998509303/10000000000 : ℝ)*X 0 1+(448386151/1000000000 : ℝ)*X 0 2+(1058908767/2500000000 : ℝ)*X 1 0+(3998509303/10000000000 : ℝ)*X 1 1+(448386151/1000000000 : ℝ)*X 1 2+(1058908767/2500000000 : ℝ)*X 2 0+(3998509303/10000000000 : ℝ)*X 2 1+(448386151/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-880661527/5000000000 : ℝ)*X 0 0+(1305396341/2500000000 : ℝ)*X 0 1+(5422566771/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((529325471/1000000000 : ℝ)*X 1 0+(-831566403/5000000000 : ℝ)*X 1 1+(5422566779/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293254727/10000000000 : ℝ)*X 2 0+(5422566773/10000000000 : ℝ)*X 2 1+(-1663132791/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2117848909/5000000000 : ℝ)*X 0 0+(2240660427/5000000000 : ℝ)*X 0 1+(800213751/2000000000 : ℝ)*X 0 2+(2117848909/5000000000 : ℝ)*X 1 0+(2240660427/5000000000 : ℝ)*X 1 1+(800213751/2000000000 : ℝ)*X 1 2+(2117848909/5000000000 : ℝ)*X 2 0+(2240660427/5000000000 : ℝ)*X 2 1+(800213751/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5265843170621901254243031/1135156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (677165423/100000000000000 : ℝ)*(base19) + (53994599/10000000000000 : ℝ)*(base23) + (61087661/100000000000000 : ℝ)*(lower2) + (72168959/50000000000000 : ℝ)*(upper3) + (1500313/100000000000000 : ℝ)*(lower4) + (43648089613149/1250000000000 : ℝ)*(major0) + (43648089613149/1250000000000 : ℝ)*(major1) + (43648089613149/1250000000000 : ℝ)*(major2) + (1230829977831921/25000000000000 : ℝ)*(sp0) + (4923323990919167/100000000000000 : ℝ)*(sp1) + (24616620640693/500000000000 : ℝ)*(sp2) + (206036352580289/10000000000000 : ℝ)*(sp3) + (2378378453/50000000000000 : ℝ)*(sp4) + (46793651/781250000000 : ℝ)*(sp7) + (1030184757695109/50000000000000 : ℝ)*(f.failure) + (492332466808459/10000000000000 : ℝ)*(f.sum) + (1247344937801/363250000000000000000000000 : ℝ)*base66 + (86692458207381167/18162500000000000000000000000000 : ℝ)*base68 + (136757360542681167/18162500000000000000000000000000 : ℝ)*base70 + (37333103266993667/18162500000000000000000000000000 : ℝ)*base72 + (435010594997/290600000000000000000000000 : ℝ)*base74 + (241234649116693667/18162500000000000000000000000000 : ℝ)*base76 + (71969310213443833/18162500000000000000000000000000 : ℝ)*base77 + (244298133811231167/18162500000000000000000000000000 : ℝ)*base80 + (214509164753/72650000000000000000000000 : ℝ)*base82 + (2255637/625000000000000000000 : ℝ)*base89 + (2255637/625000000000000000000 : ℝ)*base91 + (2255637/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2166443053482036819582871053/181625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (182478007/10000000000000 : ℝ)*(base19) + (1996266123/100000000000000 : ℝ)*(base23) + (248708837/100000000000000 : ℝ)*(upper3) + (4255567/6250000000000 : ℝ)*(lower4) + (245346481/100000000000000 : ℝ)*(upper5) + (882227899593603/25000000000000 : ℝ)*(major0) + (882227899593603/25000000000000 : ℝ)*(major1) + (882227899593603/25000000000000 : ℝ)*(major2) + (7307206169/25000000000000 : ℝ)*(sp1) + (31870377783/100000000000000 : ℝ)*(sp2) + (4975583363170127/100000000000000 : ℝ)*(sp4) + (4975552309565381/100000000000000 : ℝ)*(sp5) + (2487774748263111/50000000000000 : ℝ)*(sp6) + (208223943597501/10000000000000 : ℝ)*(sp7) + (208223943597501/10000000000000 : ℝ)*(f.failure) + (4975583363170127/100000000000000 : ℝ)*(f.sum) + (778211036987/145300000000000000000000000 : ℝ)*base65 + (649699182653834649/363250000000000000000000000000000 : ℝ)*base68 + (1919647001934415351/363250000000000000000000000000000 : ℝ)*base69 + (1936153487684665351/363250000000000000000000000000000 : ℝ)*base71 + (972388035551/726500000000000000000000000 : ℝ)*base73 + (3162059167843084649/363250000000000000000000000000000 : ℝ)*base76 + (968898050219084649/363250000000000000000000000000000 : ℝ)*base78 + (1188162685388084649/363250000000000000000000000000000 : ℝ)*base80 + (3664182230581/1453000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (497907/125000000000000000000 : ℝ)*base90 + (497907/125000000000000000000 : ℝ)*base92 + (497907/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1588_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21184593/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15511/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (697/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1397/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1588_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1588_s5_0 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-176131269/1000000000 : ℝ)*x 0 + (5423522411/10000000000 : ℝ)*x 1 + (5220627133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (176131269/1000000000 : ℝ)^4673 ≤ (5409653585911/50000000000000 : ℝ)^3649 := by
    have hnat : (176131269 : ℕ)^4673*50000000000000^3649 ≤ 5409653585911^3649*1000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176131269 1000000000 5409653585911 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423522411/10000000000 : ℝ)^4673 ≤ (11419687566107/25000000000000 : ℝ)^3649 := by
    have hnat : (5423522411 : ℕ)^4673*25000000000000^3649 ≤ 11419687566107^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423522411 10000000000 11419687566107 25000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220627133/10000000000 : ℝ)^4673 ≤ (43501942552897/100000000000000 : ℝ)^3649 := by
    have hnat : (5220627133 : ℕ)^4673*100000000000000^3649 ≤ 43501942552897^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220627133 10000000000 43501942552897 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-176131269/1000000000 : ℝ), (5423522411/10000000000 : ℝ), (5220627133/10000000000 : ℝ)] ![(5409653585911/50000000000000 : ℝ), (11419687566107/25000000000000 : ℝ), (43501942552897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-176131269/1000000000 : ℝ)|^4673 ≤ (5409653585911/50000000000000 : ℝ)^3649
        have hw : |(-176131269/1000000000 : ℝ)|=(176131269/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423522411/10000000000 : ℝ)|^4673 ≤ (11419687566107/25000000000000 : ℝ)^3649
        have hw : |(5423522411/10000000000 : ℝ)|=(5423522411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220627133/10000000000 : ℝ)|^4673 ≤ (43501942552897/100000000000000 : ℝ)^3649
        have hw : |(5220627133/10000000000 : ℝ)|=(5220627133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s5_1 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347073479/10000000000 : ℝ)*x 0 + (-466269507/2500000000 : ℝ)*x 1 + (5220627129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347073479/10000000000 : ℝ)^4673 ≤ (2803488708799/6250000000000 : ℝ)^3649 := by
    have hnat : (5347073479 : ℕ)^4673*6250000000000^3649 ≤ 2803488708799^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347073479 10000000000 2803488708799 6250000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (466269507/2500000000 : ℝ)^4673 ≤ (2910559531767/25000000000000 : ℝ)^3649 := by
    have hnat : (466269507 : ℕ)^4673*25000000000000^3649 ≤ 2910559531767^3649*2500000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466269507 2500000000 2910559531767 25000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220627129/10000000000 : ℝ)^4673 ≤ (10875485627553/25000000000000 : ℝ)^3649 := by
    have hnat : (5220627129 : ℕ)^4673*25000000000000^3649 ≤ 10875485627553^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220627129 10000000000 10875485627553 25000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347073479/10000000000 : ℝ), (-466269507/2500000000 : ℝ), (5220627129/10000000000 : ℝ)] ![(2803488708799/6250000000000 : ℝ), (2910559531767/25000000000000 : ℝ), (10875485627553/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347073479/10000000000 : ℝ)|^4673 ≤ (2803488708799/6250000000000 : ℝ)^3649
        have hw : |(5347073479/10000000000 : ℝ)|=(5347073479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-466269507/2500000000 : ℝ)|^4673 ≤ (2910559531767/25000000000000 : ℝ)^3649
        have hw : |(-466269507/2500000000 : ℝ)|=(466269507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220627129/10000000000 : ℝ)|^4673 ≤ (10875485627553/25000000000000 : ℝ)^3649
        have hw : |(5220627129/10000000000 : ℝ)|=(5220627129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s5_2 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336768363/2500000000 : ℝ)*x 0 + (1044125431/2000000000 : ℝ)*x 1 + (-1865078031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336768363/2500000000 : ℝ)^4673 ≤ (11213954762681/25000000000000 : ℝ)^3649 := by
    have hnat : (1336768363 : ℕ)^4673*25000000000000^3649 ≤ 11213954762681^3649*2500000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336768363 2500000000 11213954762681 25000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044125431/2000000000 : ℝ)^4673 ≤ (2175097139383/5000000000000 : ℝ)^3649 := by
    have hnat : (1044125431 : ℕ)^4673*5000000000000^3649 ≤ 2175097139383^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044125431 2000000000 2175097139383 5000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1865078031/10000000000 : ℝ)^4673 ≤ (232844763021/2000000000000 : ℝ)^3649 := by
    have hnat : (1865078031 : ℕ)^4673*2000000000000^3649 ≤ 232844763021^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865078031 10000000000 232844763021 2000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336768363/2500000000 : ℝ), (1044125431/2000000000 : ℝ), (-1865078031/10000000000 : ℝ)] ![(11213954762681/25000000000000 : ℝ), (2175097139383/5000000000000 : ℝ), (232844763021/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336768363/2500000000 : ℝ)|^4673 ≤ (11213954762681/25000000000000 : ℝ)^3649
        have hw : |(1336768363/2500000000 : ℝ)|=(1336768363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044125431/2000000000 : ℝ)|^4673 ≤ (2175097139383/5000000000000 : ℝ)^3649
        have hw : |(1044125431/2000000000 : ℝ)|=(1044125431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1865078031/10000000000 : ℝ)|^4673 ≤ (232844763021/2000000000000 : ℝ)^3649
        have hw : |(-1865078031/10000000000 : ℝ)|=(1865078031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s5_3 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2117822967/5000000000 : ℝ)*x 0 + (799754309/2000000000 : ℝ)*x 1 + (4483596867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117822967/5000000000 : ℝ)^4673 ≤ (16641560349537/50000000000000 : ℝ)^3649 := by
    have hnat : (2117822967 : ℕ)^4673*50000000000000^3649 ≤ 16641560349537^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117822967 5000000000 16641560349537 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (799754309/2000000000 : ℝ)^4673 ≤ (30918421351839/100000000000000 : ℝ)^3649 := by
    have hnat : (799754309 : ℕ)^4673*100000000000000^3649 ≤ 30918421351839^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      799754309 2000000000 30918421351839 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4483596867/10000000000 : ℝ)^4673 ≤ (7159691587093/20000000000000 : ℝ)^3649 := by
    have hnat : (4483596867 : ℕ)^4673*20000000000000^3649 ≤ 7159691587093^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483596867 10000000000 7159691587093 20000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2117822967/5000000000 : ℝ), (799754309/2000000000 : ℝ), (4483596867/10000000000 : ℝ)] ![(16641560349537/50000000000000 : ℝ), (30918421351839/100000000000000 : ℝ), (7159691587093/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2117822967/5000000000 : ℝ)|^4673 ≤ (16641560349537/50000000000000 : ℝ)^3649
        have hw : |(2117822967/5000000000 : ℝ)|=(2117822967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(799754309/2000000000 : ℝ)|^4673 ≤ (30918421351839/100000000000000 : ℝ)^3649
        have hw : |(799754309/2000000000 : ℝ)|=(799754309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4483596867/10000000000 : ℝ)|^4673 ≤ (7159691587093/20000000000000 : ℝ)^3649
        have hw : |(4483596867/10000000000 : ℝ)|=(4483596867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s5_4 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-88066943/500000000 : ℝ)*x 0 + (1305421929/2500000000 : ℝ)*x 1 + (5422453969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88066943/500000000 : ℝ)^4673 ≤ (10819513040147/100000000000000 : ℝ)^3649 := by
    have hnat : (88066943 : ℕ)^4673*100000000000000^3649 ≤ 10819513040147^3649*500000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88066943 500000000 10819513040147 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305421929/2500000000 : ℝ)^4673 ≤ (21756630214459/50000000000000 : ℝ)^3649 := by
    have hnat : (1305421929 : ℕ)^4673*50000000000000^3649 ≤ 21756630214459^3649*2500000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305421929 2500000000 21756630214459 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422453969/10000000000 : ℝ)^4673 ≤ (45667226519463/100000000000000 : ℝ)^3649 := by
    have hnat : (5422453969 : ℕ)^4673*100000000000000^3649 ≤ 45667226519463^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422453969 10000000000 45667226519463 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88066943/500000000 : ℝ), (1305421929/2500000000 : ℝ), (5422453969/10000000000 : ℝ)] ![(10819513040147/100000000000000 : ℝ), (21756630214459/50000000000000 : ℝ), (45667226519463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88066943/500000000 : ℝ)|^4673 ≤ (10819513040147/100000000000000 : ℝ)^3649
        have hw : |(-88066943/500000000 : ℝ)|=(88066943/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305421929/2500000000 : ℝ)|^4673 ≤ (21756630214459/50000000000000 : ℝ)^3649
        have hw : |(1305421929/2500000000 : ℝ)|=(1305421929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422453969/10000000000 : ℝ)|^4673 ≤ (45667226519463/100000000000000 : ℝ)^3649
        have hw : |(5422453969/10000000000 : ℝ)|=(5422453969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s5_5 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646641781/5000000000 : ℝ)*x 0 + (-831625537/5000000000 : ℝ)*x 1 + (1084490647/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646641781/5000000000 : ℝ)^4673 ≤ (11069693311339/25000000000000 : ℝ)^3649 := by
    have hnat : (2646641781 : ℕ)^4673*25000000000000^3649 ≤ 11069693311339^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646641781 5000000000 11069693311339 25000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (831625537/5000000000 : ℝ)^4673 ≤ (251350203283/2500000000000 : ℝ)^3649 := by
    have hnat : (831625537 : ℕ)^4673*2500000000000^3649 ≤ 251350203283^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831625537 5000000000 251350203283 2500000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084490647/2000000000 : ℝ)^4673 ≤ (45667218603081/100000000000000 : ℝ)^3649 := by
    have hnat : (1084490647 : ℕ)^4673*100000000000000^3649 ≤ 45667218603081^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084490647 2000000000 45667218603081 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646641781/5000000000 : ℝ), (-831625537/5000000000 : ℝ), (1084490647/2000000000 : ℝ)] ![(11069693311339/25000000000000 : ℝ), (251350203283/2500000000000 : ℝ), (45667218603081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646641781/5000000000 : ℝ)|^4673 ≤ (11069693311339/25000000000000 : ℝ)^3649
        have hw : |(2646641781/5000000000 : ℝ)|=(2646641781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-831625537/5000000000 : ℝ)|^4673 ≤ (251350203283/2500000000000 : ℝ)^3649
        have hw : |(-831625537/5000000000 : ℝ)|=(831625537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084490647/2000000000 : ℝ)|^4673 ≤ (45667218603081/100000000000000 : ℝ)^3649
        have hw : |(1084490647/2000000000 : ℝ)|=(1084490647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s5_6 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293282701/10000000000 : ℝ)*x 0 + (338903341/625000000 : ℝ)*x 1 + (-1663251959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293282701/10000000000 : ℝ)^4673 ≤ (44278764021861/100000000000000 : ℝ)^3649 := by
    have hnat : (5293282701 : ℕ)^4673*100000000000000^3649 ≤ 44278764021861^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293282701 10000000000 44278764021861 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338903341/625000000 : ℝ)^4673 ≤ (178387581979/390625000000 : ℝ)^3649 := by
    have hnat : (338903341 : ℕ)^4673*390625000000^3649 ≤ 178387581979^3649*625000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338903341 625000000 178387581979 390625000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1663251959/10000000000 : ℝ)^4673 ≤ (2513503745551/25000000000000 : ℝ)^3649 := by
    have hnat : (1663251959 : ℕ)^4673*25000000000000^3649 ≤ 2513503745551^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1663251959 10000000000 2513503745551 25000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293282701/10000000000 : ℝ), (338903341/625000000 : ℝ), (-1663251959/10000000000 : ℝ)] ![(44278764021861/100000000000000 : ℝ), (178387581979/390625000000 : ℝ), (2513503745551/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293282701/10000000000 : ℝ)|^4673 ≤ (44278764021861/100000000000000 : ℝ)^3649
        have hw : |(5293282701/10000000000 : ℝ)|=(5293282701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338903341/625000000 : ℝ)|^4673 ≤ (178387581979/390625000000 : ℝ)^3649
        have hw : |(338903341/625000000 : ℝ)|=(338903341/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1663251959/10000000000 : ℝ)|^4673 ≤ (2513503745551/25000000000000 : ℝ)^3649
        have hw : |(-1663251959/10000000000 : ℝ)|=(1663251959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s5_7 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4235707979/10000000000 : ℝ)*x 0 + (560132769/1250000000 : ℝ)*x 1 + (400132549/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4235707979/10000000000 : ℝ)^4673 ≤ (16641872528759/50000000000000 : ℝ)^3649 := by
    have hnat : (4235707979 : ℕ)^4673*50000000000000^3649 ≤ 16641872528759^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235707979 10000000000 16641872528759 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560132769/1250000000 : ℝ)^4673 ≤ (35772542747733/100000000000000 : ℝ)^3649 := by
    have hnat : (560132769 : ℕ)^4673*100000000000000^3649 ≤ 35772542747733^3649*1250000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560132769 1250000000 35772542747733 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (400132549/1000000000 : ℝ)^4673 ≤ (3867964022771/12500000000000 : ℝ)^3649 := by
    have hnat : (400132549 : ℕ)^4673*12500000000000^3649 ≤ 3867964022771^3649*1000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400132549 1000000000 3867964022771 12500000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4235707979/10000000000 : ℝ), (560132769/1250000000 : ℝ), (400132549/1000000000 : ℝ)] ![(16641872528759/50000000000000 : ℝ), (35772542747733/100000000000000 : ℝ), (3867964022771/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4235707979/10000000000 : ℝ)|^4673 ≤ (16641872528759/50000000000000 : ℝ)^3649
        have hw : |(4235707979/10000000000 : ℝ)|=(4235707979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(560132769/1250000000 : ℝ)|^4673 ≤ (35772542747733/100000000000000 : ℝ)^3649
        have hw : |(560132769/1250000000 : ℝ)|=(560132769/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(400132549/1000000000 : ℝ)|^4673 ≤ (3867964022771/12500000000000 : ℝ)^3649
        have hw : |(400132549/1000000000 : ℝ)|=(400132549/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1588_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21184593/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1397/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5589/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7743/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1397/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7743/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1397/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7743/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1397/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7743/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1397/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7743/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1397/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7743/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1397/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1397/12500 : ℝ) ^ (4671/1024 : ℝ) ≤ (4557598634878359/100000000000000000000 : ℝ) := by
    have hpowers : (1397/12500 : ℝ)^4671 ≤ (4557598634878359/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1397 : ℕ)^4671*100000000000000000000^1024 ≤ 4557598634878359^1024*12500^4671 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1397 12500 4557598634878359 100000000000000000000 4671 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1397/12500 : ℝ)) (X := (4557598634878359/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7743/50000 : ℝ) ^ (4671/1024 : ℝ) ≤ (20178502156066873/100000000000000000000 : ℝ) := by
    have hpowers : (7743/50000 : ℝ)^4671 ≤ (20178502156066873/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7743 : ℕ)^4671*100000000000000000000^1024 ≤ 20178502156066873^1024*50000^4671 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7743 50000 20178502156066873 100000000000000000000 4671 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7743/50000 : ℝ)) (X := (20178502156066873/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004557598634878359/50000000000000000000 : ℝ) ≤ (2000039964161323/2000000000000000 : ℝ) ^ (4671/1024 : ℝ) := by
    have hpowers : (50004557598634878359/50000000000000000000 : ℝ)^1024 ≤ (2000039964161323/2000000000000000 : ℝ)^4671 := by
      have hnat : (50004557598634878359 : ℕ)^1024*2000000000000000^4671 ≤ 2000039964161323^4671*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004557598634878359 50000000000000000000 2000039964161323 2000000000000000 1024 4671 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000039964161323/2000000000000000 : ℝ)) (X := (50004557598634878359/50000000000000000000 : ℝ)) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6251546006299434077/6250000000000000000 : ℝ) ≤ (10000542224824629/10000000000000000 : ℝ) ^ (4671/1024 : ℝ) := by
    have hpowers : (6251546006299434077/6250000000000000000 : ℝ)^1024 ≤ (10000542224824629/10000000000000000 : ℝ)^4671 := by
      have hnat : (6251546006299434077 : ℕ)^1024*10000000000000000^4671 ≤ 10000542224824629^4671*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251546006299434077 6250000000000000000 10000542224824629 10000000000000000 1024 4671 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000542224824629/10000000000000000 : ℝ)) (X := (6251546006299434077/6250000000000000000 : ℝ)) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020178502156066873/50000000000000000000 : ℝ) ≤ (10000884628842643/10000000000000000 : ℝ) ^ (4671/1024 : ℝ) := by
    have hpowers : (50020178502156066873/50000000000000000000 : ℝ)^1024 ≤ (10000884628842643/10000000000000000 : ℝ)^4671 := by
      have hnat : (50020178502156066873 : ℕ)^1024*10000000000000000^4671 ≤ 10000884628842643^4671*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020178502156066873 50000000000000000000 10000884628842643 10000000000000000 1024 4671 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000884628842643/10000000000000000 : ℝ)) (X := (50020178502156066873/50000000000000000000 : ℝ)) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4557598634878359/100000000000000000000 : ℝ) ≤ ((21546603906532930861/21550000000000000000 : ℝ)+2*(171202009007/215500000000000 : ℝ)*(1397/12500 : ℝ))^(4671/1024 : ℝ) := by
    rw [show (21546603906532930861/21550000000000000000 : ℝ)+2*(171202009007/215500000000000 : ℝ)*(1397/12500 : ℝ)=(2000039964161323/2000000000000000 : ℝ) by norm_num, show 1+2*(4557598634878359/100000000000000000000 : ℝ)=(50004557598634878359/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20178502156066873/100000000000000000000 : ℝ)+(4557598634878359/100000000000000000000 : ℝ) ≤ ((21546603906532930861/21550000000000000000 : ℝ)+(171202009007/215500000000000 : ℝ)*((7743/50000 : ℝ)+(1397/12500 : ℝ)))^(4671/1024 : ℝ) := by
    rw [show (21546603906532930861/21550000000000000000 : ℝ)+(171202009007/215500000000000 : ℝ)*((7743/50000 : ℝ)+(1397/12500 : ℝ))=(10000542224824629/10000000000000000 : ℝ) by norm_num, show 1+(20178502156066873/100000000000000000000 : ℝ)+(4557598634878359/100000000000000000000 : ℝ)=(6251546006299434077/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20178502156066873/100000000000000000000 : ℝ) ≤ ((21546603906532930861/21550000000000000000 : ℝ)+2*(171202009007/215500000000000 : ℝ)*(7743/50000 : ℝ))^(4671/1024 : ℝ) := by
    rw [show (21546603906532930861/21550000000000000000 : ℝ)+2*(171202009007/215500000000000 : ℝ)*(7743/50000 : ℝ)=(10000884628842643/10000000000000000 : ℝ) by norm_num, show 1+2*(20178502156066873/100000000000000000000 : ℝ)=(50020178502156066873/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21546603906532930861/21550000000000000000 : ℝ)*(X 1 0+X 2 0)+(171202009007/215500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4671/1024 : ℝ)) (lo := (1397/12500 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (21546603906532930861/21550000000000000000 : ℝ)) (alpha := (171202009007/215500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21546603906532930861/21550000000000000000 : ℝ)*(X 0 1+X 2 1)+(171202009007/215500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4671/1024 : ℝ)) (lo := (1397/12500 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (21546603906532930861/21550000000000000000 : ℝ)) (alpha := (171202009007/215500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21546603906532930861/21550000000000000000 : ℝ)*(X 0 2+X 1 2)+(171202009007/215500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4671/1024 : ℝ)) (lo := (1397/12500 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (21546603906532930861/21550000000000000000 : ℝ)) (alpha := (171202009007/215500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-176131269/1000000000 : ℝ)*X 0 0+(5423522411/10000000000 : ℝ)*X 0 1+(5220627133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347073479/10000000000 : ℝ)*X 1 0+(-466269507/2500000000 : ℝ)*X 1 1+(5220627129/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336768363/2500000000 : ℝ)*X 2 0+(1044125431/2000000000 : ℝ)*X 2 1+(-1865078031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2117822967/5000000000 : ℝ)*X 0 0+(799754309/2000000000 : ℝ)*X 0 1+(4483596867/10000000000 : ℝ)*X 0 2+(2117822967/5000000000 : ℝ)*X 1 0+(799754309/2000000000 : ℝ)*X 1 1+(4483596867/10000000000 : ℝ)*X 1 2+(2117822967/5000000000 : ℝ)*X 2 0+(799754309/2000000000 : ℝ)*X 2 1+(4483596867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-88066943/500000000 : ℝ)*X 0 0+(1305421929/2500000000 : ℝ)*X 0 1+(5422453969/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646641781/5000000000 : ℝ)*X 1 0+(-831625537/5000000000 : ℝ)*X 1 1+(1084490647/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293282701/10000000000 : ℝ)*X 2 0+(338903341/625000000 : ℝ)*X 2 1+(-1663251959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4235707979/10000000000 : ℝ)*X 0 0+(560132769/1250000000 : ℝ)*X 0 1+(400132549/1000000000 : ℝ)*X 0 2+(4235707979/10000000000 : ℝ)*X 1 0+(560132769/1250000000 : ℝ)*X 1 1+(400132549/1000000000 : ℝ)*X 1 2+(4235707979/10000000000 : ℝ)*X 2 0+(560132769/1250000000 : ℝ)*X 2 1+(400132549/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14882558678242854118059/2155000000000000000000000000 : ℝ) := by norm_num
    linear_combination (591086053/50000000000000 : ℝ)*(base19) + (272674271/25000000000000 : ℝ)*(base23) + (4450613/12500000000000 : ℝ)*(lower2) + (86079203/50000000000000 : ℝ)*(upper3) + (5918133/5000000000000 : ℝ)*(upper5) + (699130595364939/20000000000000 : ℝ)*(major0) + (699130595364939/20000000000000 : ℝ)*(major1) + (699130595364939/20000000000000 : ℝ)*(major2) + (2464335609408623/50000000000000 : ℝ)*(sp0) + (4928689403457501/100000000000000 : ℝ)*(sp1) + (4928689494932523/100000000000000 : ℝ)*(sp2) + (1031303214125029/50000000000000 : ℝ)*(sp3) + (19366812361/100000000000000 : ℝ)*(sp4) + (8709567727/100000000000000 : ℝ)*(sp7) + (1031307568908893/50000000000000 : ℝ)*(f.failure) + (4928690585629607/100000000000000 : ℝ)*(f.sum) + (2949775674351/1077500000000000000000000000 : ℝ)*base66 + (326819160868217521/431000000000000000000000000000000 : ℝ)*base68 + (2555988839574782479/431000000000000000000000000000000 : ℝ)*base69 + (880261770103782479/431000000000000000000000000000000 : ℝ)*base71 + (725444579757/2155000000000000000000000000 : ℝ)*base74 + (762925842387217521/431000000000000000000000000000000 : ℝ)*base76 + (2466006462623217521/431000000000000000000000000000000 : ℝ)*base78 + (7275372406958782479/431000000000000000000000000000000 : ℝ)*base79 + (1707492583451/269375000000000000000000000 : ℝ)*base81 + (8535549/625000000000000000000 : ℝ)*base89 + (8535549/625000000000000000000 : ℝ)*base91 + (8535549/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2567775639737061211029500457/538750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (320902869/20000000000000 : ℝ)*(base19) + (714965483/100000000000000 : ℝ)*(base23) + (19738469/25000000000000 : ℝ)*(upper2) + (12174969/25000000000000 : ℝ)*(upper3) + (7507979/12500000000000 : ℝ)*(upper5) + (3532698447440879/100000000000000 : ℝ)*(major0) + (3532698447440879/100000000000000 : ℝ)*(major1) + (3532698447440879/100000000000000 : ℝ)*(major2) + (6623575429/100000000000000 : ℝ)*(sp0) + (11243735169/50000000000000 : ℝ)*(sp1) + (2490458120321813/50000000000000 : ℝ)*(sp4) + (1245224693058593/25000000000000 : ℝ)*(sp5) + (1245230537313393/25000000000000 : ℝ)*(sp6) + (2084473871790267/100000000000000 : ℝ)*(sp7) + (2084473871790267/100000000000000 : ℝ)*(f.failure) + (996184572843811/20000000000000 : ℝ)*(f.sum) + (16656555734333/673437500000000000000000000 : ℝ)*base65 + (3622842911837633181/2155000000000000000000000000000000 : ℝ)*base68 + (4779561491947633181/2155000000000000000000000000000000 : ℝ)*base70 + (18379393414037633181/2155000000000000000000000000000000 : ℝ)*base72 + (31286797243353/10775000000000000000000000000 : ℝ)*base73 + (19320265321452633181/2155000000000000000000000000000000 : ℝ)*base76 + (8233866771967633181/2155000000000000000000000000000000 : ℝ)*base78 + (23609014363127366819/2155000000000000000000000000000000 : ℝ)*base79 + (24360275008603/10775000000000000000000000000 : ℝ)*base81 + (256331/1250000000000000000000 : ℝ)*base89 + (256331/1250000000000000000000 : ℝ)*base91 + (256331/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1588_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21184593/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1397/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5589/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1588_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1588_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21184593/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7883/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10917/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5589/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1588_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1588_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1588_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21184593/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7883/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10917/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5589/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1588_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

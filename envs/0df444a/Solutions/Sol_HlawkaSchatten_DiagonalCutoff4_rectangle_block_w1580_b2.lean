-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1580_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:29:58.381263+00:00
-- url     : https://prove2.me/submissions/12212f28-c468-4f16-ac62-1c5650d51aab

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
theorem support_rectangle_w1580_box_0 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-784913039/5000000000 : ℝ)*x 0 + (1348880873/2500000000 : ℝ)*x 1 + (5395522893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (784913039/5000000000 : ℝ)^4657 ≤ (1164403996257/12500000000000 : ℝ)^3633 := by
    have hnat : (784913039 : ℕ)^4657*12500000000000^3633 ≤ 1164403996257^3633*5000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784913039 5000000000 1164403996257 12500000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348880873/2500000000 : ℝ)^4657 ≤ (9068477446903/20000000000000 : ℝ)^3633 := by
    have hnat : (1348880873 : ℕ)^4657*20000000000000^3633 ≤ 9068477446903^3633*2500000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348880873 2500000000 9068477446903 20000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395522893/10000000000 : ℝ)^4657 ≤ (2267119039093/5000000000000 : ℝ)^3633 := by
    have hnat : (5395522893 : ℕ)^4657*5000000000000^3633 ≤ 2267119039093^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395522893 10000000000 2267119039093 5000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-784913039/5000000000 : ℝ), (1348880873/2500000000 : ℝ), (5395522893/10000000000 : ℝ)] ![(1164403996257/12500000000000 : ℝ), (9068477446903/20000000000000 : ℝ), (2267119039093/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-784913039/5000000000 : ℝ)|^4657 ≤ (1164403996257/12500000000000 : ℝ)^3633
        have hw : |(-784913039/5000000000 : ℝ)|=(784913039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348880873/2500000000 : ℝ)|^4657 ≤ (9068477446903/20000000000000 : ℝ)^3633
        have hw : |(1348880873/2500000000 : ℝ)|=(1348880873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395522893/10000000000 : ℝ)|^4657 ≤ (2267119039093/5000000000000 : ℝ)^3633
        have hw : |(5395522893/10000000000 : ℝ)|=(5395522893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_box_1 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271134953/10000000000 : ℝ)*x 0 + (-1742792427/10000000000 : ℝ)*x 1 + (2697761683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271134953/10000000000 : ℝ)^4657 ≤ (44006804535331/100000000000000 : ℝ)^3633 := by
    have hnat : (5271134953 : ℕ)^4657*100000000000000^3633 ≤ 44006804535331^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271134953 10000000000 44006804535331 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1742792427/10000000000 : ℝ)^4657 ≤ (1331351196199/12500000000000 : ℝ)^3633 := by
    have hnat : (1742792427 : ℕ)^4657*12500000000000^3633 ≤ 1331351196199^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742792427 10000000000 1331351196199 12500000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697761683/5000000000 : ℝ)^4657 ≤ (11335596469299/25000000000000 : ℝ)^3633 := by
    have hnat : (2697761683 : ℕ)^4657*25000000000000^3633 ≤ 11335596469299^3633*5000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697761683 5000000000 11335596469299 25000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271134953/10000000000 : ℝ), (-1742792427/10000000000 : ℝ), (2697761683/5000000000 : ℝ)] ![(44006804535331/100000000000000 : ℝ), (1331351196199/12500000000000 : ℝ), (11335596469299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271134953/10000000000 : ℝ)|^4657 ≤ (44006804535331/100000000000000 : ℝ)^3633
        have hw : |(5271134953/10000000000 : ℝ)|=(5271134953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1742792427/10000000000 : ℝ)|^4657 ≤ (1331351196199/12500000000000 : ℝ)^3633
        have hw : |(-1742792427/10000000000 : ℝ)|=(1742792427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697761683/5000000000 : ℝ)|^4657 ≤ (11335596469299/25000000000000 : ℝ)^3633
        have hw : |(2697761683/5000000000 : ℝ)|=(2697761683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_box_2 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054227043/2000000000 : ℝ)*x 0 + (5395523383/10000000000 : ℝ)*x 1 + (-871396023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054227043/2000000000 : ℝ)^4657 ≤ (27504254587/62500000000 : ℝ)^3633 := by
    have hnat : (1054227043 : ℕ)^4657*62500000000^3633 ≤ 27504254587^3633*2000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054227043 2000000000 27504254587 62500000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395523383/10000000000 : ℝ)^4657 ≤ (22671193030163/50000000000000 : ℝ)^3633 := by
    have hnat : (5395523383 : ℕ)^4657*50000000000000^3633 ≤ 22671193030163^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395523383 10000000000 22671193030163 50000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (871396023/5000000000 : ℝ)^4657 ≤ (10650806584877/100000000000000 : ℝ)^3633 := by
    have hnat : (871396023 : ℕ)^4657*100000000000000^3633 ≤ 10650806584877^3633*5000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871396023 5000000000 10650806584877 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054227043/2000000000 : ℝ), (5395523383/10000000000 : ℝ), (-871396023/5000000000 : ℝ)] ![(27504254587/62500000000 : ℝ), (22671193030163/50000000000000 : ℝ), (10650806584877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054227043/2000000000 : ℝ)|^4657 ≤ (27504254587/62500000000 : ℝ)^3633
        have hw : |(1054227043/2000000000 : ℝ)|=(1054227043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395523383/10000000000 : ℝ)|^4657 ≤ (22671193030163/50000000000000 : ℝ)^3633
        have hw : |(5395523383/10000000000 : ℝ)|=(5395523383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-871396023/5000000000 : ℝ)|^4657 ≤ (10650806584877/100000000000000 : ℝ)^3633
        have hw : |(-871396023/5000000000 : ℝ)|=(871396023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_box_3 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (277465563/625000000 : ℝ)*x 0 + (1036385017/2500000000 : ℝ)*x 1 + (414554027/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (277465563/625000000 : ℝ)^4657 ≤ (7062443485429/20000000000000 : ℝ)^3633 := by
    have hnat : (277465563 : ℕ)^4657*20000000000000^3633 ≤ 7062443485429^3633*625000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277465563 625000000 7062443485429 20000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036385017/2500000000 : ℝ)^4657 ≤ (32343890272837/100000000000000 : ℝ)^3633 := by
    have hnat : (1036385017 : ℕ)^4657*100000000000000^3633 ≤ 32343890272837^3633*2500000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036385017 2500000000 32343890272837 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (414554027/1000000000 : ℝ)^4657 ≤ (32343892293079/100000000000000 : ℝ)^3633 := by
    have hnat : (414554027 : ℕ)^4657*100000000000000^3633 ≤ 32343892293079^3633*1000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414554027 1000000000 32343892293079 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(277465563/625000000 : ℝ), (1036385017/2500000000 : ℝ), (414554027/1000000000 : ℝ)] ![(7062443485429/20000000000000 : ℝ), (32343890272837/100000000000000 : ℝ), (32343892293079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(277465563/625000000 : ℝ)|^4657 ≤ (7062443485429/20000000000000 : ℝ)^3633
        have hw : |(277465563/625000000 : ℝ)|=(277465563/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036385017/2500000000 : ℝ)|^4657 ≤ (32343890272837/100000000000000 : ℝ)^3633
        have hw : |(1036385017/2500000000 : ℝ)|=(1036385017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(414554027/1000000000 : ℝ)|^4657 ≤ (32343892293079/100000000000000 : ℝ)^3633
        have hw : |(414554027/1000000000 : ℝ)|=(414554027/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_box_4 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1979644181/10000000000 : ℝ)*x 0 + (81956529/156250000 : ℝ)*x 1 + (5245217747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1979644181/10000000000 : ℝ)^4657 ≤ (6270363027351/50000000000000 : ℝ)^3633 := by
    have hnat : (1979644181 : ℕ)^4657*50000000000000^3633 ≤ 6270363027351^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1979644181 10000000000 6270363027351 50000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81956529/156250000 : ℝ)^4657 ≤ (43729637548909/100000000000000 : ℝ)^3633 := by
    have hnat : (81956529 : ℕ)^4657*100000000000000^3633 ≤ 43729637548909^3633*156250000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81956529 156250000 43729637548909 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245217747/10000000000 : ℝ)^4657 ≤ (43729636384033/100000000000000 : ℝ)^3633 := by
    have hnat : (5245217747 : ℕ)^4657*100000000000000^3633 ≤ 43729636384033^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245217747 10000000000 43729636384033 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1979644181/10000000000 : ℝ), (81956529/156250000 : ℝ), (5245217747/10000000000 : ℝ)] ![(6270363027351/50000000000000 : ℝ), (43729637548909/100000000000000 : ℝ), (43729636384033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1979644181/10000000000 : ℝ)|^4657 ≤ (6270363027351/50000000000000 : ℝ)^3633
        have hw : |(-1979644181/10000000000 : ℝ)|=(1979644181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81956529/156250000 : ℝ)|^4657 ≤ (43729637548909/100000000000000 : ℝ)^3633
        have hw : |(81956529/156250000 : ℝ)|=(81956529/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245217747/10000000000 : ℝ)|^4657 ≤ (43729636384033/100000000000000 : ℝ)^3633
        have hw : |(5245217747/10000000000 : ℝ)|=(5245217747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_box_5 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687623401/5000000000 : ℝ)*x 0 + (-1805723023/10000000000 : ℝ)*x 1 + (655652219/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687623401/5000000000 : ℝ)^4657 ≤ (45124074829461/100000000000000 : ℝ)^3633 := by
    have hnat : (2687623401 : ℕ)^4657*100000000000000^3633 ≤ 45124074829461^3633*5000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687623401 5000000000 45124074829461 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1805723023/10000000000 : ℝ)^4657 ≤ (5573144359553/50000000000000 : ℝ)^3633 := by
    have hnat : (1805723023 : ℕ)^4657*50000000000000^3633 ≤ 5573144359553^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1805723023 10000000000 5573144359553 50000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655652219/1250000000 : ℝ)^4657 ≤ (43729636437467/100000000000000 : ℝ)^3633 := by
    have hnat : (655652219 : ℕ)^4657*100000000000000^3633 ≤ 43729636437467^3633*1250000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655652219 1250000000 43729636437467 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687623401/5000000000 : ℝ), (-1805723023/10000000000 : ℝ), (655652219/1250000000 : ℝ)] ![(45124074829461/100000000000000 : ℝ), (5573144359553/50000000000000 : ℝ), (43729636437467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687623401/5000000000 : ℝ)|^4657 ≤ (45124074829461/100000000000000 : ℝ)^3633
        have hw : |(2687623401/5000000000 : ℝ)|=(2687623401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1805723023/10000000000 : ℝ)|^4657 ≤ (5573144359553/50000000000000 : ℝ)^3633
        have hw : |(-1805723023/10000000000 : ℝ)|=(1805723023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655652219/1250000000 : ℝ)|^4657 ≤ (43729636437467/100000000000000 : ℝ)^3633
        have hw : |(655652219/1250000000 : ℝ)|=(655652219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_box_6 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5375246761/10000000000 : ℝ)*x 0 + (1049043557/2000000000 : ℝ)*x 1 + (-1805723033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375246761/10000000000 : ℝ)^4657 ≤ (22562037194131/50000000000000 : ℝ)^3633 := by
    have hnat : (5375246761 : ℕ)^4657*50000000000000^3633 ≤ 22562037194131^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375246761 10000000000 22562037194131 50000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049043557/2000000000 : ℝ)^4657 ≤ (5466204598767/12500000000000 : ℝ)^3633 := by
    have hnat : (1049043557 : ℕ)^4657*12500000000000^3633 ≤ 5466204598767^3633*2000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049043557 2000000000 5466204598767 12500000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1805723033/10000000000 : ℝ)^4657 ≤ (1393286099779/12500000000000 : ℝ)^3633 := by
    have hnat : (1805723033 : ℕ)^4657*12500000000000^3633 ≤ 1393286099779^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1805723033 10000000000 1393286099779 12500000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375246761/10000000000 : ℝ), (1049043557/2000000000 : ℝ), (-1805723033/10000000000 : ℝ)] ![(22562037194131/50000000000000 : ℝ), (5466204598767/12500000000000 : ℝ), (1393286099779/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375246761/10000000000 : ℝ)|^4657 ≤ (22562037194131/50000000000000 : ℝ)^3633
        have hw : |(5375246761/10000000000 : ℝ)|=(5375246761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049043557/2000000000 : ℝ)|^4657 ≤ (5466204598767/12500000000000 : ℝ)^3633
        have hw : |(1049043557/2000000000 : ℝ)|=(1049043557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1805723033/10000000000 : ℝ)|^4657 ≤ (1393286099779/12500000000000 : ℝ)^3633
        have hw : |(-1805723033/10000000000 : ℝ)|=(1805723033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_box_7 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4036061801/10000000000 : ℝ)*x 0 + (2173553703/5000000000 : ℝ)*x 1 + (4347107383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4036061801/10000000000 : ℝ)^4657 ≤ (31253077659207/100000000000000 : ℝ)^3633 := by
    have hnat : (4036061801 : ℕ)^4657*100000000000000^3633 ≤ 31253077659207^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4036061801 10000000000 31253077659207 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2173553703/5000000000 : ℝ)^4657 ≤ (34373461280553/100000000000000 : ℝ)^3633 := by
    have hnat : (2173553703 : ℕ)^4657*100000000000000^3633 ≤ 34373461280553^3633*5000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173553703 5000000000 34373461280553 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4347107383/10000000000 : ℝ)^4657 ≤ (17186730523713/50000000000000 : ℝ)^3633 := by
    have hnat : (4347107383 : ℕ)^4657*50000000000000^3633 ≤ 17186730523713^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347107383 10000000000 17186730523713 50000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4036061801/10000000000 : ℝ), (2173553703/5000000000 : ℝ), (4347107383/10000000000 : ℝ)] ![(31253077659207/100000000000000 : ℝ), (34373461280553/100000000000000 : ℝ), (17186730523713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4036061801/10000000000 : ℝ)|^4657 ≤ (31253077659207/100000000000000 : ℝ)^3633
        have hw : |(4036061801/10000000000 : ℝ)|=(4036061801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2173553703/5000000000 : ℝ)|^4657 ≤ (34373461280553/100000000000000 : ℝ)^3633
        have hw : |(2173553703/5000000000 : ℝ)|=(2173553703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4347107383/10000000000 : ℝ)|^4657 ≤ (17186730523713/50000000000000 : ℝ)^3633
        have hw : |(4347107383/10000000000 : ℝ)|=(4347107383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_box_8 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-378547251/2000000000 : ℝ)*x 0 + (5139219213/10000000000 : ℝ)*x 1 + (676970113/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (378547251/2000000000 : ℝ)^4657 ≤ (11839413682641/100000000000000 : ℝ)^3633 := by
    have hnat : (378547251 : ℕ)^4657*100000000000000^3633 ≤ 11839413682641^3633*2000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378547251 2000000000 11839413682641 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5139219213/10000000000 : ℝ)^4657 ≤ (42600078862119/100000000000000 : ℝ)^3633 := by
    have hnat : (5139219213 : ℕ)^4657*100000000000000^3633 ≤ 42600078862119^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139219213 10000000000 42600078862119 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676970113/1250000000 : ℝ)^4657 ≤ (22780253722537/50000000000000 : ℝ)^3633 := by
    have hnat : (676970113 : ℕ)^4657*50000000000000^3633 ≤ 22780253722537^3633*1250000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676970113 1250000000 22780253722537 50000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-378547251/2000000000 : ℝ), (5139219213/10000000000 : ℝ), (676970113/1250000000 : ℝ)] ![(11839413682641/100000000000000 : ℝ), (42600078862119/100000000000000 : ℝ), (22780253722537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-378547251/2000000000 : ℝ)|^4657 ≤ (11839413682641/100000000000000 : ℝ)^3633
        have hw : |(-378547251/2000000000 : ℝ)|=(378547251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5139219213/10000000000 : ℝ)|^4657 ≤ (42600078862119/100000000000000 : ℝ)^3633
        have hw : |(5139219213/10000000000 : ℝ)|=(5139219213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676970113/1250000000 : ℝ)|^4657 ≤ (22780253722537/50000000000000 : ℝ)^3633
        have hw : |(676970113/1250000000 : ℝ)|=(676970113/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_box_9 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257114257/10000000000 : ℝ)*x 0 + (-1734089379/10000000000 : ℝ)*x 1 + (1083152171/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257114257/10000000000 : ℝ)^4657 ≤ (2741050889623/6250000000000 : ℝ)^3633 := by
    have hnat : (5257114257 : ℕ)^4657*6250000000000^3633 ≤ 2741050889623^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257114257 10000000000 2741050889623 6250000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1734089379/10000000000 : ℝ)^4657 ≤ (10582678837213/100000000000000 : ℝ)^3633 := by
    have hnat : (1734089379 : ℕ)^4657*100000000000000^3633 ≤ 10582678837213^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1734089379 10000000000 10582678837213 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083152171/2000000000 : ℝ)^4657 ≤ (4556050691667/10000000000000 : ℝ)^3633 := by
    have hnat : (1083152171 : ℕ)^4657*10000000000000^3633 ≤ 4556050691667^3633*2000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083152171 2000000000 4556050691667 10000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257114257/10000000000 : ℝ), (-1734089379/10000000000 : ℝ), (1083152171/2000000000 : ℝ)] ![(2741050889623/6250000000000 : ℝ), (10582678837213/100000000000000 : ℝ), (4556050691667/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257114257/10000000000 : ℝ)|^4657 ≤ (2741050889623/6250000000000 : ℝ)^3633
        have hw : |(5257114257/10000000000 : ℝ)|=(5257114257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1734089379/10000000000 : ℝ)|^4657 ≤ (10582678837213/100000000000000 : ℝ)^3633
        have hw : |(-1734089379/10000000000 : ℝ)|=(1734089379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083152171/2000000000 : ℝ)|^4657 ≤ (4556050691667/10000000000000 : ℝ)^3633
        have hw : |(1083152171/2000000000 : ℝ)|=(1083152171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_box_10 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628557089/5000000000 : ℝ)*x 0 + (5415760869/10000000000 : ℝ)*x 1 + (-1734089467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628557089/5000000000 : ℝ)^4657 ≤ (43856813389161/100000000000000 : ℝ)^3633 := by
    have hnat : (2628557089 : ℕ)^4657*100000000000000^3633 ≤ 43856813389161^3633*5000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628557089 5000000000 43856813389161 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415760869/10000000000 : ℝ)^4657 ≤ (22780253533821/50000000000000 : ℝ)^3633 := by
    have hnat : (5415760869 : ℕ)^4657*50000000000000^3633 ≤ 22780253533821^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415760869 10000000000 22780253533821 50000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1734089467/10000000000 : ℝ)^4657 ≤ (1322834940703/12500000000000 : ℝ)^3633 := by
    have hnat : (1734089467 : ℕ)^4657*12500000000000^3633 ≤ 1322834940703^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1734089467 10000000000 1322834940703 12500000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628557089/5000000000 : ℝ), (5415760869/10000000000 : ℝ), (-1734089467/10000000000 : ℝ)] ![(43856813389161/100000000000000 : ℝ), (22780253533821/50000000000000 : ℝ), (1322834940703/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628557089/5000000000 : ℝ)|^4657 ≤ (43856813389161/100000000000000 : ℝ)^3633
        have hw : |(2628557089/5000000000 : ℝ)|=(2628557089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415760869/10000000000 : ℝ)|^4657 ≤ (22780253533821/50000000000000 : ℝ)^3633
        have hw : |(5415760869/10000000000 : ℝ)|=(5415760869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1734089467/10000000000 : ℝ)|^4657 ≤ (1322834940703/12500000000000 : ℝ)^3633
        have hw : |(-1734089467/10000000000 : ℝ)|=(1734089467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_box_11 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4492618961/10000000000 : ℝ)*x 0 + (4118366133/10000000000 : ℝ)*x 1 + (164734649/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4492618961/10000000000 : ℝ)^4657 ≤ (3585525935997/10000000000000 : ℝ)^3633 := by
    have hnat : (4492618961 : ℕ)^4657*10000000000000^3633 ≤ 3585525935997^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492618961 10000000000 3585525935997 10000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4118366133/10000000000 : ℝ)^4657 ≤ (3207236985491/10000000000000 : ℝ)^3633 := by
    have hnat : (4118366133 : ℕ)^4657*10000000000000^3633 ≤ 3207236985491^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4118366133 10000000000 3207236985491 10000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164734649/400000000 : ℝ)^4657 ≤ (8018092693329/25000000000000 : ℝ)^3633 := by
    have hnat : (164734649 : ℕ)^4657*25000000000000^3633 ≤ 8018092693329^3633*400000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164734649 400000000 8018092693329 25000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4492618961/10000000000 : ℝ), (4118366133/10000000000 : ℝ), (164734649/400000000 : ℝ)] ![(3585525935997/10000000000000 : ℝ), (3207236985491/10000000000000 : ℝ), (8018092693329/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4492618961/10000000000 : ℝ)|^4657 ≤ (3585525935997/10000000000000 : ℝ)^3633
        have hw : |(4492618961/10000000000 : ℝ)|=(4492618961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4118366133/10000000000 : ℝ)|^4657 ≤ (3207236985491/10000000000000 : ℝ)^3633
        have hw : |(4118366133/10000000000 : ℝ)|=(4118366133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164734649/400000000 : ℝ)|^4657 ≤ (8018092693329/25000000000000 : ℝ)^3633
        have hw : |(164734649/400000000 : ℝ)|=(164734649/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_box_12 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1656350849/10000000000 : ℝ)*x 0 + (5498319859/10000000000 : ℝ)*x 1 + (326885497/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1656350849/10000000000 : ℝ)^4657 ≤ (2494606543823/25000000000000 : ℝ)^3633 := by
    have hnat : (1656350849 : ℕ)^4657*25000000000000^3633 ≤ 2494606543823^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1656350849 10000000000 2494606543823 25000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5498319859/10000000000 : ℝ)^4657 ≤ (46452708528787/100000000000000 : ℝ)^3633 := by
    have hnat : (5498319859 : ℕ)^4657*100000000000000^3633 ≤ 46452708528787^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498319859 10000000000 46452708528787 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326885497/625000000 : ℝ)^4657 ≤ (21784432639007/50000000000000 : ℝ)^3633 := by
    have hnat : (326885497 : ℕ)^4657*50000000000000^3633 ≤ 21784432639007^3633*625000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326885497 625000000 21784432639007 50000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1656350849/10000000000 : ℝ), (5498319859/10000000000 : ℝ), (326885497/625000000 : ℝ)] ![(2494606543823/25000000000000 : ℝ), (46452708528787/100000000000000 : ℝ), (21784432639007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1656350849/10000000000 : ℝ)|^4657 ≤ (2494606543823/25000000000000 : ℝ)^3633
        have hw : |(-1656350849/10000000000 : ℝ)|=(1656350849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5498319859/10000000000 : ℝ)|^4657 ≤ (46452708528787/100000000000000 : ℝ)^3633
        have hw : |(5498319859/10000000000 : ℝ)|=(5498319859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326885497/625000000 : ℝ)|^4657 ≤ (21784432639007/50000000000000 : ℝ)^3633
        have hw : |(326885497/625000000 : ℝ)|=(326885497/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_box_13 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385671907/10000000000 : ℝ)*x 0 + (-90592763/500000000 : ℝ)*x 1 + (2615084501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385671907/10000000000 : ℝ)^4657 ≤ (9047257909027/20000000000000 : ℝ)^3633 := by
    have hnat : (5385671907 : ℕ)^4657*20000000000000^3633 ≤ 9047257909027^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385671907 10000000000 9047257909027 20000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90592763/500000000 : ℝ)^4657 ≤ (699677121791/6250000000000 : ℝ)^3633 := by
    have hnat : (90592763 : ℕ)^4657*6250000000000^3633 ≤ 699677121791^3633*500000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90592763 500000000 699677121791 6250000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615084501/5000000000 : ℝ)^4657 ≤ (10892219122553/25000000000000 : ℝ)^3633 := by
    have hnat : (2615084501 : ℕ)^4657*25000000000000^3633 ≤ 10892219122553^3633*5000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615084501 5000000000 10892219122553 25000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385671907/10000000000 : ℝ), (-90592763/500000000 : ℝ), (2615084501/5000000000 : ℝ)] ![(9047257909027/20000000000000 : ℝ), (699677121791/6250000000000 : ℝ), (10892219122553/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385671907/10000000000 : ℝ)|^4657 ≤ (9047257909027/20000000000000 : ℝ)^3633
        have hw : |(5385671907/10000000000 : ℝ)|=(5385671907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-90592763/500000000 : ℝ)|^4657 ≤ (699677121791/6250000000000 : ℝ)^3633
        have hw : |(-90592763/500000000 : ℝ)|=(90592763/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615084501/5000000000 : ℝ)|^4657 ≤ (10892219122553/25000000000000 : ℝ)^3633
        have hw : |(2615084501/5000000000 : ℝ)|=(2615084501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_box_14 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692836199/5000000000 : ℝ)*x 0 + (5230168347/10000000000 : ℝ)*x 1 + (-452963869/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692836199/5000000000 : ℝ)^4657 ≤ (45236294831649/100000000000000 : ℝ)^3633 := by
    have hnat : (2692836199 : ℕ)^4657*100000000000000^3633 ≤ 45236294831649^3633*5000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692836199 5000000000 45236294831649 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230168347/10000000000 : ℝ)^4657 ≤ (340381792937/781250000000 : ℝ)^3633 := by
    have hnat : (5230168347 : ℕ)^4657*781250000000^3633 ≤ 340381792937^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230168347 10000000000 340381792937 781250000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (452963869/2500000000 : ℝ)^4657 ≤ (5597417829707/50000000000000 : ℝ)^3633 := by
    have hnat : (452963869 : ℕ)^4657*50000000000000^3633 ≤ 5597417829707^3633*2500000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452963869 2500000000 5597417829707 50000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692836199/5000000000 : ℝ), (5230168347/10000000000 : ℝ), (-452963869/2500000000 : ℝ)] ![(45236294831649/100000000000000 : ℝ), (340381792937/781250000000 : ℝ), (5597417829707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692836199/5000000000 : ℝ)|^4657 ≤ (45236294831649/100000000000000 : ℝ)^3633
        have hw : |(2692836199/5000000000 : ℝ)|=(2692836199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230168347/10000000000 : ℝ)|^4657 ≤ (340381792937/781250000000 : ℝ)^3633
        have hw : |(5230168347/10000000000 : ℝ)|=(5230168347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-452963869/2500000000 : ℝ)|^4657 ≤ (5597417829707/50000000000000 : ℝ)^3633
        have hw : |(-452963869/2500000000 : ℝ)|=(452963869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1580_box_15 (p : ℝ) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (998702193/2500000000 : ℝ)*x 0 + (4367264667/10000000000 : ℝ)*x 1 + (218363211/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (998702193/2500000000 : ℝ)^4657 ≤ (7711047479747/25000000000000 : ℝ)^3633 := by
    have hnat : (998702193 : ℕ)^4657*25000000000000^3633 ≤ 7711047479747^3633*2500000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998702193 2500000000 7711047479747 25000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4367264667/10000000000 : ℝ)^4657 ≤ (6915581459399/20000000000000 : ℝ)^3633 := by
    have hnat : (4367264667 : ℕ)^4657*20000000000000^3633 ≤ 6915581459399^3633*10000000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367264667 10000000000 6915581459399 20000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218363211/500000000 : ℝ)^4657 ≤ (34577902760321/100000000000000 : ℝ)^3633 := by
    have hnat : (218363211 : ℕ)^4657*100000000000000^3633 ≤ 34577902760321^3633*500000000^4657 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218363211 500000000 34577902760321 100000000000000 4657 3633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4657/1024 : ℝ)) 4657 3633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(998702193/2500000000 : ℝ), (4367264667/10000000000 : ℝ), (218363211/500000000 : ℝ)] ![(7711047479747/25000000000000 : ℝ), (6915581459399/20000000000000 : ℝ), (34577902760321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(998702193/2500000000 : ℝ)|^4657 ≤ (7711047479747/25000000000000 : ℝ)^3633
        have hw : |(998702193/2500000000 : ℝ)|=(998702193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4367264667/10000000000 : ℝ)|^4657 ≤ (6915581459399/20000000000000 : ℝ)^3633
        have hw : |(4367264667/10000000000 : ℝ)|=(4367264667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218363211/500000000 : ℝ)|^4657 ≤ (34577902760321/100000000000000 : ℝ)^3633
        have hw : |(218363211/500000000 : ℝ)|=(218363211/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1580_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21104071/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11153/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63847/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1179/2000 : ℝ) ∧ (81019/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (86427/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11153/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11153/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11153/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11153/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11153/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11153/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11153/100000 : ℝ) ^ (4655/1024 : ℝ) ≤ (4672393676358409/100000000000000000000 : ℝ) := by
    have hpowers : (11153/100000 : ℝ)^4655 ≤ (4672393676358409/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11153 : ℕ)^4655*100000000000000000000^1024 ≤ 4672393676358409^1024*100000^4655 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11153 100000 4672393676358409 100000000000000000000 4655 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11153/100000 : ℝ)) (X := (4672393676358409/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4655 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4655/1024 : ℝ) ≤ (10381524643526883/50000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4655 ≤ (10381524643526883/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4655*50000000000000000000^1024 ≤ 10381524643526883^1024*25000^4655 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 10381524643526883 50000000000000000000 4655 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (10381524643526883/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4655 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004672393676358409/50000000000000000000 : ℝ) ≤ (250005138943887/250000000000000 : ℝ) ^ (4655/1024 : ℝ) := by
    have hpowers : (50004672393676358409/50000000000000000000 : ℝ)^1024 ≤ (250005138943887/250000000000000 : ℝ)^4655 := by
      have hnat : (50004672393676358409 : ℕ)^1024*250000000000000^4655 ≤ 250005138943887^4655*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004672393676358409 50000000000000000000 250005138943887 250000000000000 1024 4655 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250005138943887/250000000000000 : ℝ)) (X := (50004672393676358409/50000000000000000000 : ℝ)) (by norm_num) 4655 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001017417718536487/4000000000000000000 : ℝ) ≤ (500027973480351/500000000000000 : ℝ) ^ (4655/1024 : ℝ) := by
    have hpowers : (4001017417718536487/4000000000000000000 : ℝ)^1024 ≤ (500027973480351/500000000000000 : ℝ)^4655 := by
      have hnat : (4001017417718536487 : ℕ)^1024*500000000000000^4655 ≤ 500027973480351^4655*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001017417718536487 4000000000000000000 500027973480351 500000000000000 1024 4655 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500027973480351/500000000000000 : ℝ)) (X := (4001017417718536487/4000000000000000000 : ℝ)) (by norm_num) 4655 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010381524643526883/25000000000000000000 : ℝ) ≤ (15626427158529/15625000000000 : ℝ) ^ (4655/1024 : ℝ) := by
    have hpowers : (25010381524643526883/25000000000000000000 : ℝ)^1024 ≤ (15626427158529/15625000000000 : ℝ)^4655 := by
      have hnat : (25010381524643526883 : ℕ)^1024*15625000000000^4655 ≤ 15626427158529^4655*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010381524643526883 25000000000000000000 15626427158529 15625000000000 1024 4655 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (15626427158529/15625000000000 : ℝ)) (X := (25010381524643526883/25000000000000000000 : ℝ)) (by norm_num) 4655 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4672393676358409/100000000000000000000 : ℝ) ≤ ((270643724455490829/270687500000000000 : ℝ)+2*(17695592577/21655000000000 : ℝ)*(11153/100000 : ℝ))^(4655/1024 : ℝ) := by
    rw [show (270643724455490829/270687500000000000 : ℝ)+2*(17695592577/21655000000000 : ℝ)*(11153/100000 : ℝ)=(250005138943887/250000000000000 : ℝ) by norm_num, show 1+2*(4672393676358409/100000000000000000000 : ℝ)=(50004672393676358409/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10381524643526883/50000000000000000000 : ℝ)+(4672393676358409/100000000000000000000 : ℝ) ≤ ((270643724455490829/270687500000000000 : ℝ)+(17695592577/21655000000000 : ℝ)*((3871/25000 : ℝ)+(11153/100000 : ℝ)))^(4655/1024 : ℝ) := by
    rw [show (270643724455490829/270687500000000000 : ℝ)+(17695592577/21655000000000 : ℝ)*((3871/25000 : ℝ)+(11153/100000 : ℝ))=(500027973480351/500000000000000 : ℝ) by norm_num, show 1+(10381524643526883/50000000000000000000 : ℝ)+(4672393676358409/100000000000000000000 : ℝ)=(4001017417718536487/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10381524643526883/50000000000000000000 : ℝ) ≤ ((270643724455490829/270687500000000000 : ℝ)+2*(17695592577/21655000000000 : ℝ)*(3871/25000 : ℝ))^(4655/1024 : ℝ) := by
    rw [show (270643724455490829/270687500000000000 : ℝ)+2*(17695592577/21655000000000 : ℝ)*(3871/25000 : ℝ)=(15626427158529/15625000000000 : ℝ) by norm_num, show 1+2*(10381524643526883/50000000000000000000 : ℝ)=(25010381524643526883/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (270643724455490829/270687500000000000 : ℝ)*(X 1 0+X 2 0)+(17695592577/21655000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4655/1024 : ℝ)) (lo := (11153/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (270643724455490829/270687500000000000 : ℝ)) (alpha := (17695592577/21655000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (270643724455490829/270687500000000000 : ℝ)*(X 0 1+X 2 1)+(17695592577/21655000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4655/1024 : ℝ)) (lo := (11153/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (270643724455490829/270687500000000000 : ℝ)) (alpha := (17695592577/21655000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (270643724455490829/270687500000000000 : ℝ)*(X 0 2+X 1 2)+(17695592577/21655000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4655/1024 : ℝ)) (lo := (11153/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (270643724455490829/270687500000000000 : ℝ)) (alpha := (17695592577/21655000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-784913039/5000000000 : ℝ)*X 0 0+(1348880873/2500000000 : ℝ)*X 0 1+(5395522893/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5271134953/10000000000 : ℝ)*X 1 0+(-1742792427/10000000000 : ℝ)*X 1 1+(2697761683/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1054227043/2000000000 : ℝ)*X 2 0+(5395523383/10000000000 : ℝ)*X 2 1+(-871396023/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((277465563/625000000 : ℝ)*X 0 0+(1036385017/2500000000 : ℝ)*X 0 1+(414554027/1000000000 : ℝ)*X 0 2+(277465563/625000000 : ℝ)*X 1 0+(1036385017/2500000000 : ℝ)*X 1 1+(414554027/1000000000 : ℝ)*X 1 2+(277465563/625000000 : ℝ)*X 2 0+(1036385017/2500000000 : ℝ)*X 2 1+(414554027/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1979644181/10000000000 : ℝ)*X 0 0+(81956529/156250000 : ℝ)*X 0 1+(5245217747/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2687623401/5000000000 : ℝ)*X 1 0+(-1805723023/10000000000 : ℝ)*X 1 1+(655652219/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5375246761/10000000000 : ℝ)*X 2 0+(1049043557/2000000000 : ℝ)*X 2 1+(-1805723033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4036061801/10000000000 : ℝ)*X 0 0+(2173553703/5000000000 : ℝ)*X 0 1+(4347107383/10000000000 : ℝ)*X 0 2+(4036061801/10000000000 : ℝ)*X 1 0+(2173553703/5000000000 : ℝ)*X 1 1+(4347107383/10000000000 : ℝ)*X 1 2+(4036061801/10000000000 : ℝ)*X 2 0+(2173553703/5000000000 : ℝ)*X 2 1+(4347107383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-378547251/2000000000 : ℝ)*X 0 0+(5139219213/10000000000 : ℝ)*X 0 1+(676970113/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5257114257/10000000000 : ℝ)*X 1 0+(-1734089379/10000000000 : ℝ)*X 1 1+(1083152171/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2628557089/5000000000 : ℝ)*X 2 0+(5415760869/10000000000 : ℝ)*X 2 1+(-1734089467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4492618961/10000000000 : ℝ)*X 0 0+(4118366133/10000000000 : ℝ)*X 0 1+(164734649/400000000 : ℝ)*X 0 2+(4492618961/10000000000 : ℝ)*X 1 0+(4118366133/10000000000 : ℝ)*X 1 1+(164734649/400000000 : ℝ)*X 1 2+(4492618961/10000000000 : ℝ)*X 2 0+(4118366133/10000000000 : ℝ)*X 2 1+(164734649/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1656350849/10000000000 : ℝ)*X 0 0+(5498319859/10000000000 : ℝ)*X 0 1+(326885497/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5385671907/10000000000 : ℝ)*X 1 0+(-90592763/500000000 : ℝ)*X 1 1+(2615084501/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2692836199/5000000000 : ℝ)*X 2 0+(5230168347/10000000000 : ℝ)*X 2 1+(-452963869/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((998702193/2500000000 : ℝ)*X 0 0+(4367264667/10000000000 : ℝ)*X 0 1+(218363211/500000000 : ℝ)*X 0 2+(998702193/2500000000 : ℝ)*X 1 0+(4367264667/10000000000 : ℝ)*X 1 1+(218363211/500000000 : ℝ)*X 1 2+(998702193/2500000000 : ℝ)*X 2 0+(4367264667/10000000000 : ℝ)*X 2 1+(218363211/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1580_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63847/100000 : ℝ) ≤ (-1382544617796487979786066997/2165500000000000000000000000 : ℝ) := by norm_num
    linear_combination (8753617/100000000000000 : ℝ)*(upper3) + (1066307/20000000000000 : ℝ)*(lower4) + (2630483/100000000000000 : ℝ)*(lower5) + (1161021123011411/50000000000000 : ℝ)*(major0) + (1161021123011411/50000000000000 : ℝ)*(major1) + (1161021123011411/50000000000000 : ℝ)*(major2) + (302994463/20000000000000 : ℝ)*(sp1) + (182860003/25000000000000 : ℝ)*(sp2) + (224071711/50000000000000 : ℝ)*(sp3) + (3290012863958139/100000000000000 : ℝ)*(sp4) + (1645006133680919/50000000000000 : ℝ)*(sp5) + (1645006525447071/50000000000000 : ℝ)*(sp6) + (1375351637967607/100000000000000 : ℝ)*(sp7) + (183675203/20000000000000 : ℝ)*(sp8) + (1375352086111029/100000000000000 : ℝ)*(f.failure) + (1645006891167077/50000000000000 : ℝ)*(f.sum) + (18173108872907/4331000000000000000000000000 : ℝ)*base65 + (13054806008213707/1691796875000000000000000000000 : ℝ)*base68 + (51389389229794031/13534375000000000000000000000000 : ℝ)*base70 + (112848667331955969/13534375000000000000000000000000 : ℝ)*base71 + (29159232710653/4331000000000000000000000000 : ℝ)*base74 + (23337977000473297/6767187500000000000000000000000 : ℝ)*base75 + (1368659162949289/3383593750000000000000000000000 : ℝ)*base78 + (14490678119924719/13534375000000000000000000000000 : ℝ)*base79 + (4917126422397/4331000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (5100941/1250000000000000000000 : ℝ)*base90 + (5100941/1250000000000000000000 : ℝ)*base92 + (5100941/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (1179/2000 : ℝ) ≤ (3989442639496749236852247053673/6767187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (9484311/50000000000000 : ℝ)*(upper0) + (90824281/100000000000000 : ℝ)*(lower1) + (83005531/50000000000000 : ℝ)*(upper4) + (600741965365009/25000000000000 : ℝ)*(major0) + (600741965365009/25000000000000 : ℝ)*(major1) + (600741965365009/25000000000000 : ℝ)*(major2) + (420374135125229/12500000000000 : ℝ)*(sp0) + (3362996680785057/100000000000000 : ℝ)*(sp1) + (336298919837159/10000000000000 : ℝ)*(sp2) + (8895514935291/625000000000 : ℝ)*(sp3) + (893618651/25000000000000 : ℝ)*(sp5) + (1382111009/12500000000000 : ℝ)*(sp6) + (1081878937/50000000000000 : ℝ)*(sp7) + (7174257829/100000000000000 : ℝ)*(sp8) + (1423284553404433/100000000000000 : ℝ)*(f.failure) + (3363000255259661/100000000000000 : ℝ)*(f.sum) + (2708913357193/866200000000000000000000000 : ℝ)*base66 + (74919031713966953/13534375000000000000000000000000 : ℝ)*base68 + (2646980511848479/422949218750000000000000000000 : ℝ)*base70 + (86794233610773203/13534375000000000000000000000000 : ℝ)*base72 + (8033350713859/866200000000000000000000000 : ℝ)*base74 + (54505926955853789/6767187500000000000000000000000 : ℝ)*base76 + (64023930049453789/6767187500000000000000000000000 : ℝ)*base78 + (1020217650044151/105737304687500000000000000000 : ℝ)*base80 + (11747089061459/2165500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4253257/1250000000000000000000 : ℝ)*base90 + (4253257/1250000000000000000000 : ℝ)*base92 + (4253257/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (81019/100000 : ℝ) ≤ (5482896125386382371523929253829/6767187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (17377589/100000000000000 : ℝ)*(upper0) + (14283557/50000000000000 : ℝ)*(upper2) + (2426651/25000000000000 : ℝ)*(lower3) + (2800209/6250000000000 : ℝ)*(lower5) + (2587983843446903/100000000000000 : ℝ)*(major0) + (2587983843446903/100000000000000 : ℝ)*(major1) + (2587983843446903/100000000000000 : ℝ)*(major2) + (422010157/100000000000000 : ℝ)*(sp0) + (1798289537/50000000000000 : ℝ)*(sp3) + (1808044791437587/50000000000000 : ℝ)*(sp8) + (90402259764437/2500000000000 : ℝ)*(sp9) + (90402259764437/2500000000000 : ℝ)*(sp10) + (383216609494753/25000000000000 : ℝ)*(sp11) + (385692149/100000000000000 : ℝ)*(sp12) + (306574006911617/20000000000000 : ℝ)*(f.failure) + (90402259764437/2500000000000 : ℝ)*(f.sum) + (15066289177193/4331000000000000000000000000 : ℝ)*base66 + (82618284923253663/27068750000000000000000000000000 : ℝ)*base68 + (67707710311378663/27068750000000000000000000000000 : ℝ)*base70 + (95784161092184913/27068750000000000000000000000000 : ℝ)*base72 + (1537626488889/270687500000000000000000000 : ℝ)*base74 + (109862282206409913/27068750000000000000000000000000 : ℝ)*base76 + (72623572313934913/27068750000000000000000000000000 : ℝ)*base78 + (197170983425834913/27068750000000000000000000000000 : ℝ)*base80 + (121996287999/1082750000000000000000000000 : ℝ)*base82 + (1607193/250000000000000000000 : ℝ)*base90 + (1607193/250000000000000000000 : ℝ)*base92 + (1607193/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-86427/100000 : ℝ) ≤ (-2924271109851125847506496256113/3383593750000000000000000000000 : ℝ) := by norm_num
    linear_combination (5837623/10000000000000 : ℝ)*(lower2) + (180627183/100000000000000 : ℝ)*(upper3) + (811303/781250000000 : ℝ)*(upper5) + (41073795772637/1562500000000 : ℝ)*(major0) + (41073795772637/1562500000000 : ℝ)*(major1) + (41073795772637/1562500000000 : ℝ)*(major2) + (148137111/10000000000000 : ℝ)*(sp4) + (59818961517/50000000000000 : ℝ)*(sp6) + (12468621847/25000000000000 : ℝ)*(sp7) + (5622925901/50000000000000 : ℝ)*(sp8) + (466155194811207/12500000000000 : ℝ)*(sp12) + (466156785714071/12500000000000 : ℝ)*(sp13) + (1864567323894767/50000000000000 : ℝ)*(sp14) + (38923750852841/2500000000000 : ℝ)*(sp15) + (389249977150257/25000000000000 : ℝ)*(f.failure) + (466156785714071/12500000000000 : ℝ)*(f.sum) + (134103827767/27068750000000000000000000 : ℝ)*base65 + (53587894931359707/6767187500000000000000000000000 : ℝ)*base68 + (36165399843665957/6767187500000000000000000000000 : ℝ)*base70 + (24272828872965791/3383593750000000000000000000000 : ℝ)*base72 + (343630558357/135343750000000000000000000 : ℝ)*base74 + (34276831504353291/3383593750000000000000000000000 : ℝ)*base76 + (30263750377384707/6767187500000000000000000000000 : ℝ)*base78 + (33859397056178291/3383593750000000000000000000000 : ℝ)*base80 + (4098388480053/2165500000000000000000000000 : ℝ)*base81 + (1396247/312500000000000000000 : ℝ)*base89 + (1396247/312500000000000000000 : ℝ)*base91 + (1396247/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1580_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21104071/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11153/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63847/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1179/2000 : ℝ) else (81019/100000 : ℝ) ≤ X j i ∧ X j i ≤ (86427/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1580_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1580_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21104071/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11153/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63847/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1179/2000 : ℝ) else (81019/100000 : ℝ) ≤ X j i ∧ X j i ≤ (86427/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1580_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4655/1024 : ℝ) ≤ p) (hpb : p ≤ (4657/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21104071/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11153/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63847/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1179/2000 : ℝ) else (81019/100000 : ℝ) ≤ X j i ∧ X j i ≤ (86427/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1580_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

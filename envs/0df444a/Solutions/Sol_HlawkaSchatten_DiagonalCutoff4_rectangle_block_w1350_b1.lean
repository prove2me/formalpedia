-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1350_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:07:23.140428+00:00
-- url     : https://prove2.me/submissions/1be88ef3-048b-4f43-a88c-0badb1a72bac

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
theorem support_rectangle_w1350_s3_0 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2035398993/10000000000 : ℝ)*x 0 + (5426158263/10000000000 : ℝ)*x 1 + (261604561/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2035398993/10000000000 : ℝ)^2155 ≤ (2478776761883/20000000000000 : ℝ)^1643 := by
    have hnat : (2035398993 : ℕ)^2155*20000000000000^1643 ≤ 2478776761883^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035398993 10000000000 2478776761883 20000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426158263/10000000000 : ℝ)^2155 ≤ (44849091299793/100000000000000 : ℝ)^1643 := by
    have hnat : (5426158263 : ℕ)^2155*100000000000000^1643 ≤ 44849091299793^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426158263 10000000000 44849091299793 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261604561/500000000 : ℝ)^2155 ≤ (668078513559/1562500000000 : ℝ)^1643 := by
    have hnat : (261604561 : ℕ)^2155*1562500000000^1643 ≤ 668078513559^1643*500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261604561 500000000 668078513559 1562500000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2035398993/10000000000 : ℝ), (5426158263/10000000000 : ℝ), (261604561/500000000 : ℝ)] ![(2478776761883/20000000000000 : ℝ), (44849091299793/100000000000000 : ℝ), (668078513559/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2035398993/10000000000 : ℝ)|^2155 ≤ (2478776761883/20000000000000 : ℝ)^1643
        have hw : |(-2035398993/10000000000 : ℝ)|=(2035398993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426158263/10000000000 : ℝ)|^2155 ≤ (44849091299793/100000000000000 : ℝ)^1643
        have hw : |(5426158263/10000000000 : ℝ)|=(5426158263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261604561/500000000 : ℝ)|^2155 ≤ (668078513559/1562500000000 : ℝ)^1643
        have hw : |(261604561/500000000 : ℝ)|=(261604561/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s3_1 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5352399037/10000000000 : ℝ)*x 0 + (-1067280563/5000000000 : ℝ)*x 1 + (5232091509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352399037/10000000000 : ℝ)^2155 ≤ (8810232717069/20000000000000 : ℝ)^1643 := by
    have hnat : (5352399037 : ℕ)^2155*20000000000000^1643 ≤ 8810232717069^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352399037 10000000000 8810232717069 20000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1067280563/5000000000 : ℝ)^2155 ≤ (13191808435781/100000000000000 : ℝ)^1643 := by
    have hnat : (1067280563 : ℕ)^2155*100000000000000^1643 ≤ 13191808435781^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067280563 5000000000 13191808435781 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5232091509/10000000000 : ℝ)^2155 ≤ (42757027965479/100000000000000 : ℝ)^1643 := by
    have hnat : (5232091509 : ℕ)^2155*100000000000000^1643 ≤ 42757027965479^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232091509 10000000000 42757027965479 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352399037/10000000000 : ℝ), (-1067280563/5000000000 : ℝ), (5232091509/10000000000 : ℝ)] ![(8810232717069/20000000000000 : ℝ), (13191808435781/100000000000000 : ℝ), (42757027965479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352399037/10000000000 : ℝ)|^2155 ≤ (8810232717069/20000000000000 : ℝ)^1643
        have hw : |(5352399037/10000000000 : ℝ)|=(5352399037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1067280563/5000000000 : ℝ)|^2155 ≤ (13191808435781/100000000000000 : ℝ)^1643
        have hw : |(-1067280563/5000000000 : ℝ)|=(1067280563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5232091509/10000000000 : ℝ)|^2155 ≤ (42757027965479/100000000000000 : ℝ)^1643
        have hw : |(5232091509/10000000000 : ℝ)|=(5232091509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s3_2 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (267619951/500000000 : ℝ)*x 0 + (2616045643/5000000000 : ℝ)*x 1 + (-2134561443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267619951/500000000 : ℝ)^2155 ≤ (5506395425229/12500000000000 : ℝ)^1643 := by
    have hnat : (267619951 : ℕ)^2155*12500000000000^1643 ≤ 5506395425229^1643*500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267619951 500000000 5506395425229 12500000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2616045643/5000000000 : ℝ)^2155 ≤ (4275702557521/10000000000000 : ℝ)^1643 := by
    have hnat : (2616045643 : ℕ)^2155*10000000000000^1643 ≤ 4275702557521^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616045643 5000000000 4275702557521 10000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2134561443/10000000000 : ℝ)^2155 ≤ (206122046959/1562500000000 : ℝ)^1643 := by
    have hnat : (2134561443 : ℕ)^2155*1562500000000^1643 ≤ 206122046959^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134561443 10000000000 206122046959 1562500000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267619951/500000000 : ℝ), (2616045643/5000000000 : ℝ), (-2134561443/10000000000 : ℝ)] ![(5506395425229/12500000000000 : ℝ), (4275702557521/10000000000000 : ℝ), (206122046959/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267619951/500000000 : ℝ)|^2155 ≤ (5506395425229/12500000000000 : ℝ)^1643
        have hw : |(267619951/500000000 : ℝ)|=(267619951/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2616045643/5000000000 : ℝ)|^2155 ≤ (4275702557521/10000000000000 : ℝ)^1643
        have hw : |(2616045643/5000000000 : ℝ)|=(2616045643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2134561443/10000000000 : ℝ)|^2155 ≤ (206122046959/1562500000000 : ℝ)^1643
        have hw : |(-2134561443/10000000000 : ℝ)|=(2134561443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s3_3 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2161757459/5000000000 : ℝ)*x 0 + (128879131/312500000 : ℝ)*x 1 + (2265921891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161757459/5000000000 : ℝ)^2155 ≤ (16646565029401/50000000000000 : ℝ)^1643 := by
    have hnat : (2161757459 : ℕ)^2155*50000000000000^1643 ≤ 16646565029401^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161757459 5000000000 16646565029401 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128879131/312500000 : ℝ)^2155 ≤ (31293962843081/100000000000000 : ℝ)^1643 := by
    have hnat : (128879131 : ℕ)^2155*100000000000000^1643 ≤ 31293962843081^1643*312500000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128879131 312500000 31293962843081 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2265921891/5000000000 : ℝ)^2155 ≤ (7082581417469/20000000000000 : ℝ)^1643 := by
    have hnat : (2265921891 : ℕ)^2155*20000000000000^1643 ≤ 7082581417469^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265921891 5000000000 7082581417469 20000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2161757459/5000000000 : ℝ), (128879131/312500000 : ℝ), (2265921891/5000000000 : ℝ)] ![(16646565029401/50000000000000 : ℝ), (31293962843081/100000000000000 : ℝ), (7082581417469/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2161757459/5000000000 : ℝ)|^2155 ≤ (16646565029401/50000000000000 : ℝ)^1643
        have hw : |(2161757459/5000000000 : ℝ)|=(2161757459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(128879131/312500000 : ℝ)|^2155 ≤ (31293962843081/100000000000000 : ℝ)^1643
        have hw : |(128879131/312500000 : ℝ)|=(128879131/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2265921891/5000000000 : ℝ)|^2155 ≤ (7082581417469/20000000000000 : ℝ)^1643
        have hw : |(2265921891/5000000000 : ℝ)|=(2265921891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s3_4 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-127213587/625000000 : ℝ)*x 0 + (1308224093/2500000000 : ℝ)*x 1 + (2712674303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127213587/625000000 : ℝ)^2155 ≤ (1549253844623/12500000000000 : ℝ)^1643 := by
    have hnat : (127213587 : ℕ)^2155*12500000000000^1643 ≤ 1549253844623^1643*625000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127213587 625000000 1549253844623 12500000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1308224093/2500000000 : ℝ)^2155 ≤ (26728534533/62500000000 : ℝ)^1643 := by
    have hnat : (1308224093 : ℕ)^2155*62500000000^1643 ≤ 26728534533^1643*2500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308224093 2500000000 26728534533 62500000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712674303/5000000000 : ℝ)^2155 ≤ (22420156990421/50000000000000 : ℝ)^1643 := by
    have hnat : (2712674303 : ℕ)^2155*50000000000000^1643 ≤ 22420156990421^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712674303 5000000000 22420156990421 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-127213587/625000000 : ℝ), (1308224093/2500000000 : ℝ), (2712674303/5000000000 : ℝ)] ![(1549253844623/12500000000000 : ℝ), (26728534533/62500000000 : ℝ), (22420156990421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-127213587/625000000 : ℝ)|^2155 ≤ (1549253844623/12500000000000 : ℝ)^1643
        have hw : |(-127213587/625000000 : ℝ)|=(127213587/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1308224093/2500000000 : ℝ)|^2155 ≤ (26728534533/62500000000 : ℝ)^1643
        have hw : |(1308224093/2500000000 : ℝ)|=(1308224093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712674303/5000000000 : ℝ)|^2155 ≤ (22420156990421/50000000000000 : ℝ)^1643
        have hw : |(2712674303/5000000000 : ℝ)|=(2712674303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s3_5 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (331397789/625000000 : ℝ)*x 0 + (-388260803/2000000000 : ℝ)*x 1 + (5425348941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331397789/625000000 : ℝ)^2155 ≤ (43511835511141/100000000000000 : ℝ)^1643 := by
    have hnat : (331397789 : ℕ)^2155*100000000000000^1643 ≤ 43511835511141^1643*625000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331397789 625000000 43511835511141 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (388260803/2000000000 : ℝ)^2155 ≤ (11647846855729/100000000000000 : ℝ)^1643 := by
    have hnat : (388260803 : ℕ)^2155*100000000000000^1643 ≤ 11647846855729^1643*2000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388260803 2000000000 11647846855729 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425348941/10000000000 : ℝ)^2155 ≤ (44840317612421/100000000000000 : ℝ)^1643 := by
    have hnat : (5425348941 : ℕ)^2155*100000000000000^1643 ≤ 44840317612421^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425348941 10000000000 44840317612421 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331397789/625000000 : ℝ), (-388260803/2000000000 : ℝ), (5425348941/10000000000 : ℝ)] ![(43511835511141/100000000000000 : ℝ), (11647846855729/100000000000000 : ℝ), (44840317612421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331397789/625000000 : ℝ)|^2155 ≤ (43511835511141/100000000000000 : ℝ)^1643
        have hw : |(331397789/625000000 : ℝ)|=(331397789/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-388260803/2000000000 : ℝ)|^2155 ≤ (11647846855729/100000000000000 : ℝ)^1643
        have hw : |(-388260803/2000000000 : ℝ)|=(388260803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425348941/10000000000 : ℝ)|^2155 ≤ (44840317612421/100000000000000 : ℝ)^1643
        have hw : |(5425348941/10000000000 : ℝ)|=(5425348941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s3_6 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5302365457/10000000000 : ℝ)*x 0 + (5425348391/10000000000 : ℝ)*x 1 + (-970651817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302365457/10000000000 : ℝ)^2155 ≤ (43511844477013/100000000000000 : ℝ)^1643 := by
    have hnat : (5302365457 : ℕ)^2155*100000000000000^1643 ≤ 43511844477013^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302365457 10000000000 43511844477013 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425348391/10000000000 : ℝ)^2155 ≤ (44840311650127/100000000000000 : ℝ)^1643 := by
    have hnat : (5425348391 : ℕ)^2155*100000000000000^1643 ≤ 44840311650127^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425348391 10000000000 44840311650127 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (970651817/5000000000 : ℝ)^2155 ≤ (11647843857349/100000000000000 : ℝ)^1643 := by
    have hnat : (970651817 : ℕ)^2155*100000000000000^1643 ≤ 11647843857349^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970651817 5000000000 11647843857349 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302365457/10000000000 : ℝ), (5425348391/10000000000 : ℝ), (-970651817/5000000000 : ℝ)] ![(43511844477013/100000000000000 : ℝ), (44840311650127/100000000000000 : ℝ), (11647843857349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302365457/10000000000 : ℝ)|^2155 ≤ (43511844477013/100000000000000 : ℝ)^1643
        have hw : |(5302365457/10000000000 : ℝ)|=(5302365457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425348391/10000000000 : ℝ)|^2155 ≤ (44840311650127/100000000000000 : ℝ)^1643
        have hw : |(5425348391/10000000000 : ℝ)|=(5425348391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-970651817/5000000000 : ℝ)|^2155 ≤ (11647843857349/100000000000000 : ℝ)^1643
        have hw : |(-970651817/5000000000 : ℝ)|=(970651817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s3_7 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (216177759/500000000 : ℝ)*x 0 + (17695907/39062500 : ℝ)*x 1 + (825166629/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216177759/500000000 : ℝ)^2155 ≤ (8323384177803/25000000000000 : ℝ)^1643 := by
    have hnat : (216177759 : ℕ)^2155*25000000000000^1643 ≤ 8323384177803^1643*500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216177759 500000000 8323384177803 25000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17695907/39062500 : ℝ)^2155 ≤ (35395570396371/100000000000000 : ℝ)^1643 := by
    have hnat : (17695907 : ℕ)^2155*100000000000000^1643 ≤ 35395570396371^1643*39062500^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17695907 39062500 35395570396371 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (825166629/2000000000 : ℝ)^2155 ≤ (31310892880397/100000000000000 : ℝ)^1643 := by
    have hnat : (825166629 : ℕ)^2155*100000000000000^1643 ≤ 31310892880397^1643*2000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825166629 2000000000 31310892880397 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216177759/500000000 : ℝ), (17695907/39062500 : ℝ), (825166629/2000000000 : ℝ)] ![(8323384177803/25000000000000 : ℝ), (35395570396371/100000000000000 : ℝ), (31310892880397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216177759/500000000 : ℝ)|^2155 ≤ (8323384177803/25000000000000 : ℝ)^1643
        have hw : |(216177759/500000000 : ℝ)|=(216177759/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(17695907/39062500 : ℝ)|^2155 ≤ (35395570396371/100000000000000 : ℝ)^1643
        have hw : |(17695907/39062500 : ℝ)|=(17695907/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(825166629/2000000000 : ℝ)|^2155 ≤ (31310892880397/100000000000000 : ℝ)^1643
        have hw : |(825166629/2000000000 : ℝ)|=(825166629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1350_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (619/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (2179/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7501/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (619/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (619/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (619/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (619/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (619/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (619/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (619/6250 : ℝ) ^ (4309/1024 : ℝ) ≤ (5947894995595211/100000000000000000000 : ℝ) := by
    have hpowers : (619/6250 : ℝ)^4309 ≤ (5947894995595211/100000000000000000000 : ℝ)^1024 := by
      have hnat : (619 : ℕ)^4309*100000000000000000000^1024 ≤ 5947894995595211^1024*6250^4309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        619 6250 5947894995595211 100000000000000000000 4309 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (619/6250 : ℝ)) (X := (5947894995595211/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16073/100000 : ℝ) ^ (4309/1024 : ℝ) ≤ (365039388246009/800000000000000000 : ℝ) := by
    have hpowers : (16073/100000 : ℝ)^4309 ≤ (365039388246009/800000000000000000 : ℝ)^1024 := by
      have hnat : (16073 : ℕ)^4309*800000000000000000^1024 ≤ 365039388246009^1024*100000^4309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16073 100000 365039388246009 800000000000000000 4309 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16073/100000 : ℝ)) (X := (365039388246009/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005947894995595211/50000000000000000000 : ℝ) ≤ (10000282681286569/10000000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (50005947894995595211/50000000000000000000 : ℝ)^1024 ≤ (10000282681286569/10000000000000000 : ℝ)^4309 := by
      have hnat : (50005947894995595211 : ℕ)^1024*10000000000000000^4309 ≤ 10000282681286569^4309*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005947894995595211 50000000000000000000 10000282681286569 10000000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000282681286569/10000000000000000 : ℝ)) (X := (50005947894995595211/50000000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126611806828948323/3125000000000000000 : ℝ) ≤ (250030636635851/250000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (3126611806828948323/3125000000000000000 : ℝ)^1024 ≤ (250030636635851/250000000000000 : ℝ)^4309 := by
      have hnat : (3126611806828948323 : ℕ)^1024*250000000000000^4309 ≤ 250030636635851^4309*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126611806828948323 3125000000000000000 250030636635851 250000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250030636635851/250000000000000 : ℝ)) (X := (3126611806828948323/3125000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (400365039388246009/400000000000000000 : ℝ) ≤ (10002168249581511/10000000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (400365039388246009/400000000000000000 : ℝ)^1024 ≤ (10002168249581511/10000000000000000 : ℝ)^4309 := by
      have hnat : (400365039388246009 : ℕ)^1024*10000000000000000^4309 ≤ 10002168249581511^4309*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400365039388246009 400000000000000000 10002168249581511 10000000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002168249581511/10000000000000000 : ℝ)) (X := (400365039388246009/400000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5947894995595211/100000000000000000000 : ℝ) ≤ ((61673069192463738593/61690000000000000000 : ℝ)+2*(942784147471/616900000000000 : ℝ)*(619/6250 : ℝ))^(4309/1024 : ℝ) := by
    rw [show (61673069192463738593/61690000000000000000 : ℝ)+2*(942784147471/616900000000000 : ℝ)*(619/6250 : ℝ)=(10000282681286569/10000000000000000 : ℝ) by norm_num, show 1+2*(5947894995595211/100000000000000000000 : ℝ)=(50005947894995595211/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(365039388246009/800000000000000000 : ℝ)+(5947894995595211/100000000000000000000 : ℝ) ≤ ((61673069192463738593/61690000000000000000 : ℝ)+(942784147471/616900000000000 : ℝ)*((16073/100000 : ℝ)+(619/6250 : ℝ)))^(4309/1024 : ℝ) := by
    rw [show (61673069192463738593/61690000000000000000 : ℝ)+(942784147471/616900000000000 : ℝ)*((16073/100000 : ℝ)+(619/6250 : ℝ))=(250030636635851/250000000000000 : ℝ) by norm_num, show 1+(365039388246009/800000000000000000 : ℝ)+(5947894995595211/100000000000000000000 : ℝ)=(3126611806828948323/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(365039388246009/800000000000000000 : ℝ) ≤ ((61673069192463738593/61690000000000000000 : ℝ)+2*(942784147471/616900000000000 : ℝ)*(16073/100000 : ℝ))^(4309/1024 : ℝ) := by
    rw [show (61673069192463738593/61690000000000000000 : ℝ)+2*(942784147471/616900000000000 : ℝ)*(16073/100000 : ℝ)=(10002168249581511/10000000000000000 : ℝ) by norm_num, show 1+2*(365039388246009/800000000000000000 : ℝ)=(400365039388246009/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (61673069192463738593/61690000000000000000 : ℝ)*(X 1 0+X 2 0)+(942784147471/616900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (619/6250 : ℝ)) (hi := (16073/100000 : ℝ)) (c := (61673069192463738593/61690000000000000000 : ℝ)) (alpha := (942784147471/616900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (61673069192463738593/61690000000000000000 : ℝ)*(X 0 1+X 2 1)+(942784147471/616900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (619/6250 : ℝ)) (hi := (16073/100000 : ℝ)) (c := (61673069192463738593/61690000000000000000 : ℝ)) (alpha := (942784147471/616900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (61673069192463738593/61690000000000000000 : ℝ)*(X 0 2+X 1 2)+(942784147471/616900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (619/6250 : ℝ)) (hi := (16073/100000 : ℝ)) (c := (61673069192463738593/61690000000000000000 : ℝ)) (alpha := (942784147471/616900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2035398993/10000000000 : ℝ)*X 0 0+(5426158263/10000000000 : ℝ)*X 0 1+(261604561/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352399037/10000000000 : ℝ)*X 1 0+(-1067280563/5000000000 : ℝ)*X 1 1+(5232091509/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267619951/500000000 : ℝ)*X 2 0+(2616045643/5000000000 : ℝ)*X 2 1+(-2134561443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2161757459/5000000000 : ℝ)*X 0 0+(128879131/312500000 : ℝ)*X 0 1+(2265921891/5000000000 : ℝ)*X 0 2+(2161757459/5000000000 : ℝ)*X 1 0+(128879131/312500000 : ℝ)*X 1 1+(2265921891/5000000000 : ℝ)*X 1 2+(2161757459/5000000000 : ℝ)*X 2 0+(128879131/312500000 : ℝ)*X 2 1+(2265921891/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-127213587/625000000 : ℝ)*X 0 0+(1308224093/2500000000 : ℝ)*X 0 1+(2712674303/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331397789/625000000 : ℝ)*X 1 0+(-388260803/2000000000 : ℝ)*X 1 1+(5425348941/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302365457/10000000000 : ℝ)*X 2 0+(5425348391/10000000000 : ℝ)*X 2 1+(-970651817/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((216177759/500000000 : ℝ)*X 0 0+(17695907/39062500 : ℝ)*X 0 1+(825166629/2000000000 : ℝ)*X 0 2+(216177759/500000000 : ℝ)*X 1 0+(17695907/39062500 : ℝ)*X 1 1+(825166629/2000000000 : ℝ)*X 1 2+(216177759/500000000 : ℝ)*X 2 0+(17695907/39062500 : ℝ)*X 2 1+(825166629/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19905033804682015744413/3855625000000000000000000000 : ℝ) := by norm_num
    linear_combination (831294939/50000000000000 : ℝ)*(base19) + (1413756881/100000000000000 : ℝ)*(base23) + (41549853/100000000000000 : ℝ)*(upper2) + (512367619/100000000000000 : ℝ)*(upper3) + (165975247/100000000000000 : ℝ)*(upper4) + (3802830510054479/100000000000000 : ℝ)*(major0) + (3802830510054479/100000000000000 : ℝ)*(major1) + (3802830510054479/100000000000000 : ℝ)*(major2) + (644111853958891/12500000000000 : ℝ)*(sp0) + (5152915380875161/100000000000000 : ℝ)*(sp1) + (2576457814854079/50000000000000 : ℝ)*(sp2) + (1226362644332781/50000000000000 : ℝ)*(sp3) + (22211793911/100000000000000 : ℝ)*(sp4) + (18515891823/100000000000000 : ℝ)*(sp7) + (490548760911477/20000000000000 : ℝ)*(f.failure) + (5152917043465039/100000000000000 : ℝ)*(f.sum) + (91357791322809/30845000000000000000000000000 : ℝ)*base65 + (7081456964261708047/6169000000000000000000000000000000 : ℝ)*base67 + (19213266967100708047/6169000000000000000000000000000000 : ℝ)*base69 + (94255148591491291953/6169000000000000000000000000000000 : ℝ)*base72 + (141603253946879/30845000000000000000000000000 : ℝ)*base73 + (4915537769913708047/6169000000000000000000000000000000 : ℝ)*base75 + (19064817708798291953/6169000000000000000000000000000000 : ℝ)*base78 + (44834315475546291953/6169000000000000000000000000000000 : ℝ)*base80 + (18813527701371/7711250000000000000000000000 : ℝ)*base81 + (148399/400000000000000000000 : ℝ)*base89 + (148399/400000000000000000000 : ℝ)*base91 + (148399/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7554592771468799874400878441/1542250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (254534067/25000000000000 : ℝ)*(base19) + (238548829/10000000000000 : ℝ)*(base23) + (63888737/25000000000000 : ℝ)*(upper3) + (46576481/25000000000000 : ℝ)*(lower4) + (43187637/20000000000000 : ℝ)*(upper5) + (3834696435473821/100000000000000 : ℝ)*(major0) + (3834696435473821/100000000000000 : ℝ)*(major1) + (3834696435473821/100000000000000 : ℝ)*(major2) + (397683113/2000000000000 : ℝ)*(sp1) + (8209232563/20000000000000 : ℝ)*(sp2) + (1299024016820771/25000000000000 : ℝ)*(sp4) + (1039215032998233/20000000000000 : ℝ)*(sp5) + (2598026317815989/50000000000000 : ℝ)*(sp6) + (1236648320191893/50000000000000 : ℝ)*(sp7) + (1236648320191893/50000000000000 : ℝ)*(f.failure) + (1299024016820771/25000000000000 : ℝ)*(f.sum) + (43473706500251/30845000000000000000000000000 : ℝ)*base65 + (44646076005667973853/6169000000000000000000000000000000 : ℝ)*base67 + (17389003751998026147/6169000000000000000000000000000000 : ℝ)*base70 + (43254119316897973853/6169000000000000000000000000000000 : ℝ)*base71 + (18582103993963/15422500000000000000000000000 : ℝ)*base73 + (11483759477342973853/6169000000000000000000000000000000 : ℝ)*base75 + (18013228700013973853/6169000000000000000000000000000000 : ℝ)*base77 + (161557224111107973853/6169000000000000000000000000000000 : ℝ)*base79 + (2694348254503/15422500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (836209/1000000000000000000000 : ℝ)*base90 + (836209/1000000000000000000000 : ℝ)*base92 + (836209/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1350_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (619/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2179/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7501/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1350_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1350_s4_0 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-25459969/125000000 : ℝ)*x 0 + (1082942633/2000000000 : ℝ)*x 1 + (5242617669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25459969/125000000 : ℝ)^2155 ≤ (387657957059/3125000000000 : ℝ)^1643 := by
    have hnat : (25459969 : ℕ)^2155*3125000000000^1643 ≤ 387657957059^1643*125000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25459969 125000000 387657957059 3125000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082942633/2000000000 : ℝ)^2155 ≤ (22362527672193/50000000000000 : ℝ)^1643 := by
    have hnat : (1082942633 : ℕ)^2155*50000000000000^1643 ≤ 22362527672193^1643*2000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082942633 2000000000 22362527672193 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242617669/10000000000 : ℝ)^2155 ≤ (21434945004741/50000000000000 : ℝ)^1643 := by
    have hnat : (5242617669 : ℕ)^2155*50000000000000^1643 ≤ 21434945004741^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242617669 10000000000 21434945004741 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-25459969/125000000 : ℝ), (1082942633/2000000000 : ℝ), (5242617669/10000000000 : ℝ)] ![(387657957059/3125000000000 : ℝ), (22362527672193/50000000000000 : ℝ), (21434945004741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-25459969/125000000 : ℝ)|^2155 ≤ (387657957059/3125000000000 : ℝ)^1643
        have hw : |(-25459969/125000000 : ℝ)|=(25459969/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082942633/2000000000 : ℝ)|^2155 ≤ (22362527672193/50000000000000 : ℝ)^1643
        have hw : |(1082942633/2000000000 : ℝ)|=(1082942633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242617669/10000000000 : ℝ)|^2155 ≤ (21434945004741/50000000000000 : ℝ)^1643
        have hw : |(5242617669/10000000000 : ℝ)|=(5242617669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s4_1 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349477447/10000000000 : ℝ)*x 0 + (-2124521263/10000000000 : ℝ)*x 1 + (2621308683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349477447/10000000000 : ℝ)^2155 ≤ (44019627996973/100000000000000 : ℝ)^1643 := by
    have hnat : (5349477447 : ℕ)^2155*100000000000000^1643 ≤ 44019627996973^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349477447 10000000000 44019627996973 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2124521263/10000000000 : ℝ)^2155 ≤ (6555242614159/50000000000000 : ℝ)^1643 := by
    have hnat : (2124521263 : ℕ)^2155*50000000000000^1643 ≤ 6555242614159^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124521263 10000000000 6555242614159 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621308683/5000000000 : ℝ)^2155 ≤ (42869886759683/100000000000000 : ℝ)^1643 := by
    have hnat : (2621308683 : ℕ)^2155*100000000000000^1643 ≤ 42869886759683^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621308683 5000000000 42869886759683 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349477447/10000000000 : ℝ), (-2124521263/10000000000 : ℝ), (2621308683/5000000000 : ℝ)] ![(44019627996973/100000000000000 : ℝ), (6555242614159/50000000000000 : ℝ), (42869886759683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349477447/10000000000 : ℝ)|^2155 ≤ (44019627996973/100000000000000 : ℝ)^1643
        have hw : |(5349477447/10000000000 : ℝ)|=(5349477447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2124521263/10000000000 : ℝ)|^2155 ≤ (6555242614159/50000000000000 : ℝ)^1643
        have hw : |(-2124521263/10000000000 : ℝ)|=(2124521263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621308683/5000000000 : ℝ)|^2155 ≤ (42869886759683/100000000000000 : ℝ)^1643
        have hw : |(2621308683/5000000000 : ℝ)|=(2621308683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s4_2 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (167171187/312500000 : ℝ)*x 0 + (8388187/16000000 : ℝ)*x 1 + (-2124521197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167171187/312500000 : ℝ)^2155 ≤ (2751227112053/6250000000000 : ℝ)^1643 := by
    have hnat : (167171187 : ℕ)^2155*6250000000000^1643 ≤ 2751227112053^1643*312500000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167171187 312500000 2751227112053 6250000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8388187/16000000 : ℝ)^2155 ≤ (42869881493507/100000000000000 : ℝ)^1643 := by
    have hnat : (8388187 : ℕ)^2155*100000000000000^1643 ≤ 42869881493507^1643*16000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8388187 16000000 42869881493507 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124521197/10000000000 : ℝ)^2155 ≤ (13110484694109/100000000000000 : ℝ)^1643 := by
    have hnat : (2124521197 : ℕ)^2155*100000000000000^1643 ≤ 13110484694109^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124521197 10000000000 13110484694109 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167171187/312500000 : ℝ), (8388187/16000000 : ℝ), (-2124521197/10000000000 : ℝ)] ![(2751227112053/6250000000000 : ℝ), (42869881493507/100000000000000 : ℝ), (13110484694109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167171187/312500000 : ℝ)|^2155 ≤ (2751227112053/6250000000000 : ℝ)^1643
        have hw : |(167171187/312500000 : ℝ)|=(167171187/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8388187/16000000 : ℝ)|^2155 ≤ (42869881493507/100000000000000 : ℝ)^1643
        have hw : |(8388187/16000000 : ℝ)|=(8388187/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2124521197/10000000000 : ℝ)|^2155 ≤ (13110484694109/100000000000000 : ℝ)^1643
        have hw : |(-2124521197/10000000000 : ℝ)|=(2124521197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s4_3 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1081090991/2500000000 : ℝ)*x 0 + (4147106803/10000000000 : ℝ)*x 1 + (2254329873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081090991/2500000000 : ℝ)^2155 ≤ (16650852902157/50000000000000 : ℝ)^1643 := by
    have hnat : (1081090991 : ℕ)^2155*50000000000000^1643 ≤ 16650852902157^1643*2500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081090991 2500000000 16650852902157 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4147106803/10000000000 : ℝ)^2155 ≤ (31522818781061/100000000000000 : ℝ)^1643 := by
    have hnat : (4147106803 : ℕ)^2155*100000000000000^1643 ≤ 31522818781061^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147106803 10000000000 31522818781061 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254329873/5000000000 : ℝ)^2155 ≤ (17587737700241/50000000000000 : ℝ)^1643 := by
    have hnat : (2254329873 : ℕ)^2155*50000000000000^1643 ≤ 17587737700241^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254329873 5000000000 17587737700241 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081090991/2500000000 : ℝ), (4147106803/10000000000 : ℝ), (2254329873/5000000000 : ℝ)] ![(16650852902157/50000000000000 : ℝ), (31522818781061/100000000000000 : ℝ), (17587737700241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081090991/2500000000 : ℝ)|^2155 ≤ (16650852902157/50000000000000 : ℝ)^1643
        have hw : |(1081090991/2500000000 : ℝ)|=(1081090991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4147106803/10000000000 : ℝ)|^2155 ≤ (31522818781061/100000000000000 : ℝ)^1643
        have hw : |(4147106803/10000000000 : ℝ)|=(4147106803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2254329873/5000000000 : ℝ)|^2155 ≤ (17587737700241/50000000000000 : ℝ)^1643
        have hw : |(2254329873/5000000000 : ℝ)|=(2254329873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s4_4 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1018405553/5000000000 : ℝ)*x 0 + (2621625369/5000000000 : ℝ)*x 1 + (1082815279/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1018405553/5000000000 : ℝ)^2155 ≤ (6202581578293/50000000000000 : ℝ)^1643 := by
    have hnat : (1018405553 : ℕ)^2155*50000000000000^1643 ≤ 6202581578293^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018405553 5000000000 6202581578293 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621625369/5000000000 : ℝ)^2155 ≤ (21438340030833/50000000000000 : ℝ)^1643 := by
    have hnat : (2621625369 : ℕ)^2155*50000000000000^1643 ≤ 21438340030833^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621625369 5000000000 21438340030833 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082815279/2000000000 : ℝ)^2155 ≤ (44718156763219/100000000000000 : ℝ)^1643 := by
    have hnat : (1082815279 : ℕ)^2155*100000000000000^1643 ≤ 44718156763219^1643*2000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082815279 2000000000 44718156763219 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1018405553/5000000000 : ℝ), (2621625369/5000000000 : ℝ), (1082815279/2000000000 : ℝ)] ![(6202581578293/50000000000000 : ℝ), (21438340030833/50000000000000 : ℝ), (44718156763219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1018405553/5000000000 : ℝ)|^2155 ≤ (6202581578293/50000000000000 : ℝ)^1643
        have hw : |(-1018405553/5000000000 : ℝ)|=(1018405553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621625369/5000000000 : ℝ)|^2155 ≤ (21438340030833/50000000000000 : ℝ)^1643
        have hw : |(2621625369/5000000000 : ℝ)|=(2621625369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082815279/2000000000 : ℝ)|^2155 ≤ (44718156763219/100000000000000 : ℝ)^1643
        have hw : |(1082815279/2000000000 : ℝ)|=(1082815279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s4_5 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652554519/5000000000 : ℝ)*x 0 + (-488265447/2500000000 : ℝ)*x 1 + (5414076511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652554519/5000000000 : ℝ)^2155 ≤ (21770688492891/50000000000000 : ℝ)^1643 := by
    have hnat : (2652554519 : ℕ)^2155*50000000000000^1643 ≤ 21770688492891^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652554519 5000000000 21770688492891 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (488265447/2500000000 : ℝ)^2155 ≤ (1467558122049/12500000000000 : ℝ)^1643 := by
    have hnat : (488265447 : ℕ)^2155*12500000000000^1643 ≤ 1467558122049^1643*2500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488265447 2500000000 1467558122049 12500000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414076511/10000000000 : ℝ)^2155 ≤ (44718158019907/100000000000000 : ℝ)^1643 := by
    have hnat : (5414076511 : ℕ)^2155*100000000000000^1643 ≤ 44718158019907^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414076511 10000000000 44718158019907 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652554519/5000000000 : ℝ), (-488265447/2500000000 : ℝ), (5414076511/10000000000 : ℝ)] ![(21770688492891/50000000000000 : ℝ), (1467558122049/12500000000000 : ℝ), (44718158019907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652554519/5000000000 : ℝ)|^2155 ≤ (21770688492891/50000000000000 : ℝ)^1643
        have hw : |(2652554519/5000000000 : ℝ)|=(2652554519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-488265447/2500000000 : ℝ)|^2155 ≤ (1467558122049/12500000000000 : ℝ)^1643
        have hw : |(-488265447/2500000000 : ℝ)|=(488265447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414076511/10000000000 : ℝ)|^2155 ≤ (44718158019907/100000000000000 : ℝ)^1643
        have hw : |(5414076511/10000000000 : ℝ)|=(5414076511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s4_6 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305109273/10000000000 : ℝ)*x 0 + (5414076391/10000000000 : ℝ)*x 1 + (-1953061633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305109273/10000000000 : ℝ)^2155 ≤ (43541379515577/100000000000000 : ℝ)^1643 := by
    have hnat : (5305109273 : ℕ)^2155*100000000000000^1643 ≤ 43541379515577^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305109273 10000000000 43541379515577 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414076391/10000000000 : ℝ)^2155 ≤ (8943631343977/20000000000000 : ℝ)^1643 := by
    have hnat : (5414076391 : ℕ)^2155*20000000000000^1643 ≤ 8943631343977^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414076391 10000000000 8943631343977 20000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1953061633/10000000000 : ℝ)^2155 ≤ (11740463754281/100000000000000 : ℝ)^1643 := by
    have hnat : (1953061633 : ℕ)^2155*100000000000000^1643 ≤ 11740463754281^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953061633 10000000000 11740463754281 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305109273/10000000000 : ℝ), (5414076391/10000000000 : ℝ), (-1953061633/10000000000 : ℝ)] ![(43541379515577/100000000000000 : ℝ), (8943631343977/20000000000000 : ℝ), (11740463754281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305109273/10000000000 : ℝ)|^2155 ≤ (43541379515577/100000000000000 : ℝ)^1643
        have hw : |(5305109273/10000000000 : ℝ)|=(5305109273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414076391/10000000000 : ℝ)|^2155 ≤ (8943631343977/20000000000000 : ℝ)^1643
        have hw : |(5414076391/10000000000 : ℝ)|=(5414076391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1953061633/10000000000 : ℝ)|^2155 ≤ (11740463754281/100000000000000 : ℝ)^1643
        have hw : |(-1953061633/10000000000 : ℝ)|=(1953061633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s4_7 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4324392111/10000000000 : ℝ)*x 0 + (2253664403/5000000000 : ℝ)*x 1 + (207422211/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324392111/10000000000 : ℝ)^2155 ≤ (8325497527657/25000000000000 : ℝ)^1643 := by
    have hnat : (4324392111 : ℕ)^2155*25000000000000^1643 ≤ 8325497527657^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324392111 10000000000 8325497527657 25000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253664403/5000000000 : ℝ)^2155 ≤ (35161856541429/100000000000000 : ℝ)^1643 := by
    have hnat : (2253664403 : ℕ)^2155*100000000000000^1643 ≤ 35161856541429^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253664403 5000000000 35161856541429 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207422211/500000000 : ℝ)^2155 ≤ (31536153325897/100000000000000 : ℝ)^1643 := by
    have hnat : (207422211 : ℕ)^2155*100000000000000^1643 ≤ 31536153325897^1643*500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207422211 500000000 31536153325897 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324392111/10000000000 : ℝ), (2253664403/5000000000 : ℝ), (207422211/500000000 : ℝ)] ![(8325497527657/25000000000000 : ℝ), (35161856541429/100000000000000 : ℝ), (31536153325897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324392111/10000000000 : ℝ)|^2155 ≤ (8325497527657/25000000000000 : ℝ)^1643
        have hw : |(4324392111/10000000000 : ℝ)|=(4324392111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2253664403/5000000000 : ℝ)|^2155 ≤ (35161856541429/100000000000000 : ℝ)^1643
        have hw : |(2253664403/5000000000 : ℝ)|=(2253664403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207422211/500000000 : ℝ)|^2155 ≤ (31536153325897/100000000000000 : ℝ)^1643
        have hw : |(207422211/500000000 : ℝ)|=(207422211/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1350_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7501/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2179/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (139/1250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14763/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7501/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2179/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7501/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2179/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7501/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2179/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7501/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2179/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7501/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2179/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7501/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2179/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (2179/20000 : ℝ) ^ (4309/1024 : ℝ) ≤ (8884739144416129/100000000000000000000 : ℝ) := by
    have hpowers : (2179/20000 : ℝ)^4309 ≤ (8884739144416129/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2179 : ℕ)^4309*100000000000000000000^1024 ≤ 8884739144416129^1024*20000^4309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2179 20000 8884739144416129 100000000000000000000 4309 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2179/20000 : ℝ)) (X := (8884739144416129/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7501/50000 : ℝ) ^ (4309/1024 : ℝ) ≤ (34137305103693053/100000000000000000000 : ℝ) := by
    have hpowers : (7501/50000 : ℝ)^4309 ≤ (34137305103693053/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7501 : ℕ)^4309*100000000000000000000^1024 ≤ 34137305103693053^1024*50000^4309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7501 50000 34137305103693053 100000000000000000000 4309 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7501/50000 : ℝ)) (X := (34137305103693053/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008884739144416129/50000000000000000000 : ℝ) ≤ (10000422249093089/10000000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (50008884739144416129/50000000000000000000 : ℝ)^1024 ≤ (10000422249093089/10000000000000000 : ℝ)^4309 := by
      have hnat : (50008884739144416129 : ℕ)^1024*10000000000000000^4309 ≤ 10000422249093089^4309*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008884739144416129 50000000000000000000 10000422249093089 10000000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000422249093089/10000000000000000 : ℝ)) (X := (50008884739144416129/50000000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021511022124054591/50000000000000000000 : ℝ) ≤ (10001022217465383/10000000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (50021511022124054591/50000000000000000000 : ℝ)^1024 ≤ (10001022217465383/10000000000000000 : ℝ)^4309 := by
      have hnat : (50021511022124054591 : ℕ)^1024*10000000000000000^4309 ≤ 10001022217465383^4309*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021511022124054591 50000000000000000000 10001022217465383 10000000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001022217465383/10000000000000000 : ℝ)) (X := (50021511022124054591/50000000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034137305103693053/50000000000000000000 : ℝ) ≤ (10001622185837677/10000000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (50034137305103693053/50000000000000000000 : ℝ)^1024 ≤ (10001622185837677/10000000000000000 : ℝ)^4309 := by
      have hnat : (50034137305103693053 : ℕ)^1024*10000000000000000^4309 ≤ 10001622185837677^4309*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034137305103693053 50000000000000000000 10001622185837677 10000000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001622185837677/10000000000000000 : ℝ)) (X := (50034137305103693053/50000000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8884739144416129/100000000000000000000 : ℝ) ≤ ((41058660866193030263/41070000000000000000 : ℝ)+2*(299984186147/205350000000000 : ℝ)*(2179/20000 : ℝ))^(4309/1024 : ℝ) := by
    rw [show (41058660866193030263/41070000000000000000 : ℝ)+2*(299984186147/205350000000000 : ℝ)*(2179/20000 : ℝ)=(10000422249093089/10000000000000000 : ℝ) by norm_num, show 1+2*(8884739144416129/100000000000000000000 : ℝ)=(50008884739144416129/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34137305103693053/100000000000000000000 : ℝ)+(8884739144416129/100000000000000000000 : ℝ) ≤ ((41058660866193030263/41070000000000000000 : ℝ)+(299984186147/205350000000000 : ℝ)*((7501/50000 : ℝ)+(2179/20000 : ℝ)))^(4309/1024 : ℝ) := by
    rw [show (41058660866193030263/41070000000000000000 : ℝ)+(299984186147/205350000000000 : ℝ)*((7501/50000 : ℝ)+(2179/20000 : ℝ))=(10001022217465383/10000000000000000 : ℝ) by norm_num, show 1+(34137305103693053/100000000000000000000 : ℝ)+(8884739144416129/100000000000000000000 : ℝ)=(50021511022124054591/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34137305103693053/100000000000000000000 : ℝ) ≤ ((41058660866193030263/41070000000000000000 : ℝ)+2*(299984186147/205350000000000 : ℝ)*(7501/50000 : ℝ))^(4309/1024 : ℝ) := by
    rw [show (41058660866193030263/41070000000000000000 : ℝ)+2*(299984186147/205350000000000 : ℝ)*(7501/50000 : ℝ)=(10001622185837677/10000000000000000 : ℝ) by norm_num, show 1+2*(34137305103693053/100000000000000000000 : ℝ)=(50034137305103693053/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (41058660866193030263/41070000000000000000 : ℝ)*(X 1 0+X 2 0)+(299984186147/205350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (2179/20000 : ℝ)) (hi := (7501/50000 : ℝ)) (c := (41058660866193030263/41070000000000000000 : ℝ)) (alpha := (299984186147/205350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (41058660866193030263/41070000000000000000 : ℝ)*(X 0 1+X 2 1)+(299984186147/205350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (2179/20000 : ℝ)) (hi := (7501/50000 : ℝ)) (c := (41058660866193030263/41070000000000000000 : ℝ)) (alpha := (299984186147/205350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (41058660866193030263/41070000000000000000 : ℝ)*(X 0 2+X 1 2)+(299984186147/205350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (2179/20000 : ℝ)) (hi := (7501/50000 : ℝ)) (c := (41058660866193030263/41070000000000000000 : ℝ)) (alpha := (299984186147/205350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-25459969/125000000 : ℝ)*X 0 0+(1082942633/2000000000 : ℝ)*X 0 1+(5242617669/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349477447/10000000000 : ℝ)*X 1 0+(-2124521263/10000000000 : ℝ)*X 1 1+(2621308683/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167171187/312500000 : ℝ)*X 2 0+(8388187/16000000 : ℝ)*X 2 1+(-2124521197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1081090991/2500000000 : ℝ)*X 0 0+(4147106803/10000000000 : ℝ)*X 0 1+(2254329873/5000000000 : ℝ)*X 0 2+(1081090991/2500000000 : ℝ)*X 1 0+(4147106803/10000000000 : ℝ)*X 1 1+(2254329873/5000000000 : ℝ)*X 1 2+(1081090991/2500000000 : ℝ)*X 2 0+(4147106803/10000000000 : ℝ)*X 2 1+(2254329873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1018405553/5000000000 : ℝ)*X 0 0+(2621625369/5000000000 : ℝ)*X 0 1+(1082815279/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652554519/5000000000 : ℝ)*X 1 0+(-488265447/2500000000 : ℝ)*X 1 1+(5414076511/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305109273/10000000000 : ℝ)*X 2 0+(5414076391/10000000000 : ℝ)*X 2 1+(-1953061633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4324392111/10000000000 : ℝ)*X 0 0+(2253664403/5000000000 : ℝ)*X 0 1+(207422211/500000000 : ℝ)*X 0 2+(4324392111/10000000000 : ℝ)*X 1 0+(2253664403/5000000000 : ℝ)*X 1 1+(207422211/500000000 : ℝ)*X 1 2+(4324392111/10000000000 : ℝ)*X 2 0+(2253664403/5000000000 : ℝ)*X 2 1+(207422211/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24299103834611231543319/3422500000000000000000000000 : ℝ) := by norm_num
    linear_combination (87070431/100000000000000 : ℝ)*(base8) + (12437403/25000000000000 : ℝ)*(base21) + (20568271/10000000000000 : ℝ)*(lower2) + (25094247/25000000000000 : ℝ)*(upper4) + (4288283217162781/100000000000000 : ℝ)*(major0) + (4288283217162781/100000000000000 : ℝ)*(major1) + (4288283217162781/100000000000000 : ℝ)*(major2) + (581071576168379/10000000000000 : ℝ)*(sp0) + (5810708242452813/100000000000000 : ℝ)*(sp1) + (2905350815697301/50000000000000 : ℝ)*(sp2) + (1382923128651817/50000000000000 : ℝ)*(sp3) + (237696919/3125000000000 : ℝ)*(sp5) + (14167610007/100000000000000 : ℝ)*(sp6) + (163664293/4000000000000 : ℝ)*(sp7) + (34573129361387/1250000000000 : ℝ)*(f.failure) + (5810715848754221/100000000000000 : ℝ)*(f.sum) + (107602349633329/20535000000000000000000000000 : ℝ)*base65 + (17734945101559213801/1369000000000000000000000000000000 : ℝ)*base67 + (12762336570491213801/1369000000000000000000000000000000 : ℝ)*base69 + (9669109274356786199/1369000000000000000000000000000000 : ℝ)*base72 + (115331553644599/20535000000000000000000000000 : ℝ)*base73 + (6216784711292786199/1369000000000000000000000000000000 : ℝ)*base76 + (2222575279672786199/1369000000000000000000000000000000 : ℝ)*base78 + (9872698512006213801/1369000000000000000000000000000000 : ℝ)*base79 + (52099715294749/20535000000000000000000000000 : ℝ)*base81 + (257569/25000000000000000000 : ℝ)*base89 + (257569/25000000000000000000 : ℝ)*base91 + (257569/25000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56845055908385624177571/6845000000000000000000000000 : ℝ) := by norm_num
    linear_combination (496602337/50000000000000 : ℝ)*(base19) + (752755289/50000000000000 : ℝ)*(base23) + (50603659/20000000000000 : ℝ)*(upper3) + (73536997/100000000000000 : ℝ)*(lower4) + (4402501/4000000000000 : ℝ)*(upper5) + (2160082864242117/50000000000000 : ℝ)*(major0) + (2160082864242117/50000000000000 : ℝ)*(major1) + (2160082864242117/50000000000000 : ℝ)*(major2) + (7884187509/50000000000000 : ℝ)*(sp1) + (14722269347/50000000000000 : ℝ)*(sp2) + (2926958648930499/50000000000000 : ℝ)*(sp4) + (2926950268140653/50000000000000 : ℝ)*(sp5) + (234155453912469/4000000000000 : ℝ)*(sp6) + (278641388228713/10000000000000 : ℝ)*(sp7) + (278641388228713/10000000000000 : ℝ)*(f.failure) + (2926958648930499/50000000000000 : ℝ)*(f.sum) + (2983773030721/3422500000000000000000000000 : ℝ)*base65 + (2075974042338662257/684500000000000000000000000000000 : ℝ)*base67 + (1127723825518337743/684500000000000000000000000000000 : ℝ)*base70 + (6202748699738662257/684500000000000000000000000000000 : ℝ)*base71 + (4913769873889/3422500000000000000000000000 : ℝ)*base74 + (2364905378286337743/684500000000000000000000000000000 : ℝ)*base76 + (741145222882837743/684500000000000000000000000000000 : ℝ)*base78 + (5494757754254162257/684500000000000000000000000000000 : ℝ)*base79 + (15224281759733/6845000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (701131/200000000000000000000 : ℝ)*base89 + (701131/200000000000000000000 : ℝ)*base91 + (701131/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1350_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7501/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2179/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (139/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1350_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1350_s5_0 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1018517469/5000000000 : ℝ)*x 0 + (2706328081/5000000000 : ℝ)*x 1 + (327782401/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1018517469/5000000000 : ℝ)^2155 ≤ (310173781337/2500000000000 : ℝ)^1643 := by
    have hnat : (1018517469 : ℕ)^2155*2500000000000^1643 ≤ 310173781337^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018517469 5000000000 310173781337 2500000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706328081/5000000000 : ℝ)^2155 ≤ (2793923205151/6250000000000 : ℝ)^1643 := by
    have hnat : (2706328081 : ℕ)^2155*6250000000000^1643 ≤ 2793923205151^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706328081 5000000000 2793923205151 6250000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327782401/625000000 : ℝ)^2155 ≤ (21445138725731/50000000000000 : ℝ)^1643 := by
    have hnat : (327782401 : ℕ)^2155*50000000000000^1643 ≤ 21445138725731^1643*625000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327782401 625000000 21445138725731 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1018517469/5000000000 : ℝ), (2706328081/5000000000 : ℝ), (327782401/625000000 : ℝ)] ![(310173781337/2500000000000 : ℝ), (2793923205151/6250000000000 : ℝ), (21445138725731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1018517469/5000000000 : ℝ)|^2155 ≤ (310173781337/2500000000000 : ℝ)^1643
        have hw : |(-1018517469/5000000000 : ℝ)|=(1018517469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706328081/5000000000 : ℝ)|^2155 ≤ (2793923205151/6250000000000 : ℝ)^1643
        have hw : |(2706328081/5000000000 : ℝ)|=(2706328081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327782401/625000000 : ℝ)|^2155 ≤ (21445138725731/50000000000000 : ℝ)^1643
        have hw : |(327782401/625000000 : ℝ)|=(327782401/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s5_1 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668618993/1250000000 : ℝ)*x 0 + (-2122702531/10000000000 : ℝ)*x 1 + (5244518417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668618993/1250000000 : ℝ)^2155 ≤ (22006978148361/50000000000000 : ℝ)^1643 := by
    have hnat : (668618993 : ℕ)^2155*50000000000000^1643 ≤ 22006978148361^1643*1250000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668618993 1250000000 22006978148361 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2122702531/10000000000 : ℝ)^2155 ≤ (13095766233287/100000000000000 : ℝ)^1643 := by
    have hnat : (2122702531 : ℕ)^2155*100000000000000^1643 ≤ 13095766233287^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122702531 10000000000 13095766233287 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244518417/10000000000 : ℝ)^2155 ≤ (42890277462189/100000000000000 : ℝ)^1643 := by
    have hnat : (5244518417 : ℕ)^2155*100000000000000^1643 ≤ 42890277462189^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244518417 10000000000 42890277462189 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668618993/1250000000 : ℝ), (-2122702531/10000000000 : ℝ), (5244518417/10000000000 : ℝ)] ![(22006978148361/50000000000000 : ℝ), (13095766233287/100000000000000 : ℝ), (42890277462189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668618993/1250000000 : ℝ)|^2155 ≤ (22006978148361/50000000000000 : ℝ)^1643
        have hw : |(668618993/1250000000 : ℝ)|=(668618993/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2122702531/10000000000 : ℝ)|^2155 ≤ (13095766233287/100000000000000 : ℝ)^1643
        have hw : |(-2122702531/10000000000 : ℝ)|=(2122702531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244518417/10000000000 : ℝ)|^2155 ≤ (42890277462189/100000000000000 : ℝ)^1643
        have hw : |(5244518417/10000000000 : ℝ)|=(5244518417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s5_2 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674475973/5000000000 : ℝ)*x 0 + (327782401/625000000 : ℝ)*x 1 + (-2122702529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674475973/5000000000 : ℝ)^2155 ≤ (11003489079577/25000000000000 : ℝ)^1643 := by
    have hnat : (2674475973 : ℕ)^2155*25000000000000^1643 ≤ 11003489079577^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674475973 5000000000 11003489079577 25000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327782401/625000000 : ℝ)^2155 ≤ (21445138725731/50000000000000 : ℝ)^1643 := by
    have hnat : (327782401 : ℕ)^2155*50000000000000^1643 ≤ 21445138725731^1643*625000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327782401 625000000 21445138725731 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122702529/10000000000 : ℝ)^2155 ≤ (13095766217103/100000000000000 : ℝ)^1643 := by
    have hnat : (2122702529 : ℕ)^2155*100000000000000^1643 ≤ 13095766217103^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122702529 10000000000 13095766217103 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674475973/5000000000 : ℝ), (327782401/625000000 : ℝ), (-2122702529/10000000000 : ℝ)] ![(11003489079577/25000000000000 : ℝ), (21445138725731/50000000000000 : ℝ), (13095766217103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674475973/5000000000 : ℝ)|^2155 ≤ (11003489079577/25000000000000 : ℝ)^1643
        have hw : |(2674475973/5000000000 : ℝ)|=(2674475973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327782401/625000000 : ℝ)|^2155 ≤ (21445138725731/50000000000000 : ℝ)^1643
        have hw : |(327782401/625000000 : ℝ)|=(327782401/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2122702529/10000000000 : ℝ)|^2155 ≤ (13095766217103/100000000000000 : ℝ)^1643
        have hw : |(-2122702529/10000000000 : ℝ)|=(2122702529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s5_3 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1081126679/2500000000 : ℝ)*x 0 + (2075623463/5000000000 : ℝ)*x 1 + (140765123/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081126679/2500000000 : ℝ)^2155 ≤ (33303147715087/100000000000000 : ℝ)^1643 := by
    have hnat : (1081126679 : ℕ)^2155*100000000000000^1643 ≤ 33303147715087^1643*2500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081126679 2500000000 33303147715087 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2075623463/5000000000 : ℝ)^2155 ≤ (15782050846061/50000000000000 : ℝ)^1643 := by
    have hnat : (2075623463 : ℕ)^2155*50000000000000^1643 ≤ 15782050846061^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075623463 5000000000 15782050846061 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140765123/312500000 : ℝ)^2155 ≤ (35132750578269/100000000000000 : ℝ)^1643 := by
    have hnat : (140765123 : ℕ)^2155*100000000000000^1643 ≤ 35132750578269^1643*312500000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140765123 312500000 35132750578269 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081126679/2500000000 : ℝ), (2075623463/5000000000 : ℝ), (140765123/312500000 : ℝ)] ![(33303147715087/100000000000000 : ℝ), (15782050846061/50000000000000 : ℝ), (35132750578269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081126679/2500000000 : ℝ)|^2155 ≤ (33303147715087/100000000000000 : ℝ)^1643
        have hw : |(1081126679/2500000000 : ℝ)|=(1081126679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2075623463/5000000000 : ℝ)|^2155 ≤ (15782050846061/50000000000000 : ℝ)^1643
        have hw : |(2075623463/5000000000 : ℝ)|=(2075623463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140765123/312500000 : ℝ)|^2155 ≤ (35132750578269/100000000000000 : ℝ)^1643
        have hw : |(140765123/312500000 : ℝ)|=(140765123/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s5_4 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2037047209/10000000000 : ℝ)*x 0 + (5245123239/10000000000 : ℝ)*x 1 + (5412048187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037047209/10000000000 : ℝ)^2155 ≤ (6203524641477/50000000000000 : ℝ)^1643 := by
    have hnat : (2037047209 : ℕ)^2155*50000000000000^1643 ≤ 6203524641477^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037047209 10000000000 6203524641477 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245123239/10000000000 : ℝ)^2155 ≤ (21448382637683/50000000000000 : ℝ)^1643 := by
    have hnat : (5245123239 : ℕ)^2155*50000000000000^1643 ≤ 21448382637683^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245123239 10000000000 21448382637683 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412048187/10000000000 : ℝ)^2155 ≤ (893923708647/2000000000000 : ℝ)^1643 := by
    have hnat : (5412048187 : ℕ)^2155*2000000000000^1643 ≤ 893923708647^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412048187 10000000000 893923708647 2000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2037047209/10000000000 : ℝ), (5245123239/10000000000 : ℝ), (5412048187/10000000000 : ℝ)] ![(6203524641477/50000000000000 : ℝ), (21448382637683/50000000000000 : ℝ), (893923708647/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2037047209/10000000000 : ℝ)|^2155 ≤ (6203524641477/50000000000000 : ℝ)^1643
        have hw : |(-2037047209/10000000000 : ℝ)|=(2037047209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245123239/10000000000 : ℝ)|^2155 ≤ (21448382637683/50000000000000 : ℝ)^1643
        have hw : |(5245123239/10000000000 : ℝ)|=(5245123239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412048187/10000000000 : ℝ)|^2155 ≤ (893923708647/2000000000000 : ℝ)^1643
        have hw : |(5412048187/10000000000 : ℝ)|=(5412048187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s5_5 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061120749/2000000000 : ℝ)*x 0 + (-1955172747/10000000000 : ℝ)*x 1 + (5412048197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061120749/2000000000 : ℝ)^2155 ≤ (43546702627199/100000000000000 : ℝ)^1643 := by
    have hnat : (1061120749 : ℕ)^2155*100000000000000^1643 ≤ 43546702627199^1643*2000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061120749 2000000000 43546702627199 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1955172747/10000000000 : ℝ)^2155 ≤ (23514223643/200000000000 : ℝ)^1643 := by
    have hnat : (1955172747 : ℕ)^2155*200000000000^1643 ≤ 23514223643^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955172747 10000000000 23514223643 200000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412048197/10000000000 : ℝ)^2155 ≤ (698377899073/1562500000000 : ℝ)^1643 := by
    have hnat : (5412048197 : ℕ)^2155*1562500000000^1643 ≤ 698377899073^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412048197 10000000000 698377899073 1562500000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061120749/2000000000 : ℝ), (-1955172747/10000000000 : ℝ), (5412048197/10000000000 : ℝ)] ![(43546702627199/100000000000000 : ℝ), (23514223643/200000000000 : ℝ), (698377899073/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061120749/2000000000 : ℝ)|^2155 ≤ (43546702627199/100000000000000 : ℝ)^1643
        have hw : |(1061120749/2000000000 : ℝ)|=(1061120749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1955172747/10000000000 : ℝ)|^2155 ≤ (23514223643/200000000000 : ℝ)^1643
        have hw : |(-1955172747/10000000000 : ℝ)|=(1955172747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412048197/10000000000 : ℝ)|^2155 ≤ (698377899073/1562500000000 : ℝ)^1643
        have hw : |(5412048197/10000000000 : ℝ)|=(5412048197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s5_6 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326400933/2500000000 : ℝ)*x 0 + (2706024103/5000000000 : ℝ)*x 1 + (-1955172751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326400933/2500000000 : ℝ)^2155 ≤ (43546702487249/100000000000000 : ℝ)^1643 := by
    have hnat : (1326400933 : ℕ)^2155*100000000000000^1643 ≤ 43546702487249^1643*2500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326400933 2500000000 43546702487249 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706024103/5000000000 : ℝ)^2155 ≤ (44696185638163/100000000000000 : ℝ)^1643 := by
    have hnat : (2706024103 : ℕ)^2155*100000000000000^1643 ≤ 44696185638163^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706024103 5000000000 44696185638163 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1955172751/10000000000 : ℝ)^2155 ≤ (11757111853049/100000000000000 : ℝ)^1643 := by
    have hnat : (1955172751 : ℕ)^2155*100000000000000^1643 ≤ 11757111853049^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955172751 10000000000 11757111853049 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326400933/2500000000 : ℝ), (2706024103/5000000000 : ℝ), (-1955172751/10000000000 : ℝ)] ![(43546702487249/100000000000000 : ℝ), (44696185638163/100000000000000 : ℝ), (11757111853049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326400933/2500000000 : ℝ)|^2155 ≤ (43546702487249/100000000000000 : ℝ)^1643
        have hw : |(1326400933/2500000000 : ℝ)|=(1326400933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706024103/5000000000 : ℝ)|^2155 ≤ (44696185638163/100000000000000 : ℝ)^1643
        have hw : |(2706024103/5000000000 : ℝ)|=(2706024103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1955172751/10000000000 : ℝ)|^2155 ≤ (11757111853049/100000000000000 : ℝ)^1643
        have hw : |(-1955172751/10000000000 : ℝ)|=(1955172751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s5_7 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (172981297/400000000 : ℝ)*x 0 + (4503213287/10000000000 : ℝ)*x 1 + (4152524169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172981297/400000000 : ℝ)^2155 ≤ (33303407398377/100000000000000 : ℝ)^1643 := by
    have hnat : (172981297 : ℕ)^2155*100000000000000^1643 ≤ 33303407398377^1643*400000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172981297 400000000 33303407398377 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503213287/10000000000 : ℝ)^2155 ≤ (1404790094993/4000000000000 : ℝ)^1643 := by
    have hnat : (4503213287 : ℕ)^2155*4000000000000^1643 ≤ 1404790094993^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503213287 10000000000 1404790094993 4000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4152524169/10000000000 : ℝ)^2155 ≤ (31576840210771/100000000000000 : ℝ)^1643 := by
    have hnat : (4152524169 : ℕ)^2155*100000000000000^1643 ≤ 31576840210771^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152524169 10000000000 31576840210771 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172981297/400000000 : ℝ), (4503213287/10000000000 : ℝ), (4152524169/10000000000 : ℝ)] ![(33303407398377/100000000000000 : ℝ), (1404790094993/4000000000000 : ℝ), (31576840210771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172981297/400000000 : ℝ)|^2155 ≤ (33303407398377/100000000000000 : ℝ)^1643
        have hw : |(172981297/400000000 : ℝ)|=(172981297/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503213287/10000000000 : ℝ)|^2155 ≤ (1404790094993/4000000000000 : ℝ)^1643
        have hw : |(4503213287/10000000000 : ℝ)|=(4503213287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4152524169/10000000000 : ℝ)|^2155 ≤ (31576840210771/100000000000000 : ℝ)^1643
        have hw : |(4152524169/10000000000 : ℝ)|=(4152524169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1350_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (139/1250 : ℝ)*pair X i i ≤ pair X i h) :
    (279/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (92/625 : ℝ)*pair X 0 0 := by
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
  have lower0 : (139/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14763/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (139/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14763/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (139/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14763/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (139/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14763/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (139/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14763/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (139/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (139/1250 : ℝ) ^ (4309/1024 : ℝ) ≤ (9682811836913789/100000000000000000000 : ℝ) := by
    have hpowers : (139/1250 : ℝ)^4309 ≤ (9682811836913789/100000000000000000000 : ℝ)^1024 := by
      have hnat : (139 : ℕ)^4309*100000000000000000000^1024 ≤ 9682811836913789^1024*1250^4309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        139 1250 9682811836913789 100000000000000000000 4309 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (139/1250 : ℝ)) (X := (9682811836913789/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14763/100000 : ℝ) ^ (4309/1024 : ℝ) ≤ (7976645983276209/25000000000000000000 : ℝ) := by
    have hpowers : (14763/100000 : ℝ)^4309 ≤ (7976645983276209/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14763 : ℕ)^4309*25000000000000000000^1024 ≤ 7976645983276209^1024*100000^4309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14763 100000 7976645983276209 25000000000000000000 4309 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14763/100000 : ℝ)) (X := (7976645983276209/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009682811836913789/50000000000000000000 : ℝ) ≤ (625028760929123/625000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (50009682811836913789/50000000000000000000 : ℝ)^1024 ≤ (625028760929123/625000000000000 : ℝ)^4309 := by
      have hnat : (50009682811836913789 : ℕ)^1024*625000000000000^4309 ≤ 625028760929123^4309*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009682811836913789 50000000000000000000 625028760929123 625000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625028760929123/625000000000000 : ℝ)) (X := (50009682811836913789/50000000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (800332715166160149/800000000000000000 : ℝ) ≤ (10000988182676121/10000000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (800332715166160149/800000000000000000 : ℝ)^1024 ≤ (10000988182676121/10000000000000000 : ℝ)^4309 := by
      have hnat : (800332715166160149 : ℕ)^1024*10000000000000000^4309 ≤ 10000988182676121^4309*800000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        800332715166160149 800000000000000000 10000988182676121 10000000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000988182676121/10000000000000000 : ℝ)) (X := (800332715166160149/800000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507976645983276209/12500000000000000000 : ℝ) ≤ (5000758095243137/5000000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (12507976645983276209/12500000000000000000 : ℝ)^1024 ≤ (5000758095243137/5000000000000000 : ℝ)^4309 := by
      have hnat : (12507976645983276209 : ℕ)^1024*5000000000000000^4309 ≤ 5000758095243137^4309*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507976645983276209 12500000000000000000 5000758095243137 5000000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000758095243137/5000000000000000 : ℝ)) (X := (12507976645983276209/12500000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9682811836913789/100000000000000000000 : ℝ) ≤ ((2276245845208682419/2276875000000000000 : ℝ)+2*(528007810153/364300000000000 : ℝ)*(139/1250 : ℝ))^(4309/1024 : ℝ) := by
    rw [show (2276245845208682419/2276875000000000000 : ℝ)+2*(528007810153/364300000000000 : ℝ)*(139/1250 : ℝ)=(625028760929123/625000000000000 : ℝ) by norm_num, show 1+2*(9682811836913789/100000000000000000000 : ℝ)=(50009682811836913789/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7976645983276209/25000000000000000000 : ℝ)+(9682811836913789/100000000000000000000 : ℝ) ≤ ((2276245845208682419/2276875000000000000 : ℝ)+(528007810153/364300000000000 : ℝ)*((14763/100000 : ℝ)+(139/1250 : ℝ)))^(4309/1024 : ℝ) := by
    rw [show (2276245845208682419/2276875000000000000 : ℝ)+(528007810153/364300000000000 : ℝ)*((14763/100000 : ℝ)+(139/1250 : ℝ))=(10000988182676121/10000000000000000 : ℝ) by norm_num, show 1+(7976645983276209/25000000000000000000 : ℝ)+(9682811836913789/100000000000000000000 : ℝ)=(800332715166160149/800000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7976645983276209/25000000000000000000 : ℝ) ≤ ((2276245845208682419/2276875000000000000 : ℝ)+2*(528007810153/364300000000000 : ℝ)*(14763/100000 : ℝ))^(4309/1024 : ℝ) := by
    rw [show (2276245845208682419/2276875000000000000 : ℝ)+2*(528007810153/364300000000000 : ℝ)*(14763/100000 : ℝ)=(5000758095243137/5000000000000000 : ℝ) by norm_num, show 1+2*(7976645983276209/25000000000000000000 : ℝ)=(12507976645983276209/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2276245845208682419/2276875000000000000 : ℝ)*(X 1 0+X 2 0)+(528007810153/364300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (139/1250 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (2276245845208682419/2276875000000000000 : ℝ)) (alpha := (528007810153/364300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2276245845208682419/2276875000000000000 : ℝ)*(X 0 1+X 2 1)+(528007810153/364300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (139/1250 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (2276245845208682419/2276875000000000000 : ℝ)) (alpha := (528007810153/364300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2276245845208682419/2276875000000000000 : ℝ)*(X 0 2+X 1 2)+(528007810153/364300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (139/1250 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (2276245845208682419/2276875000000000000 : ℝ)) (alpha := (528007810153/364300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1018517469/5000000000 : ℝ)*X 0 0+(2706328081/5000000000 : ℝ)*X 0 1+(327782401/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668618993/1250000000 : ℝ)*X 1 0+(-2122702531/10000000000 : ℝ)*X 1 1+(5244518417/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674475973/5000000000 : ℝ)*X 2 0+(327782401/625000000 : ℝ)*X 2 1+(-2122702529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1081126679/2500000000 : ℝ)*X 0 0+(2075623463/5000000000 : ℝ)*X 0 1+(140765123/312500000 : ℝ)*X 0 2+(1081126679/2500000000 : ℝ)*X 1 0+(2075623463/5000000000 : ℝ)*X 1 1+(140765123/312500000 : ℝ)*X 1 2+(1081126679/2500000000 : ℝ)*X 2 0+(2075623463/5000000000 : ℝ)*X 2 1+(140765123/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2037047209/10000000000 : ℝ)*X 0 0+(5245123239/10000000000 : ℝ)*X 0 1+(5412048187/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061120749/2000000000 : ℝ)*X 1 0+(-1955172747/10000000000 : ℝ)*X 1 1+(5412048197/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326400933/2500000000 : ℝ)*X 2 0+(2706024103/5000000000 : ℝ)*X 2 1+(-1955172751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((172981297/400000000 : ℝ)*X 0 0+(4503213287/10000000000 : ℝ)*X 0 1+(4152524169/10000000000 : ℝ)*X 0 2+(172981297/400000000 : ℝ)*X 1 0+(4503213287/10000000000 : ℝ)*X 1 1+(4152524169/10000000000 : ℝ)*X 1 2+(172981297/400000000 : ℝ)*X 2 0+(4503213287/10000000000 : ℝ)*X 2 1+(4152524169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (289117338994999459507214829/28460937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1901267201/100000000000000 : ℝ)*(base19) + (887111191/50000000000000 : ℝ)*(base23) + (69145181/100000000000000 : ℝ)*(lower2) + (126913131/50000000000000 : ℝ)*(upper3) + (16102611/10000000000000 : ℝ)*(upper5) + (2194645627161427/50000000000000 : ℝ)*(major0) + (2194645627161427/50000000000000 : ℝ)*(major1) + (2194645627161427/50000000000000 : ℝ)*(major2) + (2973772479147043/50000000000000 : ℝ)*(sp0) + (5947581910575659/100000000000000 : ℝ)*(sp1) + (5947582037620477/100000000000000 : ℝ)*(sp2) + (283097837657577/10000000000000 : ℝ)*(sp3) + (38853548773/100000000000000 : ℝ)*(sp4) + (799264561/4000000000000 : ℝ)*(sp7) + (707749589547449/25000000000000 : ℝ)*(f.failure) + (5947583811842859/100000000000000 : ℝ)*(f.sum) + (17277171035931/9107500000000000000000000000 : ℝ)*base65 + (1648145221554983163/113843750000000000000000000000000 : ℝ)*base67 + (1598226285682670663/113843750000000000000000000000000 : ℝ)*base69 + (407426379168076913/113843750000000000000000000000000 : ℝ)*base71 + (6567096293217/1138437500000000000000000000 : ℝ)*base73 + (1678395114086795663/113843750000000000000000000000000 : ℝ)*base75 + (2651119666265639413/113843750000000000000000000000000 : ℝ)*base77 + (285787225518139413/113843750000000000000000000000000 : ℝ)*base79 + (18007869510459/9107500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2434363/500000000000000000000 : ℝ)*base89 + (2434363/500000000000000000000 : ℝ)*base91 + (2434363/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (893897366817979212584159901/113843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1412106209/100000000000000 : ℝ)*(base19) + (1472279687/100000000000000 : ℝ)*(base23) + (10807463/6250000000000 : ℝ)*(upper3) + (33269761/100000000000000 : ℝ)*(lower4) + (159850927/100000000000000 : ℝ)*(upper5) + (4421121820379907/100000000000000 : ℝ)*(major0) + (4421121820379907/100000000000000 : ℝ)*(major1) + (4421121820379907/100000000000000 : ℝ)*(major2) + (448557217/1562500000000 : ℝ)*(sp1) + (30194179219/100000000000000 : ℝ)*(sp2) + (5990714991038767/100000000000000 : ℝ)*(sp4) + (599068487127067/10000000000000 : ℝ)*(sp5) + (2995341662289931/50000000000000 : ℝ)*(sp6) + (1425764193994401/50000000000000 : ℝ)*(sp7) + (1425764193994401/50000000000000 : ℝ)*(f.failure) + (5990714991038767/100000000000000 : ℝ)*(f.sum) + (58551805468583/9107500000000000000000000000 : ℝ)*base65 + (1074642316956511283/227687500000000000000000000000000 : ℝ)*base67 + (2301308158541511283/227687500000000000000000000000000 : ℝ)*base69 + (2879280740409323783/227687500000000000000000000000000 : ℝ)*base71 + (45671856209231/18215000000000000000000000000 : ℝ)*base73 + (1594062455399176217/227687500000000000000000000000000 : ℝ)*base76 + (299789531893823783/227687500000000000000000000000000 : ℝ)*base77 + (2192495339069051217/227687500000000000000000000000000 : ℝ)*base80 + (11923195103237/2276875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (10198413/1000000000000000000000 : ℝ)*base90 + (10198413/1000000000000000000000 : ℝ)*base92 + (10198413/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1350_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (139/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (92/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1350_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1350_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (619/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (92/625 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1350_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1350_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1350_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (619/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (92/625 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1350_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

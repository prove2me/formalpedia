-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1424_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:52:14.048854+00:00
-- url     : https://prove2.me/submissions/65124fe6-7b8b-4cd0-ba99-ae19baa83bc9

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
theorem support_rectangle_w1424_s0_0 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-440412011/2500000000 : ℝ)*x 0 + (5962247043/10000000000 : ℝ)*x 1 + (966018629/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (440412011/2500000000 : ℝ)^137 ≤ (2594442423677/25000000000000 : ℝ)^105 := by
    have hnat : (440412011 : ℕ)^137*25000000000000^105 ≤ 2594442423677^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440412011 2500000000 2594442423677 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5962247043/10000000000 : ℝ)^137 ≤ (10185760873837/20000000000000 : ℝ)^105 := by
    have hnat : (5962247043 : ℕ)^137*20000000000000^105 ≤ 10185760873837^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5962247043 10000000000 10185760873837 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (966018629/2000000000 : ℝ)^137 ≤ (38693425918793/100000000000000 : ℝ)^105 := by
    have hnat : (966018629 : ℕ)^137*100000000000000^105 ≤ 38693425918793^105*2000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966018629 2000000000 38693425918793 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-440412011/2500000000 : ℝ), (5962247043/10000000000 : ℝ), (966018629/2000000000 : ℝ)] ![(2594442423677/25000000000000 : ℝ), (10185760873837/20000000000000 : ℝ), (38693425918793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-440412011/2500000000 : ℝ)|^137 ≤ (2594442423677/25000000000000 : ℝ)^105
        have hw : |(-440412011/2500000000 : ℝ)|=(440412011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5962247043/10000000000 : ℝ)|^137 ≤ (10185760873837/20000000000000 : ℝ)^105
        have hw : |(5962247043/10000000000 : ℝ)|=(5962247043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(966018629/2000000000 : ℝ)|^137 ≤ (38693425918793/100000000000000 : ℝ)^105
        have hw : |(966018629/2000000000 : ℝ)|=(966018629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s0_1 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5492655463/10000000000 : ℝ)*x 0 + (-240141983/1000000000 : ℝ)*x 1 + (1207523389/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5492655463/10000000000 : ℝ)^137 ≤ (45759148429093/100000000000000 : ℝ)^105 := by
    have hnat : (5492655463 : ℕ)^137*100000000000000^105 ≤ 45759148429093^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492655463 10000000000 45759148429093 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (240141983/1000000000 : ℝ)^137 ≤ (15547421344817/100000000000000 : ℝ)^105 := by
    have hnat : (240141983 : ℕ)^137*100000000000000^105 ≤ 15547421344817^105*1000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240141983 1000000000 15547421344817 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1207523389/2500000000 : ℝ)^137 ≤ (38693430214699/100000000000000 : ℝ)^105 := by
    have hnat : (1207523389 : ℕ)^137*100000000000000^105 ≤ 38693430214699^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207523389 2500000000 38693430214699 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5492655463/10000000000 : ℝ), (-240141983/1000000000 : ℝ), (1207523389/2500000000 : ℝ)] ![(45759148429093/100000000000000 : ℝ), (15547421344817/100000000000000 : ℝ), (38693430214699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5492655463/10000000000 : ℝ)|^137 ≤ (45759148429093/100000000000000 : ℝ)^105
        have hw : |(5492655463/10000000000 : ℝ)|=(5492655463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-240141983/1000000000 : ℝ)|^137 ≤ (15547421344817/100000000000000 : ℝ)^105
        have hw : |(-240141983/1000000000 : ℝ)|=(240141983/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1207523389/2500000000 : ℝ)|^137 ≤ (38693430214699/100000000000000 : ℝ)^105
        have hw : |(1207523389/2500000000 : ℝ)|=(1207523389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s0_2 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (274632793/500000000 : ℝ)*x 0 + (966018677/2000000000 : ℝ)*x 1 + (-240141953/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (274632793/500000000 : ℝ)^137 ≤ (5719894093057/12500000000000 : ℝ)^105 := by
    have hnat : (274632793 : ℕ)^137*12500000000000^105 ≤ 5719894093057^105*500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274632793 500000000 5719894093057 12500000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (966018677/2000000000 : ℝ)^137 ≤ (38693428427351/100000000000000 : ℝ)^105 := by
    have hnat : (966018677 : ℕ)^137*100000000000000^105 ≤ 38693428427351^105*2000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966018677 2000000000 38693428427351 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240141953/1000000000 : ℝ)^137 ≤ (7773709405303/50000000000000 : ℝ)^105 := by
    have hnat : (240141953 : ℕ)^137*50000000000000^105 ≤ 7773709405303^105*1000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240141953 1000000000 7773709405303 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(274632793/500000000 : ℝ), (966018677/2000000000 : ℝ), (-240141953/1000000000 : ℝ)] ![(5719894093057/12500000000000 : ℝ), (38693428427351/100000000000000 : ℝ), (7773709405303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(274632793/500000000 : ℝ)|^137 ≤ (5719894093057/12500000000000 : ℝ)^105
        have hw : |(274632793/500000000 : ℝ)|=(274632793/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(966018677/2000000000 : ℝ)|^137 ≤ (38693428427351/100000000000000 : ℝ)^105
        have hw : |(966018677/2000000000 : ℝ)|=(966018677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-240141953/1000000000 : ℝ)|^137 ≤ (7773709405303/50000000000000 : ℝ)^105
        have hw : |(-240141953/1000000000 : ℝ)|=(240141953/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s0_3 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4166718691/10000000000 : ℝ)*x 0 + (48491931/156250000 : ℝ)*x 1 + (5548225541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4166718691/10000000000 : ℝ)^137 ≤ (31909641950597/100000000000000 : ℝ)^105 := by
    have hnat : (4166718691 : ℕ)^137*100000000000000^105 ≤ 31909641950597^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166718691 10000000000 31909641950597 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48491931/156250000 : ℝ)^137 ≤ (21726237552083/100000000000000 : ℝ)^105 := by
    have hnat : (48491931 : ℕ)^137*100000000000000^105 ≤ 21726237552083^105*156250000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48491931 156250000 21726237552083 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5548225541/10000000000 : ℝ)^137 ≤ (9272824095539/20000000000000 : ℝ)^105 := by
    have hnat : (5548225541 : ℕ)^137*20000000000000^105 ≤ 9272824095539^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5548225541 10000000000 9272824095539 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4166718691/10000000000 : ℝ), (48491931/156250000 : ℝ), (5548225541/10000000000 : ℝ)] ![(31909641950597/100000000000000 : ℝ), (21726237552083/100000000000000 : ℝ), (9272824095539/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4166718691/10000000000 : ℝ)|^137 ≤ (31909641950597/100000000000000 : ℝ)^105
        have hw : |(4166718691/10000000000 : ℝ)|=(4166718691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(48491931/156250000 : ℝ)|^137 ≤ (21726237552083/100000000000000 : ℝ)^105
        have hw : |(48491931/156250000 : ℝ)|=(48491931/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5548225541/10000000000 : ℝ)|^137 ≤ (9272824095539/20000000000000 : ℝ)^105
        have hw : |(5548225541/10000000000 : ℝ)|=(5548225541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s0_4 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1765689447/10000000000 : ℝ)*x 0 + (2429535709/5000000000 : ℝ)*x 1 + (1483058523/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1765689447/10000000000 : ℝ)^137 ≤ (2602210974859/25000000000000 : ℝ)^105 := by
    have hnat : (1765689447 : ℕ)^137*25000000000000^105 ≤ 2602210974859^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1765689447 10000000000 2602210974859 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2429535709/5000000000 : ℝ)^137 ≤ (38996592797213/100000000000000 : ℝ)^105 := by
    have hnat : (2429535709 : ℕ)^137*100000000000000^105 ≤ 38996592797213^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2429535709 5000000000 38996592797213 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1483058523/2500000000 : ℝ)^137 ≤ (50594563283421/100000000000000 : ℝ)^105 := by
    have hnat : (1483058523 : ℕ)^137*100000000000000^105 ≤ 50594563283421^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1483058523 2500000000 50594563283421 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1765689447/10000000000 : ℝ), (2429535709/5000000000 : ℝ), (1483058523/2500000000 : ℝ)] ![(2602210974859/25000000000000 : ℝ), (38996592797213/100000000000000 : ℝ), (50594563283421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1765689447/10000000000 : ℝ)|^137 ≤ (2602210974859/25000000000000 : ℝ)^105
        have hw : |(-1765689447/10000000000 : ℝ)|=(1765689447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2429535709/5000000000 : ℝ)|^137 ≤ (38996592797213/100000000000000 : ℝ)^105
        have hw : |(2429535709/5000000000 : ℝ)|=(2429535709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1483058523/2500000000 : ℝ)|^137 ≤ (50594563283421/100000000000000 : ℝ)^105
        have hw : |(1483058523/2500000000 : ℝ)|=(1483058523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s0_5 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2591834391/5000000000 : ℝ)*x 0 + (-129927869/1000000000 : ℝ)*x 1 + (1483058543/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2591834391/5000000000 : ℝ)^137 ≤ (42429659521953/100000000000000 : ℝ)^105 := by
    have hnat : (2591834391 : ℕ)^137*100000000000000^105 ≤ 42429659521953^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591834391 5000000000 42429659521953 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129927869/1000000000 : ℝ)^137 ≤ (6975776296793/100000000000000 : ℝ)^105 := by
    have hnat : (129927869 : ℕ)^137*100000000000000^105 ≤ 6975776296793^105*1000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129927869 1000000000 6975776296793 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1483058543/2500000000 : ℝ)^137 ≤ (2529728208683/5000000000000 : ℝ)^105 := by
    have hnat : (1483058543 : ℕ)^137*5000000000000^105 ≤ 2529728208683^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1483058543 2500000000 2529728208683 5000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2591834391/5000000000 : ℝ), (-129927869/1000000000 : ℝ), (1483058543/2500000000 : ℝ)] ![(42429659521953/100000000000000 : ℝ), (6975776296793/100000000000000 : ℝ), (2529728208683/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2591834391/5000000000 : ℝ)|^137 ≤ (42429659521953/100000000000000 : ℝ)^105
        have hw : |(2591834391/5000000000 : ℝ)|=(2591834391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-129927869/1000000000 : ℝ)|^137 ≤ (6975776296793/100000000000000 : ℝ)^105
        have hw : |(-129927869/1000000000 : ℝ)|=(129927869/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1483058543/2500000000 : ℝ)|^137 ≤ (2529728208683/5000000000000 : ℝ)^105
        have hw : |(1483058543/2500000000 : ℝ)|=(1483058543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s0_6 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5183668801/10000000000 : ℝ)*x 0 + (1483058501/2500000000 : ℝ)*x 1 + (-81204933/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183668801/10000000000 : ℝ)^137 ≤ (42429659724869/100000000000000 : ℝ)^105 := by
    have hnat : (5183668801 : ℕ)^137*100000000000000^105 ≤ 42429659724869^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183668801 10000000000 42429659724869 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1483058501/2500000000 : ℝ)^137 ≤ (50594562304157/100000000000000 : ℝ)^105 := by
    have hnat : (1483058501 : ℕ)^137*100000000000000^105 ≤ 50594562304157^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1483058501 2500000000 50594562304157 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81204933/625000000 : ℝ)^137 ≤ (3487888982017/50000000000000 : ℝ)^105 := by
    have hnat : (81204933 : ℕ)^137*50000000000000^105 ≤ 3487888982017^105*625000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81204933 625000000 3487888982017 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183668801/10000000000 : ℝ), (1483058501/2500000000 : ℝ), (-81204933/625000000 : ℝ)] ![(42429659724869/100000000000000 : ℝ), (50594562304157/100000000000000 : ℝ), (3487888982017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183668801/10000000000 : ℝ)|^137 ≤ (42429659724869/100000000000000 : ℝ)^105
        have hw : |(5183668801/10000000000 : ℝ)|=(5183668801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1483058501/2500000000 : ℝ)|^137 ≤ (50594562304157/100000000000000 : ℝ)^105
        have hw : |(1483058501/2500000000 : ℝ)|=(1483058501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-81204933/625000000 : ℝ)|^137 ≤ (3487888982017/50000000000000 : ℝ)^105
        have hw : |(-81204933/625000000 : ℝ)|=(81204933/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s0_7 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4175447613/10000000000 : ℝ)*x 0 + (2742825243/5000000000 : ℝ)*x 1 + (5069269/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4175447613/10000000000 : ℝ)^137 ≤ (6399378098571/20000000000000 : ℝ)^105 := by
    have hnat : (4175447613 : ℕ)^137*20000000000000^105 ≤ 6399378098571^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4175447613 10000000000 6399378098571 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2742825243/5000000000 : ℝ)^137 ≤ (22841509802207/50000000000000 : ℝ)^105 := by
    have hnat : (2742825243 : ℕ)^137*50000000000000^105 ≤ 22841509802207^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742825243 5000000000 22841509802207 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5069269/16000000 : ℝ)^137 ≤ (22320089890379/100000000000000 : ℝ)^105 := by
    have hnat : (5069269 : ℕ)^137*100000000000000^105 ≤ 22320089890379^105*16000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5069269 16000000 22320089890379 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4175447613/10000000000 : ℝ), (2742825243/5000000000 : ℝ), (5069269/16000000 : ℝ)] ![(6399378098571/20000000000000 : ℝ), (22841509802207/50000000000000 : ℝ), (22320089890379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4175447613/10000000000 : ℝ)|^137 ≤ (6399378098571/20000000000000 : ℝ)^105
        have hw : |(4175447613/10000000000 : ℝ)|=(4175447613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2742825243/5000000000 : ℝ)|^137 ≤ (22841509802207/50000000000000 : ℝ)^105
        have hw : |(2742825243/5000000000 : ℝ)|=(2742825243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5069269/16000000 : ℝ)|^137 ≤ (22320089890379/100000000000000 : ℝ)^105
        have hw : |(5069269/16000000 : ℝ)|=(5069269/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1424_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (503/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26293/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4383/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4383 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4383*1^1024 ≤ 0^1024*1^4383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4383/1024 : ℝ) ≤ (990097480806065533/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4383 ≤ (990097480806065533/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4383*50000000000000000000^1024 ≤ 990097480806065533^1024*5^4383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 990097480806065533 50000000000000000000 4383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (990097480806065533/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4383 := by
      have hnat : (1 : ℕ)^1024*1^4383 ≤ 1^4383*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50990097480806065533/50000000000000000000 : ℝ) ≤ (10045916282340933/10000000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (50990097480806065533/50000000000000000000 : ℝ)^1024 ≤ (10045916282340933/10000000000000000 : ℝ)^4383 := by
      have hnat : (50990097480806065533 : ℕ)^1024*10000000000000000^4383 ≤ 10045916282340933^4383*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50990097480806065533 50000000000000000000 10045916282340933 10000000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10045916282340933/10000000000000000 : ℝ)) (X := (50990097480806065533/50000000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25990097480806065533/25000000000000000000 : ℝ) ≤ (5045916282340933/5000000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (25990097480806065533/25000000000000000000 : ℝ)^1024 ≤ (5045916282340933/5000000000000000 : ℝ)^4383 := by
      have hnat : (25990097480806065533 : ℕ)^1024*5000000000000000^4383 ≤ 5045916282340933^4383*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25990097480806065533 25000000000000000000 5045916282340933 5000000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5045916282340933/5000000000000000 : ℝ)) (X := (25990097480806065533/25000000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(45916282340933/4000000000000000 : ℝ)*(0 : ℝ))^(4383/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(45916282340933/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(990097480806065533/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(45916282340933/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4383/1024 : ℝ) := by
    rw [show (1 : ℝ)+(45916282340933/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10045916282340933/10000000000000000 : ℝ) by norm_num, show 1+(990097480806065533/50000000000000000000 : ℝ)+(0 : ℝ)=(50990097480806065533/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(990097480806065533/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(45916282340933/4000000000000000 : ℝ)*(2/5 : ℝ))^(4383/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(45916282340933/4000000000000000 : ℝ)*(2/5 : ℝ)=(5045916282340933/5000000000000000 : ℝ) by norm_num, show 1+2*(990097480806065533/50000000000000000000 : ℝ)=(25990097480806065533/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(45916282340933/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45916282340933/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(45916282340933/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45916282340933/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(45916282340933/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45916282340933/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-440412011/2500000000 : ℝ)*X 0 0+(5962247043/10000000000 : ℝ)*X 0 1+(966018629/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5492655463/10000000000 : ℝ)*X 1 0+(-240141983/1000000000 : ℝ)*X 1 1+(1207523389/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((274632793/500000000 : ℝ)*X 2 0+(966018677/2000000000 : ℝ)*X 2 1+(-240141953/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4166718691/10000000000 : ℝ)*X 0 0+(48491931/156250000 : ℝ)*X 0 1+(5548225541/10000000000 : ℝ)*X 0 2+(4166718691/10000000000 : ℝ)*X 1 0+(48491931/156250000 : ℝ)*X 1 1+(5548225541/10000000000 : ℝ)*X 1 2+(4166718691/10000000000 : ℝ)*X 2 0+(48491931/156250000 : ℝ)*X 2 1+(5548225541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1765689447/10000000000 : ℝ)*X 0 0+(2429535709/5000000000 : ℝ)*X 0 1+(1483058523/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2591834391/5000000000 : ℝ)*X 1 0+(-129927869/1000000000 : ℝ)*X 1 1+(1483058543/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5183668801/10000000000 : ℝ)*X 2 0+(1483058501/2500000000 : ℝ)*X 2 1+(-81204933/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4175447613/10000000000 : ℝ)*X 0 0+(2742825243/5000000000 : ℝ)*X 0 1+(5069269/16000000 : ℝ)*X 0 2+(4175447613/10000000000 : ℝ)*X 1 0+(2742825243/5000000000 : ℝ)*X 1 1+(5069269/16000000 : ℝ)*X 1 2+(4175447613/10000000000 : ℝ)*X 2 0+(2742825243/5000000000 : ℝ)*X 2 1+(5069269/16000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6763630011795615801/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (101084011/6250000000000 : ℝ)*(base19) + (413214269/25000000000000 : ℝ)*(base23) + (44315031/25000000000000 : ℝ)*(upper3) + (486259/3125000000000 : ℝ)*(upper4) + (251437509/100000000000000 : ℝ)*(upper5) + (646165371466313/100000000000000 : ℝ)*(major0) + (646165371466313/100000000000000 : ℝ)*(major1) + (646165371466313/100000000000000 : ℝ)*(major2) + (3533109983407/400000000000 : ℝ)*(sp0) + (441641093091097/50000000000000 : ℝ)*(sp1) + (441641075334647/50000000000000 : ℝ)*(sp2) + (204521963424237/50000000000000 : ℝ)*(sp3) + (6307674621/100000000000000 : ℝ)*(sp4) + (1393551721/50000000000000 : ℝ)*(sp7) + (102261678487979/25000000000000 : ℝ)*(f.failure) + (88328380352637/10000000000000 : ℝ)*(f.sum) + (977256411890029/200000000000000000000000000000 : ℝ)*base65 + (1801394191909971/400000000000000000000000000000 : ℝ)*base68 + (5554899035909971/400000000000000000000000000000 : ℝ)*base70 + (1715383469690029/400000000000000000000000000000 : ℝ)*base71 + (201895068890029/200000000000000000000000000000 : ℝ)*base73 + (3927182628709971/400000000000000000000000000000 : ℝ)*base76 + (2134111337509971/400000000000000000000000000000 : ℝ)*base78 + (549380863290029/400000000000000000000000000000 : ℝ)*base79 + (490841382309971/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (12947379/2500000000000000000000 : ℝ)*base89 + (12947379/2500000000000000000000 : ℝ)*base91 + (12947379/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4505289316203873423/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2055817387/100000000000000 : ℝ)*(base19) + (259030787/12500000000000 : ℝ)*(base23) + (197382657/100000000000000 : ℝ)*(base32) + (77661217/25000000000000 : ℝ)*(upper3) + (182084283/100000000000000 : ℝ)*(upper5) + (170418789875987/25000000000000 : ℝ)*(major0) + (170418789875987/25000000000000 : ℝ)*(major1) + (170418789875987/25000000000000 : ℝ)*(major2) + (24183307/500000000000 : ℝ)*(sp1) + (2527486683/50000000000000 : ℝ)*(sp2) + (931824288105853/100000000000000 : ℝ)*(sp4) + (465908697813533/50000000000000 : ℝ)*(sp5) + (931817160886191/100000000000000 : ℝ)*(sp6) + (431525533166763/100000000000000 : ℝ)*(sp7) + (21576286527471/5000000000000 : ℝ)*(f.failure) + (931824288105853/100000000000000 : ℝ)*(f.sum) + (78503547524129/50000000000000000000000000000 : ℝ)*base66 + (129328486675871/100000000000000000000000000000 : ℝ)*base67 + (557134638775871/100000000000000000000000000000 : ℝ)*base69 + (9487729224129/100000000000000000000000000000 : ℝ)*base72 + (25261440024129/50000000000000000000000000000 : ℝ)*base74 + (185544911175871/100000000000000000000000000000 : ℝ)*base75 + (6744723124129/100000000000000000000000000000 : ℝ)*base78 + (147207174675871/100000000000000000000000000000 : ℝ)*base79 + (144574966525871/50000000000000000000000000000 : ℝ)*base81 + (1938071/500000000000000000000 : ℝ)*base89 + (1938071/500000000000000000000 : ℝ)*base91 + (1938071/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1424_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (503/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26293/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1424_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1424_s1_0 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-96735537/500000000 : ℝ)*x 0 + (1121448957/2000000000 : ℝ)*x 1 + (2537078461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (96735537/500000000 : ℝ)^137 ≤ (1172745536863/10000000000000 : ℝ)^105 := by
    have hnat : (96735537 : ℕ)^137*10000000000000^105 ≤ 1172745536863^105*500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96735537 500000000 1172745536863 10000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121448957/2000000000 : ℝ)^137 ≤ (9401733469751/20000000000000 : ℝ)^105 := by
    have hnat : (1121448957 : ℕ)^137*20000000000000^105 ≤ 9401733469751^105*2000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121448957 2000000000 9401733469751 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2537078461/5000000000 : ℝ)^137 ≤ (41263877269481/100000000000000 : ℝ)^105 := by
    have hnat : (2537078461 : ℕ)^137*100000000000000^105 ≤ 41263877269481^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2537078461 5000000000 41263877269481 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-96735537/500000000 : ℝ), (1121448957/2000000000 : ℝ), (2537078461/5000000000 : ℝ)] ![(1172745536863/10000000000000 : ℝ), (9401733469751/20000000000000 : ℝ), (41263877269481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-96735537/500000000 : ℝ)|^137 ≤ (1172745536863/10000000000000 : ℝ)^105
        have hw : |(-96735537/500000000 : ℝ)|=(96735537/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121448957/2000000000 : ℝ)|^137 ≤ (9401733469751/20000000000000 : ℝ)^105
        have hw : |(1121448957/2000000000 : ℝ)|=(1121448957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2537078461/5000000000 : ℝ)|^137 ≤ (41263877269481/100000000000000 : ℝ)^105
        have hw : |(2537078461/5000000000 : ℝ)|=(2537078461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s1_1 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5397314307/10000000000 : ℝ)*x 0 + (-554323893/2500000000 : ℝ)*x 1 + (5074158093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5397314307/10000000000 : ℝ)^137 ≤ (11181387196431/25000000000000 : ℝ)^105 := by
    have hnat : (5397314307 : ℕ)^137*25000000000000^105 ≤ 11181387196431^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397314307 10000000000 11181387196431 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (554323893/2500000000 : ℝ)^137 ≤ (14010561501067/100000000000000 : ℝ)^105 := by
    have hnat : (554323893 : ℕ)^137*100000000000000^105 ≤ 14010561501067^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554323893 2500000000 14010561501067 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5074158093/10000000000 : ℝ)^137 ≤ (20631944847211/50000000000000 : ℝ)^105 := by
    have hnat : (5074158093 : ℕ)^137*50000000000000^105 ≤ 20631944847211^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5074158093 10000000000 20631944847211 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5397314307/10000000000 : ℝ), (-554323893/2500000000 : ℝ), (5074158093/10000000000 : ℝ)] ![(11181387196431/25000000000000 : ℝ), (14010561501067/100000000000000 : ℝ), (20631944847211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5397314307/10000000000 : ℝ)|^137 ≤ (11181387196431/25000000000000 : ℝ)^105
        have hw : |(5397314307/10000000000 : ℝ)|=(5397314307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-554323893/2500000000 : ℝ)|^137 ≤ (14010561501067/100000000000000 : ℝ)^105
        have hw : |(-554323893/2500000000 : ℝ)|=(554323893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5074158093/10000000000 : ℝ)|^137 ≤ (20631944847211/50000000000000 : ℝ)^105
        have hw : |(5074158093/10000000000 : ℝ)|=(5074158093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s1_2 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2698657617/5000000000 : ℝ)*x 0 + (2537078529/5000000000 : ℝ)*x 1 + (-2217295689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698657617/5000000000 : ℝ)^137 ≤ (22362779404261/50000000000000 : ℝ)^105 := by
    have hnat : (2698657617 : ℕ)^137*50000000000000^105 ≤ 22362779404261^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698657617 5000000000 22362779404261 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2537078529/5000000000 : ℝ)^137 ≤ (8252775742503/20000000000000 : ℝ)^105 := by
    have hnat : (2537078529 : ℕ)^137*20000000000000^105 ≤ 8252775742503^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2537078529 5000000000 8252775742503 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2217295689/10000000000 : ℝ)^137 ≤ (14010562465671/100000000000000 : ℝ)^105 := by
    have hnat : (2217295689 : ℕ)^137*100000000000000^105 ≤ 14010562465671^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217295689 10000000000 14010562465671 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698657617/5000000000 : ℝ), (2537078529/5000000000 : ℝ), (-2217295689/10000000000 : ℝ)] ![(22362779404261/50000000000000 : ℝ), (8252775742503/20000000000000 : ℝ), (14010562465671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698657617/5000000000 : ℝ)|^137 ≤ (22362779404261/50000000000000 : ℝ)^105
        have hw : |(2698657617/5000000000 : ℝ)|=(2698657617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2537078529/5000000000 : ℝ)|^137 ≤ (8252775742503/20000000000000 : ℝ)^105
        have hw : |(2537078529/5000000000 : ℝ)|=(2537078529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2217295689/10000000000 : ℝ)|^137 ≤ (14010562465671/100000000000000 : ℝ)^105
        have hw : |(-2217295689/10000000000 : ℝ)|=(2217295689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s1_3 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4277545089/10000000000 : ℝ)*x 0 + (747323859/2000000000 : ℝ)*x 1 + (488775211/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4277545089/10000000000 : ℝ)^137 ≤ (16510748536601/50000000000000 : ℝ)^105 := by
    have hnat : (4277545089 : ℕ)^137*50000000000000^105 ≤ 16510748536601^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4277545089 10000000000 16510748536601 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (747323859/2000000000 : ℝ)^137 ≤ (1730082088991/6250000000000 : ℝ)^105 := by
    have hnat : (747323859 : ℕ)^137*6250000000000^105 ≤ 1730082088991^105*2000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      747323859 2000000000 1730082088991 6250000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (488775211/1000000000 : ℝ)^137 ≤ (19648594740167/50000000000000 : ℝ)^105 := by
    have hnat : (488775211 : ℕ)^137*50000000000000^105 ≤ 19648594740167^105*1000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488775211 1000000000 19648594740167 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4277545089/10000000000 : ℝ), (747323859/2000000000 : ℝ), (488775211/1000000000 : ℝ)] ![(16510748536601/50000000000000 : ℝ), (1730082088991/6250000000000 : ℝ), (19648594740167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4277545089/10000000000 : ℝ)|^137 ≤ (16510748536601/50000000000000 : ℝ)^105
        have hw : |(4277545089/10000000000 : ℝ)|=(4277545089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(747323859/2000000000 : ℝ)|^137 ≤ (1730082088991/6250000000000 : ℝ)^105
        have hw : |(747323859/2000000000 : ℝ)|=(747323859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(488775211/1000000000 : ℝ)|^137 ≤ (19648594740167/50000000000000 : ℝ)^105
        have hw : |(488775211/1000000000 : ℝ)|=(488775211/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s1_4 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-387023133/2000000000 : ℝ)*x 0 + (5080432817/10000000000 : ℝ)*x 1 + (1400215511/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (387023133/2000000000 : ℝ)^137 ≤ (11730658003701/100000000000000 : ℝ)^105 := by
    have hnat : (387023133 : ℕ)^137*100000000000000^105 ≤ 11730658003701^105*2000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387023133 2000000000 11730658003701 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5080432817/10000000000 : ℝ)^137 ≤ (41330480438937/100000000000000 : ℝ)^105 := by
    have hnat : (5080432817 : ℕ)^137*100000000000000^105 ≤ 41330480438937^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080432817 10000000000 41330480438937 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1400215511/2500000000 : ℝ)^137 ≤ (46938861541047/100000000000000 : ℝ)^105 := by
    have hnat : (1400215511 : ℕ)^137*100000000000000^105 ≤ 46938861541047^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1400215511 2500000000 46938861541047 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-387023133/2000000000 : ℝ), (5080432817/10000000000 : ℝ), (1400215511/2500000000 : ℝ)] ![(11730658003701/100000000000000 : ℝ), (41330480438937/100000000000000 : ℝ), (46938861541047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-387023133/2000000000 : ℝ)|^137 ≤ (11730658003701/100000000000000 : ℝ)^105
        have hw : |(-387023133/2000000000 : ℝ)|=(387023133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5080432817/10000000000 : ℝ)|^137 ≤ (41330480438937/100000000000000 : ℝ)^105
        have hw : |(5080432817/10000000000 : ℝ)|=(5080432817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1400215511/2500000000 : ℝ)|^137 ≤ (46938861541047/100000000000000 : ℝ)^105
        have hw : |(1400215511/2500000000 : ℝ)|=(1400215511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s1_5 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5258084991/10000000000 : ℝ)*x 0 + (-422647771/2500000000 : ℝ)*x 1 + (700107757/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258084991/10000000000 : ℝ)^137 ≤ (8645228679409/20000000000000 : ℝ)^105 := by
    have hnat : (5258084991 : ℕ)^137*20000000000000^105 ≤ 8645228679409^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258084991 10000000000 8645228679409 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422647771/2500000000 : ℝ)^137 ≤ (2458748728681/25000000000000 : ℝ)^105 := by
    have hnat : (422647771 : ℕ)^137*25000000000000^105 ≤ 2458748728681^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422647771 2500000000 2458748728681 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (700107757/1250000000 : ℝ)^137 ≤ (5867357709033/12500000000000 : ℝ)^105 := by
    have hnat : (700107757 : ℕ)^137*12500000000000^105 ≤ 5867357709033^105*1250000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      700107757 1250000000 5867357709033 12500000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258084991/10000000000 : ℝ), (-422647771/2500000000 : ℝ), (700107757/1250000000 : ℝ)] ![(8645228679409/20000000000000 : ℝ), (2458748728681/25000000000000 : ℝ), (5867357709033/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258084991/10000000000 : ℝ)|^137 ≤ (8645228679409/20000000000000 : ℝ)^105
        have hw : |(5258084991/10000000000 : ℝ)|=(5258084991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-422647771/2500000000 : ℝ)|^137 ≤ (2458748728681/25000000000000 : ℝ)^105
        have hw : |(-422647771/2500000000 : ℝ)|=(422647771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(700107757/1250000000 : ℝ)|^137 ≤ (5867357709033/12500000000000 : ℝ)^105
        have hw : |(700107757/1250000000 : ℝ)|=(700107757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s1_6 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2629042477/5000000000 : ℝ)*x 0 + (280043101/500000000 : ℝ)*x 1 + (-1690591189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2629042477/5000000000 : ℝ)^137 ≤ (10806535750043/25000000000000 : ℝ)^105 := by
    have hnat : (2629042477 : ℕ)^137*25000000000000^105 ≤ 10806535750043^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629042477 5000000000 10806535750043 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280043101/500000000 : ℝ)^137 ≤ (46938861278613/100000000000000 : ℝ)^105 := by
    have hnat : (280043101 : ℕ)^137*100000000000000^105 ≤ 46938861278613^105*500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280043101 500000000 46938861278613 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1690591189/10000000000 : ℝ)^137 ≤ (245874892793/2500000000000 : ℝ)^105 := by
    have hnat : (1690591189 : ℕ)^137*2500000000000^105 ≤ 245874892793^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1690591189 10000000000 245874892793 2500000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2629042477/5000000000 : ℝ), (280043101/500000000 : ℝ), (-1690591189/10000000000 : ℝ)] ![(10806535750043/25000000000000 : ℝ), (46938861278613/100000000000000 : ℝ), (245874892793/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2629042477/5000000000 : ℝ)|^137 ≤ (10806535750043/25000000000000 : ℝ)^105
        have hw : |(2629042477/5000000000 : ℝ)|=(2629042477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280043101/500000000 : ℝ)|^137 ≤ (46938861278613/100000000000000 : ℝ)^105
        have hw : |(280043101/500000000 : ℝ)|=(280043101/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1690591189/10000000000 : ℝ)|^137 ≤ (245874892793/2500000000000 : ℝ)^105
        have hw : |(-1690591189/10000000000 : ℝ)|=(1690591189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s1_7 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2139209891/5000000000 : ℝ)*x 0 + (974840219/2000000000 : ℝ)*x 1 + (1875200281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139209891/5000000000 : ℝ)^137 ≤ (33030307614947/100000000000000 : ℝ)^105 := by
    have hnat : (2139209891 : ℕ)^137*100000000000000^105 ≤ 33030307614947^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139209891 5000000000 33030307614947 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (974840219/2000000000 : ℝ)^137 ≤ (19577548387823/50000000000000 : ℝ)^105 := by
    have hnat : (974840219 : ℕ)^137*50000000000000^105 ≤ 19577548387823^105*2000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974840219 2000000000 19577548387823 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1875200281/5000000000 : ℝ)^137 ≤ (217301528077/781250000000 : ℝ)^105 := by
    have hnat : (1875200281 : ℕ)^137*781250000000^105 ≤ 217301528077^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875200281 5000000000 217301528077 781250000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2139209891/5000000000 : ℝ), (974840219/2000000000 : ℝ), (1875200281/5000000000 : ℝ)] ![(33030307614947/100000000000000 : ℝ), (19577548387823/50000000000000 : ℝ), (217301528077/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2139209891/5000000000 : ℝ)|^137 ≤ (33030307614947/100000000000000 : ℝ)^105
        have hw : |(2139209891/5000000000 : ℝ)|=(2139209891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(974840219/2000000000 : ℝ)|^137 ≤ (19577548387823/50000000000000 : ℝ)^105
        have hw : |(974840219/2000000000 : ℝ)|=(974840219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1875200281/5000000000 : ℝ)|^137 ≤ (217301528077/781250000000 : ℝ)^105
        have hw : |(1875200281/5000000000 : ℝ)|=(1875200281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1424_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26293/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (503/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (761/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (118/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26293/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (503/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26293/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (503/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26293/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (503/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26293/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (503/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26293/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (503/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26293/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (503/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (503/25000 : ℝ) ^ (4383/1024 : ℝ) ≤ (2741788127627/50000000000000000000 : ℝ) := by
    have hpowers : (503/25000 : ℝ)^4383 ≤ (2741788127627/50000000000000000000 : ℝ)^1024 := by
      have hnat : (503 : ℕ)^4383*50000000000000000000^1024 ≤ 2741788127627^1024*25000^4383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        503 25000 2741788127627 50000000000000000000 4383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (503/25000 : ℝ)) (X := (2741788127627/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (26293/100000 : ℝ) ^ (4383/1024 : ℝ) ≤ (328667807580627773/100000000000000000000 : ℝ) := by
    have hpowers : (26293/100000 : ℝ)^4383 ≤ (328667807580627773/100000000000000000000 : ℝ)^1024 := by
      have hnat : (26293 : ℕ)^4383*100000000000000000000^1024 ≤ 328667807580627773^1024*100000^4383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26293 100000 328667807580627773 100000000000000000000 4383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26293/100000 : ℝ)) (X := (328667807580627773/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000002741788127627/25000000000000000000 : ℝ) ≤ (10000000256225501/10000000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (25000002741788127627/25000000000000000000 : ℝ)^1024 ≤ (10000000256225501/10000000000000000 : ℝ)^4383 := by
      have hnat : (25000002741788127627 : ℕ)^1024*10000000000000000^4383 ≤ 10000000256225501^4383*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000002741788127627 25000000000000000000 10000000256225501 10000000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000256225501/10000000000000000 : ℝ)) (X := (25000002741788127627/25000000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100328673291156883027/100000000000000000000 : ℝ) ≤ (5003834569861221/5000000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (100328673291156883027/100000000000000000000 : ℝ)^1024 ≤ (5003834569861221/5000000000000000 : ℝ)^4383 := by
      have hnat : (100328673291156883027 : ℕ)^1024*5000000000000000^4383 ≤ 5003834569861221^4383*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100328673291156883027 100000000000000000000 5003834569861221 5000000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003834569861221/5000000000000000 : ℝ)) (X := (100328673291156883027/100000000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50328667807580627773/50000000000000000000 : ℝ) ≤ (10015338023219383/10000000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (50328667807580627773/50000000000000000000 : ℝ)^1024 ≤ (10015338023219383/10000000000000000 : ℝ)^4383 := by
      have hnat : (50328667807580627773 : ℕ)^1024*10000000000000000^4383 ≤ 10015338023219383^4383*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50328667807580627773 50000000000000000000 10015338023219383 10000000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015338023219383/10000000000000000 : ℝ)) (X := (50328667807580627773/50000000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2741788127627/50000000000000000000 : ℝ) ≤ ((242779146634219699197/242810000000000000000 : ℝ)+2*(7668883496941/2428100000000000 : ℝ)*(503/25000 : ℝ))^(4383/1024 : ℝ) := by
    rw [show (242779146634219699197/242810000000000000000 : ℝ)+2*(7668883496941/2428100000000000 : ℝ)*(503/25000 : ℝ)=(10000000256225501/10000000000000000 : ℝ) by norm_num, show 1+2*(2741788127627/50000000000000000000 : ℝ)=(25000002741788127627/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(328667807580627773/100000000000000000000 : ℝ)+(2741788127627/50000000000000000000 : ℝ) ≤ ((242779146634219699197/242810000000000000000 : ℝ)+(7668883496941/2428100000000000 : ℝ)*((26293/100000 : ℝ)+(503/25000 : ℝ)))^(4383/1024 : ℝ) := by
    rw [show (242779146634219699197/242810000000000000000 : ℝ)+(7668883496941/2428100000000000 : ℝ)*((26293/100000 : ℝ)+(503/25000 : ℝ))=(5003834569861221/5000000000000000 : ℝ) by norm_num, show 1+(328667807580627773/100000000000000000000 : ℝ)+(2741788127627/50000000000000000000 : ℝ)=(100328673291156883027/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(328667807580627773/100000000000000000000 : ℝ) ≤ ((242779146634219699197/242810000000000000000 : ℝ)+2*(7668883496941/2428100000000000 : ℝ)*(26293/100000 : ℝ))^(4383/1024 : ℝ) := by
    rw [show (242779146634219699197/242810000000000000000 : ℝ)+2*(7668883496941/2428100000000000 : ℝ)*(26293/100000 : ℝ)=(10015338023219383/10000000000000000 : ℝ) by norm_num, show 1+2*(328667807580627773/100000000000000000000 : ℝ)=(50328667807580627773/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (242779146634219699197/242810000000000000000 : ℝ)*(X 1 0+X 2 0)+(7668883496941/2428100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (503/25000 : ℝ)) (hi := (26293/100000 : ℝ)) (c := (242779146634219699197/242810000000000000000 : ℝ)) (alpha := (7668883496941/2428100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (242779146634219699197/242810000000000000000 : ℝ)*(X 0 1+X 2 1)+(7668883496941/2428100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (503/25000 : ℝ)) (hi := (26293/100000 : ℝ)) (c := (242779146634219699197/242810000000000000000 : ℝ)) (alpha := (7668883496941/2428100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (242779146634219699197/242810000000000000000 : ℝ)*(X 0 2+X 1 2)+(7668883496941/2428100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (503/25000 : ℝ)) (hi := (26293/100000 : ℝ)) (c := (242779146634219699197/242810000000000000000 : ℝ)) (alpha := (7668883496941/2428100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-96735537/500000000 : ℝ)*X 0 0+(1121448957/2000000000 : ℝ)*X 0 1+(2537078461/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5397314307/10000000000 : ℝ)*X 1 0+(-554323893/2500000000 : ℝ)*X 1 1+(5074158093/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2698657617/5000000000 : ℝ)*X 2 0+(2537078529/5000000000 : ℝ)*X 2 1+(-2217295689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4277545089/10000000000 : ℝ)*X 0 0+(747323859/2000000000 : ℝ)*X 0 1+(488775211/1000000000 : ℝ)*X 0 2+(4277545089/10000000000 : ℝ)*X 1 0+(747323859/2000000000 : ℝ)*X 1 1+(488775211/1000000000 : ℝ)*X 1 2+(4277545089/10000000000 : ℝ)*X 2 0+(747323859/2000000000 : ℝ)*X 2 1+(488775211/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-387023133/2000000000 : ℝ)*X 0 0+(5080432817/10000000000 : ℝ)*X 0 1+(1400215511/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5258084991/10000000000 : ℝ)*X 1 0+(-422647771/2500000000 : ℝ)*X 1 1+(700107757/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2629042477/5000000000 : ℝ)*X 2 0+(280043101/500000000 : ℝ)*X 2 1+(-1690591189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2139209891/5000000000 : ℝ)*X 0 0+(974840219/2000000000 : ℝ)*X 0 1+(1875200281/5000000000 : ℝ)*X 0 2+(2139209891/5000000000 : ℝ)*X 1 0+(974840219/2000000000 : ℝ)*X 1 1+(1875200281/5000000000 : ℝ)*X 1 2+(2139209891/5000000000 : ℝ)*X 2 0+(974840219/2000000000 : ℝ)*X 2 1+(1875200281/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21512470932826301771720385177/3035125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2237759/12500000000000 : ℝ)*(base1) + (295071857/25000000000000 : ℝ)*(base19) + (300494941/20000000000000 : ℝ)*(base23) + (16311749/12500000000000 : ℝ)*(upper3) + (37385859/25000000000000 : ℝ)*(upper5) + (1372303172370211/100000000000000 : ℝ)*(major0) + (1372303172370211/100000000000000 : ℝ)*(major1) + (343075793092553/25000000000000 : ℝ)*(major2) + (46896865432151/2500000000000 : ℝ)*(sp0) + (1875885977917447/100000000000000 : ℝ)*(sp1) + (187588565573017/10000000000000 : ℝ)*(sp2) + (868714020370389/100000000000000 : ℝ)*(sp3) + (12558820907/100000000000000 : ℝ)*(sp4) + (614000231/12500000000000 : ℝ)*(sp7) + (868718950274309/100000000000000 : ℝ)*(f.failure) + (468971789551219/25000000000000 : ℝ)*(f.sum) + (203710922629577/242810000000000000000000000000 : ℝ)*base66 + (157557987293161379433/24281000000000000000000000000000000 : ℝ)*base68 + (57645871541836054941/6070250000000000000000000000000000 : ℝ)*base69 + (14452131333026620567/24281000000000000000000000000000000 : ℝ)*base71 + (909458979207067/242810000000000000000000000000 : ℝ)*base74 + (76760932282580304941/6070250000000000000000000000000000 : ℝ)*base75 + (63440817390498479433/24281000000000000000000000000000000 : ℝ)*base78 + (15108639176223520567/24281000000000000000000000000000000 : ℝ)*base79 + (371059772787029/121405000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (58971709/10000000000000000000000 : ℝ)*base89 + (58971709/10000000000000000000000 : ℝ)*base91 + (41028291/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (89704257751985920275146654853/12140500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32053959/50000000000000 : ℝ)*(base1) + (153442159/10000000000000 : ℝ)*(base19) + (1514230651/100000000000000 : ℝ)*(base23) + (88555643/50000000000000 : ℝ)*(upper3) + (19959851/12500000000000 : ℝ)*(upper5) + (1405664252502883/100000000000000 : ℝ)*(major0) + (1405664252502883/100000000000000 : ℝ)*(major1) + (1405664252502883/100000000000000 : ℝ)*(major2) + (8815232071/100000000000000 : ℝ)*(sp1) + (535205121/6250000000000 : ℝ)*(sp2) + (960745283985541/50000000000000 : ℝ)*(sp4) + (60046254819047/3125000000000 : ℝ)*(sp5) + (1921480426350577/100000000000000 : ℝ)*(sp6) + (177967538147977/20000000000000 : ℝ)*(sp7) + (444918877423901/50000000000000 : ℝ)*(f.failure) + (480372625965791/25000000000000 : ℝ)*(f.sum) + (20920004402797/121405000000000000000000000000 : ℝ)*base66 + (23889559721336584951/24281000000000000000000000000000000 : ℝ)*base67 + (64533463124092415049/24281000000000000000000000000000000 : ℝ)*base70 + (178583076927285415049/24281000000000000000000000000000000 : ℝ)*base72 + (147715514463117/30351250000000000000000000000 : ℝ)*base73 + (42742946330631415049/24281000000000000000000000000000000 : ℝ)*base76 + (174044126109613584951/24281000000000000000000000000000000 : ℝ)*base77 + (98071276900017415049/24281000000000000000000000000000000 : ℝ)*base80 + (220428120917181/60702500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (25067499/5000000000000000000000 : ℝ)*base90 + (25067499/5000000000000000000000 : ℝ)*base92 + (25067499/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1424_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26293/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (503/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (761/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (118/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1424_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1424_s2_0 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-984109051/5000000000 : ℝ)*x 0 + (21325411/39062500 : ℝ)*x 1 + (520053441/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (984109051/5000000000 : ℝ)^137 ≤ (11993160126699/100000000000000 : ℝ)^105 := by
    have hnat : (984109051 : ℕ)^137*100000000000000^105 ≤ 11993160126699^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984109051 5000000000 11993160126699 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21325411/39062500 : ℝ)^137 ≤ (4539696937923/10000000000000 : ℝ)^105 := by
    have hnat : (21325411 : ℕ)^137*10000000000000^105 ≤ 4539696937923^105*39062500^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21325411 39062500 4539696937923 10000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520053441/1000000000 : ℝ)^137 ≤ (5326233809743/12500000000000 : ℝ)^105 := by
    have hnat : (520053441 : ℕ)^137*12500000000000^105 ≤ 5326233809743^105*1000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520053441 1000000000 5326233809743 12500000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-984109051/5000000000 : ℝ), (21325411/39062500 : ℝ), (520053441/1000000000 : ℝ)] ![(11993160126699/100000000000000 : ℝ), (4539696937923/10000000000000 : ℝ), (5326233809743/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-984109051/5000000000 : ℝ)|^137 ≤ (11993160126699/100000000000000 : ℝ)^105
        have hw : |(-984109051/5000000000 : ℝ)|=(984109051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21325411/39062500 : ℝ)|^137 ≤ (4539696937923/10000000000000 : ℝ)^105
        have hw : |(21325411/39062500 : ℝ)|=(21325411/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(520053441/1000000000 : ℝ)|^137 ≤ (5326233809743/12500000000000 : ℝ)^105
        have hw : |(520053441/1000000000 : ℝ)|=(520053441/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s2_1 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2680229941/5000000000 : ℝ)*x 0 + (-2101384197/10000000000 : ℝ)*x 1 + (2600267163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680229941/5000000000 : ℝ)^137 ≤ (22163745538261/50000000000000 : ℝ)^105 := by
    have hnat : (2680229941 : ℕ)^137*50000000000000^105 ≤ 22163745538261^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680229941 5000000000 22163745538261 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2101384197/10000000000 : ℝ)^137 ≤ (6531319668477/50000000000000 : ℝ)^105 := by
    have hnat : (2101384197 : ℕ)^137*50000000000000^105 ≤ 6531319668477^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101384197 10000000000 6531319668477 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2600267163/5000000000 : ℝ)^137 ≤ (42609869579951/100000000000000 : ℝ)^105 := by
    have hnat : (2600267163 : ℕ)^137*100000000000000^105 ≤ 42609869579951^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600267163 5000000000 42609869579951 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680229941/5000000000 : ℝ), (-2101384197/10000000000 : ℝ), (2600267163/5000000000 : ℝ)] ![(22163745538261/50000000000000 : ℝ), (6531319668477/50000000000000 : ℝ), (42609869579951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680229941/5000000000 : ℝ)|^137 ≤ (22163745538261/50000000000000 : ℝ)^105
        have hw : |(2680229941/5000000000 : ℝ)|=(2680229941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2101384197/10000000000 : ℝ)|^137 ≤ (6531319668477/50000000000000 : ℝ)^105
        have hw : |(-2101384197/10000000000 : ℝ)|=(2101384197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2600267163/5000000000 : ℝ)|^137 ≤ (42609869579951/100000000000000 : ℝ)^105
        have hw : |(2600267163/5000000000 : ℝ)|=(2600267163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s2_2 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2680229763/5000000000 : ℝ)*x 0 + (5200534729/10000000000 : ℝ)*x 1 + (-2101384139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680229763/5000000000 : ℝ)^137 ≤ (44327487235451/100000000000000 : ℝ)^105 := by
    have hnat : (2680229763 : ℕ)^137*100000000000000^105 ≤ 44327487235451^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680229763 5000000000 44327487235451 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5200534729/10000000000 : ℝ)^137 ≤ (21304936944089/50000000000000 : ℝ)^105 := by
    have hnat : (5200534729 : ℕ)^137*50000000000000^105 ≤ 21304936944089^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200534729 10000000000 21304936944089 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2101384139/10000000000 : ℝ)^137 ≤ (2612527773307/20000000000000 : ℝ)^105 := by
    have hnat : (2101384139 : ℕ)^137*20000000000000^105 ≤ 2612527773307^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101384139 10000000000 2612527773307 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680229763/5000000000 : ℝ), (5200534729/10000000000 : ℝ), (-2101384139/10000000000 : ℝ)] ![(44327487235451/100000000000000 : ℝ), (21304936944089/50000000000000 : ℝ), (2612527773307/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680229763/5000000000 : ℝ)|^137 ≤ (44327487235451/100000000000000 : ℝ)^105
        have hw : |(2680229763/5000000000 : ℝ)|=(2680229763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5200534729/10000000000 : ℝ)|^137 ≤ (21304936944089/50000000000000 : ℝ)^105
        have hw : |(5200534729/10000000000 : ℝ)|=(5200534729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2101384139/10000000000 : ℝ)|^137 ≤ (2612527773307/20000000000000 : ℝ)^105
        have hw : |(-2101384139/10000000000 : ℝ)|=(2101384139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s2_3 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4301186819/10000000000 : ℝ)*x 0 + (1007489667/2500000000 : ℝ)*x 1 + (286796317/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4301186819/10000000000 : ℝ)^137 ≤ (6651965317271/20000000000000 : ℝ)^105 := by
    have hnat : (4301186819 : ℕ)^137*20000000000000^105 ≤ 6651965317271^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301186819 10000000000 6651965317271 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007489667/2500000000 : ℝ)^137 ≤ (30550002390163/100000000000000 : ℝ)^105 := by
    have hnat : (1007489667 : ℕ)^137*100000000000000^105 ≤ 30550002390163^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007489667 2500000000 30550002390163 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (286796317/625000000 : ℝ)^137 ≤ (36190171003463/100000000000000 : ℝ)^105 := by
    have hnat : (286796317 : ℕ)^137*100000000000000^105 ≤ 36190171003463^105*625000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286796317 625000000 36190171003463 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4301186819/10000000000 : ℝ), (1007489667/2500000000 : ℝ), (286796317/625000000 : ℝ)] ![(6651965317271/20000000000000 : ℝ), (30550002390163/100000000000000 : ℝ), (36190171003463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4301186819/10000000000 : ℝ)|^137 ≤ (6651965317271/20000000000000 : ℝ)^105
        have hw : |(4301186819/10000000000 : ℝ)|=(4301186819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1007489667/2500000000 : ℝ)|^137 ≤ (30550002390163/100000000000000 : ℝ)^105
        have hw : |(1007489667/2500000000 : ℝ)|=(1007489667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(286796317/625000000 : ℝ)|^137 ≤ (36190171003463/100000000000000 : ℝ)^105
        have hw : |(286796317/625000000 : ℝ)|=(286796317/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s2_4 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-61508271/312500000 : ℝ)*x 0 + (2601011123/5000000000 : ℝ)*x 1 + (682225623/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61508271/312500000 : ℝ)^137 ≤ (11993530380463/100000000000000 : ℝ)^105 := by
    have hnat : (61508271 : ℕ)^137*100000000000000^105 ≤ 11993530380463^105*312500000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61508271 312500000 11993530380463 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2601011123/5000000000 : ℝ)^137 ≤ (21312888358443/50000000000000 : ℝ)^105 := by
    have hnat : (2601011123 : ℕ)^137*50000000000000^105 ≤ 21312888358443^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601011123 5000000000 21312888358443 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682225623/1250000000 : ℝ)^137 ≤ (45380692880407/100000000000000 : ℝ)^105 := by
    have hnat : (682225623 : ℕ)^137*100000000000000^105 ≤ 45380692880407^105*1250000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682225623 1250000000 45380692880407 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-61508271/312500000 : ℝ), (2601011123/5000000000 : ℝ), (682225623/1250000000 : ℝ)] ![(11993530380463/100000000000000 : ℝ), (21312888358443/50000000000000 : ℝ), (45380692880407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-61508271/312500000 : ℝ)|^137 ≤ (11993530380463/100000000000000 : ℝ)^105
        have hw : |(-61508271/312500000 : ℝ)|=(61508271/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2601011123/5000000000 : ℝ)|^137 ≤ (21312888358443/50000000000000 : ℝ)^105
        have hw : |(2601011123/5000000000 : ℝ)|=(2601011123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(682225623/1250000000 : ℝ)|^137 ≤ (45380692880407/100000000000000 : ℝ)^105
        have hw : |(682225623/1250000000 : ℝ)|=(682225623/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s2_5 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (330825167/625000000 : ℝ)*x 0 + (-1844113353/10000000000 : ℝ)*x 1 + (2728902659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330825167/625000000 : ℝ)^137 ≤ (68130014271/156250000000 : ℝ)^105 := by
    have hnat : (330825167 : ℕ)^137*156250000000^105 ≤ 68130014271^105*625000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330825167 625000000 68130014271 156250000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1844113353/10000000000 : ℝ)^137 ≤ (5508047174163/50000000000000 : ℝ)^105 := by
    have hnat : (1844113353 : ℕ)^137*50000000000000^105 ≤ 5508047174163^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1844113353 10000000000 5508047174163 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728902659/5000000000 : ℝ)^137 ≤ (5672587062991/12500000000000 : ℝ)^105 := by
    have hnat : (2728902659 : ℕ)^137*12500000000000^105 ≤ 5672587062991^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728902659 5000000000 5672587062991 12500000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330825167/625000000 : ℝ), (-1844113353/10000000000 : ℝ), (2728902659/5000000000 : ℝ)] ![(68130014271/156250000000 : ℝ), (5508047174163/50000000000000 : ℝ), (5672587062991/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330825167/625000000 : ℝ)|^137 ≤ (68130014271/156250000000 : ℝ)^105
        have hw : |(330825167/625000000 : ℝ)|=(330825167/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1844113353/10000000000 : ℝ)|^137 ≤ (5508047174163/50000000000000 : ℝ)^105
        have hw : |(-1844113353/10000000000 : ℝ)|=(1844113353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2728902659/5000000000 : ℝ)|^137 ≤ (5672587062991/12500000000000 : ℝ)^105
        have hw : |(2728902659/5000000000 : ℝ)|=(2728902659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s2_6 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (661650327/1250000000 : ℝ)*x 0 + (1091561059/2000000000 : ℝ)*x 1 + (-1844113461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661650327/1250000000 : ℝ)^137 ≤ (43603208531547/100000000000000 : ℝ)^105 := by
    have hnat : (661650327 : ℕ)^137*100000000000000^105 ≤ 43603208531547^105*1250000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661650327 1250000000 43603208531547 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091561059/2000000000 : ℝ)^137 ≤ (11345174063601/25000000000000 : ℝ)^105 := by
    have hnat : (1091561059 : ℕ)^137*25000000000000^105 ≤ 11345174063601^105*2000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091561059 2000000000 11345174063601 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1844113461/10000000000 : ℝ)^137 ≤ (11016095190099/100000000000000 : ℝ)^105 := by
    have hnat : (1844113461 : ℕ)^137*100000000000000^105 ≤ 11016095190099^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1844113461 10000000000 11016095190099 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661650327/1250000000 : ℝ), (1091561059/2000000000 : ℝ), (-1844113461/10000000000 : ℝ)] ![(43603208531547/100000000000000 : ℝ), (11345174063601/25000000000000 : ℝ), (11016095190099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661650327/1250000000 : ℝ)|^137 ≤ (43603208531547/100000000000000 : ℝ)^105
        have hw : |(661650327/1250000000 : ℝ)|=(661650327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1091561059/2000000000 : ℝ)|^137 ≤ (11345174063601/25000000000000 : ℝ)^105
        have hw : |(1091561059/2000000000 : ℝ)|=(1091561059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1844113461/10000000000 : ℝ)|^137 ≤ (11016095190099/100000000000000 : ℝ)^105
        have hw : |(-1844113461/10000000000 : ℝ)|=(1844113461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s2_7 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1075321783/2500000000 : ℝ)*x 0 + (4585528473/10000000000 : ℝ)*x 1 + (252074867/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075321783/2500000000 : ℝ)^137 ≤ (16630419341173/50000000000000 : ℝ)^105 := by
    have hnat : (1075321783 : ℕ)^137*50000000000000^105 ≤ 16630419341173^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075321783 2500000000 16630419341173 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4585528473/10000000000 : ℝ)^137 ≤ (4519639487423/12500000000000 : ℝ)^105 := by
    have hnat : (4585528473 : ℕ)^137*12500000000000^105 ≤ 4519639487423^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4585528473 10000000000 4519639487423 12500000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (252074867/625000000 : ℝ)^137 ≤ (3058204540747/10000000000000 : ℝ)^105 := by
    have hnat : (252074867 : ℕ)^137*10000000000000^105 ≤ 3058204540747^105*625000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252074867 625000000 3058204540747 10000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075321783/2500000000 : ℝ), (4585528473/10000000000 : ℝ), (252074867/625000000 : ℝ)] ![(16630419341173/50000000000000 : ℝ), (4519639487423/12500000000000 : ℝ), (3058204540747/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075321783/2500000000 : ℝ)|^137 ≤ (16630419341173/50000000000000 : ℝ)^105
        have hw : |(1075321783/2500000000 : ℝ)|=(1075321783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4585528473/10000000000 : ℝ)|^137 ≤ (4519639487423/12500000000000 : ℝ)^105
        have hw : |(4585528473/10000000000 : ℝ)|=(4585528473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(252074867/625000000 : ℝ)|^137 ≤ (3058204540747/10000000000000 : ℝ)^105
        have hw : |(252074867/625000000 : ℝ)|=(252074867/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1424_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (118/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (761/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (517/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3163/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (118/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (761/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (118/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (761/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (118/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (761/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (118/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (761/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (118/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (761/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (118/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (761/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (761/10000 : ℝ) ^ (4383/1024 : ℝ) ≤ (203671598814583/12500000000000000000 : ℝ) := by
    have hpowers : (761/10000 : ℝ)^4383 ≤ (203671598814583/12500000000000000000 : ℝ)^1024 := by
      have hnat : (761 : ℕ)^4383*12500000000000000000^1024 ≤ 203671598814583^1024*10000^4383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        761 10000 203671598814583 12500000000000000000 4383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (761/10000 : ℝ)) (X := (203671598814583/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (118/625 : ℝ) ^ (4383/1024 : ℝ) ≤ (79632536407382537/100000000000000000000 : ℝ) := by
    have hpowers : (118/625 : ℝ)^4383 ≤ (79632536407382537/100000000000000000000 : ℝ)^1024 := by
      have hnat : (118 : ℕ)^4383*100000000000000000000^1024 ≤ 79632536407382537^1024*625^4383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        118 625 79632536407382537 100000000000000000000 4383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (118/625 : ℝ)) (X := (79632536407382537/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250203671598814583/6250000000000000000 : ℝ) ≤ (10000076133100779/10000000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (6250203671598814583/6250000000000000000 : ℝ)^1024 ≤ (10000076133100779/10000000000000000 : ℝ)^4383 := by
      have hnat : (6250203671598814583 : ℕ)^1024*10000000000000000^4383 ≤ 10000076133100779^4383*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250203671598814583 6250000000000000000 10000076133100779 10000000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000076133100779/10000000000000000 : ℝ)) (X := (6250203671598814583/6250000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100081261909197899201/100000000000000000000 : ℝ) ≤ (5000948965280707/5000000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (100081261909197899201/100000000000000000000 : ℝ)^1024 ≤ (5000948965280707/5000000000000000 : ℝ)^4383 := by
      have hnat : (100081261909197899201 : ℕ)^1024*5000000000000000^4383 ≤ 5000948965280707^4383*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100081261909197899201 100000000000000000000 5000948965280707 5000000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000948965280707/5000000000000000 : ℝ)) (X := (100081261909197899201/100000000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50079632536407382537/50000000000000000000 : ℝ) ≤ (10003719728022049/10000000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (50079632536407382537/50000000000000000000 : ℝ)^1024 ≤ (10003719728022049/10000000000000000 : ℝ)^4383 := by
      have hnat : (50079632536407382537 : ℕ)^1024*10000000000000000^4383 ≤ 10003719728022049^4383*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50079632536407382537 50000000000000000000 10003719728022049 10000000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003719728022049/10000000000000000 : ℝ)) (X := (50079632536407382537/50000000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(203671598814583/12500000000000000000 : ℝ) ≤ ((489883175055195281/490000000000000000 : ℝ)+2*(15841717049/9800000000000 : ℝ)*(761/10000 : ℝ))^(4383/1024 : ℝ) := by
    rw [show (489883175055195281/490000000000000000 : ℝ)+2*(15841717049/9800000000000 : ℝ)*(761/10000 : ℝ)=(10000076133100779/10000000000000000 : ℝ) by norm_num, show 1+2*(203671598814583/12500000000000000000 : ℝ)=(6250203671598814583/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(79632536407382537/100000000000000000000 : ℝ)+(203671598814583/12500000000000000000 : ℝ) ≤ ((489883175055195281/490000000000000000 : ℝ)+(15841717049/9800000000000 : ℝ)*((118/625 : ℝ)+(761/10000 : ℝ)))^(4383/1024 : ℝ) := by
    rw [show (489883175055195281/490000000000000000 : ℝ)+(15841717049/9800000000000 : ℝ)*((118/625 : ℝ)+(761/10000 : ℝ))=(5000948965280707/5000000000000000 : ℝ) by norm_num, show 1+(79632536407382537/100000000000000000000 : ℝ)+(203671598814583/12500000000000000000 : ℝ)=(100081261909197899201/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(79632536407382537/100000000000000000000 : ℝ) ≤ ((489883175055195281/490000000000000000 : ℝ)+2*(15841717049/9800000000000 : ℝ)*(118/625 : ℝ))^(4383/1024 : ℝ) := by
    rw [show (489883175055195281/490000000000000000 : ℝ)+2*(15841717049/9800000000000 : ℝ)*(118/625 : ℝ)=(10003719728022049/10000000000000000 : ℝ) by norm_num, show 1+2*(79632536407382537/100000000000000000000 : ℝ)=(50079632536407382537/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (489883175055195281/490000000000000000 : ℝ)*(X 1 0+X 2 0)+(15841717049/9800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (761/10000 : ℝ)) (hi := (118/625 : ℝ)) (c := (489883175055195281/490000000000000000 : ℝ)) (alpha := (15841717049/9800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (489883175055195281/490000000000000000 : ℝ)*(X 0 1+X 2 1)+(15841717049/9800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (761/10000 : ℝ)) (hi := (118/625 : ℝ)) (c := (489883175055195281/490000000000000000 : ℝ)) (alpha := (15841717049/9800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (489883175055195281/490000000000000000 : ℝ)*(X 0 2+X 1 2)+(15841717049/9800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (761/10000 : ℝ)) (hi := (118/625 : ℝ)) (c := (489883175055195281/490000000000000000 : ℝ)) (alpha := (15841717049/9800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-984109051/5000000000 : ℝ)*X 0 0+(21325411/39062500 : ℝ)*X 0 1+(520053441/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2680229941/5000000000 : ℝ)*X 1 0+(-2101384197/10000000000 : ℝ)*X 1 1+(2600267163/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2680229763/5000000000 : ℝ)*X 2 0+(5200534729/10000000000 : ℝ)*X 2 1+(-2101384139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4301186819/10000000000 : ℝ)*X 0 0+(1007489667/2500000000 : ℝ)*X 0 1+(286796317/625000000 : ℝ)*X 0 2+(4301186819/10000000000 : ℝ)*X 1 0+(1007489667/2500000000 : ℝ)*X 1 1+(286796317/625000000 : ℝ)*X 1 2+(4301186819/10000000000 : ℝ)*X 2 0+(1007489667/2500000000 : ℝ)*X 2 1+(286796317/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-61508271/312500000 : ℝ)*X 0 0+(2601011123/5000000000 : ℝ)*X 0 1+(682225623/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((330825167/625000000 : ℝ)*X 1 0+(-1844113353/10000000000 : ℝ)*X 1 1+(2728902659/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661650327/1250000000 : ℝ)*X 2 0+(1091561059/2000000000 : ℝ)*X 2 1+(-1844113461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1075321783/2500000000 : ℝ)*X 0 0+(4585528473/10000000000 : ℝ)*X 0 1+(252074867/625000000 : ℝ)*X 0 2+(1075321783/2500000000 : ℝ)*X 1 0+(4585528473/10000000000 : ℝ)*X 1 1+(252074867/625000000 : ℝ)*X 1 2+(1075321783/2500000000 : ℝ)*X 2 0+(4585528473/10000000000 : ℝ)*X 2 1+(252074867/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (300204872984044674078513063/24500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3771051/195312500000 : ℝ)*(base19) + (277005259/20000000000000 : ℝ)*(base23) + (2421453/1562500000000 : ℝ)*(lower2) + (356068329/100000000000000 : ℝ)*(upper3) + (125952833/100000000000000 : ℝ)*(upper5) + (141352432465909/5000000000000 : ℝ)*(major0) + (141352432465909/5000000000000 : ℝ)*(major1) + (2827048649318181/100000000000000 : ℝ)*(major2) + (1932224513575309/50000000000000 : ℝ)*(sp0) + (193223400683379/5000000000000 : ℝ)*(sp1) + (966117139854849/25000000000000 : ℝ)*(sp2) + (894807431423797/50000000000000 : ℝ)*(sp3) + (10458647537/50000000000000 : ℝ)*(sp4) + (6041450531/50000000000000 : ℝ)*(sp7) + (111851684109291/6250000000000 : ℝ)*(f.failure) + (966117486111423/25000000000000 : ℝ)*(f.sum) + (5648949810809/980000000000000000000000000 : ℝ)*base65 + (46568788094652071/2450000000000000000000000000000 : ℝ)*base68 + (308872971372296139/49000000000000000000000000000000 : ℝ)*base70 + (30489439123652071/2450000000000000000000000000000 : ℝ)*base72 + (4813985842151/980000000000000000000000000 : ℝ)*base74 + (167054078688296139/49000000000000000000000000000000 : ℝ)*base76 + (176461174210653/350000000000000000000000000000 : ℝ)*base78 + (4353579166810653/350000000000000000000000000000 : ℝ)*base80 + (2247844479/700000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5371891/625000000000000000000 : ℝ)*base89 + (5371891/625000000000000000000 : ℝ)*base91 + (878109/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (226929688977058525068609/35000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23927317/4000000000000 : ℝ)*(base19) + (714522721/100000000000000 : ℝ)*(base23) + (5484223/3125000000000 : ℝ)*(upper3) + (72894209/100000000000000 : ℝ)*(lower4) + (24331839/25000000000000 : ℝ)*(upper5) + (57200751670059/2000000000000 : ℝ)*(major0) + (57200751670059/2000000000000 : ℝ)*(major1) + (57200751670059/2000000000000 : ℝ)*(major2) + (8815244057/100000000000000 : ℝ)*(sp1) + (2597102441/25000000000000 : ℝ)*(sp2) + (1954782391393521/50000000000000 : ℝ)*(sp4) + (195477768468003/5000000000000 : ℝ)*(sp5) + (1954776839927279/50000000000000 : ℝ)*(sp6) + (362102033619067/20000000000000 : ℝ)*(sp7) + (362102033619067/20000000000000 : ℝ)*(f.failure) + (1954782391393521/50000000000000 : ℝ)*(f.sum) + (241494978651/49000000000000000000000000 : ℝ)*base65 + (3314162329081579/980000000000000000000000000000 : ℝ)*base67 + (4140464361301579/980000000000000000000000000000 : ℝ)*base69 + (6178975722621579/980000000000000000000000000000 : ℝ)*base71 + (39841552201/49000000000000000000000000 : ℝ)*base73 + (9057533673981579/980000000000000000000000000000 : ℝ)*base75 + (1877441595418421/980000000000000000000000000000 : ℝ)*base78 + (5389368939761579/980000000000000000000000000000 : ℝ)*base79 + (140259033841/49000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (19084733/2000000000000000000000 : ℝ)*base90 + (19084733/2000000000000000000000 : ℝ)*base92 + (19084733/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1424_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (118/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (761/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (517/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3163/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1424_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1424_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (517/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3163/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1424_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1424_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1424_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (517/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3163/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1424_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

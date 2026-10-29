-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1683_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:33:01.010044+00:00
-- url     : https://prove2.me/submissions/c838cfc1-ae9d-4d87-aad1-4fd26a684a1d

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
theorem support_rectangle_w1683_s3_0 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1515941423/10000000000 : ℝ)*x 0 + (5488018159/10000000000 : ℝ)*x 1 + (2566985509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1515941423/10000000000 : ℝ)^5087 ≤ (4711502104001/50000000000000 : ℝ)^4063 := by
    have hnat : (1515941423 : ℕ)^5087*50000000000000^4063 ≤ 4711502104001^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1515941423 10000000000 4711502104001 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5488018159/10000000000 : ℝ)^5087 ≤ (11794521096539/25000000000000 : ℝ)^4063 := by
    have hnat : (5488018159 : ℕ)^5087*25000000000000^4063 ≤ 11794521096539^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488018159 10000000000 11794521096539 25000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2566985509/5000000000 : ℝ)^5087 ≤ (21699455696539/50000000000000 : ℝ)^4063 := by
    have hnat : (2566985509 : ℕ)^5087*50000000000000^4063 ≤ 21699455696539^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566985509 5000000000 21699455696539 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1515941423/10000000000 : ℝ), (5488018159/10000000000 : ℝ), (2566985509/5000000000 : ℝ)] ![(4711502104001/50000000000000 : ℝ), (11794521096539/25000000000000 : ℝ), (21699455696539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1515941423/10000000000 : ℝ)|^5087 ≤ (4711502104001/50000000000000 : ℝ)^4063
        have hw : |(-1515941423/10000000000 : ℝ)|=(1515941423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5488018159/10000000000 : ℝ)|^5087 ≤ (11794521096539/25000000000000 : ℝ)^4063
        have hw : |(5488018159/10000000000 : ℝ)|=(5488018159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2566985509/5000000000 : ℝ)|^5087 ≤ (21699455696539/50000000000000 : ℝ)^4063
        have hw : |(2566985509/5000000000 : ℝ)|=(2566985509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s3_1 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535254703/1000000000 : ℝ)*x 0 + (-849983891/5000000000 : ℝ)*x 1 + (1283494173/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535254703/1000000000 : ℝ)^5087 ≤ (228622756141/500000000000 : ℝ)^4063 := by
    have hnat : (535254703 : ℕ)^5087*500000000000^4063 ≤ 228622756141^4063*1000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535254703 1000000000 228622756141 500000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849983891/5000000000 : ℝ)^5087 ≤ (5438238656149/50000000000000 : ℝ)^4063 := by
    have hnat : (849983891 : ℕ)^5087*50000000000000^4063 ≤ 5438238656149^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849983891 5000000000 5438238656149 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1283494173/2500000000 : ℝ)^5087 ≤ (4339897144539/10000000000000 : ℝ)^4063 := by
    have hnat : (1283494173 : ℕ)^5087*10000000000000^4063 ≤ 4339897144539^4063*2500000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283494173 2500000000 4339897144539 10000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535254703/1000000000 : ℝ), (-849983891/5000000000 : ℝ), (1283494173/2500000000 : ℝ)] ![(228622756141/500000000000 : ℝ), (5438238656149/50000000000000 : ℝ), (4339897144539/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535254703/1000000000 : ℝ)|^5087 ≤ (228622756141/500000000000 : ℝ)^4063
        have hw : |(535254703/1000000000 : ℝ)|=(535254703/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-849983891/5000000000 : ℝ)|^5087 ≤ (5438238656149/50000000000000 : ℝ)^4063
        have hw : |(-849983891/5000000000 : ℝ)|=(849983891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1283494173/2500000000 : ℝ)|^5087 ≤ (4339897144539/10000000000000 : ℝ)^4063
        have hw : |(1283494173/2500000000 : ℝ)|=(1283494173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s3_2 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352552589/10000000000 : ℝ)*x 0 + (5133970159/10000000000 : ℝ)*x 1 + (-1699968991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352552589/10000000000 : ℝ)^5087 ≤ (45724610684873/100000000000000 : ℝ)^4063 := by
    have hnat : (5352552589 : ℕ)^5087*100000000000000^4063 ≤ 45724610684873^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352552589 10000000000 45724610684873 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5133970159/10000000000 : ℝ)^5087 ≤ (43398902301621/100000000000000 : ℝ)^4063 := by
    have hnat : (5133970159 : ℕ)^5087*100000000000000^4063 ≤ 43398902301621^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133970159 10000000000 43398902301621 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1699968991/10000000000 : ℝ)^5087 ≤ (10876486997057/100000000000000 : ℝ)^4063 := by
    have hnat : (1699968991 : ℕ)^5087*100000000000000^4063 ≤ 10876486997057^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1699968991 10000000000 10876486997057 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352552589/10000000000 : ℝ), (5133970159/10000000000 : ℝ), (-1699968991/10000000000 : ℝ)] ![(45724610684873/100000000000000 : ℝ), (43398902301621/100000000000000 : ℝ), (10876486997057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352552589/10000000000 : ℝ)|^5087 ≤ (45724610684873/100000000000000 : ℝ)^4063
        have hw : |(5352552589/10000000000 : ℝ)|=(5352552589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5133970159/10000000000 : ℝ)|^5087 ≤ (43398902301621/100000000000000 : ℝ)^4063
        have hw : |(5133970159/10000000000 : ℝ)|=(5133970159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1699968991/10000000000 : ℝ)|^5087 ≤ (10876486997057/100000000000000 : ℝ)^4063
        have hw : |(-1699968991/10000000000 : ℝ)|=(1699968991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s3_3 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4140954067/10000000000 : ℝ)*x 0 + (1839140829/5000000000 : ℝ)*x 1 + (2320875757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4140954067/10000000000 : ℝ)^5087 ≤ (16579370459469/50000000000000 : ℝ)^4063 := by
    have hnat : (4140954067 : ℕ)^5087*50000000000000^4063 ≤ 16579370459469^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4140954067 10000000000 16579370459469 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1839140829/5000000000 : ℝ)^5087 ≤ (28587373815113/100000000000000 : ℝ)^4063 := by
    have hnat : (1839140829 : ℕ)^5087*100000000000000^4063 ≤ 28587373815113^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1839140829 5000000000 28587373815113 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2320875757/5000000000 : ℝ)^5087 ≤ (38253885252091/100000000000000 : ℝ)^4063 := by
    have hnat : (2320875757 : ℕ)^5087*100000000000000^4063 ≤ 38253885252091^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2320875757 5000000000 38253885252091 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4140954067/10000000000 : ℝ), (1839140829/5000000000 : ℝ), (2320875757/5000000000 : ℝ)] ![(16579370459469/50000000000000 : ℝ), (28587373815113/100000000000000 : ℝ), (38253885252091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4140954067/10000000000 : ℝ)|^5087 ≤ (16579370459469/50000000000000 : ℝ)^4063
        have hw : |(4140954067/10000000000 : ℝ)|=(4140954067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1839140829/5000000000 : ℝ)|^5087 ≤ (28587373815113/100000000000000 : ℝ)^4063
        have hw : |(1839140829/5000000000 : ℝ)|=(1839140829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2320875757/5000000000 : ℝ)|^5087 ≤ (38253885252091/100000000000000 : ℝ)^4063
        have hw : |(2320875757/5000000000 : ℝ)|=(2320875757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s3_4 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1516105987/10000000000 : ℝ)*x 0 + (5137803179/10000000000 : ℝ)*x 1 + (5484130173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1516105987/10000000000 : ℝ)^5087 ≤ (2356071238241/25000000000000 : ℝ)^4063 := by
    have hnat : (1516105987 : ℕ)^5087*25000000000000^4063 ≤ 2356071238241^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1516105987 10000000000 2356071238241 25000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5137803179/10000000000 : ℝ)^5087 ≤ (10859868478223/25000000000000 : ℝ)^4063 := by
    have hnat : (5137803179 : ℕ)^5087*25000000000000^4063 ≤ 10859868478223^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137803179 10000000000 10859868478223 25000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5484130173/10000000000 : ℝ)^5087 ≤ (47136241118691/100000000000000 : ℝ)^4063 := by
    have hnat : (5484130173 : ℕ)^5087*100000000000000^4063 ≤ 47136241118691^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484130173 10000000000 47136241118691 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1516105987/10000000000 : ℝ), (5137803179/10000000000 : ℝ), (5484130173/10000000000 : ℝ)] ![(2356071238241/25000000000000 : ℝ), (10859868478223/25000000000000 : ℝ), (47136241118691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1516105987/10000000000 : ℝ)|^5087 ≤ (2356071238241/25000000000000 : ℝ)^4063
        have hw : |(-1516105987/10000000000 : ℝ)|=(1516105987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5137803179/10000000000 : ℝ)|^5087 ≤ (10859868478223/25000000000000 : ℝ)^4063
        have hw : |(5137803179/10000000000 : ℝ)|=(5137803179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5484130173/10000000000 : ℝ)|^5087 ≤ (47136241118691/100000000000000 : ℝ)^4063
        have hw : |(5484130173/10000000000 : ℝ)|=(5484130173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s3_5 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210318977/400000000 : ℝ)*x 0 + (-674905491/5000000000 : ℝ)*x 1 + (5484130139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210318977/400000000 : ℝ)^5087 ≤ (2794706599849/6250000000000 : ℝ)^4063 := by
    have hnat : (210318977 : ℕ)^5087*6250000000000^4063 ≤ 2794706599849^4063*400000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210318977 400000000 2794706599849 6250000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674905491/5000000000 : ℝ)^5087 ≤ (509278352447/6250000000000 : ℝ)^4063 := by
    have hnat : (674905491 : ℕ)^5087*6250000000000^4063 ≤ 509278352447^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674905491 5000000000 509278352447 6250000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5484130139/10000000000 : ℝ)^5087 ≤ (47136240752809/100000000000000 : ℝ)^4063 := by
    have hnat : (5484130139 : ℕ)^5087*100000000000000^4063 ≤ 47136240752809^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484130139 10000000000 47136240752809 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210318977/400000000 : ℝ), (-674905491/5000000000 : ℝ), (5484130139/10000000000 : ℝ)] ![(2794706599849/6250000000000 : ℝ), (509278352447/6250000000000 : ℝ), (47136240752809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210318977/400000000 : ℝ)|^5087 ≤ (2794706599849/6250000000000 : ℝ)^4063
        have hw : |(210318977/400000000 : ℝ)|=(210318977/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-674905491/5000000000 : ℝ)|^5087 ≤ (509278352447/6250000000000 : ℝ)^4063
        have hw : |(-674905491/5000000000 : ℝ)|=(674905491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5484130139/10000000000 : ℝ)|^5087 ≤ (47136240752809/100000000000000 : ℝ)^4063
        have hw : |(5484130139/10000000000 : ℝ)|=(5484130139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s3_6 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328623403/625000000 : ℝ)*x 0 + (5484130143/10000000000 : ℝ)*x 1 + (-5272699/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328623403/625000000 : ℝ)^5087 ≤ (558941323031/1250000000000 : ℝ)^4063 := by
    have hnat : (328623403 : ℕ)^5087*1250000000000^4063 ≤ 558941323031^4063*625000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328623403 625000000 558941323031 1250000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5484130143/10000000000 : ℝ)^5087 ≤ (23568120397927/50000000000000 : ℝ)^4063 := by
    have hnat : (5484130143 : ℕ)^5087*50000000000000^4063 ≤ 23568120397927^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484130143 10000000000 23568120397927 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272699/39062500 : ℝ)^5087 ≤ (4074226675971/50000000000000 : ℝ)^4063 := by
    have hnat : (5272699 : ℕ)^5087*50000000000000^4063 ≤ 4074226675971^4063*39062500^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272699 39062500 4074226675971 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328623403/625000000 : ℝ), (5484130143/10000000000 : ℝ), (-5272699/39062500 : ℝ)] ![(558941323031/1250000000000 : ℝ), (23568120397927/50000000000000 : ℝ), (4074226675971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328623403/625000000 : ℝ)|^5087 ≤ (558941323031/1250000000000 : ℝ)^4063
        have hw : |(328623403/625000000 : ℝ)|=(328623403/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5484130143/10000000000 : ℝ)|^5087 ≤ (23568120397927/50000000000000 : ℝ)^4063
        have hw : |(5484130143/10000000000 : ℝ)|=(5484130143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5272699/39062500 : ℝ)|^5087 ≤ (4074226675971/50000000000000 : ℝ)^4063
        have hw : |(-5272699/39062500 : ℝ)|=(5272699/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s3_7 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (12941889/31250000 : ℝ)*x 0 + (4631331941/10000000000 : ℝ)*x 1 + (3688859407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12941889/31250000 : ℝ)^5087 ≤ (8290814165967/25000000000000 : ℝ)^4063 := by
    have hnat : (12941889 : ℕ)^5087*25000000000000^4063 ≤ 8290814165967^4063*31250000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12941889 31250000 8290814165967 25000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4631331941/10000000000 : ℝ)^5087 ≤ (38146403295483/100000000000000 : ℝ)^4063 := by
    have hnat : (4631331941 : ℕ)^5087*100000000000000^4063 ≤ 38146403295483^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4631331941 10000000000 38146403295483 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3688859407/10000000000 : ℝ)^5087 ≤ (1147613600677/4000000000000 : ℝ)^4063 := by
    have hnat : (3688859407 : ℕ)^5087*4000000000000^4063 ≤ 1147613600677^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3688859407 10000000000 1147613600677 4000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(12941889/31250000 : ℝ), (4631331941/10000000000 : ℝ), (3688859407/10000000000 : ℝ)] ![(8290814165967/25000000000000 : ℝ), (38146403295483/100000000000000 : ℝ), (1147613600677/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(12941889/31250000 : ℝ)|^5087 ≤ (8290814165967/25000000000000 : ℝ)^4063
        have hw : |(12941889/31250000 : ℝ)|=(12941889/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4631331941/10000000000 : ℝ)|^5087 ≤ (38146403295483/100000000000000 : ℝ)^4063
        have hw : |(4631331941/10000000000 : ℝ)|=(4631331941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3688859407/10000000000 : ℝ)|^5087 ≤ (1147613600677/4000000000000 : ℝ)^4063
        have hw : |(3688859407/10000000000 : ℝ)|=(3688859407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1683_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186066867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8657/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9733/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4879/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3457/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8657/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9733/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8657/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9733/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8657/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9733/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8657/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9733/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8657/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9733/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8657/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9733/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9733/100000 : ℝ) ^ (5079/1024 : ℝ) ≤ (958833655478081/100000000000000000000 : ℝ) := by
    have hpowers : (9733/100000 : ℝ)^5079 ≤ (958833655478081/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9733 : ℕ)^5079*100000000000000000000^1024 ≤ 958833655478081^1024*100000^5079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9733 100000 958833655478081 100000000000000000000 5079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9733/100000 : ℝ)) (X := (958833655478081/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8657/50000 : ℝ) ^ (5079/1024 : ℝ) ≤ (16690944747346199/100000000000000000000 : ℝ) := by
    have hpowers : (8657/50000 : ℝ)^5079 ≤ (16690944747346199/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8657 : ℕ)^5079*100000000000000000000^1024 ≤ 16690944747346199^1024*50000^5079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8657 50000 16690944747346199 100000000000000000000 5079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8657/50000 : ℝ)) (X := (16690944747346199/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000958833655478081/50000000000000000000 : ℝ) ≤ (125000483283199/125000000000000 : ℝ) ^ (5079/1024 : ℝ) := by
    have hpowers : (50000958833655478081/50000000000000000000 : ℝ)^1024 ≤ (125000483283199/125000000000000 : ℝ)^5079 := by
      have hnat : (50000958833655478081 : ℕ)^1024*125000000000000^5079 ≤ 125000483283199^5079*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000958833655478081 50000000000000000000 125000483283199 125000000000000 1024 5079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125000483283199/125000000000000 : ℝ)) (X := (50000958833655478081/50000000000000000000 : ℝ)) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2500441244460070607/2500000000000000000 : ℝ) ≤ (10000355820039971/10000000000000000 : ℝ) ^ (5079/1024 : ℝ) := by
    have hpowers : (2500441244460070607/2500000000000000000 : ℝ)^1024 ≤ (10000355820039971/10000000000000000 : ℝ)^5079 := by
      have hnat : (2500441244460070607 : ℕ)^1024*10000000000000000^5079 ≤ 10000355820039971^5079*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500441244460070607 2500000000000000000 10000355820039971 10000000000000000 1024 5079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000355820039971/10000000000000000 : ℝ)) (X := (2500441244460070607/2500000000000000000 : ℝ)) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50016690944747346199/50000000000000000000 : ℝ) ≤ (5000336488712011/5000000000000000 : ℝ) ^ (5079/1024 : ℝ) := by
    have hpowers : (50016690944747346199/50000000000000000000 : ℝ)^1024 ≤ (5000336488712011/5000000000000000 : ℝ)^5079 := by
      have hnat : (50016690944747346199 : ℕ)^1024*5000000000000000^5079 ≤ 5000336488712011^5079*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016690944747346199 50000000000000000000 5000336488712011 5000000000000000 1024 5079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000336488712011/5000000000000000 : ℝ)) (X := (50016690944747346199/50000000000000000000 : ℝ)) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(958833655478081/100000000000000000000 : ℝ) ≤ ((12634019885992765459/12635000000000000000 : ℝ)+2*(105719128017/252700000000000 : ℝ)*(9733/100000 : ℝ))^(5079/1024 : ℝ) := by
    rw [show (12634019885992765459/12635000000000000000 : ℝ)+2*(105719128017/252700000000000 : ℝ)*(9733/100000 : ℝ)=(125000483283199/125000000000000 : ℝ) by norm_num, show 1+2*(958833655478081/100000000000000000000 : ℝ)=(50000958833655478081/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16690944747346199/100000000000000000000 : ℝ)+(958833655478081/100000000000000000000 : ℝ) ≤ ((12634019885992765459/12635000000000000000 : ℝ)+(105719128017/252700000000000 : ℝ)*((8657/50000 : ℝ)+(9733/100000 : ℝ)))^(5079/1024 : ℝ) := by
    rw [show (12634019885992765459/12635000000000000000 : ℝ)+(105719128017/252700000000000 : ℝ)*((8657/50000 : ℝ)+(9733/100000 : ℝ))=(10000355820039971/10000000000000000 : ℝ) by norm_num, show 1+(16690944747346199/100000000000000000000 : ℝ)+(958833655478081/100000000000000000000 : ℝ)=(2500441244460070607/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16690944747346199/100000000000000000000 : ℝ) ≤ ((12634019885992765459/12635000000000000000 : ℝ)+2*(105719128017/252700000000000 : ℝ)*(8657/50000 : ℝ))^(5079/1024 : ℝ) := by
    rw [show (12634019885992765459/12635000000000000000 : ℝ)+2*(105719128017/252700000000000 : ℝ)*(8657/50000 : ℝ)=(5000336488712011/5000000000000000 : ℝ) by norm_num, show 1+2*(16690944747346199/100000000000000000000 : ℝ)=(50016690944747346199/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12634019885992765459/12635000000000000000 : ℝ)*(X 1 0+X 2 0)+(105719128017/252700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5079/1024 : ℝ)) (lo := (9733/100000 : ℝ)) (hi := (8657/50000 : ℝ)) (c := (12634019885992765459/12635000000000000000 : ℝ)) (alpha := (105719128017/252700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12634019885992765459/12635000000000000000 : ℝ)*(X 0 1+X 2 1)+(105719128017/252700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5079/1024 : ℝ)) (lo := (9733/100000 : ℝ)) (hi := (8657/50000 : ℝ)) (c := (12634019885992765459/12635000000000000000 : ℝ)) (alpha := (105719128017/252700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12634019885992765459/12635000000000000000 : ℝ)*(X 0 2+X 1 2)+(105719128017/252700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5079/1024 : ℝ)) (lo := (9733/100000 : ℝ)) (hi := (8657/50000 : ℝ)) (c := (12634019885992765459/12635000000000000000 : ℝ)) (alpha := (105719128017/252700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1515941423/10000000000 : ℝ)*X 0 0+(5488018159/10000000000 : ℝ)*X 0 1+(2566985509/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535254703/1000000000 : ℝ)*X 1 0+(-849983891/5000000000 : ℝ)*X 1 1+(1283494173/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352552589/10000000000 : ℝ)*X 2 0+(5133970159/10000000000 : ℝ)*X 2 1+(-1699968991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4140954067/10000000000 : ℝ)*X 0 0+(1839140829/5000000000 : ℝ)*X 0 1+(2320875757/5000000000 : ℝ)*X 0 2+(4140954067/10000000000 : ℝ)*X 1 0+(1839140829/5000000000 : ℝ)*X 1 1+(2320875757/5000000000 : ℝ)*X 1 2+(4140954067/10000000000 : ℝ)*X 2 0+(1839140829/5000000000 : ℝ)*X 2 1+(2320875757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1516105987/10000000000 : ℝ)*X 0 0+(5137803179/10000000000 : ℝ)*X 0 1+(5484130173/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((210318977/400000000 : ℝ)*X 1 0+(-674905491/5000000000 : ℝ)*X 1 1+(5484130139/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((328623403/625000000 : ℝ)*X 2 0+(5484130143/10000000000 : ℝ)*X 2 1+(-5272699/39062500 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((12941889/31250000 : ℝ)*X 0 0+(4631331941/10000000000 : ℝ)*X 0 1+(3688859407/10000000000 : ℝ)*X 0 2+(12941889/31250000 : ℝ)*X 1 0+(4631331941/10000000000 : ℝ)*X 1 1+(3688859407/10000000000 : ℝ)*X 1 2+(12941889/31250000 : ℝ)*X 2 0+(4631331941/10000000000 : ℝ)*X 2 1+(3688859407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (94077447323465658338576763/78968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2358907667/100000000000000 : ℝ)*(base23) + (5873037/20000000000000 : ℝ)*(lower2) + (802292433/100000000000000 : ℝ)*(upper3) + (17385769/6250000000000 : ℝ)*(upper4) + (92534599/100000000000000 : ℝ)*(upper5) + (1931223709032553/100000000000000 : ℝ)*(major0) + (1931223709032553/100000000000000 : ℝ)*(major1) + (965611854516277/50000000000000 : ℝ)*(major2) + (1412252668507227/50000000000000 : ℝ)*(sp0) + (2824528193617009/100000000000000 : ℝ)*(sp1) + (1412262917354671/50000000000000 : ℝ)*(sp2) + (1037913129857453/100000000000000 : ℝ)*(sp3) + (5714150639/25000000000000 : ℝ)*(sp4) + (6054879803/100000000000000 : ℝ)*(sp7) + (129739898092157/12500000000000 : ℝ)*(f.failure) + (2824528193617009/100000000000000 : ℝ)*(f.sum) + (7257475688209/1330000000000000000000000000 : ℝ)*base66 + (2137981883006944739/180500000000000000000000000000000 : ℝ)*base68 + (105716484613651143/631750000000000000000000000000000 : ℝ)*base69 + (1727250821553944739/180500000000000000000000000000000 : ℝ)*base72 + (8840285655269/1330000000000000000000000000 : ℝ)*base74 + (1199188636504651143/631750000000000000000000000000000 : ℝ)*base75 + (9700639235046463173/1263500000000000000000000000000000 : ℝ)*base78 + (10564993072967463173/1263500000000000000000000000000000 : ℝ)*base80 + (35654775892567/6317500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (17762119/1250000000000000000000 : ℝ)*base89 + (17762119/1250000000000000000000 : ℝ)*base91 + (5262119/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8302062685054954482951/1263500000000000000000000000 : ℝ) := by norm_num
    linear_combination (918975271/100000000000000 : ℝ)*(base19) + (1039721979/100000000000000 : ℝ)*(base23) + (26623121/10000000000000 : ℝ)*(lower1) + (69474389/50000000000000 : ℝ)*(upper3) + (5804213/12500000000000 : ℝ)*(lower4) + (140552011/100000000000000 : ℝ)*(upper5) + (394847257489151/20000000000000 : ℝ)*(major0) + (394847257489151/20000000000000 : ℝ)*(major1) + (394847257489151/20000000000000 : ℝ)*(major2) + (137630959/12500000000000 : ℝ)*(sp2) + (2887436439438767/100000000000000 : ℝ)*(sp4) + (360929440057937/12500000000000 : ℝ)*(sp5) + (721858574667279/25000000000000 : ℝ)*(sp6) + (1061035916429847/100000000000000 : ℝ)*(sp7) + (1061035916429847/100000000000000 : ℝ)*(f.failure) + (2887436439438767/100000000000000 : ℝ)*(f.sum) + (71361243027/252700000000000000000000000 : ℝ)*base66 + (69136629605614691/252700000000000000000000000000000 : ℝ)*base68 + (543950439324385309/252700000000000000000000000000000 : ℝ)*base69 + (1545541696413614691/252700000000000000000000000000000 : ℝ)*base72 + (2090576323641/1263500000000000000000000000 : ℝ)*base73 + (2077127054908714691/252700000000000000000000000000000 : ℝ)*base76 + (72577020951185309/252700000000000000000000000000000 : ℝ)*base77 + (574049778158285309/252700000000000000000000000000000 : ℝ)*base79 + (519878537553/78968750000000000000000000 : ℝ)*base81 + (43420651/10000000000000000000000 : ℝ)*base90 + (43420651/10000000000000000000000 : ℝ)*base92 + (43420651/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1683_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186066867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8657/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9733/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4879/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3457/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1683_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1683_s4_0 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-303191673/2000000000 : ℝ)*x 0 + (5487945519/10000000000 : ℝ)*x 1 + (513403243/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (303191673/2000000000 : ℝ)^5087 ≤ (4711568030069/50000000000000 : ℝ)^4063 := by
    have hnat : (303191673 : ℕ)^5087*50000000000000^4063 ≤ 4711568030069^4063*2000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303191673 2000000000 4711568030069 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5487945519/10000000000 : ℝ)^5087 ≤ (4717730255173/10000000000000 : ℝ)^4063 := by
    have hnat : (5487945519 : ℕ)^5087*10000000000000^4063 ≤ 4717730255173^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487945519 10000000000 4717730255173 10000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513403243/1000000000 : ℝ)^5087 ≤ (43399561364459/100000000000000 : ℝ)^4063 := by
    have hnat : (513403243 : ℕ)^5087*100000000000000^4063 ≤ 43399561364459^4063*1000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513403243 1000000000 43399561364459 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-303191673/2000000000 : ℝ), (5487945519/10000000000 : ℝ), (513403243/1000000000 : ℝ)] ![(4711568030069/50000000000000 : ℝ), (4717730255173/10000000000000 : ℝ), (43399561364459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-303191673/2000000000 : ℝ)|^5087 ≤ (4711568030069/50000000000000 : ℝ)^4063
        have hw : |(-303191673/2000000000 : ℝ)|=(303191673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5487945519/10000000000 : ℝ)|^5087 ≤ (4717730255173/10000000000000 : ℝ)^4063
        have hw : |(5487945519/10000000000 : ℝ)|=(5487945519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(513403243/1000000000 : ℝ)|^5087 ≤ (43399561364459/100000000000000 : ℝ)^4063
        have hw : |(513403243/1000000000 : ℝ)|=(513403243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s4_1 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352530671/10000000000 : ℝ)*x 0 + (-212489501/1250000000 : ℝ)*x 1 + (513403241/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352530671/10000000000 : ℝ)^5087 ≤ (45724376259461/100000000000000 : ℝ)^4063 := by
    have hnat : (5352530671 : ℕ)^5087*100000000000000^4063 ≤ 45724376259461^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352530671 10000000000 45724376259461 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212489501/1250000000 : ℝ)^5087 ≤ (10876062575533/100000000000000 : ℝ)^4063 := by
    have hnat : (212489501 : ℕ)^5087*100000000000000^4063 ≤ 10876062575533^4063*1250000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212489501 1250000000 10876062575533 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513403241/1000000000 : ℝ)^5087 ≤ (43399561152783/100000000000000 : ℝ)^4063 := by
    have hnat : (513403241 : ℕ)^5087*100000000000000^4063 ≤ 43399561152783^4063*1000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513403241 1000000000 43399561152783 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352530671/10000000000 : ℝ), (-212489501/1250000000 : ℝ), (513403241/1000000000 : ℝ)] ![(45724376259461/100000000000000 : ℝ), (10876062575533/100000000000000 : ℝ), (43399561152783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352530671/10000000000 : ℝ)|^5087 ≤ (45724376259461/100000000000000 : ℝ)^4063
        have hw : |(5352530671/10000000000 : ℝ)|=(5352530671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212489501/1250000000 : ℝ)|^5087 ≤ (10876062575533/100000000000000 : ℝ)^4063
        have hw : |(-212489501/1250000000 : ℝ)|=(212489501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(513403241/1000000000 : ℝ)|^5087 ≤ (43399561152783/100000000000000 : ℝ)^4063
        have hw : |(513403241/1000000000 : ℝ)|=(513403241/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s4_2 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676265327/5000000000 : ℝ)*x 0 + (1283508109/2500000000 : ℝ)*x 1 + (-424978999/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676265327/5000000000 : ℝ)^5087 ≤ (45724376077637/100000000000000 : ℝ)^4063 := by
    have hnat : (2676265327 : ℕ)^5087*100000000000000^4063 ≤ 45724376077637^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676265327 5000000000 45724376077637 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1283508109/2500000000 : ℝ)^5087 ≤ (21699780713981/50000000000000 : ℝ)^4063 := by
    have hnat : (1283508109 : ℕ)^5087*50000000000000^4063 ≤ 21699780713981^4063*2500000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283508109 2500000000 21699780713981 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424978999/2500000000 : ℝ)^5087 ≤ (10876062479407/100000000000000 : ℝ)^4063 := by
    have hnat : (424978999 : ℕ)^5087*100000000000000^4063 ≤ 10876062479407^4063*2500000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424978999 2500000000 10876062479407 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676265327/5000000000 : ℝ), (1283508109/2500000000 : ℝ), (-424978999/2500000000 : ℝ)] ![(45724376077637/100000000000000 : ℝ), (21699780713981/50000000000000 : ℝ), (10876062479407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676265327/5000000000 : ℝ)|^5087 ≤ (45724376077637/100000000000000 : ℝ)^4063
        have hw : |(2676265327/5000000000 : ℝ)|=(2676265327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1283508109/2500000000 : ℝ)|^5087 ≤ (21699780713981/50000000000000 : ℝ)^4063
        have hw : |(1283508109/2500000000 : ℝ)|=(1283508109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-424978999/2500000000 : ℝ)|^5087 ≤ (10876062479407/100000000000000 : ℝ)^4063
        have hw : |(-424978999/2500000000 : ℝ)|=(424978999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s4_3 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4140964341/10000000000 : ℝ)*x 0 + (3678458147/10000000000 : ℝ)*x 1 + (4641575091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4140964341/10000000000 : ℝ)^5087 ≤ (33158843922497/100000000000000 : ℝ)^4063 := by
    have hnat : (4140964341 : ℕ)^5087*100000000000000^4063 ≤ 33158843922497^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4140964341 10000000000 33158843922497 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3678458147/10000000000 : ℝ)^5087 ≤ (3573636398431/12500000000000 : ℝ)^4063 := by
    have hnat : (3678458147 : ℕ)^5087*12500000000000^4063 ≤ 3573636398431^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3678458147 10000000000 3573636398431 12500000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4641575091/10000000000 : ℝ)^5087 ≤ (4781508109197/12500000000000 : ℝ)^4063 := by
    have hnat : (4641575091 : ℕ)^5087*12500000000000^4063 ≤ 4781508109197^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4641575091 10000000000 4781508109197 12500000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4140964341/10000000000 : ℝ), (3678458147/10000000000 : ℝ), (4641575091/10000000000 : ℝ)] ![(33158843922497/100000000000000 : ℝ), (3573636398431/12500000000000 : ℝ), (4781508109197/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4140964341/10000000000 : ℝ)|^5087 ≤ (33158843922497/100000000000000 : ℝ)^4063
        have hw : |(4140964341/10000000000 : ℝ)|=(4140964341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3678458147/10000000000 : ℝ)|^5087 ≤ (3573636398431/12500000000000 : ℝ)^4063
        have hw : |(3678458147/10000000000 : ℝ)|=(3678458147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4641575091/10000000000 : ℝ)|^5087 ≤ (4781508109197/12500000000000 : ℝ)^4063
        have hw : |(4641575091/10000000000 : ℝ)|=(4641575091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s4_4 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-189515571/1250000000 : ℝ)*x 0 + (2568929699/5000000000 : ℝ)*x 1 + (685507679/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (189515571/1250000000 : ℝ)^5087 ≤ (2356107391173/25000000000000 : ℝ)^4063 := by
    have hnat : (189515571 : ℕ)^5087*25000000000000^4063 ≤ 2356107391173^4063*1250000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189515571 1250000000 2356107391173 25000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2568929699/5000000000 : ℝ)^5087 ≤ (43440069034507/100000000000000 : ℝ)^4063 := by
    have hnat : (2568929699 : ℕ)^5087*100000000000000^4063 ≤ 43440069034507^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568929699 5000000000 43440069034507 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (685507679/1250000000 : ℝ)^5087 ≤ (47135501381819/100000000000000 : ℝ)^4063 := by
    have hnat : (685507679 : ℕ)^5087*100000000000000^4063 ≤ 47135501381819^4063*1250000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685507679 1250000000 47135501381819 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-189515571/1250000000 : ℝ), (2568929699/5000000000 : ℝ), (685507679/1250000000 : ℝ)] ![(2356107391173/25000000000000 : ℝ), (43440069034507/100000000000000 : ℝ), (47135501381819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-189515571/1250000000 : ℝ)|^5087 ≤ (2356107391173/25000000000000 : ℝ)^4063
        have hw : |(-189515571/1250000000 : ℝ)|=(189515571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2568929699/5000000000 : ℝ)|^5087 ≤ (43440069034507/100000000000000 : ℝ)^4063
        have hw : |(2568929699/5000000000 : ℝ)|=(2568929699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(685507679/1250000000 : ℝ)|^5087 ≤ (47135501381819/100000000000000 : ℝ)^4063
        have hw : |(685507679/1250000000 : ℝ)|=(685507679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s4_5 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257989997/10000000000 : ℝ)*x 0 + (-269977423/2000000000 : ℝ)*x 1 + (5484061259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257989997/10000000000 : ℝ)^5087 ≤ (1788618856097/4000000000000 : ℝ)^4063 := by
    have hnat : (5257989997 : ℕ)^5087*4000000000000^4063 ≤ 1788618856097^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257989997 10000000000 1788618856097 4000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269977423/2000000000 : ℝ)^5087 ≤ (8149029070063/100000000000000 : ℝ)^4063 := by
    have hnat : (269977423 : ℕ)^5087*100000000000000^4063 ≤ 8149029070063^4063*2000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269977423 2000000000 8149029070063 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5484061259/10000000000 : ℝ)^5087 ≤ (47135499520131/100000000000000 : ℝ)^4063 := by
    have hnat : (5484061259 : ℕ)^5087*100000000000000^4063 ≤ 47135499520131^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484061259 10000000000 47135499520131 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257989997/10000000000 : ℝ), (-269977423/2000000000 : ℝ), (5484061259/10000000000 : ℝ)] ![(1788618856097/4000000000000 : ℝ), (8149029070063/100000000000000 : ℝ), (47135499520131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257989997/10000000000 : ℝ)|^5087 ≤ (1788618856097/4000000000000 : ℝ)^4063
        have hw : |(5257989997/10000000000 : ℝ)|=(5257989997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-269977423/2000000000 : ℝ)|^5087 ≤ (8149029070063/100000000000000 : ℝ)^4063
        have hw : |(-269977423/2000000000 : ℝ)|=(269977423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5484061259/10000000000 : ℝ)|^5087 ≤ (47135499520131/100000000000000 : ℝ)^4063
        have hw : |(5484061259/10000000000 : ℝ)|=(5484061259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s4_6 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257989953/10000000000 : ℝ)*x 0 + (2742030657/5000000000 : ℝ)*x 1 + (-674943549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257989953/10000000000 : ℝ)^5087 ≤ (44715470933929/100000000000000 : ℝ)^4063 := by
    have hnat : (5257989953 : ℕ)^5087*100000000000000^4063 ≤ 44715470933929^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257989953 10000000000 44715470933929 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2742030657/5000000000 : ℝ)^5087 ≤ (47135500111997/100000000000000 : ℝ)^4063 := by
    have hnat : (2742030657 : ℕ)^5087*100000000000000^4063 ≤ 47135500111997^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742030657 5000000000 47135500111997 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674943549/5000000000 : ℝ)^5087 ≤ (2037257235393/25000000000000 : ℝ)^4063 := by
    have hnat : (674943549 : ℕ)^5087*25000000000000^4063 ≤ 2037257235393^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674943549 5000000000 2037257235393 25000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257989953/10000000000 : ℝ), (2742030657/5000000000 : ℝ), (-674943549/5000000000 : ℝ)] ![(44715470933929/100000000000000 : ℝ), (47135500111997/100000000000000 : ℝ), (2037257235393/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257989953/10000000000 : ℝ)|^5087 ≤ (44715470933929/100000000000000 : ℝ)^4063
        have hw : |(5257989953/10000000000 : ℝ)|=(5257989953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2742030657/5000000000 : ℝ)|^5087 ≤ (47135500111997/100000000000000 : ℝ)^4063
        have hw : |(2742030657/5000000000 : ℝ)|=(2742030657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-674943549/5000000000 : ℝ)|^5087 ≤ (2037257235393/25000000000000 : ℝ)^4063
        have hw : |(-674943549/5000000000 : ℝ)|=(674943549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_s4_7 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165656667/400000000 : ℝ)*x 0 + (1157790093/2500000000 : ℝ)*x 1 + (737805709/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165656667/400000000 : ℝ)^5087 ≤ (6632675786013/20000000000000 : ℝ)^4063 := by
    have hnat : (165656667 : ℕ)^5087*20000000000000^4063 ≤ 6632675786013^4063*400000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165656667 400000000 6632675786013 20000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1157790093/2500000000 : ℝ)^5087 ≤ (38144634003969/100000000000000 : ℝ)^4063 := by
    have hnat : (1157790093 : ℕ)^5087*100000000000000^4063 ≤ 38144634003969^4063*2500000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1157790093 2500000000 38144634003969 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (737805709/2000000000 : ℝ)^5087 ≤ (28691987049571/100000000000000 : ℝ)^4063 := by
    have hnat : (737805709 : ℕ)^5087*100000000000000^4063 ≤ 28691987049571^4063*2000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737805709 2000000000 28691987049571 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165656667/400000000 : ℝ), (1157790093/2500000000 : ℝ), (737805709/2000000000 : ℝ)] ![(6632675786013/20000000000000 : ℝ), (38144634003969/100000000000000 : ℝ), (28691987049571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165656667/400000000 : ℝ)|^5087 ≤ (6632675786013/20000000000000 : ℝ)^4063
        have hw : |(165656667/400000000 : ℝ)|=(165656667/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1157790093/2500000000 : ℝ)|^5087 ≤ (38144634003969/100000000000000 : ℝ)^4063
        have hw : |(1157790093/2500000000 : ℝ)|=(1157790093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(737805709/2000000000 : ℝ)|^5087 ≤ (28691987049571/100000000000000 : ℝ)^4063
        have hw : |(737805709/2000000000 : ℝ)|=(737805709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1683_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186066867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3457/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4879/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9759/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4321/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3457/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4879/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3457/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4879/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3457/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4879/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3457/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4879/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3457/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4879/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3457/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4879/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4879/50000 : ℝ) ^ (5079/1024 : ℝ) ≤ (971111538710347/100000000000000000000 : ℝ) := by
    have hpowers : (4879/50000 : ℝ)^5079 ≤ (971111538710347/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4879 : ℕ)^5079*100000000000000000000^1024 ≤ 971111538710347^1024*50000^5079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4879 50000 971111538710347 100000000000000000000 5079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4879/50000 : ℝ)) (X := (971111538710347/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3457/20000 : ℝ) ^ (5079/1024 : ℝ) ≤ (16552741108897607/100000000000000000000 : ℝ) := by
    have hpowers : (3457/20000 : ℝ)^5079 ≤ (16552741108897607/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3457 : ℕ)^5079*100000000000000000000^1024 ≤ 16552741108897607^1024*20000^5079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3457 20000 16552741108897607 100000000000000000000 5079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3457/20000 : ℝ)) (X := (16552741108897607/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000971111538710347/50000000000000000000 : ℝ) ≤ (78125305919751/78125000000000 : ℝ) ^ (5079/1024 : ℝ) := by
    have hpowers : (50000971111538710347/50000000000000000000 : ℝ)^1024 ≤ (78125305919751/78125000000000 : ℝ)^5079 := by
      have hnat : (50000971111538710347 : ℕ)^1024*78125000000000^5079 ≤ 78125305919751^5079*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000971111538710347 50000000000000000000 78125305919751 78125000000000 1024 5079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78125305919751/78125000000000 : ℝ)) (X := (50000971111538710347/50000000000000000000 : ℝ)) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50008761926323803977/50000000000000000000 : ℝ) ≤ (10000353281550691/10000000000000000 : ℝ) ^ (5079/1024 : ℝ) := by
    have hpowers : (50008761926323803977/50000000000000000000 : ℝ)^1024 ≤ (10000353281550691/10000000000000000 : ℝ)^5079 := by
      have hnat : (50008761926323803977 : ℕ)^1024*10000000000000000^5079 ≤ 10000353281550691^5079*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008761926323803977 50000000000000000000 10000353281550691 10000000000000000 1024 5079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000353281550691/10000000000000000 : ℝ)) (X := (50008761926323803977/50000000000000000000 : ℝ)) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50016552741108897607/50000000000000000000 : ℝ) ≤ (5000333702686627/5000000000000000 : ℝ) ^ (5079/1024 : ℝ) := by
    have hpowers : (50016552741108897607/50000000000000000000 : ℝ)^1024 ≤ (5000333702686627/5000000000000000 : ℝ)^5079 := by
      have hnat : (50016552741108897607 : ℕ)^1024*5000000000000000^5079 ≤ 5000333702686627^5079*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016552741108897607 50000000000000000000 5000333702686627 5000000000000000 1024 5079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000333702686627/5000000000000000 : ℝ)) (X := (50016552741108897607/50000000000000000000 : ℝ)) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(971111538710347/100000000000000000000 : ℝ) ≤ ((18816041074924619987/18817500000000000000 : ℝ)+2*(314123822563/752700000000000 : ℝ)*(4879/50000 : ℝ))^(5079/1024 : ℝ) := by
    rw [show (18816041074924619987/18817500000000000000 : ℝ)+2*(314123822563/752700000000000 : ℝ)*(4879/50000 : ℝ)=(78125305919751/78125000000000 : ℝ) by norm_num, show 1+2*(971111538710347/100000000000000000000 : ℝ)=(50000971111538710347/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16552741108897607/100000000000000000000 : ℝ)+(971111538710347/100000000000000000000 : ℝ) ≤ ((18816041074924619987/18817500000000000000 : ℝ)+(314123822563/752700000000000 : ℝ)*((3457/20000 : ℝ)+(4879/50000 : ℝ)))^(5079/1024 : ℝ) := by
    rw [show (18816041074924619987/18817500000000000000 : ℝ)+(314123822563/752700000000000 : ℝ)*((3457/20000 : ℝ)+(4879/50000 : ℝ))=(10000353281550691/10000000000000000 : ℝ) by norm_num, show 1+(16552741108897607/100000000000000000000 : ℝ)+(971111538710347/100000000000000000000 : ℝ)=(50008761926323803977/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16552741108897607/100000000000000000000 : ℝ) ≤ ((18816041074924619987/18817500000000000000 : ℝ)+2*(314123822563/752700000000000 : ℝ)*(3457/20000 : ℝ))^(5079/1024 : ℝ) := by
    rw [show (18816041074924619987/18817500000000000000 : ℝ)+2*(314123822563/752700000000000 : ℝ)*(3457/20000 : ℝ)=(5000333702686627/5000000000000000 : ℝ) by norm_num, show 1+2*(16552741108897607/100000000000000000000 : ℝ)=(50016552741108897607/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18816041074924619987/18817500000000000000 : ℝ)*(X 1 0+X 2 0)+(314123822563/752700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5079/1024 : ℝ)) (lo := (4879/50000 : ℝ)) (hi := (3457/20000 : ℝ)) (c := (18816041074924619987/18817500000000000000 : ℝ)) (alpha := (314123822563/752700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18816041074924619987/18817500000000000000 : ℝ)*(X 0 1+X 2 1)+(314123822563/752700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5079/1024 : ℝ)) (lo := (4879/50000 : ℝ)) (hi := (3457/20000 : ℝ)) (c := (18816041074924619987/18817500000000000000 : ℝ)) (alpha := (314123822563/752700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18816041074924619987/18817500000000000000 : ℝ)*(X 0 2+X 1 2)+(314123822563/752700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5079/1024 : ℝ)) (lo := (4879/50000 : ℝ)) (hi := (3457/20000 : ℝ)) (c := (18816041074924619987/18817500000000000000 : ℝ)) (alpha := (314123822563/752700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-303191673/2000000000 : ℝ)*X 0 0+(5487945519/10000000000 : ℝ)*X 0 1+(513403243/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352530671/10000000000 : ℝ)*X 1 0+(-212489501/1250000000 : ℝ)*X 1 1+(513403241/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676265327/5000000000 : ℝ)*X 2 0+(1283508109/2500000000 : ℝ)*X 2 1+(-424978999/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4140964341/10000000000 : ℝ)*X 0 0+(3678458147/10000000000 : ℝ)*X 0 1+(4641575091/10000000000 : ℝ)*X 0 2+(4140964341/10000000000 : ℝ)*X 1 0+(3678458147/10000000000 : ℝ)*X 1 1+(4641575091/10000000000 : ℝ)*X 1 2+(4140964341/10000000000 : ℝ)*X 2 0+(3678458147/10000000000 : ℝ)*X 2 1+(4641575091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-189515571/1250000000 : ℝ)*X 0 0+(2568929699/5000000000 : ℝ)*X 0 1+(685507679/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5257989997/10000000000 : ℝ)*X 1 0+(-269977423/2000000000 : ℝ)*X 1 1+(5484061259/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5257989953/10000000000 : ℝ)*X 2 0+(2742030657/5000000000 : ℝ)*X 2 1+(-674943549/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((165656667/400000000 : ℝ)*X 0 0+(1157790093/2500000000 : ℝ)*X 0 1+(737805709/2000000000 : ℝ)*X 0 2+(165656667/400000000 : ℝ)*X 1 0+(1157790093/2500000000 : ℝ)*X 1 1+(737805709/2000000000 : ℝ)*X 1 2+(165656667/400000000 : ℝ)*X 2 0+(1157790093/2500000000 : ℝ)*X 2 1+(737805709/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1101239396449256934009656241/156812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1082060063/100000000000000 : ℝ)*(base19) + (503139787/50000000000000 : ℝ)*(base23) + (35758267/100000000000000 : ℝ)*(lower2) + (85379071/50000000000000 : ℝ)*(upper3) + (12780327/10000000000000 : ℝ)*(upper5) + (1931937956821443/100000000000000 : ℝ)*(major0) + (1931937956821443/100000000000000 : ℝ)*(major1) + (1931937956821443/100000000000000 : ℝ)*(major2) + (35319532826219/1250000000000 : ℝ)*(sp0) + (353196443321191/12500000000000 : ℝ)*(sp1) + (1412785811175009/50000000000000 : ℝ)*(sp2) + (1038299064050399/100000000000000 : ℝ)*(sp3) + (10002532071/100000000000000 : ℝ)*(sp4) + (3986874537/100000000000000 : ℝ)*(sp7) + (129787881365617/12500000000000 : ℝ)*(f.failure) + (2825572628629591/100000000000000 : ℝ)*(f.sum) + (50149829515467/12545000000000000000000000000 : ℝ)*base66 + (5574630590092318747/627250000000000000000000000000000 : ℝ)*base67 + (1393279337337431253/627250000000000000000000000000000 : ℝ)*base70 + (621191401133431253/627250000000000000000000000000000 : ℝ)*base72 + (21163177860809/6272500000000000000000000000 : ℝ)*base73 + (5240607039555431253/627250000000000000000000000000000 : ℝ)*base76 + (6522646985222431253/627250000000000000000000000000000 : ℝ)*base78 + (2474503418505181253/627250000000000000000000000000000 : ℝ)*base80 + (37228220105733/12545000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (788061/1250000000000000000000 : ℝ)*base90 + (788061/1250000000000000000000 : ℝ)*base92 + (788061/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (195132432626244674991381489/15681250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35365443/2000000000000 : ℝ)*(base19) + (376169813/20000000000000 : ℝ)*(base23) + (10571493/2000000000000 : ℝ)*(lower1) + (10999783/5000000000000 : ℝ)*(upper3) + (33675169/50000000000000 : ℝ)*(lower4) + (55256003/20000000000000 : ℝ)*(upper5) + (98747213231949/5000000000000 : ℝ)*(major0) + (98747213231949/5000000000000 : ℝ)*(major1) + (98747213231949/5000000000000 : ℝ)*(major2) + (60182517/12500000000000 : ℝ)*(sp2) + (2888471701947591/100000000000000 : ℝ)*(sp4) + (1444234966837721/50000000000000 : ℝ)*(sp5) + (288846933963839/10000000000000 : ℝ)*(sp6) + (1061416412541079/100000000000000 : ℝ)*(sp7) + (1061416412541079/100000000000000 : ℝ)*(f.failure) + (2888471701947591/100000000000000 : ℝ)*(f.sum) + (9139543771483/2509000000000000000000000000 : ℝ)*base65 + (395472331311661779/31362500000000000000000000000000 : ℝ)*base68 + (3368281453524279/31362500000000000000000000000000 : ℝ)*base70 + (669703346462124279/31362500000000000000000000000000 : ℝ)*base72 + (4976490032653/1254500000000000000000000000 : ℝ)*base74 + (249987023147199279/31362500000000000000000000000000 : ℝ)*base76 + (306260612817874279/31362500000000000000000000000000 : ℝ)*base78 + (109772674997186779/31362500000000000000000000000000 : ℝ)*base80 + (2019949750961/501800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (78329493/10000000000000000000000 : ℝ)*base89 + (78329493/10000000000000000000000 : ℝ)*base91 + (78329493/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1683_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186066867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3457/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4879/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9759/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4321/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1683_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1683_box_0 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-587428277/5000000000 : ℝ)*x 0 + (1357996657/2500000000 : ℝ)*x 1 + (5431984039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (587428277/5000000000 : ℝ)^5087 ≤ (3424227774193/50000000000000 : ℝ)^4063 := by
    have hnat : (587428277 : ℕ)^5087*50000000000000^4063 ≤ 3424227774193^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587428277 5000000000 3424227774193 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357996657/2500000000 : ℝ)^5087 ≤ (46575786112253/100000000000000 : ℝ)^4063 := by
    have hnat : (1357996657 : ℕ)^5087*100000000000000^4063 ≤ 46575786112253^4063*2500000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357996657 2500000000 46575786112253 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431984039/10000000000 : ℝ)^5087 ≤ (2328787915921/5000000000000 : ℝ)^4063 := by
    have hnat : (5431984039 : ℕ)^5087*5000000000000^4063 ≤ 2328787915921^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431984039 10000000000 2328787915921 5000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-587428277/5000000000 : ℝ), (1357996657/2500000000 : ℝ), (5431984039/10000000000 : ℝ)] ![(3424227774193/50000000000000 : ℝ), (46575786112253/100000000000000 : ℝ), (2328787915921/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-587428277/5000000000 : ℝ)|^5087 ≤ (3424227774193/50000000000000 : ℝ)^4063
        have hw : |(-587428277/5000000000 : ℝ)|=(587428277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357996657/2500000000 : ℝ)|^5087 ≤ (46575786112253/100000000000000 : ℝ)^4063
        have hw : |(1357996657/2500000000 : ℝ)|=(1357996657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431984039/10000000000 : ℝ)|^5087 ≤ (2328787915921/5000000000000 : ℝ)^4063
        have hw : |(5431984039/10000000000 : ℝ)|=(5431984039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_box_1 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2613047417/5000000000 : ℝ)*x 0 + (-366893551/2500000000 : ℝ)*x 1 + (5431984839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2613047417/5000000000 : ℝ)^5087 ≤ (22188061742589/50000000000000 : ℝ)^4063 := by
    have hnat : (2613047417 : ℕ)^5087*50000000000000^4063 ≤ 22188061742589^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613047417 5000000000 22188061742589 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366893551/2500000000 : ℝ)^5087 ≤ (565506849413/6250000000000 : ℝ)^4063 := by
    have hnat : (366893551 : ℕ)^5087*6250000000000^4063 ≤ 565506849413^4063*2500000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366893551 2500000000 565506849413 6250000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431984839/10000000000 : ℝ)^5087 ≤ (46575766906703/100000000000000 : ℝ)^4063 := by
    have hnat : (5431984839 : ℕ)^5087*100000000000000^4063 ≤ 46575766906703^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431984839 10000000000 46575766906703 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2613047417/5000000000 : ℝ), (-366893551/2500000000 : ℝ), (5431984839/10000000000 : ℝ)] ![(22188061742589/50000000000000 : ℝ), (565506849413/6250000000000 : ℝ), (46575766906703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2613047417/5000000000 : ℝ)|^5087 ≤ (22188061742589/50000000000000 : ℝ)^4063
        have hw : |(2613047417/5000000000 : ℝ)|=(2613047417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-366893551/2500000000 : ℝ)|^5087 ≤ (565506849413/6250000000000 : ℝ)^4063
        have hw : |(-366893551/2500000000 : ℝ)|=(366893551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431984839/10000000000 : ℝ)|^5087 ≤ (46575766906703/100000000000000 : ℝ)^4063
        have hw : |(5431984839/10000000000 : ℝ)|=(5431984839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_box_2 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1045219123/2000000000 : ℝ)*x 0 + (543198361/1000000000 : ℝ)*x 1 + (-733787419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045219123/2000000000 : ℝ)^5087 ≤ (11094032947059/25000000000000 : ℝ)^4063 := by
    have hnat : (1045219123 : ℕ)^5087*25000000000000^4063 ≤ 11094032947059^4063*2000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045219123 2000000000 11094032947059 25000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543198361/1000000000 : ℝ)^5087 ≤ (46575753712953/100000000000000 : ℝ)^4063 := by
    have hnat : (543198361 : ℕ)^5087*100000000000000^4063 ≤ 46575753712953^4063*1000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543198361 1000000000 46575753712953 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (733787419/5000000000 : ℝ)^5087 ≤ (1809622896917/20000000000000 : ℝ)^4063 := by
    have hnat : (733787419 : ℕ)^5087*20000000000000^4063 ≤ 1809622896917^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733787419 5000000000 1809622896917 20000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1045219123/2000000000 : ℝ), (543198361/1000000000 : ℝ), (-733787419/5000000000 : ℝ)] ![(11094032947059/25000000000000 : ℝ), (46575753712953/100000000000000 : ℝ), (1809622896917/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1045219123/2000000000 : ℝ)|^5087 ≤ (11094032947059/25000000000000 : ℝ)^4063
        have hw : |(1045219123/2000000000 : ℝ)|=(1045219123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543198361/1000000000 : ℝ)|^5087 ≤ (46575753712953/100000000000000 : ℝ)^4063
        have hw : |(543198361/1000000000 : ℝ)|=(543198361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-733787419/5000000000 : ℝ)|^5087 ≤ (1809622896917/20000000000000 : ℝ)^4063
        have hw : |(-733787419/5000000000 : ℝ)|=(733787419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_box_3 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2263142391/5000000000 : ℝ)*x 0 + (62051843/156250000 : ℝ)*x 1 + (3971315849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2263142391/5000000000 : ℝ)^5087 ≤ (4633277735509/12500000000000 : ℝ)^4063 := by
    have hnat : (2263142391 : ℕ)^5087*12500000000000^4063 ≤ 4633277735509^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263142391 5000000000 4633277735509 12500000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62051843/156250000 : ℝ)^5087 ≤ (3933362435047/12500000000000 : ℝ)^4063 := by
    have hnat : (62051843 : ℕ)^5087*12500000000000^4063 ≤ 3933362435047^4063*156250000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62051843 156250000 3933362435047 12500000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3971315849/10000000000 : ℝ)^5087 ≤ (15733439308767/50000000000000 : ℝ)^4063 := by
    have hnat : (3971315849 : ℕ)^5087*50000000000000^4063 ≤ 15733439308767^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3971315849 10000000000 15733439308767 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2263142391/5000000000 : ℝ), (62051843/156250000 : ℝ), (3971315849/10000000000 : ℝ)] ![(4633277735509/12500000000000 : ℝ), (3933362435047/12500000000000 : ℝ), (15733439308767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2263142391/5000000000 : ℝ)|^5087 ≤ (4633277735509/12500000000000 : ℝ)^4063
        have hw : |(2263142391/5000000000 : ℝ)|=(2263142391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(62051843/156250000 : ℝ)|^5087 ≤ (3933362435047/12500000000000 : ℝ)^4063
        have hw : |(62051843/156250000 : ℝ)|=(62051843/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3971315849/10000000000 : ℝ)|^5087 ≤ (15733439308767/50000000000000 : ℝ)^4063
        have hw : |(3971315849/10000000000 : ℝ)|=(3971315849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_box_4 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-15025013/80000000 : ℝ)*x 0 + (5175509341/10000000000 : ℝ)*x 1 + (2587755321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15025013/80000000 : ℝ)^5087 ≤ (1232200472867/10000000000000 : ℝ)^4063 := by
    have hnat : (15025013 : ℕ)^5087*10000000000000^4063 ≤ 1232200472867^4063*80000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15025013 80000000 1232200472867 10000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5175509341/10000000000 : ℝ)^5087 ≤ (8767798146113/20000000000000 : ℝ)^4063 := by
    have hnat : (5175509341 : ℕ)^5087*20000000000000^4063 ≤ 8767798146113^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175509341 10000000000 8767798146113 20000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2587755321/5000000000 : ℝ)^5087 ≤ (21919502264021/50000000000000 : ℝ)^4063 := by
    have hnat : (2587755321 : ℕ)^5087*50000000000000^4063 ≤ 21919502264021^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587755321 5000000000 21919502264021 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15025013/80000000 : ℝ), (5175509341/10000000000 : ℝ), (2587755321/5000000000 : ℝ)] ![(1232200472867/10000000000000 : ℝ), (8767798146113/20000000000000 : ℝ), (21919502264021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15025013/80000000 : ℝ)|^5087 ≤ (1232200472867/10000000000000 : ℝ)^4063
        have hw : |(-15025013/80000000 : ℝ)|=(15025013/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5175509341/10000000000 : ℝ)|^5087 ≤ (8767798146113/20000000000000 : ℝ)^4063
        have hw : |(5175509341/10000000000 : ℝ)|=(5175509341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2587755321/5000000000 : ℝ)|^5087 ≤ (21919502264021/50000000000000 : ℝ)^4063
        have hw : |(2587755321/5000000000 : ℝ)|=(2587755321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_box_5 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5401194433/10000000000 : ℝ)*x 0 + (-315780979/2000000000 : ℝ)*x 1 + (646938581/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5401194433/10000000000 : ℝ)^5087 ≤ (46245457433329/100000000000000 : ℝ)^4063 := by
    have hnat : (5401194433 : ℕ)^5087*100000000000000^4063 ≤ 46245457433329^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401194433 10000000000 46245457433329 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (315780979/2000000000 : ℝ)^5087 ≤ (4957779582479/50000000000000 : ℝ)^4063 := by
    have hnat : (315780979 : ℕ)^5087*50000000000000^4063 ≤ 4957779582479^4063*2000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315780979 2000000000 4957779582479 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (646938581/1250000000 : ℝ)^5087 ≤ (43838983381103/100000000000000 : ℝ)^4063 := by
    have hnat : (646938581 : ℕ)^5087*100000000000000^4063 ≤ 43838983381103^4063*1250000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646938581 1250000000 43838983381103 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5401194433/10000000000 : ℝ), (-315780979/2000000000 : ℝ), (646938581/1250000000 : ℝ)] ![(46245457433329/100000000000000 : ℝ), (4957779582479/50000000000000 : ℝ), (43838983381103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5401194433/10000000000 : ℝ)|^5087 ≤ (46245457433329/100000000000000 : ℝ)^4063
        have hw : |(5401194433/10000000000 : ℝ)|=(5401194433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-315780979/2000000000 : ℝ)|^5087 ≤ (4957779582479/50000000000000 : ℝ)^4063
        have hw : |(-315780979/2000000000 : ℝ)|=(315780979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(646938581/1250000000 : ℝ)|^5087 ≤ (43838983381103/100000000000000 : ℝ)^4063
        have hw : |(646938581/1250000000 : ℝ)|=(646938581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_box_6 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5401194213/10000000000 : ℝ)*x 0 + (2587754427/5000000000 : ℝ)*x 1 + (-789452459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5401194213/10000000000 : ℝ)^5087 ≤ (11561363768733/25000000000000 : ℝ)^4063 := by
    have hnat : (5401194213 : ℕ)^5087*25000000000000^4063 ≤ 11561363768733^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401194213 10000000000 11561363768733 25000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587754427/5000000000 : ℝ)^5087 ≤ (43838985565791/100000000000000 : ℝ)^4063 := by
    have hnat : (2587754427 : ℕ)^5087*100000000000000^4063 ≤ 43838985565791^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587754427 5000000000 43838985565791 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (789452459/5000000000 : ℝ)^5087 ≤ (4957779672901/50000000000000 : ℝ)^4063 := by
    have hnat : (789452459 : ℕ)^5087*50000000000000^4063 ≤ 4957779672901^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      789452459 5000000000 4957779672901 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5401194213/10000000000 : ℝ), (2587754427/5000000000 : ℝ), (-789452459/5000000000 : ℝ)] ![(11561363768733/25000000000000 : ℝ), (43838985565791/100000000000000 : ℝ), (4957779672901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5401194213/10000000000 : ℝ)|^5087 ≤ (11561363768733/25000000000000 : ℝ)^4063
        have hw : |(5401194213/10000000000 : ℝ)|=(5401194213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587754427/5000000000 : ℝ)|^5087 ≤ (43838985565791/100000000000000 : ℝ)^4063
        have hw : |(2587754427/5000000000 : ℝ)|=(2587754427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-789452459/5000000000 : ℝ)|^5087 ≤ (4957779672901/50000000000000 : ℝ)^4063
        have hw : |(-789452459/5000000000 : ℝ)|=(789452459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_box_7 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3741458699/10000000000 : ℝ)*x 0 + (272678411/625000000 : ℝ)*x 1 + (2181428047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3741458699/10000000000 : ℝ)^5087 ≤ (29203455729393/100000000000000 : ℝ)^4063 := by
    have hnat : (3741458699 : ℕ)^5087*100000000000000^4063 ≤ 29203455729393^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3741458699 10000000000 29203455729393 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272678411/625000000 : ℝ)^5087 ≤ (1769913220839/5000000000000 : ℝ)^4063 := by
    have hnat : (272678411 : ℕ)^5087*5000000000000^4063 ≤ 1769913220839^4063*625000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272678411 625000000 1769913220839 5000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2181428047/5000000000 : ℝ)^5087 ≤ (35398279837261/100000000000000 : ℝ)^4063 := by
    have hnat : (2181428047 : ℕ)^5087*100000000000000^4063 ≤ 35398279837261^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181428047 5000000000 35398279837261 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3741458699/10000000000 : ℝ), (272678411/625000000 : ℝ), (2181428047/5000000000 : ℝ)] ![(29203455729393/100000000000000 : ℝ), (1769913220839/5000000000000 : ℝ), (35398279837261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3741458699/10000000000 : ℝ)|^5087 ≤ (29203455729393/100000000000000 : ℝ)^4063
        have hw : |(3741458699/10000000000 : ℝ)|=(3741458699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272678411/625000000 : ℝ)|^5087 ≤ (1769913220839/5000000000000 : ℝ)^4063
        have hw : |(272678411/625000000 : ℝ)|=(272678411/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2181428047/5000000000 : ℝ)|^5087 ≤ (35398279837261/100000000000000 : ℝ)^4063
        have hw : |(2181428047/5000000000 : ℝ)|=(2181428047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_box_8 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-215922103/1250000000 : ℝ)*x 0 + (997538499/2000000000 : ℝ)*x 1 + (684481617/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215922103/1250000000 : ℝ)^5087 ≤ (11096483207881/100000000000000 : ℝ)^4063 := by
    have hnat : (215922103 : ℕ)^5087*100000000000000^4063 ≤ 11096483207881^4063*1250000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215922103 1250000000 11096483207881 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (997538499/2000000000 : ℝ)^5087 ≤ (10464083001631/25000000000000 : ℝ)^4063 := by
    have hnat : (997538499 : ℕ)^5087*25000000000000^4063 ≤ 10464083001631^4063*2000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997538499 2000000000 10464083001631 25000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (684481617/1250000000 : ℝ)^5087 ≤ (47047184775607/100000000000000 : ℝ)^4063 := by
    have hnat : (684481617 : ℕ)^5087*100000000000000^4063 ≤ 47047184775607^4063*1250000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684481617 1250000000 47047184775607 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215922103/1250000000 : ℝ), (997538499/2000000000 : ℝ), (684481617/1250000000 : ℝ)] ![(11096483207881/100000000000000 : ℝ), (10464083001631/25000000000000 : ℝ), (47047184775607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215922103/1250000000 : ℝ)|^5087 ≤ (11096483207881/100000000000000 : ℝ)^4063
        have hw : |(-215922103/1250000000 : ℝ)|=(215922103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(997538499/2000000000 : ℝ)|^5087 ≤ (10464083001631/25000000000000 : ℝ)^4063
        have hw : |(997538499/2000000000 : ℝ)|=(997538499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(684481617/1250000000 : ℝ)|^5087 ≤ (47047184775607/100000000000000 : ℝ)^4063
        have hw : |(684481617/1250000000 : ℝ)|=(684481617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_box_9 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196152363/10000000000 : ℝ)*x 0 + (-1447676689/10000000000 : ℝ)*x 1 + (10695027/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196152363/10000000000 : ℝ)^5087 ≤ (22029012900461/50000000000000 : ℝ)^4063 := by
    have hnat : (5196152363 : ℕ)^5087*50000000000000^4063 ≤ 22029012900461^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196152363 10000000000 22029012900461 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1447676689/10000000000 : ℝ)^5087 ≤ (8894779859981/100000000000000 : ℝ)^4063 := by
    have hnat : (1447676689 : ℕ)^5087*100000000000000^4063 ≤ 8894779859981^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1447676689 10000000000 8894779859981 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10695027/19531250 : ℝ)^5087 ≤ (47047194327947/100000000000000 : ℝ)^4063 := by
    have hnat : (10695027 : ℕ)^5087*100000000000000^4063 ≤ 47047194327947^4063*19531250^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10695027 19531250 47047194327947 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196152363/10000000000 : ℝ), (-1447676689/10000000000 : ℝ), (10695027/19531250 : ℝ)] ![(22029012900461/50000000000000 : ℝ), (8894779859981/100000000000000 : ℝ), (47047194327947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196152363/10000000000 : ℝ)|^5087 ≤ (22029012900461/50000000000000 : ℝ)^4063
        have hw : |(5196152363/10000000000 : ℝ)|=(5196152363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1447676689/10000000000 : ℝ)|^5087 ≤ (8894779859981/100000000000000 : ℝ)^4063
        have hw : |(-1447676689/10000000000 : ℝ)|=(1447676689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10695027/19531250 : ℝ)|^5087 ≤ (47047194327947/100000000000000 : ℝ)^4063
        have hw : |(10695027/19531250 : ℝ)|=(10695027/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_box_10 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299038183/2500000000 : ℝ)*x 0 + (2737926953/5000000000 : ℝ)*x 1 + (-45239877/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299038183/2500000000 : ℝ)^5087 ≤ (220290148591/500000000000 : ℝ)^4063 := by
    have hnat : (1299038183 : ℕ)^5087*500000000000^4063 ≤ 220290148591^4063*2500000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299038183 2500000000 220290148591 500000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2737926953/5000000000 : ℝ)^5087 ≤ (2940449700627/6250000000000 : ℝ)^4063 := by
    have hnat : (2737926953 : ℕ)^5087*6250000000000^4063 ≤ 2940449700627^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737926953 5000000000 2940449700627 6250000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45239877/312500000 : ℝ)^5087 ≤ (8894775052047/100000000000000 : ℝ)^4063 := by
    have hnat : (45239877 : ℕ)^5087*100000000000000^4063 ≤ 8894775052047^4063*312500000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45239877 312500000 8894775052047 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299038183/2500000000 : ℝ), (2737926953/5000000000 : ℝ), (-45239877/312500000 : ℝ)] ![(220290148591/500000000000 : ℝ), (2940449700627/6250000000000 : ℝ), (8894775052047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299038183/2500000000 : ℝ)|^5087 ≤ (220290148591/500000000000 : ℝ)^4063
        have hw : |(1299038183/2500000000 : ℝ)|=(1299038183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2737926953/5000000000 : ℝ)|^5087 ≤ (2940449700627/6250000000000 : ℝ)^4063
        have hw : |(2737926953/5000000000 : ℝ)|=(2737926953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-45239877/312500000 : ℝ)|^5087 ≤ (8894775052047/100000000000000 : ℝ)^4063
        have hw : |(-45239877/312500000 : ℝ)|=(45239877/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_box_11 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4655482719/10000000000 : ℝ)*x 0 + (976042903/2500000000 : ℝ)*x 1 + (976042449/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4655482719/10000000000 : ℝ)^5087 ≤ (19197810430739/50000000000000 : ℝ)^4063 := by
    have hnat : (4655482719 : ℕ)^5087*50000000000000^4063 ≤ 19197810430739^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4655482719 10000000000 19197810430739 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (976042903/2500000000 : ℝ)^5087 ≤ (3080219852629/10000000000000 : ℝ)^4063 := by
    have hnat : (976042903 : ℕ)^5087*10000000000000^4063 ≤ 3080219852629^4063*2500000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976042903 2500000000 3080219852629 10000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (976042449/2500000000 : ℝ)^5087 ≤ (3850272573487/12500000000000 : ℝ)^4063 := by
    have hnat : (976042449 : ℕ)^5087*12500000000000^4063 ≤ 3850272573487^4063*2500000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976042449 2500000000 3850272573487 12500000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4655482719/10000000000 : ℝ), (976042903/2500000000 : ℝ), (976042449/2500000000 : ℝ)] ![(19197810430739/50000000000000 : ℝ), (3080219852629/10000000000000 : ℝ), (3850272573487/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4655482719/10000000000 : ℝ)|^5087 ≤ (19197810430739/50000000000000 : ℝ)^4063
        have hw : |(4655482719/10000000000 : ℝ)|=(4655482719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(976042903/2500000000 : ℝ)|^5087 ≤ (3080219852629/10000000000000 : ℝ)^4063
        have hw : |(976042903/2500000000 : ℝ)|=(976042903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(976042449/2500000000 : ℝ)|^5087 ≤ (3850272573487/12500000000000 : ℝ)^4063
        have hw : |(976042449/2500000000 : ℝ)|=(976042449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_box_12 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-165131767/1250000000 : ℝ)*x 0 + (561031161/1000000000 : ℝ)*x 1 + (515015673/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165131767/1250000000 : ℝ)^5087 ≤ (99146136229/1250000000000 : ℝ)^4063 := by
    have hnat : (165131767 : ℕ)^5087*1250000000000^4063 ≤ 99146136229^4063*1250000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165131767 1250000000 99146136229 1250000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561031161/1000000000 : ℝ)^5087 ≤ (48498023855863/100000000000000 : ℝ)^4063 := by
    have hnat : (561031161 : ℕ)^5087*100000000000000^4063 ≤ 48498023855863^4063*1000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561031161 1000000000 48498023855863 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515015673/1000000000 : ℝ)^5087 ≤ (680785706691/1562500000000 : ℝ)^4063 := by
    have hnat : (515015673 : ℕ)^5087*1562500000000^4063 ≤ 680785706691^4063*1000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515015673 1000000000 680785706691 1562500000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-165131767/1250000000 : ℝ), (561031161/1000000000 : ℝ), (515015673/1000000000 : ℝ)] ![(99146136229/1250000000000 : ℝ), (48498023855863/100000000000000 : ℝ), (680785706691/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-165131767/1250000000 : ℝ)|^5087 ≤ (99146136229/1250000000000 : ℝ)^4063
        have hw : |(-165131767/1250000000 : ℝ)|=(165131767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561031161/1000000000 : ℝ)|^5087 ≤ (48498023855863/100000000000000 : ℝ)^4063
        have hw : |(561031161/1000000000 : ℝ)|=(561031161/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(515015673/1000000000 : ℝ)|^5087 ≤ (680785706691/1562500000000 : ℝ)^4063
        have hw : |(515015673/1000000000 : ℝ)|=(515015673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_box_13 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2709264683/5000000000 : ℝ)*x 0 + (-317885241/2000000000 : ℝ)*x 1 + (5150156421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2709264683/5000000000 : ℝ)^5087 ≤ (46431362754937/100000000000000 : ℝ)^4063 := by
    have hnat : (2709264683 : ℕ)^5087*100000000000000^4063 ≤ 46431362754937^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709264683 5000000000 46431362754937 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (317885241/2000000000 : ℝ)^5087 ≤ (9998355269159/100000000000000 : ℝ)^4063 := by
    have hnat : (317885241 : ℕ)^5087*100000000000000^4063 ≤ 9998355269159^4063*2000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317885241 2000000000 9998355269159 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5150156421/10000000000 : ℝ)^5087 ≤ (10892570488811/25000000000000 : ℝ)^4063 := by
    have hnat : (5150156421 : ℕ)^5087*25000000000000^4063 ≤ 10892570488811^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150156421 10000000000 10892570488811 25000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2709264683/5000000000 : ℝ), (-317885241/2000000000 : ℝ), (5150156421/10000000000 : ℝ)] ![(46431362754937/100000000000000 : ℝ), (9998355269159/100000000000000 : ℝ), (10892570488811/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2709264683/5000000000 : ℝ)|^5087 ≤ (46431362754937/100000000000000 : ℝ)^4063
        have hw : |(2709264683/5000000000 : ℝ)|=(2709264683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-317885241/2000000000 : ℝ)|^5087 ≤ (9998355269159/100000000000000 : ℝ)^4063
        have hw : |(-317885241/2000000000 : ℝ)|=(317885241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5150156421/10000000000 : ℝ)|^5087 ≤ (10892570488811/25000000000000 : ℝ)^4063
        have hw : |(5150156421/10000000000 : ℝ)|=(5150156421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_box_14 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2709264543/5000000000 : ℝ)*x 0 + (515015707/1000000000 : ℝ)*x 1 + (-317885143/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2709264543/5000000000 : ℝ)^5087 ≤ (11607839937729/25000000000000 : ℝ)^4063 := by
    have hnat : (2709264543 : ℕ)^5087*25000000000000^4063 ≤ 11607839937729^4063*5000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709264543 5000000000 11607839937729 25000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515015707/1000000000 : ℝ)^5087 ≤ (21785144414781/50000000000000 : ℝ)^4063 := by
    have hnat : (515015707 : ℕ)^5087*50000000000000^4063 ≤ 21785144414781^4063*1000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515015707 1000000000 21785144414781 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317885143/2000000000 : ℝ)^5087 ≤ (9998351409943/100000000000000 : ℝ)^4063 := by
    have hnat : (317885143 : ℕ)^5087*100000000000000^4063 ≤ 9998351409943^4063*2000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317885143 2000000000 9998351409943 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2709264543/5000000000 : ℝ), (515015707/1000000000 : ℝ), (-317885143/2000000000 : ℝ)] ![(11607839937729/25000000000000 : ℝ), (21785144414781/50000000000000 : ℝ), (9998351409943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2709264543/5000000000 : ℝ)|^5087 ≤ (11607839937729/25000000000000 : ℝ)^4063
        have hw : |(2709264543/5000000000 : ℝ)|=(2709264543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(515015707/1000000000 : ℝ)|^5087 ≤ (21785144414781/50000000000000 : ℝ)^4063
        have hw : |(515015707/1000000000 : ℝ)|=(515015707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-317885143/2000000000 : ℝ)|^5087 ≤ (9998351409943/100000000000000 : ℝ)^4063
        have hw : |(-317885143/2000000000 : ℝ)|=(317885143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1683_box_15 (p : ℝ) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (732179873/2000000000 : ℝ)*x 0 + (4401456267/10000000000 : ℝ)*x 1 + (4401456421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (732179873/2000000000 : ℝ)^5087 ≤ (5683666547419/20000000000000 : ℝ)^4063 := by
    have hnat : (732179873 : ℕ)^5087*20000000000000^4063 ≤ 5683666547419^4063*2000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732179873 2000000000 5683666547419 20000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4401456267/10000000000 : ℝ)^5087 ≤ (35790832841101/100000000000000 : ℝ)^4063 := by
    have hnat : (4401456267 : ℕ)^5087*100000000000000^4063 ≤ 35790832841101^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4401456267 10000000000 35790832841101 100000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4401456421/10000000000 : ℝ)^5087 ≤ (17895417204487/50000000000000 : ℝ)^4063 := by
    have hnat : (4401456421 : ℕ)^5087*50000000000000^4063 ≤ 17895417204487^4063*10000000000^5087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4401456421 10000000000 17895417204487 50000000000000 5087 4063 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5087/1024 : ℝ)) 5087 4063 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(732179873/2000000000 : ℝ), (4401456267/10000000000 : ℝ), (4401456421/10000000000 : ℝ)] ![(5683666547419/20000000000000 : ℝ), (35790832841101/100000000000000 : ℝ), (17895417204487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(732179873/2000000000 : ℝ)|^5087 ≤ (5683666547419/20000000000000 : ℝ)^4063
        have hw : |(732179873/2000000000 : ℝ)|=(732179873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4401456267/10000000000 : ℝ)|^5087 ≤ (35790832841101/100000000000000 : ℝ)^4063
        have hw : |(4401456267/10000000000 : ℝ)|=(4401456267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4401456421/10000000000 : ℝ)|^5087 ≤ (17895417204487/50000000000000 : ℝ)^4063
        have hw : |(4401456421/10000000000 : ℝ)|=(4401456421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1683_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186066867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4321/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9759/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(33259/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(57763/100000 : ℝ) ∧ (40277/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (90027/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4321/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9759/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4321/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9759/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4321/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9759/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4321/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9759/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4321/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9759/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4321/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9759/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9759/100000 : ℝ) ^ (5079/1024 : ℝ) ≤ (971605251842219/100000000000000000000 : ℝ) := by
    have hpowers : (9759/100000 : ℝ)^5079 ≤ (971605251842219/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9759 : ℕ)^5079*100000000000000000000^1024 ≤ 971605251842219^1024*100000^5079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9759 100000 971605251842219 100000000000000000000 5079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9759/100000 : ℝ)) (X := (971605251842219/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4321/25000 : ℝ) ^ (5079/1024 : ℝ) ≤ (258562372109159/1562500000000000000 : ℝ) := by
    have hpowers : (4321/25000 : ℝ)^5079 ≤ (258562372109159/1562500000000000000 : ℝ)^1024 := by
      have hnat : (4321 : ℕ)^5079*1562500000000000000^1024 ≤ 258562372109159^1024*25000^5079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4321 25000 258562372109159 1562500000000000000 5079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4321/25000 : ℝ)) (X := (258562372109159/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000971605251842219/50000000000000000000 : ℝ) ≤ (10000039177635763/10000000000000000 : ℝ) ^ (5079/1024 : ℝ) := by
    have hpowers : (50000971605251842219/50000000000000000000 : ℝ)^1024 ≤ (10000039177635763/10000000000000000 : ℝ)^5079 := by
      have hnat : (50000971605251842219 : ℕ)^1024*10000000000000000^5079 ≤ 10000039177635763^5079*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000971605251842219 50000000000000000000 10000039177635763 10000000000000000 1024 5079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000039177635763/10000000000000000 : ℝ)) (X := (50000971605251842219/50000000000000000000 : ℝ)) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20003503919413365679/20000000000000000000 : ℝ) ≤ (625022074735251/625000000000000 : ℝ) ^ (5079/1024 : ℝ) := by
    have hpowers : (20003503919413365679/20000000000000000000 : ℝ)^1024 ≤ (625022074735251/625000000000000 : ℝ)^5079 := by
      have hnat : (20003503919413365679 : ℕ)^1024*625000000000000^5079 ≤ 625022074735251^5079*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20003503919413365679 20000000000000000000 625022074735251 625000000000000 1024 5079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625022074735251/625000000000000 : ℝ)) (X := (20003503919413365679/20000000000000000000 : ℝ)) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (781508562372109159/781250000000000000 : ℝ) ≤ (10000667213892269/10000000000000000 : ℝ) ^ (5079/1024 : ℝ) := by
    have hpowers : (781508562372109159/781250000000000000 : ℝ)^1024 ≤ (10000667213892269/10000000000000000 : ℝ)^5079 := by
      have hnat : (781508562372109159 : ℕ)^1024*10000000000000000^5079 ≤ 10000667213892269^5079*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781508562372109159 781250000000000000 10000667213892269 10000000000000000 1024 5079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000667213892269/10000000000000000 : ℝ)) (X := (781508562372109159/781250000000000000 : ℝ)) (by norm_num) 5079 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(971605251842219/100000000000000000000 : ℝ) ≤ ((75244165805881874521/75250000000000000000 : ℝ)+2*(314018128253/752500000000000 : ℝ)*(9759/100000 : ℝ))^(5079/1024 : ℝ) := by
    rw [show (75244165805881874521/75250000000000000000 : ℝ)+2*(314018128253/752500000000000 : ℝ)*(9759/100000 : ℝ)=(10000039177635763/10000000000000000 : ℝ) by norm_num, show 1+2*(971605251842219/100000000000000000000 : ℝ)=(50000971605251842219/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(258562372109159/1562500000000000000 : ℝ)+(971605251842219/100000000000000000000 : ℝ) ≤ ((75244165805881874521/75250000000000000000 : ℝ)+(314018128253/752500000000000 : ℝ)*((4321/25000 : ℝ)+(9759/100000 : ℝ)))^(5079/1024 : ℝ) := by
    rw [show (75244165805881874521/75250000000000000000 : ℝ)+(314018128253/752500000000000 : ℝ)*((4321/25000 : ℝ)+(9759/100000 : ℝ))=(625022074735251/625000000000000 : ℝ) by norm_num, show 1+(258562372109159/1562500000000000000 : ℝ)+(971605251842219/100000000000000000000 : ℝ)=(20003503919413365679/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(258562372109159/1562500000000000000 : ℝ) ≤ ((75244165805881874521/75250000000000000000 : ℝ)+2*(314018128253/752500000000000 : ℝ)*(4321/25000 : ℝ))^(5079/1024 : ℝ) := by
    rw [show (75244165805881874521/75250000000000000000 : ℝ)+2*(314018128253/752500000000000 : ℝ)*(4321/25000 : ℝ)=(10000667213892269/10000000000000000 : ℝ) by norm_num, show 1+2*(258562372109159/1562500000000000000 : ℝ)=(781508562372109159/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (75244165805881874521/75250000000000000000 : ℝ)*(X 1 0+X 2 0)+(314018128253/752500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5079/1024 : ℝ)) (lo := (9759/100000 : ℝ)) (hi := (4321/25000 : ℝ)) (c := (75244165805881874521/75250000000000000000 : ℝ)) (alpha := (314018128253/752500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (75244165805881874521/75250000000000000000 : ℝ)*(X 0 1+X 2 1)+(314018128253/752500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5079/1024 : ℝ)) (lo := (9759/100000 : ℝ)) (hi := (4321/25000 : ℝ)) (c := (75244165805881874521/75250000000000000000 : ℝ)) (alpha := (314018128253/752500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (75244165805881874521/75250000000000000000 : ℝ)*(X 0 2+X 1 2)+(314018128253/752500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5079/1024 : ℝ)) (lo := (9759/100000 : ℝ)) (hi := (4321/25000 : ℝ)) (c := (75244165805881874521/75250000000000000000 : ℝ)) (alpha := (314018128253/752500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-587428277/5000000000 : ℝ)*X 0 0+(1357996657/2500000000 : ℝ)*X 0 1+(5431984039/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2613047417/5000000000 : ℝ)*X 1 0+(-366893551/2500000000 : ℝ)*X 1 1+(5431984839/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1045219123/2000000000 : ℝ)*X 2 0+(543198361/1000000000 : ℝ)*X 2 1+(-733787419/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2263142391/5000000000 : ℝ)*X 0 0+(62051843/156250000 : ℝ)*X 0 1+(3971315849/10000000000 : ℝ)*X 0 2+(2263142391/5000000000 : ℝ)*X 1 0+(62051843/156250000 : ℝ)*X 1 1+(3971315849/10000000000 : ℝ)*X 1 2+(2263142391/5000000000 : ℝ)*X 2 0+(62051843/156250000 : ℝ)*X 2 1+(3971315849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-15025013/80000000 : ℝ)*X 0 0+(5175509341/10000000000 : ℝ)*X 0 1+(2587755321/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5401194433/10000000000 : ℝ)*X 1 0+(-315780979/2000000000 : ℝ)*X 1 1+(646938581/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5401194213/10000000000 : ℝ)*X 2 0+(2587754427/5000000000 : ℝ)*X 2 1+(-789452459/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3741458699/10000000000 : ℝ)*X 0 0+(272678411/625000000 : ℝ)*X 0 1+(2181428047/5000000000 : ℝ)*X 0 2+(3741458699/10000000000 : ℝ)*X 1 0+(272678411/625000000 : ℝ)*X 1 1+(2181428047/5000000000 : ℝ)*X 1 2+(3741458699/10000000000 : ℝ)*X 2 0+(272678411/625000000 : ℝ)*X 2 1+(2181428047/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-215922103/1250000000 : ℝ)*X 0 0+(997538499/2000000000 : ℝ)*X 0 1+(684481617/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5196152363/10000000000 : ℝ)*X 1 0+(-1447676689/10000000000 : ℝ)*X 1 1+(10695027/19531250 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1299038183/2500000000 : ℝ)*X 2 0+(2737926953/5000000000 : ℝ)*X 2 1+(-45239877/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4655482719/10000000000 : ℝ)*X 0 0+(976042903/2500000000 : ℝ)*X 0 1+(976042449/2500000000 : ℝ)*X 0 2+(4655482719/10000000000 : ℝ)*X 1 0+(976042903/2500000000 : ℝ)*X 1 1+(976042449/2500000000 : ℝ)*X 1 2+(4655482719/10000000000 : ℝ)*X 2 0+(976042903/2500000000 : ℝ)*X 2 1+(976042449/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-165131767/1250000000 : ℝ)*X 0 0+(561031161/1000000000 : ℝ)*X 0 1+(515015673/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2709264683/5000000000 : ℝ)*X 1 0+(-317885241/2000000000 : ℝ)*X 1 1+(5150156421/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2709264543/5000000000 : ℝ)*X 2 0+(515015707/1000000000 : ℝ)*X 2 1+(-317885143/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((732179873/2000000000 : ℝ)*X 0 0+(4401456267/10000000000 : ℝ)*X 0 1+(4401456421/10000000000 : ℝ)*X 0 2+(732179873/2000000000 : ℝ)*X 1 0+(4401456267/10000000000 : ℝ)*X 1 1+(4401456421/10000000000 : ℝ)*X 1 2+(732179873/2000000000 : ℝ)*X 2 0+(4401456267/10000000000 : ℝ)*X 2 1+(4401456421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1683_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-33259/50000 : ℝ) ≤ (-625663570858360705622277317844789/940625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63397627/100000000000000 : ℝ)*(upper1) + (56472851/50000000000000 : ℝ)*(lower4) + (104605437/50000000000000 : ℝ)*(upper5) + (643712464314297/50000000000000 : ℝ)*(major0) + (643712464314297/50000000000000 : ℝ)*(major1) + (257484985725719/20000000000000 : ℝ)*(major2) + (6042459947/50000000000000 : ℝ)*(sp1) + (16141752351/100000000000000 : ℝ)*(sp2) + (481664313/10000000000000 : ℝ)*(sp3) + (1905103994122109/100000000000000 : ℝ)*(sp4) + (238136810651919/12500000000000 : ℝ)*(sp5) + (119068151773931/6250000000000 : ℝ)*(sp6) + (691910379966589/100000000000000 : ℝ)*(sp7) + (1288006569/50000000000000 : ℝ)*(sp12) + (691915196609719/100000000000000 : ℝ)*(f.failure) + (1905106570135247/100000000000000 : ℝ)*(f.sum) + (88963881291317/75250000000000000000000000000 : ℝ)*base65 + (26940992545925423263/3762500000000000000000000000000000 : ℝ)*base68 + (710924491663854401/1505000000000000000000000000000000 : ℝ)*base70 + (13004448021050423263/3762500000000000000000000000000000 : ℝ)*base72 + (2954304491183/75250000000000000000000000000 : ℝ)*base74 + (3292754100116145599/1505000000000000000000000000000000 : ℝ)*base75 + (2631150327139367609/537500000000000000000000000000000 : ℝ)*base78 + (3100109527914367609/537500000000000000000000000000000 : ℝ)*base80 + (3814299305981/1343750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (36080373/10000000000000000000000 : ℝ)*base89 + (36080373/10000000000000000000000 : ℝ)*base91 + (63919627/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (57763/100000 : ℝ) ≤ (310488424748188031642990997403629/537500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4983279/12500000000000 : ℝ)*(lower2) + (47626539/100000000000000 : ℝ)*(upper4) + (29958481/12500000000000 : ℝ)*(lower5) + (1384458223583159/100000000000000 : ℝ)*(major0) + (1384458223583159/100000000000000 : ℝ)*(major1) + (34611455589579/2500000000000 : ℝ)*(major2) + (1002793881152807/50000000000000 : ℝ)*(sp0) + (1002795848330151/50000000000000 : ℝ)*(sp1) + (250699455688969/12500000000000 : ℝ)*(sp2) + (744062326028487/100000000000000 : ℝ)*(sp3) + (4767453937/100000000000000 : ℝ)*(sp5) + (818602487/100000000000000 : ℝ)*(sp6) + (640228793/25000000000000 : ℝ)*(sp7) + (69614469/800000000000 : ℝ)*(sp8) + (37203244347183/5000000000000 : ℝ)*(f.failure) + (2005596464114239/100000000000000 : ℝ)*(f.sum) + (285163329734207/75250000000000000000000000000 : ℝ)*base65 + (4621116582880208161/7525000000000000000000000000000000 : ℝ)*base68 + (1360982393933159159/188125000000000000000000000000000 : ℝ)*base69 + (34576202157419791839/7525000000000000000000000000000000 : ℝ)*base71 + (206460182543/75250000000000000000000000000 : ℝ)*base74 + (1647338629553159159/188125000000000000000000000000000 : ℝ)*base75 + (7104416614044491839/7525000000000000000000000000000000 : ℝ)*base77 + (19689309080519491839/7525000000000000000000000000000000 : ℝ)*base79 + (31214009065051/18812500000000000000000000000 : ℝ)*base81 + (6085661/500000000000000000000 : ℝ)*base89 + (6085661/500000000000000000000 : ℝ)*base91 + (1085661/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (40277/50000 : ℝ) ≤ (757737337275761316793012764312483/940625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (109653/10000000000000 : ℝ)*(upper0) + (16396961/100000000000000 : ℝ)*(upper2) + (9064317/10000000000000 : ℝ)*(upper3) + (210988029/100000000000000 : ℝ)*(upper4) + (709496413282159/50000000000000 : ℝ)*(major0) + (709496413282159/50000000000000 : ℝ)*(major1) + (709496413282159/50000000000000 : ℝ)*(major2) + (20803845153/100000000000000 : ℝ)*(sp1) + (60546263693/100000000000000 : ℝ)*(sp2) + (8782199609/50000000000000 : ℝ)*(sp3) + (2048508183325471/100000000000000 : ℝ)*(sp8) + (1024243689740159/50000000000000 : ℝ)*(sp9) + (2048447637061777/100000000000000 : ℝ)*(sp10) + (95325955120007/12500000000000 : ℝ)*(sp11) + (381312602679637/50000000000000 : ℝ)*(f.failure) + (2048508183325471/100000000000000 : ℝ)*(f.sum) + (132400308773477/18812500000000000000000000000 : ℝ)*base65 + (24011147317666170839/3762500000000000000000000000000000 : ℝ)*base67 + (13432031980596329161/3762500000000000000000000000000000 : ℝ)*base70 + (21300748333628670839/3762500000000000000000000000000000 : ℝ)*base71 + (4994312657169/2351562500000000000000000000 : ℝ)*base73 + (2243526751366170839/3762500000000000000000000000000000 : ℝ)*base75 + (43441556123341170839/3762500000000000000000000000000000 : ℝ)*base77 + (49544290484578670839/3762500000000000000000000000000000 : ℝ)*base79 + (60300334449023/18812500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (38712721/5000000000000000000000 : ℝ)*base90 + (38712721/5000000000000000000000 : ℝ)*base92 + (38712721/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-90027/100000 : ℝ) ≤ (-105848809847315540700564031716117/117578125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24079879/50000000000000 : ℝ)*(lower0) + (3696519/4000000000000 : ℝ)*(lower1) + (12333729/20000000000000 : ℝ)*(lower2) + (91585005366891/6250000000000 : ℝ)*(major0) + (91585005366891/6250000000000 : ℝ)*(major1) + (91585005366891/6250000000000 : ℝ)*(major2) + (947196239/50000000000000 : ℝ)*(sp0) + (83997944111/100000000000000 : ℝ)*(sp5) + (13321178723/100000000000000 : ℝ)*(sp6) + (3447777937/50000000000000 : ℝ)*(sp7) + (2173181475558797/100000000000000 : ℝ)*(sp12) + (543274843001791/25000000000000 : ℝ)*(sp13) + (271646256096569/12500000000000 : ℝ)*(sp14) + (787537985215541/100000000000000 : ℝ)*(sp15) + (393772440385707/50000000000000 : ℝ)*(f.failure) + (86927334798051/4000000000000 : ℝ)*(f.sum) + (87334711593107/37625000000000000000000000000 : ℝ)*base66 + (2465418732373128289/470312500000000000000000000000000 : ℝ)*base68 + (2828925682910628289/470312500000000000000000000000000 : ℝ)*base70 + (2679622209174690789/470312500000000000000000000000000 : ℝ)*base72 + (28141372927259/18812500000000000000000000000 : ℝ)*base73 + (3325509613410628289/470312500000000000000000000000000 : ℝ)*base76 + (1899874835087190789/470312500000000000000000000000000 : ℝ)*base78 + (1588139459614371711/470312500000000000000000000000000 : ℝ)*base79 + (178648943735107/37625000000000000000000000000 : ℝ)*base82 + (26930031/5000000000000000000000 : ℝ)*base90 + (26930031/5000000000000000000000 : ℝ)*base92 + (26930031/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1683_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186066867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4321/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9759/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33259/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(57763/100000 : ℝ) else (40277/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90027/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1683_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1683_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186066867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8657/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9733/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33259/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(57763/100000 : ℝ) else (40277/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90027/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1683_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1683_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1683_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5079/1024 : ℝ) ≤ p) (hpb : p ≤ (5087/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186066867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8657/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9733/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33259/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(57763/100000 : ℝ) else (40277/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90027/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1683_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

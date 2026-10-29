-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1498_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:51:40.744885+00:00
-- url     : https://prove2.me/submissions/88659e28-7f23-49c6-82d0-5bc761a018f2

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
theorem support_rectangle_w1498_s6_0 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-118056147/625000000 : ℝ)*x 0 + (2717530341/5000000000 : ℝ)*x 1 + (5216898329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (118056147/625000000 : ℝ)^4493 ≤ (5774648432809/50000000000000 : ℝ)^3469 := by
    have hnat : (118056147 : ℕ)^4493*50000000000000^3469 ≤ 5774648432809^3469*625000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118056147 625000000 5774648432809 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717530341/5000000000 : ℝ)^4493 ≤ (11349597735343/25000000000000 : ℝ)^3469 := by
    have hnat : (2717530341 : ℕ)^4493*25000000000000^3469 ≤ 11349597735343^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717530341 5000000000 11349597735343 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216898329/10000000000 : ℝ)^4493 ≤ (43052312175123/100000000000000 : ℝ)^3469 := by
    have hnat : (5216898329 : ℕ)^4493*100000000000000^3469 ≤ 43052312175123^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216898329 10000000000 43052312175123 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-118056147/625000000 : ℝ), (2717530341/5000000000 : ℝ), (5216898329/10000000000 : ℝ)] ![(5774648432809/50000000000000 : ℝ), (11349597735343/25000000000000 : ℝ), (43052312175123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-118056147/625000000 : ℝ)|^4493 ≤ (5774648432809/50000000000000 : ℝ)^3469
        have hw : |(-118056147/625000000 : ℝ)|=(118056147/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717530341/5000000000 : ℝ)|^4493 ≤ (11349597735343/25000000000000 : ℝ)^3469
        have hw : |(2717530341/5000000000 : ℝ)|=(2717530341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216898329/10000000000 : ℝ)|^4493 ≤ (43052312175123/100000000000000 : ℝ)^3469
        have hw : |(5216898329/10000000000 : ℝ)|=(5216898329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s6_1 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352358043/10000000000 : ℝ)*x 0 + (-2000662701/10000000000 : ℝ)*x 1 + (5216898329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352358043/10000000000 : ℝ)^4493 ≤ (445056867471/1000000000000 : ℝ)^3469 := by
    have hnat : (5352358043 : ℕ)^4493*1000000000000^3469 ≤ 445056867471^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352358043 10000000000 445056867471 1000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2000662701/10000000000 : ℝ)^4493 ≤ (12442001067849/100000000000000 : ℝ)^3469 := by
    have hnat : (2000662701 : ℕ)^4493*100000000000000^3469 ≤ 12442001067849^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000662701 10000000000 12442001067849 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216898329/10000000000 : ℝ)^4493 ≤ (43052312175123/100000000000000 : ℝ)^3469 := by
    have hnat : (5216898329 : ℕ)^4493*100000000000000^3469 ≤ 43052312175123^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216898329 10000000000 43052312175123 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352358043/10000000000 : ℝ), (-2000662701/10000000000 : ℝ), (5216898329/10000000000 : ℝ)] ![(445056867471/1000000000000 : ℝ), (12442001067849/100000000000000 : ℝ), (43052312175123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352358043/10000000000 : ℝ)|^4493 ≤ (445056867471/1000000000000 : ℝ)^3469
        have hw : |(5352358043/10000000000 : ℝ)|=(5352358043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2000662701/10000000000 : ℝ)|^4493 ≤ (12442001067849/100000000000000 : ℝ)^3469
        have hw : |(-2000662701/10000000000 : ℝ)|=(2000662701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216898329/10000000000 : ℝ)|^4493 ≤ (43052312175123/100000000000000 : ℝ)^3469
        have hw : |(5216898329/10000000000 : ℝ)|=(5216898329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s6_2 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352358043/10000000000 : ℝ)*x 0 + (5216898329/10000000000 : ℝ)*x 1 + (-2000662701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352358043/10000000000 : ℝ)^4493 ≤ (445056867471/1000000000000 : ℝ)^3469 := by
    have hnat : (5352358043 : ℕ)^4493*1000000000000^3469 ≤ 445056867471^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352358043 10000000000 445056867471 1000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216898329/10000000000 : ℝ)^4493 ≤ (43052312175123/100000000000000 : ℝ)^3469 := by
    have hnat : (5216898329 : ℕ)^4493*100000000000000^3469 ≤ 43052312175123^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216898329 10000000000 43052312175123 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2000662701/10000000000 : ℝ)^4493 ≤ (12442001067849/100000000000000 : ℝ)^3469 := by
    have hnat : (2000662701 : ℕ)^4493*100000000000000^3469 ≤ 12442001067849^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000662701 10000000000 12442001067849 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352358043/10000000000 : ℝ), (5216898329/10000000000 : ℝ), (-2000662701/10000000000 : ℝ)] ![(445056867471/1000000000000 : ℝ), (43052312175123/100000000000000 : ℝ), (12442001067849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352358043/10000000000 : ℝ)|^4493 ≤ (445056867471/1000000000000 : ℝ)^3469
        have hw : |(5352358043/10000000000 : ℝ)|=(5352358043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216898329/10000000000 : ℝ)|^4493 ≤ (43052312175123/100000000000000 : ℝ)^3469
        have hw : |(5216898329/10000000000 : ℝ)|=(5216898329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2000662701/10000000000 : ℝ)|^4493 ≤ (12442001067849/100000000000000 : ℝ)^3469
        have hw : |(-2000662701/10000000000 : ℝ)|=(2000662701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s6_3 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2138168399/5000000000 : ℝ)*x 0 + (2018724233/5000000000 : ℝ)*x 1 + (141477307/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138168399/5000000000 : ℝ)^4493 ≤ (33278942529411/100000000000000 : ℝ)^3469 := by
    have hnat : (2138168399 : ℕ)^4493*100000000000000^3469 ≤ 33278942529411^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138168399 5000000000 33278942529411 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2018724233/5000000000 : ℝ)^4493 ≤ (3089123826221/10000000000000 : ℝ)^3469 := by
    have hnat : (2018724233 : ℕ)^4493*10000000000000^3469 ≤ 3089123826221^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018724233 5000000000 3089123826221 10000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141477307/312500000 : ℝ)^4493 ≤ (35829819200183/100000000000000 : ℝ)^3469 := by
    have hnat : (141477307 : ℕ)^4493*100000000000000^3469 ≤ 35829819200183^3469*312500000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141477307 312500000 35829819200183 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2138168399/5000000000 : ℝ), (2018724233/5000000000 : ℝ), (141477307/312500000 : ℝ)] ![(33278942529411/100000000000000 : ℝ), (3089123826221/10000000000000 : ℝ), (35829819200183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2138168399/5000000000 : ℝ)|^4493 ≤ (33278942529411/100000000000000 : ℝ)^3469
        have hw : |(2138168399/5000000000 : ℝ)|=(2138168399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2018724233/5000000000 : ℝ)|^4493 ≤ (3089123826221/10000000000000 : ℝ)^3469
        have hw : |(2018724233/5000000000 : ℝ)|=(2018724233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(141477307/312500000 : ℝ)|^4493 ≤ (35829819200183/100000000000000 : ℝ)^3469
        have hw : |(141477307/312500000 : ℝ)|=(141477307/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s6_4 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1888928201/10000000000 : ℝ)*x 0 + (1304504537/2500000000 : ℝ)*x 1 + (1358483101/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1888928201/10000000000 : ℝ)^4493 ≤ (11549533245153/100000000000000 : ℝ)^3469 := by
    have hnat : (1888928201 : ℕ)^4493*100000000000000^3469 ≤ 11549533245153^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888928201 10000000000 11549533245153 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304504537/2500000000 : ℝ)^4493 ≤ (43064281724937/100000000000000 : ℝ)^3469 := by
    have hnat : (1304504537 : ℕ)^4493*100000000000000^3469 ≤ 43064281724937^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304504537 2500000000 43064281724937 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358483101/2500000000 : ℝ)^4493 ≤ (45386185008011/100000000000000 : ℝ)^3469 := by
    have hnat : (1358483101 : ℕ)^4493*100000000000000^3469 ≤ 45386185008011^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358483101 2500000000 45386185008011 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1888928201/10000000000 : ℝ), (1304504537/2500000000 : ℝ), (1358483101/2500000000 : ℝ)] ![(11549533245153/100000000000000 : ℝ), (43064281724937/100000000000000 : ℝ), (45386185008011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1888928201/10000000000 : ℝ)|^4493 ≤ (11549533245153/100000000000000 : ℝ)^3469
        have hw : |(-1888928201/10000000000 : ℝ)|=(1888928201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304504537/2500000000 : ℝ)|^4493 ≤ (43064281724937/100000000000000 : ℝ)^3469
        have hw : |(1304504537/2500000000 : ℝ)|=(1304504537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358483101/2500000000 : ℝ)|^4493 ≤ (45386185008011/100000000000000 : ℝ)^3469
        have hw : |(1358483101/2500000000 : ℝ)|=(1358483101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s6_5 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661901529/1250000000 : ℝ)*x 0 + (-1783628821/10000000000 : ℝ)*x 1 + (2716966101/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661901529/1250000000 : ℝ)^4493 ≤ (10972804346009/25000000000000 : ℝ)^3469 := by
    have hnat : (661901529 : ℕ)^4493*25000000000000^3469 ≤ 10972804346009^3469*1250000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661901529 1250000000 10972804346009 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1783628821/10000000000 : ℝ)^4493 ≤ (2680649946101/25000000000000 : ℝ)^3469 := by
    have hnat : (1783628821 : ℕ)^4493*25000000000000^3469 ≤ 2680649946101^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1783628821 10000000000 2680649946101 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716966101/5000000000 : ℝ)^4493 ≤ (22693091411401/50000000000000 : ℝ)^3469 := by
    have hnat : (2716966101 : ℕ)^4493*50000000000000^3469 ≤ 22693091411401^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716966101 5000000000 22693091411401 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661901529/1250000000 : ℝ), (-1783628821/10000000000 : ℝ), (2716966101/5000000000 : ℝ)] ![(10972804346009/25000000000000 : ℝ), (2680649946101/25000000000000 : ℝ), (22693091411401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661901529/1250000000 : ℝ)|^4493 ≤ (10972804346009/25000000000000 : ℝ)^3469
        have hw : |(661901529/1250000000 : ℝ)|=(661901529/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1783628821/10000000000 : ℝ)|^4493 ≤ (2680649946101/25000000000000 : ℝ)^3469
        have hw : |(-1783628821/10000000000 : ℝ)|=(1783628821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716966101/5000000000 : ℝ)|^4493 ≤ (22693091411401/50000000000000 : ℝ)^3469
        have hw : |(2716966101/5000000000 : ℝ)|=(2716966101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s6_6 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295212513/10000000000 : ℝ)*x 0 + (5433932279/10000000000 : ℝ)*x 1 + (-891814163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295212513/10000000000 : ℝ)^4493 ≤ (2194561020037/5000000000000 : ℝ)^3469 := by
    have hnat : (5295212513 : ℕ)^4493*5000000000000^3469 ≤ 2194561020037^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295212513 10000000000 2194561020037 5000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433932279/10000000000 : ℝ)^4493 ≤ (45386183655777/100000000000000 : ℝ)^3469 := by
    have hnat : (5433932279 : ℕ)^4493*100000000000000^3469 ≤ 45386183655777^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433932279 10000000000 45386183655777 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (891814163/5000000000 : ℝ)^4493 ≤ (1340324491277/12500000000000 : ℝ)^3469 := by
    have hnat : (891814163 : ℕ)^4493*12500000000000^3469 ≤ 1340324491277^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891814163 5000000000 1340324491277 12500000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295212513/10000000000 : ℝ), (5433932279/10000000000 : ℝ), (-891814163/5000000000 : ℝ)] ![(2194561020037/5000000000000 : ℝ), (45386183655777/100000000000000 : ℝ), (1340324491277/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295212513/10000000000 : ℝ)|^4493 ≤ (2194561020037/5000000000000 : ℝ)^3469
        have hw : |(5295212513/10000000000 : ℝ)|=(5295212513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433932279/10000000000 : ℝ)|^4493 ≤ (45386183655777/100000000000000 : ℝ)^3469
        have hw : |(5433932279/10000000000 : ℝ)|=(5433932279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-891814163/5000000000 : ℝ)|^4493 ≤ (1340324491277/12500000000000 : ℝ)^3469
        have hw : |(-891814163/5000000000 : ℝ)|=(891814163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s6_7 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4276403367/10000000000 : ℝ)*x 0 + (2262379829/5000000000 : ℝ)*x 1 + (4039980909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4276403367/10000000000 : ℝ)^4493 ≤ (33279613498889/100000000000000 : ℝ)^3469 := by
    have hnat : (4276403367 : ℕ)^4493*100000000000000^3469 ≤ 33279613498889^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4276403367 10000000000 33279613498889 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2262379829/5000000000 : ℝ)^4493 ≤ (17902025077737/50000000000000 : ℝ)^3469 := by
    have hnat : (2262379829 : ℕ)^4493*50000000000000^3469 ≤ 17902025077737^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262379829 5000000000 17902025077737 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4039980909/10000000000 : ℝ)^4493 ≤ (30916336331873/100000000000000 : ℝ)^3469 := by
    have hnat : (4039980909 : ℕ)^4493*100000000000000^3469 ≤ 30916336331873^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4039980909 10000000000 30916336331873 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4276403367/10000000000 : ℝ), (2262379829/5000000000 : ℝ), (4039980909/10000000000 : ℝ)] ![(33279613498889/100000000000000 : ℝ), (17902025077737/50000000000000 : ℝ), (30916336331873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4276403367/10000000000 : ℝ)|^4493 ≤ (33279613498889/100000000000000 : ℝ)^3469
        have hw : |(4276403367/10000000000 : ℝ)|=(4276403367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2262379829/5000000000 : ℝ)|^4493 ≤ (17902025077737/50000000000000 : ℝ)^3469
        have hw : |(2262379829/5000000000 : ℝ)|=(2262379829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4039980909/10000000000 : ℝ)|^4493 ≤ (30916336331873/100000000000000 : ℝ)^3469
        have hw : |(4039980909/10000000000 : ℝ)|=(4039980909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1498_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (543/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (10861/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (387/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (543/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (543/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (543/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (543/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (543/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (543/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (543/5000 : ℝ) ^ (4491/1024 : ℝ) ≤ (5907424620444449/100000000000000000000 : ℝ) := by
    have hpowers : (543/5000 : ℝ)^4491 ≤ (5907424620444449/100000000000000000000 : ℝ)^1024 := by
      have hnat : (543 : ℕ)^4491*100000000000000000000^1024 ≤ 5907424620444449^1024*5000^4491 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        543 5000 5907424620444449 100000000000000000000 4491 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (543/5000 : ℝ)) (X := (5907424620444449/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15481/100000 : ℝ) ^ (4491/1024 : ℝ) ≤ (3496047733081247/12500000000000000000 : ℝ) := by
    have hpowers : (15481/100000 : ℝ)^4491 ≤ (3496047733081247/12500000000000000000 : ℝ)^1024 := by
      have hnat : (15481 : ℕ)^4491*12500000000000000000^1024 ≤ 3496047733081247^1024*100000^4491 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15481 100000 3496047733081247 12500000000000000000 4491 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15481/100000 : ℝ)) (X := (3496047733081247/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005907424620444449/50000000000000000000 : ℝ) ≤ (1000026937995809/1000000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (50005907424620444449/50000000000000000000 : ℝ)^1024 ≤ (1000026937995809/1000000000000000 : ℝ)^4491 := by
      have hnat : (50005907424620444449 : ℕ)^1024*1000000000000000^4491 ≤ 1000026937995809^4491*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005907424620444449 50000000000000000000 1000026937995809 1000000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000026937995809/1000000000000000 : ℝ)) (X := (50005907424620444449/50000000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001355032259403777/4000000000000000000 : ℝ) ≤ (10000772306632911/10000000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (4001355032259403777/4000000000000000000 : ℝ)^1024 ≤ (10000772306632911/10000000000000000 : ℝ)^4491 := by
      have hnat : (4001355032259403777 : ℕ)^1024*10000000000000000^4491 ≤ 10000772306632911^4491*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001355032259403777 4000000000000000000 10000772306632911 10000000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000772306632911/10000000000000000 : ℝ)) (X := (4001355032259403777/4000000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253496047733081247/6250000000000000000 : ℝ) ≤ (2500318808326933/2500000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (6253496047733081247/6250000000000000000 : ℝ)^1024 ≤ (2500318808326933/2500000000000000 : ℝ)^4491 := by
      have hnat : (6253496047733081247 : ℕ)^1024*2500000000000000^4491 ≤ 2500318808326933^4491*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253496047733081247 6250000000000000000 2500318808326933 2500000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500318808326933/2500000000000000 : ℝ)) (X := (6253496047733081247/6250000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5907424620444449/100000000000000000000 : ℝ) ≤ ((4620032123740922177/4621000000000000000 : ℝ)+2*(502926674821/462100000000000 : ℝ)*(543/5000 : ℝ))^(4491/1024 : ℝ) := by
    rw [show (4620032123740922177/4621000000000000000 : ℝ)+2*(502926674821/462100000000000 : ℝ)*(543/5000 : ℝ)=(1000026937995809/1000000000000000 : ℝ) by norm_num, show 1+2*(5907424620444449/100000000000000000000 : ℝ)=(50005907424620444449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3496047733081247/12500000000000000000 : ℝ)+(5907424620444449/100000000000000000000 : ℝ) ≤ ((4620032123740922177/4621000000000000000 : ℝ)+(502926674821/462100000000000 : ℝ)*((15481/100000 : ℝ)+(543/5000 : ℝ)))^(4491/1024 : ℝ) := by
    rw [show (4620032123740922177/4621000000000000000 : ℝ)+(502926674821/462100000000000 : ℝ)*((15481/100000 : ℝ)+(543/5000 : ℝ))=(10000772306632911/10000000000000000 : ℝ) by norm_num, show 1+(3496047733081247/12500000000000000000 : ℝ)+(5907424620444449/100000000000000000000 : ℝ)=(4001355032259403777/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3496047733081247/12500000000000000000 : ℝ) ≤ ((4620032123740922177/4621000000000000000 : ℝ)+2*(502926674821/462100000000000 : ℝ)*(15481/100000 : ℝ))^(4491/1024 : ℝ) := by
    rw [show (4620032123740922177/4621000000000000000 : ℝ)+2*(502926674821/462100000000000 : ℝ)*(15481/100000 : ℝ)=(2500318808326933/2500000000000000 : ℝ) by norm_num, show 1+2*(3496047733081247/12500000000000000000 : ℝ)=(6253496047733081247/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4620032123740922177/4621000000000000000 : ℝ)*(X 1 0+X 2 0)+(502926674821/462100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (543/5000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (4620032123740922177/4621000000000000000 : ℝ)) (alpha := (502926674821/462100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4620032123740922177/4621000000000000000 : ℝ)*(X 0 1+X 2 1)+(502926674821/462100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (543/5000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (4620032123740922177/4621000000000000000 : ℝ)) (alpha := (502926674821/462100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4620032123740922177/4621000000000000000 : ℝ)*(X 0 2+X 1 2)+(502926674821/462100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (543/5000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (4620032123740922177/4621000000000000000 : ℝ)) (alpha := (502926674821/462100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-118056147/625000000 : ℝ)*X 0 0+(2717530341/5000000000 : ℝ)*X 0 1+(5216898329/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352358043/10000000000 : ℝ)*X 1 0+(-2000662701/10000000000 : ℝ)*X 1 1+(5216898329/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352358043/10000000000 : ℝ)*X 2 0+(5216898329/10000000000 : ℝ)*X 2 1+(-2000662701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2138168399/5000000000 : ℝ)*X 0 0+(2018724233/5000000000 : ℝ)*X 0 1+(141477307/312500000 : ℝ)*X 0 2+(2138168399/5000000000 : ℝ)*X 1 0+(2018724233/5000000000 : ℝ)*X 1 1+(141477307/312500000 : ℝ)*X 1 2+(2138168399/5000000000 : ℝ)*X 2 0+(2018724233/5000000000 : ℝ)*X 2 1+(141477307/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1888928201/10000000000 : ℝ)*X 0 0+(1304504537/2500000000 : ℝ)*X 0 1+(1358483101/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661901529/1250000000 : ℝ)*X 1 0+(-1783628821/10000000000 : ℝ)*X 1 1+(2716966101/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295212513/10000000000 : ℝ)*X 2 0+(5433932279/10000000000 : ℝ)*X 2 1+(-891814163/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4276403367/10000000000 : ℝ)*X 0 0+(2262379829/5000000000 : ℝ)*X 0 1+(4039980909/10000000000 : ℝ)*X 0 2+(4276403367/10000000000 : ℝ)*X 1 0+(2262379829/5000000000 : ℝ)*X 1 1+(4039980909/10000000000 : ℝ)*X 1 2+(4276403367/10000000000 : ℝ)*X 2 0+(2262379829/5000000000 : ℝ)*X 2 1+(4039980909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40030355378854079955569943/11552500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (615004573/100000000000000 : ℝ)*(base19) + (573737701/100000000000000 : ℝ)*(base23) + (22087507/100000000000000 : ℝ)*(lower2) + (86873723/100000000000000 : ℝ)*(upper3) + (56589681/100000000000000 : ℝ)*(upper5) + (331265728250147/10000000000000 : ℝ)*(major0) + (331265728250147/10000000000000 : ℝ)*(major1) + (331265728250147/10000000000000 : ℝ)*(major2) + (2291876104887739/50000000000000 : ℝ)*(sp0) + (4583761145769623/100000000000000 : ℝ)*(sp1) + (916752237407299/20000000000000 : ℝ)*(sp2) + (2041548074636683/100000000000000 : ℝ)*(sp3) + (4775499359/50000000000000 : ℝ)*(sp4) + (922817867/20000000000000 : ℝ)*(sp7) + (1020776344363009/50000000000000 : ℝ)*(f.failure) + (1145940440193549/25000000000000 : ℝ)*(f.sum) + (3149660272869/4621000000000000000000000000 : ℝ)*base65 + (88196519921400019/46210000000000000000000000000000 : ℝ)*base67 + (293146664932070019/46210000000000000000000000000000 : ℝ)*base69 + (13624494723400019/46210000000000000000000000000000 : ℝ)*base71 + (1608586107311/4621000000000000000000000000 : ℝ)*base74 + (353144544431140019/46210000000000000000000000000000 : ℝ)*base75 + (183167790906759981/46210000000000000000000000000000 : ℝ)*base78 + (612530918966450019/46210000000000000000000000000000 : ℝ)*base79 + (6641236988811/2310500000000000000000000000 : ℝ)*base81 + (853253/250000000000000000000 : ℝ)*base90 + (853253/250000000000000000000 : ℝ)*base92 + (853253/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (243987120660586947582011997/23105000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1170879271/50000000000000 : ℝ)*(base19) + (1404596827/50000000000000 : ℝ)*(base23) + (582532681/100000000000000 : ℝ)*(lower1) + (25851479/100000000000000 : ℝ)*(upper2) + (393175091/100000000000000 : ℝ)*(upper3) + (4610663/2000000000000 : ℝ)*(upper5) + (334711293098371/10000000000000 : ℝ)*(major0) + (334711293098371/10000000000000 : ℝ)*(major1) + (334711293098371/10000000000000 : ℝ)*(major2) + (16015600659/100000000000000 : ℝ)*(sp2) + (2315719100136411/50000000000000 : ℝ)*(sp4) + (115785896462857/2500000000000 : ℝ)*(sp5) + (4631419375478509/100000000000000 : ℝ)*(sp6) + (206278730969701/10000000000000 : ℝ)*(sp7) + (206278730969701/10000000000000 : ℝ)*(f.failure) + (2315719100136411/50000000000000 : ℝ)*(f.sum) + (3145544798013/2310500000000000000000000000 : ℝ)*base66 + (235817061216823667/46210000000000000000000000000000 : ℝ)*base67 + (1770714098797003667/46210000000000000000000000000000 : ℝ)*base69 + (240386796120083667/46210000000000000000000000000000 : ℝ)*base71 + (971316359759/2310500000000000000000000000 : ℝ)*base74 + (252137027785883667/46210000000000000000000000000000 : ℝ)*base75 + (236160406692343667/46210000000000000000000000000000 : ℝ)*base77 + (85767776975963667/46210000000000000000000000000000 : ℝ)*base79 + (13527839077369/924200000000000000000000000 : ℝ)*base81 + (301817/50000000000000000000 : ℝ)*base90 + (301817/50000000000000000000 : ℝ)*base92 + (301817/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1498_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (543/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10861/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (387/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1498_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1498_s7_0 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676178253/5000000000 : ℝ)*x 0 + (2608451991/5000000000 : ℝ)*x 1 + (-1000328627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676178253/5000000000 : ℝ)^4493 ≤ (8901134038823/20000000000000 : ℝ)^3469 := by
    have hnat : (2676178253 : ℕ)^4493*20000000000000^3469 ≤ 8901134038823^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676178253 5000000000 8901134038823 20000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608451991/5000000000 : ℝ)^4493 ≤ (43052372597149/100000000000000 : ℝ)^3469 := by
    have hnat : (2608451991 : ℕ)^4493*100000000000000^3469 ≤ 43052372597149^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608451991 5000000000 43052372597149 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000328627/5000000000 : ℝ)^4493 ≤ (6220978597003/50000000000000 : ℝ)^3469 := by
    have hnat : (1000328627 : ℕ)^4493*50000000000000^3469 ≤ 6220978597003^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000328627 5000000000 6220978597003 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676178253/5000000000 : ℝ), (2608451991/5000000000 : ℝ), (-1000328627/5000000000 : ℝ)] ![(8901134038823/20000000000000 : ℝ), (43052372597149/100000000000000 : ℝ), (6220978597003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676178253/5000000000 : ℝ)|^4493 ≤ (8901134038823/20000000000000 : ℝ)^3469
        have hw : |(2676178253/5000000000 : ℝ)|=(2676178253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608451991/5000000000 : ℝ)|^4493 ≤ (43052372597149/100000000000000 : ℝ)^3469
        have hw : |(2608451991/5000000000 : ℝ)|=(2608451991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1000328627/5000000000 : ℝ)|^4493 ≤ (6220978597003/50000000000000 : ℝ)^3469
        have hw : |(-1000328627/5000000000 : ℝ)|=(1000328627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s7_1 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1888928271/10000000000 : ℝ)*x 0 + (2609012043/5000000000 : ℝ)*x 1 + (2716963243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1888928271/10000000000 : ℝ)^4493 ≤ (11549533799497/100000000000000 : ℝ)^3469 := by
    have hnat : (1888928271 : ℕ)^4493*100000000000000^3469 ≤ 11549533799497^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888928271 10000000000 11549533799497 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609012043/5000000000 : ℝ)^4493 ≤ (43064345197203/100000000000000 : ℝ)^3469 := by
    have hnat : (2609012043 : ℕ)^4493*100000000000000^3469 ≤ 43064345197203^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609012043 5000000000 43064345197203 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716963243/5000000000 : ℝ)^4493 ≤ (9077224197579/20000000000000 : ℝ)^3469 := by
    have hnat : (2716963243 : ℕ)^4493*20000000000000^3469 ≤ 9077224197579^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716963243 5000000000 9077224197579 20000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1888928271/10000000000 : ℝ), (2609012043/5000000000 : ℝ), (2716963243/5000000000 : ℝ)] ![(11549533799497/100000000000000 : ℝ), (43064345197203/100000000000000 : ℝ), (9077224197579/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1888928271/10000000000 : ℝ)|^4493 ≤ (11549533799497/100000000000000 : ℝ)^3469
        have hw : |(-1888928271/10000000000 : ℝ)|=(1888928271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609012043/5000000000 : ℝ)|^4493 ≤ (43064345197203/100000000000000 : ℝ)^3469
        have hw : |(2609012043/5000000000 : ℝ)|=(2609012043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716963243/5000000000 : ℝ)|^4493 ≤ (9077224197579/20000000000000 : ℝ)^3469
        have hw : |(2716963243/5000000000 : ℝ)|=(2716963243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s7_2 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295212897/10000000000 : ℝ)*x 0 + (-445908731/2500000000 : ℝ)*x 1 + (5433927149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295212897/10000000000 : ℝ)^4493 ≤ (43891224523211/100000000000000 : ℝ)^3469 := by
    have hnat : (5295212897 : ℕ)^4493*100000000000000^3469 ≤ 43891224523211^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295212897 10000000000 43891224523211 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (445908731/2500000000 : ℝ)^4493 ≤ (2144529460769/20000000000000 : ℝ)^3469 := by
    have hnat : (445908731 : ℕ)^4493*20000000000000^3469 ≤ 2144529460769^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445908731 2500000000 2144529460769 20000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433927149/10000000000 : ℝ)^4493 ≤ (45386128160137/100000000000000 : ℝ)^3469 := by
    have hnat : (5433927149 : ℕ)^4493*100000000000000^3469 ≤ 45386128160137^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433927149 10000000000 45386128160137 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295212897/10000000000 : ℝ), (-445908731/2500000000 : ℝ), (5433927149/10000000000 : ℝ)] ![(43891224523211/100000000000000 : ℝ), (2144529460769/20000000000000 : ℝ), (45386128160137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295212897/10000000000 : ℝ)|^4493 ≤ (43891224523211/100000000000000 : ℝ)^3469
        have hw : |(5295212897/10000000000 : ℝ)|=(5295212897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-445908731/2500000000 : ℝ)|^4493 ≤ (2144529460769/20000000000000 : ℝ)^3469
        have hw : |(-445908731/2500000000 : ℝ)|=(445908731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433927149/10000000000 : ℝ)|^4493 ≤ (45386128160137/100000000000000 : ℝ)^3469
        have hw : |(5433927149/10000000000 : ℝ)|=(5433927149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s7_3 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105904261/200000000 : ℝ)*x 0 + (5433927097/10000000000 : ℝ)*x 1 + (-356726957/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105904261/200000000 : ℝ)^4493 ≤ (21945613082879/50000000000000 : ℝ)^3469 := by
    have hnat : (105904261 : ℕ)^4493*50000000000000^3469 ≤ 21945613082879^3469*200000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105904261 200000000 21945613082879 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433927097/10000000000 : ℝ)^4493 ≤ (5673265949701/12500000000000 : ℝ)^3469 := by
    have hnat : (5433927097 : ℕ)^4493*12500000000000^3469 ≤ 5673265949701^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433927097 10000000000 5673265949701 12500000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356726957/2000000000 : ℝ)^4493 ≤ (10722646221557/100000000000000 : ℝ)^3469 := by
    have hnat : (356726957 : ℕ)^4493*100000000000000^3469 ≤ 10722646221557^3469*2000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356726957 2000000000 10722646221557 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105904261/200000000 : ℝ), (5433927097/10000000000 : ℝ), (-356726957/2000000000 : ℝ)] ![(21945613082879/50000000000000 : ℝ), (5673265949701/12500000000000 : ℝ), (10722646221557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105904261/200000000 : ℝ)|^4493 ≤ (21945613082879/50000000000000 : ℝ)^3469
        have hw : |(105904261/200000000 : ℝ)|=(105904261/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433927097/10000000000 : ℝ)|^4493 ≤ (5673265949701/12500000000000 : ℝ)^3469
        have hw : |(5433927097/10000000000 : ℝ)|=(5433927097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-356726957/2000000000 : ℝ)|^4493 ≤ (10722646221557/100000000000000 : ℝ)^3469
        have hw : |(-356726957/2000000000 : ℝ)|=(356726957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s7_4 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (855280981/2000000000 : ℝ)*x 0 + (2262372563/5000000000 : ℝ)*x 1 + (4039994371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855280981/2000000000 : ℝ)^4493 ≤ (16639814500451/50000000000000 : ℝ)^3469 := by
    have hnat : (855280981 : ℕ)^4493*50000000000000^3469 ≤ 16639814500451^3469*2000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855280981 2000000000 16639814500451 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2262372563/5000000000 : ℝ)^4493 ≤ (35803901221443/100000000000000 : ℝ)^3469 := by
    have hnat : (2262372563 : ℕ)^4493*100000000000000^3469 ≤ 35803901221443^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262372563 5000000000 35803901221443 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4039994371/10000000000 : ℝ)^4493 ≤ (6183293952199/20000000000000 : ℝ)^3469 := by
    have hnat : (4039994371 : ℕ)^4493*20000000000000^3469 ≤ 6183293952199^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4039994371 10000000000 6183293952199 20000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(855280981/2000000000 : ℝ), (2262372563/5000000000 : ℝ), (4039994371/10000000000 : ℝ)] ![(16639814500451/50000000000000 : ℝ), (35803901221443/100000000000000 : ℝ), (6183293952199/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(855280981/2000000000 : ℝ)|^4493 ≤ (16639814500451/50000000000000 : ℝ)^3469
        have hw : |(855280981/2000000000 : ℝ)|=(855280981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2262372563/5000000000 : ℝ)|^4493 ≤ (35803901221443/100000000000000 : ℝ)^3469
        have hw : |(2262372563/5000000000 : ℝ)|=(2262372563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4039994371/10000000000 : ℝ)|^4493 ≤ (6183293952199/20000000000000 : ℝ)^3469
        have hw : |(4039994371/10000000000 : ℝ)|=(4039994371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1498_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10861/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10861/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15479/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10861/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10861/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10861/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10861/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10861/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10861/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (10861/100000 : ℝ) ^ (4491/1024 : ℝ) ≤ (1477452667088899/25000000000000000000 : ℝ) := by
    have hpowers : (10861/100000 : ℝ)^4491 ≤ (1477452667088899/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10861 : ℕ)^4491*25000000000000000000^1024 ≤ 1477452667088899^1024*100000^4491 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10861 100000 1477452667088899 25000000000000000000 4491 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10861/100000 : ℝ)) (X := (1477452667088899/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (387/2500 : ℝ) ^ (4491/1024 : ℝ) ≤ (13980229666913877/50000000000000000000 : ℝ) := by
    have hpowers : (387/2500 : ℝ)^4491 ≤ (13980229666913877/50000000000000000000 : ℝ)^1024 := by
      have hnat : (387 : ℕ)^4491*50000000000000000000^1024 ≤ 13980229666913877^1024*2500^4491 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        387 2500 13980229666913877 50000000000000000000 4491 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (387/2500 : ℝ)) (X := (13980229666913877/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501477452667088899/12500000000000000000 : ℝ) ≤ (400010779550299/400000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (12501477452667088899/12500000000000000000 : ℝ)^1024 ≤ (400010779550299/400000000000000 : ℝ)^4491 := by
      have hnat : (12501477452667088899 : ℕ)^1024*400000000000000^4491 ≤ 400010779550299^4491*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501477452667088899 12500000000000000000 400010779550299 400000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400010779550299/400000000000000 : ℝ)) (X := (12501477452667088899/12500000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000677405400043667/2000000000000000000 : ℝ) ≤ (10000772180427691/10000000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (2000677405400043667/2000000000000000000 : ℝ)^1024 ≤ (10000772180427691/10000000000000000 : ℝ)^4491 := by
      have hnat : (2000677405400043667 : ℕ)^1024*10000000000000000^4491 ≤ 10000772180427691^4491*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000677405400043667 2000000000000000000 10000772180427691 10000000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000772180427691/10000000000000000 : ℝ)) (X := (2000677405400043667/2000000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013980229666913877/25000000000000000000 : ℝ) ≤ (10001274872097907/10000000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (25013980229666913877/25000000000000000000 : ℝ)^1024 ≤ (10001274872097907/10000000000000000 : ℝ)^4491 := by
      have hnat : (25013980229666913877 : ℕ)^1024*10000000000000000^4491 ≤ 10001274872097907^4491*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013980229666913877 25000000000000000000 10001274872097907 10000000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001274872097907/10000000000000000 : ℝ)) (X := (25013980229666913877/25000000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1477452667088899/25000000000000000000 : ℝ) ≤ ((46180325300110345073/46190000000000000000 : ℝ)+2*(62836458777/57737500000000 : ℝ)*(10861/100000 : ℝ))^(4491/1024 : ℝ) := by
    rw [show (46180325300110345073/46190000000000000000 : ℝ)+2*(62836458777/57737500000000 : ℝ)*(10861/100000 : ℝ)=(400010779550299/400000000000000 : ℝ) by norm_num, show 1+2*(1477452667088899/25000000000000000000 : ℝ)=(12501477452667088899/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13980229666913877/50000000000000000000 : ℝ)+(1477452667088899/25000000000000000000 : ℝ) ≤ ((46180325300110345073/46190000000000000000 : ℝ)+(62836458777/57737500000000 : ℝ)*((387/2500 : ℝ)+(10861/100000 : ℝ)))^(4491/1024 : ℝ) := by
    rw [show (46180325300110345073/46190000000000000000 : ℝ)+(62836458777/57737500000000 : ℝ)*((387/2500 : ℝ)+(10861/100000 : ℝ))=(10000772180427691/10000000000000000 : ℝ) by norm_num, show 1+(13980229666913877/50000000000000000000 : ℝ)+(1477452667088899/25000000000000000000 : ℝ)=(2000677405400043667/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13980229666913877/50000000000000000000 : ℝ) ≤ ((46180325300110345073/46190000000000000000 : ℝ)+2*(62836458777/57737500000000 : ℝ)*(387/2500 : ℝ))^(4491/1024 : ℝ) := by
    rw [show (46180325300110345073/46190000000000000000 : ℝ)+2*(62836458777/57737500000000 : ℝ)*(387/2500 : ℝ)=(10001274872097907/10000000000000000 : ℝ) by norm_num, show 1+2*(13980229666913877/50000000000000000000 : ℝ)=(25013980229666913877/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46180325300110345073/46190000000000000000 : ℝ)*(X 1 0+X 2 0)+(62836458777/57737500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (10861/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (46180325300110345073/46190000000000000000 : ℝ)) (alpha := (62836458777/57737500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46180325300110345073/46190000000000000000 : ℝ)*(X 0 1+X 2 1)+(62836458777/57737500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (10861/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (46180325300110345073/46190000000000000000 : ℝ)) (alpha := (62836458777/57737500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46180325300110345073/46190000000000000000 : ℝ)*(X 0 2+X 1 2)+(62836458777/57737500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (10861/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (46180325300110345073/46190000000000000000 : ℝ)) (alpha := (62836458777/57737500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2676178253/5000000000 : ℝ)*X 2 0+(2608451991/5000000000 : ℝ)*X 2 1+(-1000328627/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s7_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1888928271/10000000000 : ℝ)*X 0 0+(2609012043/5000000000 : ℝ)*X 0 1+(2716963243/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s7_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295212897/10000000000 : ℝ)*X 1 0+(-445908731/2500000000 : ℝ)*X 1 1+(5433927149/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s7_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((105904261/200000000 : ℝ)*X 2 0+(5433927097/10000000000 : ℝ)*X 2 1+(-356726957/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s7_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((855280981/2000000000 : ℝ)*X 0 0+(2262372563/5000000000 : ℝ)*X 0 1+(4039994371/10000000000 : ℝ)*X 0 2+(855280981/2000000000 : ℝ)*X 1 0+(2262372563/5000000000 : ℝ)*X 1 1+(4039994371/10000000000 : ℝ)*X 1 2+(855280981/2000000000 : ℝ)*X 2 0+(2262372563/5000000000 : ℝ)*X 2 1+(4039994371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s7_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (490855294281340906000562073/115475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (320116401/100000000000000 : ℝ)*(base15) + (32866227/50000000000000 : ℝ)*(lower1) + (20022449/10000000000000 : ℝ)*(lower2) + (67401553/100000000000000 : ℝ)*(upper3) + (54057667/20000000000000 : ℝ)*(lower4) + (3933637/2500000000000 : ℝ)*(upper5) + (334731525215333/10000000000000 : ℝ)*(major0) + (334731525215333/10000000000000 : ℝ)*(major1) + (334731525215333/10000000000000 : ℝ)*(major2) + (1693774811/100000000000000 : ℝ)*(sp0) + (185268734588067/4000000000000 : ℝ)*(sp1) + (2315859022292637/50000000000000 : ℝ)*(sp2) + (4631716670926863/100000000000000 : ℝ)*(sp3) + (2062911997913327/100000000000000 : ℝ)*(sp4) + (2062911997913327/100000000000000 : ℝ)*(f.failure) + (185268734588067/4000000000000 : ℝ)*(f.sum) + (23046253493667/2309500000000000000000000000 : ℝ)*base66 + (1201517700854604309/461900000000000000000000000000000 : ℝ)*base67 + (2916456272536104309/461900000000000000000000000000000 : ℝ)*base69 + (2551377979181295691/461900000000000000000000000000000 : ℝ)*base72 + (13235659195619/2309500000000000000000000000 : ℝ)*base74 + (1270642010001704309/461900000000000000000000000000000 : ℝ)*base75 + (3912056279236504309/461900000000000000000000000000000 : ℝ)*base77 + (2714905307754904309/461900000000000000000000000000000 : ℝ)*base79 + (26026104125609/1154750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1242859/500000000000000000000 : ℝ)*base90 + (1242859/500000000000000000000 : ℝ)*base92 + (1242859/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1498_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10861/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10861/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1498_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1498_box_0 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-836370259/5000000000 : ℝ)*x 0 + (2702172987/5000000000 : ℝ)*x 1 + (5404346031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836370259/5000000000 : ℝ)^4493 ≤ (2466809575943/25000000000000 : ℝ)^3469 := by
    have hnat : (836370259 : ℕ)^4493*25000000000000^3469 ≤ 2466809575943^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836370259 5000000000 2466809575943 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702172987/5000000000 : ℝ)^4493 ≤ (704162195781/1562500000000 : ℝ)^3469 := by
    have hnat : (2702172987 : ℕ)^4493*1562500000000^3469 ≤ 704162195781^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702172987 5000000000 704162195781 1562500000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404346031/10000000000 : ℝ)^4493 ≤ (45066381145609/100000000000000 : ℝ)^3469 := by
    have hnat : (5404346031 : ℕ)^4493*100000000000000^3469 ≤ 45066381145609^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404346031 10000000000 45066381145609 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-836370259/5000000000 : ℝ), (2702172987/5000000000 : ℝ), (5404346031/10000000000 : ℝ)] ![(2466809575943/25000000000000 : ℝ), (704162195781/1562500000000 : ℝ), (45066381145609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-836370259/5000000000 : ℝ)|^4493 ≤ (2466809575943/25000000000000 : ℝ)^3469
        have hw : |(-836370259/5000000000 : ℝ)|=(836370259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702172987/5000000000 : ℝ)|^4493 ≤ (704162195781/1562500000000 : ℝ)^3469
        have hw : |(2702172987/5000000000 : ℝ)|=(2702172987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404346031/10000000000 : ℝ)|^4493 ≤ (45066381145609/100000000000000 : ℝ)^3469
        have hw : |(5404346031/10000000000 : ℝ)|=(5404346031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_box_1 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270572873/10000000000 : ℝ)*x 0 + (-23227431/125000000 : ℝ)*x 1 + (84442913/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270572873/10000000000 : ℝ)^4493 ≤ (8725376182389/20000000000000 : ℝ)^3469 := by
    have hnat : (5270572873 : ℕ)^4493*20000000000000^3469 ≤ 8725376182389^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270572873 10000000000 8725376182389 20000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23227431/125000000 : ℝ)^4493 ≤ (11306733598281/100000000000000 : ℝ)^3469 := by
    have hnat : (23227431 : ℕ)^4493*100000000000000^3469 ≤ 11306733598281^3469*125000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23227431 125000000 11306733598281 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84442913/156250000 : ℝ)^4493 ≤ (11266596369147/25000000000000 : ℝ)^3469 := by
    have hnat : (84442913 : ℕ)^4493*25000000000000^3469 ≤ 11266596369147^3469*156250000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84442913 156250000 11266596369147 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270572873/10000000000 : ℝ), (-23227431/125000000 : ℝ), (84442913/156250000 : ℝ)] ![(8725376182389/20000000000000 : ℝ), (11306733598281/100000000000000 : ℝ), (11266596369147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270572873/10000000000 : ℝ)|^4493 ≤ (8725376182389/20000000000000 : ℝ)^3469
        have hw : |(5270572873/10000000000 : ℝ)|=(5270572873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-23227431/125000000 : ℝ)|^4493 ≤ (11306733598281/100000000000000 : ℝ)^3469
        have hw : |(-23227431/125000000 : ℝ)|=(23227431/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84442913/156250000 : ℝ)|^4493 ≤ (11266596369147/25000000000000 : ℝ)^3469
        have hw : |(84442913/156250000 : ℝ)|=(84442913/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_box_2 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527057217/1000000000 : ℝ)*x 0 + (5404346611/10000000000 : ℝ)*x 1 + (-1858195191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527057217/1000000000 : ℝ)^4493 ≤ (43626873375201/100000000000000 : ℝ)^3469 := by
    have hnat : (527057217 : ℕ)^4493*100000000000000^3469 ≤ 43626873375201^3469*1000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527057217 1000000000 43626873375201 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404346611/10000000000 : ℝ)^4493 ≤ (11266596852467/25000000000000 : ℝ)^3469 := by
    have hnat : (5404346611 : ℕ)^4493*25000000000000^3469 ≤ 11266596852467^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404346611 10000000000 11266596852467 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1858195191/10000000000 : ℝ)^4493 ≤ (11306739201631/100000000000000 : ℝ)^3469 := by
    have hnat : (1858195191 : ℕ)^4493*100000000000000^3469 ≤ 11306739201631^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1858195191 10000000000 11306739201631 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527057217/1000000000 : ℝ), (5404346611/10000000000 : ℝ), (-1858195191/10000000000 : ℝ)] ![(43626873375201/100000000000000 : ℝ), (11266596852467/25000000000000 : ℝ), (11306739201631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527057217/1000000000 : ℝ)|^4493 ≤ (43626873375201/100000000000000 : ℝ)^3469
        have hw : |(527057217/1000000000 : ℝ)|=(527057217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404346611/10000000000 : ℝ)|^4493 ≤ (11266596852467/25000000000000 : ℝ)^3469
        have hw : |(5404346611/10000000000 : ℝ)|=(5404346611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1858195191/10000000000 : ℝ)|^4493 ≤ (11306739201631/100000000000000 : ℝ)^3469
        have hw : |(-1858195191/10000000000 : ℝ)|=(1858195191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_box_3 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4480047059/10000000000 : ℝ)*x 0 + (836311347/2000000000 : ℝ)*x 1 + (32668403/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4480047059/10000000000 : ℝ)^4493 ≤ (35346474064179/100000000000000 : ℝ)^3469 := by
    have hnat : (4480047059 : ℕ)^4493*100000000000000^3469 ≤ 35346474064179^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480047059 10000000000 35346474064179 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (836311347/2000000000 : ℝ)^4493 ≤ (6465353744923/20000000000000 : ℝ)^3469 := by
    have hnat : (836311347 : ℕ)^4493*20000000000000^3469 ≤ 6465353744923^3469*2000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836311347 2000000000 6465353744923 20000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32668403/78125000 : ℝ)^4493 ≤ (1616337859993/5000000000000 : ℝ)^3469 := by
    have hnat : (32668403 : ℕ)^4493*5000000000000^3469 ≤ 1616337859993^3469*78125000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32668403 78125000 1616337859993 5000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4480047059/10000000000 : ℝ), (836311347/2000000000 : ℝ), (32668403/78125000 : ℝ)] ![(35346474064179/100000000000000 : ℝ), (6465353744923/20000000000000 : ℝ), (1616337859993/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4480047059/10000000000 : ℝ)|^4493 ≤ (35346474064179/100000000000000 : ℝ)^3469
        have hw : |(4480047059/10000000000 : ℝ)|=(4480047059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(836311347/2000000000 : ℝ)|^4493 ≤ (6465353744923/20000000000000 : ℝ)^3469
        have hw : |(836311347/2000000000 : ℝ)|=(836311347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32668403/78125000 : ℝ)|^4493 ≤ (1616337859993/5000000000000 : ℝ)^3469
        have hw : |(32668403/78125000 : ℝ)|=(32668403/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_box_4 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-527627999/2500000000 : ℝ)*x 0 + (5243145141/10000000000 : ℝ)*x 1 + (655393141/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527627999/2500000000 : ℝ)^4493 ≤ (3333470558491/25000000000000 : ℝ)^3469 := by
    have hnat : (527627999 : ℕ)^4493*25000000000000^3469 ≤ 3333470558491^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527627999 2500000000 3333470558491 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243145141/10000000000 : ℝ)^4493 ≤ (5416632368733/12500000000000 : ℝ)^3469 := by
    have hnat : (5243145141 : ℕ)^4493*12500000000000^3469 ≤ 5416632368733^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243145141 10000000000 5416632368733 12500000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655393141/1250000000 : ℝ)^4493 ≤ (10833264702677/25000000000000 : ℝ)^3469 := by
    have hnat : (655393141 : ℕ)^4493*25000000000000^3469 ≤ 10833264702677^3469*1250000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655393141 1250000000 10833264702677 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-527627999/2500000000 : ℝ), (5243145141/10000000000 : ℝ), (655393141/1250000000 : ℝ)] ![(3333470558491/25000000000000 : ℝ), (5416632368733/12500000000000 : ℝ), (10833264702677/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-527627999/2500000000 : ℝ)|^4493 ≤ (3333470558491/25000000000000 : ℝ)^3469
        have hw : |(-527627999/2500000000 : ℝ)|=(527627999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243145141/10000000000 : ℝ)|^4493 ≤ (5416632368733/12500000000000 : ℝ)^3469
        have hw : |(5243145141/10000000000 : ℝ)|=(5243145141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655393141/1250000000 : ℝ)|^4493 ≤ (10833264702677/25000000000000 : ℝ)^3469
        have hw : |(655393141/1250000000 : ℝ)|=(655393141/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_box_5 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5382926597/10000000000 : ℝ)*x 0 + (-962234439/5000000000 : ℝ)*x 1 + (2621572517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382926597/10000000000 : ℝ)^4493 ≤ (5604397146923/12500000000000 : ℝ)^3469 := by
    have hnat : (5382926597 : ℕ)^4493*12500000000000^3469 ≤ 5604397146923^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382926597 10000000000 5604397146923 12500000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (962234439/5000000000 : ℝ)^4493 ≤ (11831765007673/100000000000000 : ℝ)^3469 := by
    have hnat : (962234439 : ℕ)^4493*100000000000000^3469 ≤ 11831765007673^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962234439 5000000000 11831765007673 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621572517/5000000000 : ℝ)^4493 ≤ (43333057804501/100000000000000 : ℝ)^3469 := by
    have hnat : (2621572517 : ℕ)^4493*100000000000000^3469 ≤ 43333057804501^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621572517 5000000000 43333057804501 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382926597/10000000000 : ℝ), (-962234439/5000000000 : ℝ), (2621572517/5000000000 : ℝ)] ![(5604397146923/12500000000000 : ℝ), (11831765007673/100000000000000 : ℝ), (43333057804501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382926597/10000000000 : ℝ)|^4493 ≤ (5604397146923/12500000000000 : ℝ)^3469
        have hw : |(5382926597/10000000000 : ℝ)|=(5382926597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-962234439/5000000000 : ℝ)|^4493 ≤ (11831765007673/100000000000000 : ℝ)^3469
        have hw : |(-962234439/5000000000 : ℝ)|=(962234439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621572517/5000000000 : ℝ)|^4493 ≤ (43333057804501/100000000000000 : ℝ)^3469
        have hw : |(2621572517/5000000000 : ℝ)|=(2621572517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_box_6 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5382926851/10000000000 : ℝ)*x 0 + (5243145179/10000000000 : ℝ)*x 1 + (-962234169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382926851/10000000000 : ℝ)^4493 ≤ (44835179915483/100000000000000 : ℝ)^3469 := by
    have hnat : (5382926851 : ℕ)^4493*100000000000000^3469 ≤ 44835179915483^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382926851 10000000000 44835179915483 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243145179/10000000000 : ℝ)^4493 ≤ (43333059356629/100000000000000 : ℝ)^3469 := by
    have hnat : (5243145179 : ℕ)^4493*100000000000000^3469 ≤ 43333059356629^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243145179 10000000000 43333059356629 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (962234169/5000000000 : ℝ)^4493 ≤ (92435630529/781250000000 : ℝ)^3469 := by
    have hnat : (962234169 : ℕ)^4493*781250000000^3469 ≤ 92435630529^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962234169 5000000000 92435630529 781250000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382926851/10000000000 : ℝ), (5243145179/10000000000 : ℝ), (-962234169/5000000000 : ℝ)] ![(44835179915483/100000000000000 : ℝ), (43333059356629/100000000000000 : ℝ), (92435630529/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382926851/10000000000 : ℝ)|^4493 ≤ (44835179915483/100000000000000 : ℝ)^3469
        have hw : |(5382926851/10000000000 : ℝ)|=(5382926851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243145179/10000000000 : ℝ)|^4493 ≤ (43333059356629/100000000000000 : ℝ)^3469
        have hw : |(5243145179/10000000000 : ℝ)|=(5243145179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-962234169/5000000000 : ℝ)|^4493 ≤ (92435630529/781250000000 : ℝ)^3469
        have hw : |(-962234169/5000000000 : ℝ)|=(962234169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_box_7 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (127196153/312500000 : ℝ)*x 0 + (4386304683/10000000000 : ℝ)*x 1 + (4386305513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127196153/312500000 : ℝ)^4493 ≤ (624338955459/2000000000000 : ℝ)^3469 := by
    have hnat : (127196153 : ℕ)^4493*2000000000000^3469 ≤ 624338955459^3469*312500000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127196153 312500000 624338955459 2000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4386304683/10000000000 : ℝ)^4493 ≤ (17195760948629/50000000000000 : ℝ)^3469 := by
    have hnat : (4386304683 : ℕ)^4493*50000000000000^3469 ≤ 17195760948629^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4386304683 10000000000 17195760948629 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4386305513/10000000000 : ℝ)^4493 ≤ (34391530326001/100000000000000 : ℝ)^3469 := by
    have hnat : (4386305513 : ℕ)^4493*100000000000000^3469 ≤ 34391530326001^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4386305513 10000000000 34391530326001 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(127196153/312500000 : ℝ), (4386304683/10000000000 : ℝ), (4386305513/10000000000 : ℝ)] ![(624338955459/2000000000000 : ℝ), (17195760948629/50000000000000 : ℝ), (34391530326001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(127196153/312500000 : ℝ)|^4493 ≤ (624338955459/2000000000000 : ℝ)^3469
        have hw : |(127196153/312500000 : ℝ)|=(127196153/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4386304683/10000000000 : ℝ)|^4493 ≤ (17195760948629/50000000000000 : ℝ)^3469
        have hw : |(4386304683/10000000000 : ℝ)|=(4386304683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4386305513/10000000000 : ℝ)|^4493 ≤ (34391530326001/100000000000000 : ℝ)^3469
        have hw : |(4386305513/10000000000 : ℝ)|=(4386305513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_box_8 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1009038611/5000000000 : ℝ)*x 0 + (160323993/312500000 : ℝ)*x 1 + (5424839737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1009038611/5000000000 : ℝ)^4493 ≤ (1572806169801/12500000000000 : ℝ)^3469 := by
    have hnat : (1009038611 : ℕ)^4493*12500000000000^3469 ≤ 1572806169801^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009038611 5000000000 1572806169801 12500000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160323993/312500000 : ℝ)^4493 ≤ (21064852275953/50000000000000 : ℝ)^3469 := by
    have hnat : (160323993 : ℕ)^4493*50000000000000^3469 ≤ 21064852275953^3469*312500000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160323993 312500000 21064852275953 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424839737/10000000000 : ℝ)^4493 ≤ (4528784606417/10000000000000 : ℝ)^3469 := by
    have hnat : (5424839737 : ℕ)^4493*10000000000000^3469 ≤ 4528784606417^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424839737 10000000000 4528784606417 10000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1009038611/5000000000 : ℝ), (160323993/312500000 : ℝ), (5424839737/10000000000 : ℝ)] ![(1572806169801/12500000000000 : ℝ), (21064852275953/50000000000000 : ℝ), (4528784606417/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1009038611/5000000000 : ℝ)|^4493 ≤ (1572806169801/12500000000000 : ℝ)^3469
        have hw : |(-1009038611/5000000000 : ℝ)|=(1009038611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160323993/312500000 : ℝ)|^4493 ≤ (21064852275953/50000000000000 : ℝ)^3469
        have hw : |(160323993/312500000 : ℝ)|=(160323993/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424839737/10000000000 : ℝ)|^4493 ≤ (4528784606417/10000000000000 : ℝ)^3469
        have hw : |(5424839737/10000000000 : ℝ)|=(5424839737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_box_9 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051256471/2000000000 : ℝ)*x 0 + (-184951983/1000000000 : ℝ)*x 1 + (135620997/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051256471/2000000000 : ℝ)^4493 ≤ (43473736029017/100000000000000 : ℝ)^3469 := by
    have hnat : (1051256471 : ℕ)^4493*100000000000000^3469 ≤ 43473736029017^3469*2000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051256471 2000000000 43473736029017 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (184951983/1000000000 : ℝ)^4493 ≤ (5619208171647/50000000000000 : ℝ)^3469 := by
    have hnat : (184951983 : ℕ)^4493*50000000000000^3469 ≤ 5619208171647^3469*1000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184951983 1000000000 5619208171647 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135620997/250000000 : ℝ)^4493 ≤ (1132196190259/2500000000000 : ℝ)^3469 := by
    have hnat : (135620997 : ℕ)^4493*2500000000000^3469 ≤ 1132196190259^3469*250000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135620997 250000000 1132196190259 2500000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051256471/2000000000 : ℝ), (-184951983/1000000000 : ℝ), (135620997/250000000 : ℝ)] ![(43473736029017/100000000000000 : ℝ), (5619208171647/50000000000000 : ℝ), (1132196190259/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051256471/2000000000 : ℝ)|^4493 ≤ (43473736029017/100000000000000 : ℝ)^3469
        have hw : |(1051256471/2000000000 : ℝ)|=(1051256471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-184951983/1000000000 : ℝ)|^4493 ≤ (5619208171647/50000000000000 : ℝ)^3469
        have hw : |(-184951983/1000000000 : ℝ)|=(184951983/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135620997/250000000 : ℝ)|^4493 ≤ (1132196190259/2500000000000 : ℝ)^3469
        have hw : |(135620997/250000000 : ℝ)|=(135620997/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_box_10 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256282581/10000000000 : ℝ)*x 0 + (1356209919/2500000000 : ℝ)*x 1 + (-1849519803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256282581/10000000000 : ℝ)^4493 ≤ (679277163281/1562500000000 : ℝ)^3469 := by
    have hnat : (5256282581 : ℕ)^4493*1562500000000^3469 ≤ 679277163281^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256282581 10000000000 679277163281 1562500000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356209919/2500000000 : ℝ)^4493 ≤ (45287845404607/100000000000000 : ℝ)^3469 := by
    have hnat : (1356209919 : ℕ)^4493*100000000000000^3469 ≤ 45287845404607^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356209919 2500000000 45287845404607 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1849519803/10000000000 : ℝ)^4493 ≤ (5619208065401/50000000000000 : ℝ)^3469 := by
    have hnat : (1849519803 : ℕ)^4493*50000000000000^3469 ≤ 5619208065401^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1849519803 10000000000 5619208065401 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256282581/10000000000 : ℝ), (1356209919/2500000000 : ℝ), (-1849519803/10000000000 : ℝ)] ![(679277163281/1562500000000 : ℝ), (45287845404607/100000000000000 : ℝ), (5619208065401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256282581/10000000000 : ℝ)|^4493 ≤ (679277163281/1562500000000 : ℝ)^3469
        have hw : |(5256282581/10000000000 : ℝ)|=(5256282581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356209919/2500000000 : ℝ)|^4493 ≤ (45287845404607/100000000000000 : ℝ)^3469
        have hw : |(1356209919/2500000000 : ℝ)|=(1356209919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1849519803/10000000000 : ℝ)|^4493 ≤ (5619208065401/50000000000000 : ℝ)^3469
        have hw : |(-1849519803/10000000000 : ℝ)|=(1849519803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_box_11 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4530989407/10000000000 : ℝ)*x 0 + (4155493643/10000000000 : ℝ)*x 1 + (4155493829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4530989407/10000000000 : ℝ)^4493 ≤ (7173581990197/20000000000000 : ℝ)^3469 := by
    have hnat : (4530989407 : ℕ)^4493*20000000000000^3469 ≤ 7173581990197^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530989407 10000000000 7173581990197 20000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4155493643/10000000000 : ℝ)^4493 ≤ (1282641763591/4000000000000 : ℝ)^3469 := by
    have hnat : (4155493643 : ℕ)^4493*4000000000000^3469 ≤ 1282641763591^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155493643 10000000000 1282641763591 4000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4155493829/10000000000 : ℝ)^4493 ≤ (1282641837949/4000000000000 : ℝ)^3469 := by
    have hnat : (4155493829 : ℕ)^4493*4000000000000^3469 ≤ 1282641837949^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155493829 10000000000 1282641837949 4000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4530989407/10000000000 : ℝ), (4155493643/10000000000 : ℝ), (4155493829/10000000000 : ℝ)] ![(7173581990197/20000000000000 : ℝ), (1282641763591/4000000000000 : ℝ), (1282641837949/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4530989407/10000000000 : ℝ)|^4493 ≤ (7173581990197/20000000000000 : ℝ)^3469
        have hw : |(4530989407/10000000000 : ℝ)|=(4530989407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4155493643/10000000000 : ℝ)|^4493 ≤ (1282641763591/4000000000000 : ℝ)^3469
        have hw : |(4155493643/10000000000 : ℝ)|=(4155493643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4155493829/10000000000 : ℝ)|^4493 ≤ (1282641837949/4000000000000 : ℝ)^3469
        have hw : |(4155493829/10000000000 : ℝ)|=(4155493829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_box_12 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-882601101/5000000000 : ℝ)*x 0 + (5513448899/10000000000 : ℝ)*x 1 + (5228131857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (882601101/5000000000 : ℝ)^4493 ≤ (330604531977/3125000000000 : ℝ)^3469 := by
    have hnat : (882601101 : ℕ)^4493*3125000000000^3469 ≤ 330604531977^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882601101 5000000000 330604531977 3125000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5513448899/10000000000 : ℝ)^4493 ≤ (46248235222347/100000000000000 : ℝ)^3469 := by
    have hnat : (5513448899 : ℕ)^4493*100000000000000^3469 ≤ 46248235222347^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513448899 10000000000 46248235222347 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228131857/10000000000 : ℝ)^4493 ≤ (5396552466421/12500000000000 : ℝ)^3469 := by
    have hnat : (5228131857 : ℕ)^4493*12500000000000^3469 ≤ 5396552466421^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228131857 10000000000 5396552466421 12500000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-882601101/5000000000 : ℝ), (5513448899/10000000000 : ℝ), (5228131857/10000000000 : ℝ)] ![(330604531977/3125000000000 : ℝ), (46248235222347/100000000000000 : ℝ), (5396552466421/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-882601101/5000000000 : ℝ)|^4493 ≤ (330604531977/3125000000000 : ℝ)^3469
        have hw : |(-882601101/5000000000 : ℝ)|=(882601101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5513448899/10000000000 : ℝ)|^4493 ≤ (46248235222347/100000000000000 : ℝ)^3469
        have hw : |(5513448899/10000000000 : ℝ)|=(5513448899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228131857/10000000000 : ℝ)|^4493 ≤ (5396552466421/12500000000000 : ℝ)^3469
        have hw : |(5228131857/10000000000 : ℝ)|=(5228131857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_box_13 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696695161/5000000000 : ℝ)*x 0 + (-482615253/2500000000 : ℝ)*x 1 + (5228130791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696695161/5000000000 : ℝ)^4493 ≤ (44948090031743/100000000000000 : ℝ)^3469 := by
    have hnat : (2696695161 : ℕ)^4493*100000000000000^3469 ≤ 44948090031743^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696695161 5000000000 44948090031743 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (482615253/2500000000 : ℝ)^4493 ≤ (237590032561/2000000000000 : ℝ)^3469 := by
    have hnat : (482615253 : ℕ)^4493*2000000000000^3469 ≤ 237590032561^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482615253 2500000000 237590032561 2000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228130791/10000000000 : ℝ)^4493 ≤ (10793102082551/25000000000000 : ℝ)^3469 := by
    have hnat : (5228130791 : ℕ)^4493*25000000000000^3469 ≤ 10793102082551^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228130791 10000000000 10793102082551 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696695161/5000000000 : ℝ), (-482615253/2500000000 : ℝ), (5228130791/10000000000 : ℝ)] ![(44948090031743/100000000000000 : ℝ), (237590032561/2000000000000 : ℝ), (10793102082551/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696695161/5000000000 : ℝ)|^4493 ≤ (44948090031743/100000000000000 : ℝ)^3469
        have hw : |(2696695161/5000000000 : ℝ)|=(2696695161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-482615253/2500000000 : ℝ)|^4493 ≤ (237590032561/2000000000000 : ℝ)^3469
        have hw : |(-482615253/2500000000 : ℝ)|=(482615253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228130791/10000000000 : ℝ)|^4493 ≤ (10793102082551/25000000000000 : ℝ)^3469
        have hw : |(5228130791/10000000000 : ℝ)|=(5228130791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_box_14 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168543429/312500000 : ℝ)*x 0 + (1307032949/2500000000 : ℝ)*x 1 + (-482615117/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168543429/312500000 : ℝ)^4493 ≤ (44948083620121/100000000000000 : ℝ)^3469 := by
    have hnat : (168543429 : ℕ)^4493*100000000000000^3469 ≤ 44948083620121^3469*312500000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168543429 312500000 44948083620121 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1307032949/2500000000 : ℝ)^4493 ≤ (10793104769739/25000000000000 : ℝ)^3469 := by
    have hnat : (1307032949 : ℕ)^4493*25000000000000^3469 ≤ 10793104769739^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307032949 2500000000 10793104769739 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (482615117/2500000000 : ℝ)^4493 ≤ (593974864613/5000000000000 : ℝ)^3469 := by
    have hnat : (482615117 : ℕ)^4493*5000000000000^3469 ≤ 593974864613^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482615117 2500000000 593974864613 5000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168543429/312500000 : ℝ), (1307032949/2500000000 : ℝ), (-482615117/2500000000 : ℝ)] ![(44948083620121/100000000000000 : ℝ), (10793104769739/25000000000000 : ℝ), (593974864613/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168543429/312500000 : ℝ)|^4493 ≤ (44948083620121/100000000000000 : ℝ)^3469
        have hw : |(168543429/312500000 : ℝ)|=(168543429/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1307032949/2500000000 : ℝ)|^4493 ≤ (10793104769739/25000000000000 : ℝ)^3469
        have hw : |(1307032949/2500000000 : ℝ)|=(1307032949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-482615117/2500000000 : ℝ)|^4493 ≤ (593974864613/5000000000000 : ℝ)^3469
        have hw : |(-482615117/2500000000 : ℝ)|=(482615117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_box_15 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4031252673/10000000000 : ℝ)*x 0 + (881070601/2000000000 : ℝ)*x 1 + (2202675473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4031252673/10000000000 : ℝ)^4493 ≤ (30829853732619/100000000000000 : ℝ)^3469 := by
    have hnat : (4031252673 : ℕ)^4493*100000000000000^3469 ≤ 30829853732619^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031252673 10000000000 30829853732619 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (881070601/2000000000 : ℝ)^4493 ≤ (34585083598309/100000000000000 : ℝ)^3469 := by
    have hnat : (881070601 : ℕ)^4493*100000000000000^3469 ≤ 34585083598309^3469*2000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881070601 2000000000 34585083598309 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2202675473/5000000000 : ℝ)^4493 ≤ (8646265665543/25000000000000 : ℝ)^3469 := by
    have hnat : (2202675473 : ℕ)^4493*25000000000000^3469 ≤ 8646265665543^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202675473 5000000000 8646265665543 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4031252673/10000000000 : ℝ), (881070601/2000000000 : ℝ), (2202675473/5000000000 : ℝ)] ![(30829853732619/100000000000000 : ℝ), (34585083598309/100000000000000 : ℝ), (8646265665543/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4031252673/10000000000 : ℝ)|^4493 ≤ (30829853732619/100000000000000 : ℝ)^3469
        have hw : |(4031252673/10000000000 : ℝ)|=(4031252673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(881070601/2000000000 : ℝ)|^4493 ≤ (34585083598309/100000000000000 : ℝ)^3469
        have hw : |(881070601/2000000000 : ℝ)|=(881070601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2202675473/5000000000 : ℝ)|^4493 ≤ (8646265665543/25000000000000 : ℝ)^3469
        have hw : |(2202675473/5000000000 : ℝ)|=(2202675473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1498_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10861/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31861/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29281/50000 : ℝ) ∧ (80167/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (85911/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10861/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10861/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10861/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10861/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10861/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10861/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10861/100000 : ℝ) ^ (4491/1024 : ℝ) ≤ (1477452667088899/25000000000000000000 : ℝ) := by
    have hpowers : (10861/100000 : ℝ)^4491 ≤ (1477452667088899/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10861 : ℕ)^4491*25000000000000000000^1024 ≤ 1477452667088899^1024*100000^4491 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10861 100000 1477452667088899 25000000000000000000 4491 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10861/100000 : ℝ)) (X := (1477452667088899/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15479/100000 : ℝ) ^ (4491/1024 : ℝ) ≤ (27952538535609773/100000000000000000000 : ℝ) := by
    have hpowers : (15479/100000 : ℝ)^4491 ≤ (27952538535609773/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15479 : ℕ)^4491*100000000000000000000^1024 ≤ 27952538535609773^1024*100000^4491 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15479 100000 27952538535609773 100000000000000000000 4491 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15479/100000 : ℝ)) (X := (27952538535609773/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501477452667088899/12500000000000000000 : ℝ) ≤ (400010779550299/400000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (12501477452667088899/12500000000000000000 : ℝ)^1024 ≤ (400010779550299/400000000000000 : ℝ)^4491 := by
      have hnat : (12501477452667088899 : ℕ)^1024*400000000000000^4491 ≤ 400010779550299^4491*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501477452667088899 12500000000000000000 400010779550299 400000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400010779550299/400000000000000 : ℝ)) (X := (12501477452667088899/12500000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100033862349203965369/100000000000000000000 : ℝ) ≤ (2500192999967881/2500000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (100033862349203965369/100000000000000000000 : ℝ)^1024 ≤ (2500192999967881/2500000000000000 : ℝ)^4491 := by
      have hnat : (100033862349203965369 : ℕ)^1024*2500000000000000^4491 ≤ 2500192999967881^4491*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100033862349203965369 100000000000000000000 2500192999967881 2500000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500192999967881/2500000000000000 : ℝ)) (X := (100033862349203965369/100000000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027952538535609773/50000000000000000000 : ℝ) ≤ (10001274510985573/10000000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (50027952538535609773/50000000000000000000 : ℝ)^1024 ≤ (10001274510985573/10000000000000000 : ℝ)^4491 := by
      have hnat : (50027952538535609773 : ℕ)^1024*10000000000000000^4491 ≤ 10001274510985573^4491*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027952538535609773 50000000000000000000 10001274510985573 10000000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001274510985573/10000000000000000 : ℝ)) (X := (50027952538535609773/50000000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1477452667088899/25000000000000000000 : ℝ) ≤ ((11542582238165661793/11545000000000000000 : ℝ)+2*(502511114049/461800000000000 : ℝ)*(10861/100000 : ℝ))^(4491/1024 : ℝ) := by
    rw [show (11542582238165661793/11545000000000000000 : ℝ)+2*(502511114049/461800000000000 : ℝ)*(10861/100000 : ℝ)=(400010779550299/400000000000000 : ℝ) by norm_num, show 1+2*(1477452667088899/25000000000000000000 : ℝ)=(12501477452667088899/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27952538535609773/100000000000000000000 : ℝ)+(1477452667088899/25000000000000000000 : ℝ) ≤ ((11542582238165661793/11545000000000000000 : ℝ)+(502511114049/461800000000000 : ℝ)*((15479/100000 : ℝ)+(10861/100000 : ℝ)))^(4491/1024 : ℝ) := by
    rw [show (11542582238165661793/11545000000000000000 : ℝ)+(502511114049/461800000000000 : ℝ)*((15479/100000 : ℝ)+(10861/100000 : ℝ))=(2500192999967881/2500000000000000 : ℝ) by norm_num, show 1+(27952538535609773/100000000000000000000 : ℝ)+(1477452667088899/25000000000000000000 : ℝ)=(100033862349203965369/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27952538535609773/100000000000000000000 : ℝ) ≤ ((11542582238165661793/11545000000000000000 : ℝ)+2*(502511114049/461800000000000 : ℝ)*(15479/100000 : ℝ))^(4491/1024 : ℝ) := by
    rw [show (11542582238165661793/11545000000000000000 : ℝ)+2*(502511114049/461800000000000 : ℝ)*(15479/100000 : ℝ)=(10001274510985573/10000000000000000 : ℝ) by norm_num, show 1+2*(27952538535609773/100000000000000000000 : ℝ)=(50027952538535609773/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11542582238165661793/11545000000000000000 : ℝ)*(X 1 0+X 2 0)+(502511114049/461800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (10861/100000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (11542582238165661793/11545000000000000000 : ℝ)) (alpha := (502511114049/461800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11542582238165661793/11545000000000000000 : ℝ)*(X 0 1+X 2 1)+(502511114049/461800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (10861/100000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (11542582238165661793/11545000000000000000 : ℝ)) (alpha := (502511114049/461800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11542582238165661793/11545000000000000000 : ℝ)*(X 0 2+X 1 2)+(502511114049/461800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (10861/100000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (11542582238165661793/11545000000000000000 : ℝ)) (alpha := (502511114049/461800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-836370259/5000000000 : ℝ)*X 0 0+(2702172987/5000000000 : ℝ)*X 0 1+(5404346031/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5270572873/10000000000 : ℝ)*X 1 0+(-23227431/125000000 : ℝ)*X 1 1+(84442913/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((527057217/1000000000 : ℝ)*X 2 0+(5404346611/10000000000 : ℝ)*X 2 1+(-1858195191/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4480047059/10000000000 : ℝ)*X 0 0+(836311347/2000000000 : ℝ)*X 0 1+(32668403/78125000 : ℝ)*X 0 2+(4480047059/10000000000 : ℝ)*X 1 0+(836311347/2000000000 : ℝ)*X 1 1+(32668403/78125000 : ℝ)*X 1 2+(4480047059/10000000000 : ℝ)*X 2 0+(836311347/2000000000 : ℝ)*X 2 1+(32668403/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-527627999/2500000000 : ℝ)*X 0 0+(5243145141/10000000000 : ℝ)*X 0 1+(655393141/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5382926597/10000000000 : ℝ)*X 1 0+(-962234439/5000000000 : ℝ)*X 1 1+(2621572517/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5382926851/10000000000 : ℝ)*X 2 0+(5243145179/10000000000 : ℝ)*X 2 1+(-962234169/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((127196153/312500000 : ℝ)*X 0 0+(4386304683/10000000000 : ℝ)*X 0 1+(4386305513/10000000000 : ℝ)*X 0 2+(127196153/312500000 : ℝ)*X 1 0+(4386304683/10000000000 : ℝ)*X 1 1+(4386305513/10000000000 : ℝ)*X 1 2+(127196153/312500000 : ℝ)*X 2 0+(4386304683/10000000000 : ℝ)*X 2 1+(4386305513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1009038611/5000000000 : ℝ)*X 0 0+(160323993/312500000 : ℝ)*X 0 1+(5424839737/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1051256471/2000000000 : ℝ)*X 1 0+(-184951983/1000000000 : ℝ)*X 1 1+(135620997/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5256282581/10000000000 : ℝ)*X 2 0+(1356209919/2500000000 : ℝ)*X 2 1+(-1849519803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4530989407/10000000000 : ℝ)*X 0 0+(4155493643/10000000000 : ℝ)*X 0 1+(4155493829/10000000000 : ℝ)*X 0 2+(4530989407/10000000000 : ℝ)*X 1 0+(4155493643/10000000000 : ℝ)*X 1 1+(4155493829/10000000000 : ℝ)*X 1 2+(4530989407/10000000000 : ℝ)*X 2 0+(4155493643/10000000000 : ℝ)*X 2 1+(4155493829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-882601101/5000000000 : ℝ)*X 0 0+(5513448899/10000000000 : ℝ)*X 0 1+(5228131857/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2696695161/5000000000 : ℝ)*X 1 0+(-482615253/2500000000 : ℝ)*X 1 1+(5228130791/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((168543429/312500000 : ℝ)*X 2 0+(1307032949/2500000000 : ℝ)*X 2 1+(-482615117/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4031252673/10000000000 : ℝ)*X 0 0+(881070601/2000000000 : ℝ)*X 0 1+(2202675473/5000000000 : ℝ)*X 0 2+(4031252673/10000000000 : ℝ)*X 1 0+(881070601/2000000000 : ℝ)*X 1 1+(2202675473/5000000000 : ℝ)*X 1 2+(4031252673/10000000000 : ℝ)*X 2 0+(881070601/2000000000 : ℝ)*X 2 1+(2202675473/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31861/50000 : ℝ) ≤ (-18390982400195553180728392757931/28862500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16523069/100000000000000 : ℝ)*(upper0) + (134872623/100000000000000 : ℝ)*(lower1) + (30954383/20000000000000 : ℝ)*(lower2) + (26754739/50000000000000 : ℝ)*(lower3) + (7046443/25000000000000 : ℝ)*(upper5) + (110134683047611/5000000000000 : ℝ)*(major0) + (110134683047611/5000000000000 : ℝ)*(major1) + (110134683047611/5000000000000 : ℝ)*(major2) + (6836974663/100000000000000 : ℝ)*(sp1) + (61382644968863/2000000000000 : ℝ)*(sp4) + (1534562705734243/50000000000000 : ℝ)*(sp5) + (61382644968863/2000000000000 : ℝ)*(sp6) + (678742864772659/50000000000000 : ℝ)*(sp7) + (4554966613/50000000000000 : ℝ)*(sp15) + (84843427467409/6250000000000 : ℝ)*(f.failure) + (61382644968863/2000000000000 : ℝ)*(f.sum) + (3181984273389/577250000000000000000000000 : ℝ)*base66 + (373803968695548477/57725000000000000000000000000000 : ℝ)*base68 + (461790760563148477/57725000000000000000000000000000 : ℝ)*base70 + (72680290396026523/57725000000000000000000000000000 : ℝ)*base71 + (7679403222347/1154500000000000000000000000 : ℝ)*base73 + (278856909395351523/57725000000000000000000000000000 : ℝ)*base75 + (548970723755998477/57725000000000000000000000000000 : ℝ)*base78 + (110626440378048477/57725000000000000000000000000000 : ℝ)*base80 + (551510763887/144312500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (261947/31250000000000000000 : ℝ)*base89 + (261947/31250000000000000000 : ℝ)*base91 + (261947/31250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29281/50000 : ℝ) ≤ (84515811713529050675987551675701/144312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11341303/5000000000000 : ℝ)*(lower0) + (30746807/100000000000000 : ℝ)*(upper1) + (287569879/100000000000000 : ℝ)*(upper2) + (59728699/100000000000000 : ℝ)*(upper3) + (27282399/100000000000000 : ℝ)*(lower5) + (569496440884673/25000000000000 : ℝ)*(major0) + (569496440884673/25000000000000 : ℝ)*(major1) + (569496440884673/25000000000000 : ℝ)*(major2) + (1566276773678783/50000000000000 : ℝ)*(sp0) + (1566273776387621/50000000000000 : ℝ)*(sp1) + (1566276773678783/50000000000000 : ℝ)*(sp2) + (350973479850717/25000000000000 : ℝ)*(sp3) + (1498645581/25000000000000 : ℝ)*(sp5) + (2579337927/100000000000000 : ℝ)*(sp11) + (280779299748159/20000000000000 : ℝ)*(f.failure) + (1566276773678783/50000000000000 : ℝ)*(f.sum) + (2213655996631/11545000000000000000000000000 : ℝ)*base66 + (3176953879218301311/288625000000000000000000000000000 : ℝ)*base68 + (1203807920261301311/288625000000000000000000000000000 : ℝ)*base70 + (1310165728822051311/288625000000000000000000000000000 : ℝ)*base72 + (146539918744951/11545000000000000000000000000 : ℝ)*base74 + (1618127668677051311/288625000000000000000000000000000 : ℝ)*base76 + (814208843638801311/288625000000000000000000000000000 : ℝ)*base78 + (3080775238278051311/288625000000000000000000000000000 : ℝ)*base80 + (44221950784551/11545000000000000000000000000 : ℝ)*base82 + (1064197/100000000000000000000 : ℝ)*base89 + (1064197/100000000000000000000 : ℝ)*base91 + (1064197/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80167/100000 : ℝ) ≤ (18511248164735408643281404221/23090000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13939797/100000000000000 : ℝ)*(upper0) + (10922879/50000000000000 : ℝ)*(lower1) + (24196871/100000000000000 : ℝ)*(lower3) + (9936369/25000000000000 : ℝ)*(upper4) + (2473516818584953/100000000000000 : ℝ)*(major0) + (2473516818584953/100000000000000 : ℝ)*(major1) + (2473516818584953/100000000000000 : ℝ)*(major2) + (524689383/50000000000000 : ℝ)*(sp0) + (6473190147/25000000000000 : ℝ)*(sp1) + (5369101089/50000000000000 : ℝ)*(sp3) + (424488652014151/12500000000000 : ℝ)*(sp8) + (1697942186365693/50000000000000 : ℝ)*(sp9) + (1697955132745987/50000000000000 : ℝ)*(sp10) + (1524389307122733/100000000000000 : ℝ)*(sp11) + (1524400045324911/100000000000000 : ℝ)*(f.failure) + (1697955132745987/50000000000000 : ℝ)*(f.sum) + (1087273220513/23090000000000000000000000000 : ℝ)*base66 + (10297059205380274271/1154500000000000000000000000000000 : ℝ)*base68 + (5250624609074725729/1154500000000000000000000000000000 : ℝ)*base69 + (80535163262725729/1154500000000000000000000000000000 : ℝ)*base71 + (85654429650087/23090000000000000000000000000 : ℝ)*base73 + (12288275765468274271/1154500000000000000000000000000000 : ℝ)*base76 + (1525182325332725729/1154500000000000000000000000000000 : ℝ)*base77 + (1858110918374274271/1154500000000000000000000000000000 : ℝ)*base80 + (12641985290133/23090000000000000000000000000 : ℝ)*base82 + (89387/500000000000000000000 : ℝ)*base90 + (89387/500000000000000000000 : ℝ)*base92 + (89387/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-85911/100000 : ℝ) ≤ (-247954336822294427598363474732543/288625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38921923/20000000000000 : ℝ)*(lower0) + (22523253/20000000000000 : ℝ)*(upper1) + (6567713/12500000000000 : ℝ)*(lower2) + (4524653/4000000000000 : ℝ)*(upper3) + (142910033/100000000000000 : ℝ)*(upper5) + (1256123199985917/50000000000000 : ℝ)*(major0) + (1256123199985917/50000000000000 : ℝ)*(major1) + (1256123199985917/50000000000000 : ℝ)*(major2) + (249175521823/100000000000000 : ℝ)*(sp5) + (862345741/20000000000000 : ℝ)*(sp7) + (1752430215870233/50000000000000 : ℝ)*(sp12) + (876152814054661/25000000000000 : ℝ)*(sp13) + (1752430215870233/50000000000000 : ℝ)*(sp14) + (154826433039651/10000000000000 : ℝ)*(sp15) + (48383395066413/3125000000000 : ℝ)*(f.failure) + (1752430215870233/50000000000000 : ℝ)*(f.sum) + (25405306514077/11545000000000000000000000000 : ℝ)*base66 + (272566841110544181/577250000000000000000000000000000 : ℝ)*base67 + (9248810409162544181/577250000000000000000000000000000 : ℝ)*base69 + (2601095238044181/577250000000000000000000000000000 : ℝ)*base71 + (35895787772499/5772500000000000000000000000 : ℝ)*base73 + (1889297047441455819/577250000000000000000000000000000 : ℝ)*base76 + (2750228231577794181/577250000000000000000000000000000 : ℝ)*base77 + (300648182543955819/577250000000000000000000000000000 : ℝ)*base80 + (4698912390721/1443125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (118779/15625000000000000000 : ℝ)*base89 + (118779/15625000000000000000 : ℝ)*base91 + (118779/15625000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1498_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10861/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31861/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29281/50000 : ℝ) else (80167/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85911/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1498_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1498_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (543/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31861/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29281/50000 : ℝ) else (80167/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85911/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1498_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1498_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1498_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (543/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31861/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29281/50000 : ℝ) else (80167/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85911/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1498_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

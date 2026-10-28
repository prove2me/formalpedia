-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1199_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:02:20.700263+00:00
-- url     : https://prove2.me/submissions/683b2a78-ea57-4292-9339-5ab892c5645c

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
theorem support_rectangle_w1199_s3_0 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2136698419/10000000000 : ℝ)*x 0 + (5423569597/10000000000 : ℝ)*x 1 + (5237151201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136698419/10000000000 : ℝ)^1049 ≤ (12982782356329/100000000000000 : ℝ)^793 := by
    have hnat : (2136698419 : ℕ)^1049*100000000000000^793 ≤ 12982782356329^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136698419 10000000000 12982782356329 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423569597/10000000000 : ℝ)^1049 ≤ (4451495290831/10000000000000 : ℝ)^793 := by
    have hnat : (5423569597 : ℕ)^1049*10000000000000^793 ≤ 4451495290831^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423569597 10000000000 4451495290831 10000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5237151201/10000000000 : ℝ)^1049 ≤ (42502264722383/100000000000000 : ℝ)^793 := by
    have hnat : (5237151201 : ℕ)^1049*100000000000000^793 ≤ 42502264722383^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237151201 10000000000 42502264722383 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2136698419/10000000000 : ℝ), (5423569597/10000000000 : ℝ), (5237151201/10000000000 : ℝ)] ![(12982782356329/100000000000000 : ℝ), (4451495290831/10000000000000 : ℝ), (42502264722383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2136698419/10000000000 : ℝ)|^1049 ≤ (12982782356329/100000000000000 : ℝ)^793
        have hw : |(-2136698419/10000000000 : ℝ)|=(2136698419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423569597/10000000000 : ℝ)|^1049 ≤ (4451495290831/10000000000000 : ℝ)^793
        have hw : |(5423569597/10000000000 : ℝ)|=(5423569597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5237151201/10000000000 : ℝ)|^1049 ≤ (42502264722383/100000000000000 : ℝ)^793
        have hw : |(5237151201/10000000000 : ℝ)|=(5237151201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s3_1 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2676228847/5000000000 : ℝ)*x 0 + (-2231875779/10000000000 : ℝ)*x 1 + (5237151393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676228847/5000000000 : ℝ)^1049 ≤ (21872253232483/50000000000000 : ℝ)^793 := by
    have hnat : (2676228847 : ℕ)^1049*50000000000000^793 ≤ 21872253232483^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676228847 5000000000 21872253232483 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2231875779/10000000000 : ℝ)^1049 ≤ (3438306684067/25000000000000 : ℝ)^793 := by
    have hnat : (2231875779 : ℕ)^1049*25000000000000^793 ≤ 3438306684067^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231875779 10000000000 3438306684067 25000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5237151393/10000000000 : ℝ)^1049 ≤ (8500453356717/20000000000000 : ℝ)^793 := by
    have hnat : (5237151393 : ℕ)^1049*20000000000000^793 ≤ 8500453356717^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237151393 10000000000 8500453356717 20000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676228847/5000000000 : ℝ), (-2231875779/10000000000 : ℝ), (5237151393/10000000000 : ℝ)] ![(21872253232483/50000000000000 : ℝ), (3438306684067/25000000000000 : ℝ), (8500453356717/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676228847/5000000000 : ℝ)|^1049 ≤ (21872253232483/50000000000000 : ℝ)^793
        have hw : |(2676228847/5000000000 : ℝ)|=(2676228847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2231875779/10000000000 : ℝ)|^1049 ≤ (3438306684067/25000000000000 : ℝ)^793
        have hw : |(-2231875779/10000000000 : ℝ)|=(2231875779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5237151393/10000000000 : ℝ)|^1049 ≤ (8500453356717/20000000000000 : ℝ)^793
        have hw : |(5237151393/10000000000 : ℝ)|=(5237151393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s3_2 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (267622879/500000000 : ℝ)*x 0 + (5237151637/10000000000 : ℝ)*x 1 + (-2231875609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267622879/500000000 : ℝ)^1049 ≤ (43744505232493/100000000000000 : ℝ)^793 := by
    have hnat : (267622879 : ℕ)^1049*100000000000000^793 ≤ 43744505232493^793*500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267622879 500000000 43744505232493 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237151637/10000000000 : ℝ)^1049 ≤ (42502269403029/100000000000000 : ℝ)^793 := by
    have hnat : (5237151637 : ℕ)^1049*100000000000000^793 ≤ 42502269403029^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237151637 10000000000 42502269403029 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2231875609/10000000000 : ℝ)^1049 ≤ (2750645070103/20000000000000 : ℝ)^793 := by
    have hnat : (2231875609 : ℕ)^1049*20000000000000^793 ≤ 2750645070103^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231875609 10000000000 2750645070103 20000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267622879/500000000 : ℝ), (5237151637/10000000000 : ℝ), (-2231875609/10000000000 : ℝ)] ![(43744505232493/100000000000000 : ℝ), (42502269403029/100000000000000 : ℝ), (2750645070103/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267622879/500000000 : ℝ)|^1049 ≤ (43744505232493/100000000000000 : ℝ)^793
        have hw : |(267622879/500000000 : ℝ)|=(267622879/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237151637/10000000000 : ℝ)|^1049 ≤ (42502269403029/100000000000000 : ℝ)^793
        have hw : |(5237151637/10000000000 : ℝ)|=(5237151637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2231875609/10000000000 : ℝ)|^1049 ≤ (2750645070103/20000000000000 : ℝ)^793
        have hw : |(-2231875609/10000000000 : ℝ)|=(2231875609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s3_3 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1088696003/2500000000 : ℝ)*x 0 + (2085615627/5000000000 : ℝ)*x 1 + (2273128087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088696003/2500000000 : ℝ)^1049 ≤ (2081115283353/6250000000000 : ℝ)^793 := by
    have hnat : (1088696003 : ℕ)^1049*6250000000000^793 ≤ 2081115283353^793*2500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088696003 2500000000 2081115283353 6250000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085615627/5000000000 : ℝ)^1049 ≤ (31454022124077/100000000000000 : ℝ)^793 := by
    have hnat : (2085615627 : ℕ)^1049*100000000000000^793 ≤ 31454022124077^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085615627 5000000000 31454022124077 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2273128087/5000000000 : ℝ)^1049 ≤ (35248133323629/100000000000000 : ℝ)^793 := by
    have hnat : (2273128087 : ℕ)^1049*100000000000000^793 ≤ 35248133323629^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273128087 5000000000 35248133323629 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088696003/2500000000 : ℝ), (2085615627/5000000000 : ℝ), (2273128087/5000000000 : ℝ)] ![(2081115283353/6250000000000 : ℝ), (31454022124077/100000000000000 : ℝ), (35248133323629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088696003/2500000000 : ℝ)|^1049 ≤ (2081115283353/6250000000000 : ℝ)^793
        have hw : |(1088696003/2500000000 : ℝ)|=(1088696003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085615627/5000000000 : ℝ)|^1049 ≤ (31454022124077/100000000000000 : ℝ)^793
        have hw : |(2085615627/5000000000 : ℝ)|=(2085615627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2273128087/5000000000 : ℝ)|^1049 ≤ (35248133323629/100000000000000 : ℝ)^793
        have hw : |(2273128087/5000000000 : ℝ)|=(2273128087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s3_4 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-427342833/2000000000 : ℝ)*x 0 + (209513903/400000000 : ℝ)*x 1 + (1355717339/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427342833/2000000000 : ℝ)^1049 ≤ (12982908916663/100000000000000 : ℝ)^793 := by
    have hnat : (427342833 : ℕ)^1049*100000000000000^793 ≤ 12982908916663^793*2000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427342833 2000000000 12982908916663 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209513903/400000000 : ℝ)^1049 ≤ (42509740753991/100000000000000 : ℝ)^793 := by
    have hnat : (209513903 : ℕ)^1049*100000000000000^793 ≤ 42509740753991^793*400000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209513903 400000000 42509740753991 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355717339/2500000000 : ℝ)^1049 ≤ (44507350319777/100000000000000 : ℝ)^793 := by
    have hnat : (1355717339 : ℕ)^1049*100000000000000^793 ≤ 44507350319777^793*2500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355717339 2500000000 44507350319777 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-427342833/2000000000 : ℝ), (209513903/400000000 : ℝ), (1355717339/2500000000 : ℝ)] ![(12982908916663/100000000000000 : ℝ), (42509740753991/100000000000000 : ℝ), (44507350319777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-427342833/2000000000 : ℝ)|^1049 ≤ (12982908916663/100000000000000 : ℝ)^793
        have hw : |(-427342833/2000000000 : ℝ)|=(427342833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209513903/400000000 : ℝ)|^1049 ≤ (42509740753991/100000000000000 : ℝ)^793
        have hw : |(209513903/400000000 : ℝ)|=(209513903/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355717339/2500000000 : ℝ)|^1049 ≤ (44507350319777/100000000000000 : ℝ)^793
        have hw : |(1355717339/2500000000 : ℝ)|=(1355717339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s3_5 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652518837/5000000000 : ℝ)*x 0 + (-255769677/1250000000 : ℝ)*x 1 + (5422869279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652518837/5000000000 : ℝ)^1049 ≤ (43232575305601/100000000000000 : ℝ)^793 := by
    have hnat : (2652518837 : ℕ)^1049*100000000000000^793 ≤ 43232575305601^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652518837 5000000000 43232575305601 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (255769677/1250000000 : ℝ)^1049 ≤ (1532509399061/12500000000000 : ℝ)^793 := by
    have hnat : (255769677 : ℕ)^1049*12500000000000^793 ≤ 1532509399061^793*1250000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255769677 1250000000 1532509399061 12500000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422869279/10000000000 : ℝ)^1049 ≤ (22253674741899/50000000000000 : ℝ)^793 := by
    have hnat : (5422869279 : ℕ)^1049*50000000000000^793 ≤ 22253674741899^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422869279 10000000000 22253674741899 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652518837/5000000000 : ℝ), (-255769677/1250000000 : ℝ), (5422869279/10000000000 : ℝ)] ![(43232575305601/100000000000000 : ℝ), (1532509399061/12500000000000 : ℝ), (22253674741899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652518837/5000000000 : ℝ)|^1049 ≤ (43232575305601/100000000000000 : ℝ)^793
        have hw : |(2652518837/5000000000 : ℝ)|=(2652518837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-255769677/1250000000 : ℝ)|^1049 ≤ (1532509399061/12500000000000 : ℝ)^793
        have hw : |(-255769677/1250000000 : ℝ)|=(255769677/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422869279/10000000000 : ℝ)|^1049 ≤ (22253674741899/50000000000000 : ℝ)^793
        have hw : |(5422869279/10000000000 : ℝ)|=(5422869279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s3_6 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (530503727/1000000000 : ℝ)*x 0 + (5422869709/10000000000 : ℝ)*x 1 + (-31971209/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530503727/1000000000 : ℝ)^1049 ≤ (43232570950419/100000000000000 : ℝ)^793 := by
    have hnat : (530503727 : ℕ)^1049*100000000000000^793 ≤ 43232570950419^793*1000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530503727 1000000000 43232570950419 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422869709/10000000000 : ℝ)^1049 ≤ (8901470830451/20000000000000 : ℝ)^793 := by
    have hnat : (5422869709 : ℕ)^1049*20000000000000^793 ≤ 8901470830451^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422869709 10000000000 8901470830451 20000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31971209/156250000 : ℝ)^1049 ≤ (12260074875447/100000000000000 : ℝ)^793 := by
    have hnat : (31971209 : ℕ)^1049*100000000000000^793 ≤ 12260074875447^793*156250000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31971209 156250000 12260074875447 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530503727/1000000000 : ℝ), (5422869709/10000000000 : ℝ), (-31971209/156250000 : ℝ)] ![(43232570950419/100000000000000 : ℝ), (8901470830451/20000000000000 : ℝ), (12260074875447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530503727/1000000000 : ℝ)|^1049 ≤ (43232570950419/100000000000000 : ℝ)^793
        have hw : |(530503727/1000000000 : ℝ)|=(530503727/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422869709/10000000000 : ℝ)|^1049 ≤ (8901470830451/20000000000000 : ℝ)^793
        have hw : |(5422869709/10000000000 : ℝ)|=(5422869709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-31971209/156250000 : ℝ)|^1049 ≤ (12260074875447/100000000000000 : ℝ)^793
        have hw : |(-31971209/156250000 : ℝ)|=(31971209/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s3_7 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2177407929/5000000000 : ℝ)*x 0 + (4544854899/10000000000 : ℝ)*x 1 + (2086319791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177407929/5000000000 : ℝ)^1049 ≤ (33298166645871/100000000000000 : ℝ)^793 := by
    have hnat : (2177407929 : ℕ)^1049*100000000000000^793 ≤ 33298166645871^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177407929 5000000000 33298166645871 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4544854899/10000000000 : ℝ)^1049 ≤ (35233762346953/100000000000000 : ℝ)^793 := by
    have hnat : (4544854899 : ℕ)^1049*100000000000000^793 ≤ 35233762346953^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4544854899 10000000000 35233762346953 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086319791/5000000000 : ℝ)^1049 ≤ (31468071003991/100000000000000 : ℝ)^793 := by
    have hnat : (2086319791 : ℕ)^1049*100000000000000^793 ≤ 31468071003991^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086319791 5000000000 31468071003991 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177407929/5000000000 : ℝ), (4544854899/10000000000 : ℝ), (2086319791/5000000000 : ℝ)] ![(33298166645871/100000000000000 : ℝ), (35233762346953/100000000000000 : ℝ), (31468071003991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177407929/5000000000 : ℝ)|^1049 ≤ (33298166645871/100000000000000 : ℝ)^793
        have hw : |(2177407929/5000000000 : ℝ)|=(2177407929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4544854899/10000000000 : ℝ)|^1049 ≤ (35233762346953/100000000000000 : ℝ)^793
        have hw : |(4544854899/10000000000 : ℝ)|=(4544854899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086319791/5000000000 : ℝ)|^1049 ≤ (31468071003991/100000000000000 : ℝ)^793
        have hw : |(2086319791/5000000000 : ℝ)|=(2086319791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1199_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16339/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (233/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (10797/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14743/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16339/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (233/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16339/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (233/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16339/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (233/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16339/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (233/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16339/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (233/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16339/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (233/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (233/2500 : ℝ) ^ (8391/2048 : ℝ) ≤ (5991338911683447/100000000000000000000 : ℝ) := by
    have hpowers : (233/2500 : ℝ)^8391 ≤ (5991338911683447/100000000000000000000 : ℝ)^2048 := by
      have hnat : (233 : ℕ)^8391*100000000000000000000^2048 ≤ 5991338911683447^2048*2500^8391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        233 2500 5991338911683447 100000000000000000000 8391 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (233/2500 : ℝ)) (X := (5991338911683447/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16339/100000 : ℝ) ^ (8391/2048 : ℝ) ≤ (59765782282679731/100000000000000000000 : ℝ) := by
    have hpowers : (16339/100000 : ℝ)^8391 ≤ (59765782282679731/100000000000000000000 : ℝ)^2048 := by
      have hnat : (16339 : ℕ)^8391*100000000000000000000^2048 ≤ 59765782282679731^2048*100000^8391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16339 100000 59765782282679731 100000000000000000000 8391 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16339/100000 : ℝ)) (X := (59765782282679731/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005991338911683447/50000000000000000000 : ℝ) ≤ (500014622460263/500000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (50005991338911683447/50000000000000000000 : ℝ)^2048 ≤ (500014622460263/500000000000000 : ℝ)^8391 := by
      have hnat : (50005991338911683447 : ℕ)^2048*500000000000000^8391 ≤ 500014622460263^8391*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005991338911683447 50000000000000000000 500014622460263 500000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500014622460263/500000000000000 : ℝ)) (X := (50005991338911683447/50000000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50032878560597181589/50000000000000000000 : ℝ) ≤ (10001604542083767/10000000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (50032878560597181589/50000000000000000000 : ℝ)^2048 ≤ (10001604542083767/10000000000000000 : ℝ)^8391 := by
      have hnat : (50032878560597181589 : ℕ)^2048*10000000000000000^8391 ≤ 10001604542083767^8391*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032878560597181589 50000000000000000000 10001604542083767 10000000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001604542083767/10000000000000000 : ℝ)) (X := (50032878560597181589/50000000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50059765782282679731/50000000000000000000 : ℝ) ≤ (5001458317481137/5000000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (50059765782282679731/50000000000000000000 : ℝ)^2048 ≤ (5001458317481137/5000000000000000 : ℝ)^8391 := by
      have hnat : (50059765782282679731 : ℕ)^2048*5000000000000000^8391 ≤ 5001458317481137^8391*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50059765782282679731 50000000000000000000 5001458317481137 5000000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001458317481137/5000000000000000 : ℝ)) (X := (50059765782282679731/50000000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5991338911683447/100000000000000000000 : ℝ) ≤ ((3508379764485817473/3509500000000000000 : ℝ)+2*(1312092878507/701900000000000 : ℝ)*(233/2500 : ℝ))^(8391/2048 : ℝ) := by
    rw [show (3508379764485817473/3509500000000000000 : ℝ)+2*(1312092878507/701900000000000 : ℝ)*(233/2500 : ℝ)=(500014622460263/500000000000000 : ℝ) by norm_num, show 1+2*(5991338911683447/100000000000000000000 : ℝ)=(50005991338911683447/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(59765782282679731/100000000000000000000 : ℝ)+(5991338911683447/100000000000000000000 : ℝ) ≤ ((3508379764485817473/3509500000000000000 : ℝ)+(1312092878507/701900000000000 : ℝ)*((16339/100000 : ℝ)+(233/2500 : ℝ)))^(8391/2048 : ℝ) := by
    rw [show (3508379764485817473/3509500000000000000 : ℝ)+(1312092878507/701900000000000 : ℝ)*((16339/100000 : ℝ)+(233/2500 : ℝ))=(10001604542083767/10000000000000000 : ℝ) by norm_num, show 1+(59765782282679731/100000000000000000000 : ℝ)+(5991338911683447/100000000000000000000 : ℝ)=(50032878560597181589/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(59765782282679731/100000000000000000000 : ℝ) ≤ ((3508379764485817473/3509500000000000000 : ℝ)+2*(1312092878507/701900000000000 : ℝ)*(16339/100000 : ℝ))^(8391/2048 : ℝ) := by
    rw [show (3508379764485817473/3509500000000000000 : ℝ)+2*(1312092878507/701900000000000 : ℝ)*(16339/100000 : ℝ)=(5001458317481137/5000000000000000 : ℝ) by norm_num, show 1+2*(59765782282679731/100000000000000000000 : ℝ)=(50059765782282679731/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3508379764485817473/3509500000000000000 : ℝ)*(X 1 0+X 2 0)+(1312092878507/701900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (233/2500 : ℝ)) (hi := (16339/100000 : ℝ)) (c := (3508379764485817473/3509500000000000000 : ℝ)) (alpha := (1312092878507/701900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3508379764485817473/3509500000000000000 : ℝ)*(X 0 1+X 2 1)+(1312092878507/701900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (233/2500 : ℝ)) (hi := (16339/100000 : ℝ)) (c := (3508379764485817473/3509500000000000000 : ℝ)) (alpha := (1312092878507/701900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3508379764485817473/3509500000000000000 : ℝ)*(X 0 2+X 1 2)+(1312092878507/701900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (233/2500 : ℝ)) (hi := (16339/100000 : ℝ)) (c := (3508379764485817473/3509500000000000000 : ℝ)) (alpha := (1312092878507/701900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2136698419/10000000000 : ℝ)*X 0 0+(5423569597/10000000000 : ℝ)*X 0 1+(5237151201/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676228847/5000000000 : ℝ)*X 1 0+(-2231875779/10000000000 : ℝ)*X 1 1+(5237151393/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267622879/500000000 : ℝ)*X 2 0+(5237151637/10000000000 : ℝ)*X 2 1+(-2231875609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088696003/2500000000 : ℝ)*X 0 0+(2085615627/5000000000 : ℝ)*X 0 1+(2273128087/5000000000 : ℝ)*X 0 2+(1088696003/2500000000 : ℝ)*X 1 0+(2085615627/5000000000 : ℝ)*X 1 1+(2273128087/5000000000 : ℝ)*X 1 2+(1088696003/2500000000 : ℝ)*X 2 0+(2085615627/5000000000 : ℝ)*X 2 1+(2273128087/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-427342833/2000000000 : ℝ)*X 0 0+(209513903/400000000 : ℝ)*X 0 1+(1355717339/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652518837/5000000000 : ℝ)*X 1 0+(-255769677/1250000000 : ℝ)*X 1 1+(5422869279/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530503727/1000000000 : ℝ)*X 2 0+(5422869709/10000000000 : ℝ)*X 2 1+(-31971209/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2177407929/5000000000 : ℝ)*X 0 0+(4544854899/10000000000 : ℝ)*X 0 1+(2086319791/5000000000 : ℝ)*X 0 2+(2177407929/5000000000 : ℝ)*X 1 0+(4544854899/10000000000 : ℝ)*X 1 1+(2086319791/5000000000 : ℝ)*X 1 2+(2177407929/5000000000 : ℝ)*X 2 0+(4544854899/10000000000 : ℝ)*X 2 1+(2086319791/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (403013803787724580133081997/43868750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (288240721/20000000000000 : ℝ)*(base19) + (1142150587/100000000000000 : ℝ)*(base23) + (98913323/100000000000000 : ℝ)*(lower2) + (31557103/25000000000000 : ℝ)*(upper3) + (152672369/100000000000000 : ℝ)*(upper5) + (1003858294871537/25000000000000 : ℝ)*(major0) + (1003858294871537/25000000000000 : ℝ)*(major1) + (1003858294871537/25000000000000 : ℝ)*(major2) + (5364310865298367/100000000000000 : ℝ)*(sp0) + (670543141701069/12500000000000 : ℝ)*(sp1) + (536434543266157/10000000000000 : ℝ)*(sp2) + (166656527751631/6250000000000 : ℝ)*(sp3) + (3570951379/10000000000000 : ℝ)*(sp4) + (3006781417/20000000000000 : ℝ)*(sp7) + (1333259738966591/50000000000000 : ℝ)*(f.failure) + (5364346574812157/100000000000000 : ℝ)*(f.sum) + (4495154029931/35095000000000000000000000000 : ℝ)*base65 + (1389011852643611001/87737500000000000000000000000000 : ℝ)*base67 + (172056917101726499/87737500000000000000000000000000 : ℝ)*base70 + (150144400450886001/87737500000000000000000000000000 : ℝ)*base71 + (166504629565891/35095000000000000000000000000 : ℝ)*base73 + (896962671690136001/87737500000000000000000000000000 : ℝ)*base75 + (1410232074708213999/87737500000000000000000000000000 : ℝ)*base78 + (1422616829405123501/87737500000000000000000000000000 : ℝ)*base79 + (283915745923/274179687500000000000000000 : ℝ)*base82 + (1315381/312500000000000000000 : ℝ)*base89 + (1315381/312500000000000000000 : ℝ)*base91 + (1315381/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (326772302662776241698549/35095000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2574223859/100000000000000 : ℝ)*(base19) + (305557571/12500000000000 : ℝ)*(base23) + (91097671/50000000000000 : ℝ)*(upper3) + (145496767/100000000000000 : ℝ)*(lower4) + (329305013/100000000000000 : ℝ)*(upper5) + (252855666619731/6250000000000 : ℝ)*(major0) + (252855666619731/6250000000000 : ℝ)*(major1) + (252855666619731/6250000000000 : ℝ)*(major2) + (25696067087/50000000000000 : ℝ)*(sp1) + (52238686601/100000000000000 : ℝ)*(sp2) + (2702384262046669/50000000000000 : ℝ)*(sp4) + (675589319716913/12500000000000 : ℝ)*(sp5) + (5404713840946169/100000000000000 : ℝ)*(sp6) + (1343306248684381/50000000000000 : ℝ)*(sp7) + (1343306248684381/50000000000000 : ℝ)*(f.failure) + (2702384262046669/50000000000000 : ℝ)*(f.sum) + (107186780204201/17547500000000000000000000000 : ℝ)*base65 + (189762273673592737/21934375000000000000000000000000 : ℝ)*base68 + (207098489139392737/21934375000000000000000000000000 : ℝ)*base70 + (210112677463469763/21934375000000000000000000000000 : ℝ)*base71 + (8938740535447/8773750000000000000000000000 : ℝ)*base74 + (8771297399576013/21934375000000000000000000000000 : ℝ)*base75 + (16451304617838513/21934375000000000000000000000000 : ℝ)*base77 + (220686568695005237/21934375000000000000000000000000 : ℝ)*base80 + (118159392917427/35095000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (498271/312500000000000000000 : ℝ)*base89 + (498271/312500000000000000000 : ℝ)*base91 + (498271/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1199_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16339/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (233/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10797/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1199_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1199_s4_0 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2139272569/10000000000 : ℝ)*x 0 + (2699649873/5000000000 : ℝ)*x 1 + (5259735551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139272569/10000000000 : ℝ)^1049 ≤ (13003476388523/100000000000000 : ℝ)^793 := by
    have hnat : (2139272569 : ℕ)^1049*100000000000000^793 ≤ 13003476388523^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139272569 10000000000 13003476388523 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699649873/5000000000 : ℝ)^1049 ≤ (8850327534471/20000000000000 : ℝ)^793 := by
    have hnat : (2699649873 : ℕ)^1049*20000000000000^793 ≤ 8850327534471^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699649873 5000000000 8850327534471 20000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5259735551/10000000000 : ℝ)^1049 ≤ (21372442963331/50000000000000 : ℝ)^793 := by
    have hnat : (5259735551 : ℕ)^1049*50000000000000^793 ≤ 21372442963331^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259735551 10000000000 21372442963331 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2139272569/10000000000 : ℝ), (2699649873/5000000000 : ℝ), (5259735551/10000000000 : ℝ)] ![(13003476388523/100000000000000 : ℝ), (8850327534471/20000000000000 : ℝ), (21372442963331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2139272569/10000000000 : ℝ)|^1049 ≤ (13003476388523/100000000000000 : ℝ)^793
        have hw : |(-2139272569/10000000000 : ℝ)|=(2139272569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699649873/5000000000 : ℝ)|^1049 ≤ (8850327534471/20000000000000 : ℝ)^793
        have hw : |(2699649873/5000000000 : ℝ)|=(2699649873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5259735551/10000000000 : ℝ)|^1049 ≤ (21372442963331/50000000000000 : ℝ)^793
        have hw : |(5259735551/10000000000 : ℝ)|=(5259735551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s4_1 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1069272787/2000000000 : ℝ)*x 0 + (-2210158113/10000000000 : ℝ)*x 1 + (5259735739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069272787/2000000000 : ℝ)^1049 ≤ (5459829741023/12500000000000 : ℝ)^793 := by
    have hnat : (1069272787 : ℕ)^1049*12500000000000^793 ≤ 5459829741023^793*2000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069272787 2000000000 5459829741023 12500000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2210158113/10000000000 : ℝ)^1049 ≤ (339411852847/2500000000000 : ℝ)^793 := by
    have hnat : (2210158113 : ℕ)^1049*2500000000000^793 ≤ 339411852847^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210158113 10000000000 339411852847 2500000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5259735739/10000000000 : ℝ)^1049 ≤ (2671555496733/6250000000000 : ℝ)^793 := by
    have hnat : (5259735739 : ℕ)^1049*6250000000000^793 ≤ 2671555496733^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259735739 10000000000 2671555496733 6250000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069272787/2000000000 : ℝ), (-2210158113/10000000000 : ℝ), (5259735739/10000000000 : ℝ)] ![(5459829741023/12500000000000 : ℝ), (339411852847/2500000000000 : ℝ), (2671555496733/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069272787/2000000000 : ℝ)|^1049 ≤ (5459829741023/12500000000000 : ℝ)^793
        have hw : |(1069272787/2000000000 : ℝ)|=(1069272787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2210158113/10000000000 : ℝ)|^1049 ≤ (339411852847/2500000000000 : ℝ)^793
        have hw : |(-2210158113/10000000000 : ℝ)|=(2210158113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5259735739/10000000000 : ℝ)|^1049 ≤ (2671555496733/6250000000000 : ℝ)^793
        have hw : |(5259735739/10000000000 : ℝ)|=(5259735739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s4_2 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2673182009/5000000000 : ℝ)*x 0 + (1051947113/2000000000 : ℝ)*x 1 + (-276269779/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673182009/5000000000 : ℝ)^1049 ≤ (43678638825181/100000000000000 : ℝ)^793 := by
    have hnat : (2673182009 : ℕ)^1049*100000000000000^793 ≤ 43678638825181^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673182009 5000000000 43678638825181 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051947113/2000000000 : ℝ)^1049 ≤ (42744886077167/100000000000000 : ℝ)^793 := by
    have hnat : (1051947113 : ℕ)^1049*100000000000000^793 ≤ 42744886077167^793*2000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051947113 2000000000 42744886077167 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276269779/1250000000 : ℝ)^1049 ≤ (271529501617/2000000000000 : ℝ)^793 := by
    have hnat : (276269779 : ℕ)^1049*2000000000000^793 ≤ 271529501617^793*1250000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276269779 1250000000 271529501617 2000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673182009/5000000000 : ℝ), (1051947113/2000000000 : ℝ), (-276269779/1250000000 : ℝ)] ![(43678638825181/100000000000000 : ℝ), (42744886077167/100000000000000 : ℝ), (271529501617/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673182009/5000000000 : ℝ)|^1049 ≤ (43678638825181/100000000000000 : ℝ)^793
        have hw : |(2673182009/5000000000 : ℝ)|=(2673182009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051947113/2000000000 : ℝ)|^1049 ≤ (42744886077167/100000000000000 : ℝ)^793
        have hw : |(1051947113/2000000000 : ℝ)|=(1051947113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-276269779/1250000000 : ℝ)|^1049 ≤ (271529501617/2000000000000 : ℝ)^793
        have hw : |(-276269779/1250000000 : ℝ)|=(276269779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s4_3 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2178162609/5000000000 : ℝ)*x 0 + (843632499/2000000000 : ℝ)*x 1 + (4498928899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178162609/5000000000 : ℝ)^1049 ≤ (8328358554303/25000000000000 : ℝ)^793 := by
    have hnat : (2178162609 : ℕ)^1049*25000000000000^793 ≤ 8328358554303^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178162609 5000000000 8328358554303 25000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (843632499/2000000000 : ℝ)^1049 ≤ (31923010703003/100000000000000 : ℝ)^793 := by
    have hnat : (843632499 : ℕ)^1049*100000000000000^793 ≤ 31923010703003^793*2000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843632499 2000000000 31923010703003 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4498928899/10000000000 : ℝ)^1049 ≤ (34763555067997/100000000000000 : ℝ)^793 := by
    have hnat : (4498928899 : ℕ)^1049*100000000000000^793 ≤ 34763555067997^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498928899 10000000000 34763555067997 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178162609/5000000000 : ℝ), (843632499/2000000000 : ℝ), (4498928899/10000000000 : ℝ)] ![(8328358554303/25000000000000 : ℝ), (31923010703003/100000000000000 : ℝ), (34763555067997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178162609/5000000000 : ℝ)|^1049 ≤ (8328358554303/25000000000000 : ℝ)^793
        have hw : |(2178162609/5000000000 : ℝ)|=(2178162609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(843632499/2000000000 : ℝ)|^1049 ≤ (31923010703003/100000000000000 : ℝ)^793
        have hw : |(843632499/2000000000 : ℝ)|=(843632499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4498928899/10000000000 : ℝ)|^1049 ≤ (34763555067997/100000000000000 : ℝ)^793
        have hw : |(4498928899/10000000000 : ℝ)|=(4498928899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s4_4 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1069639503/5000000000 : ℝ)*x 0 + (5260126557/10000000000 : ℝ)*x 1 + (337431703/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069639503/5000000000 : ℝ)^1049 ≤ (3250882036687/25000000000000 : ℝ)^793 := by
    have hnat : (1069639503 : ℕ)^1049*25000000000000^793 ≤ 3250882036687^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069639503 5000000000 3250882036687 25000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260126557/10000000000 : ℝ)^1049 ≤ (4274908942797/10000000000000 : ℝ)^793 := by
    have hnat : (5260126557 : ℕ)^1049*10000000000000^793 ≤ 4274908942797^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260126557 10000000000 4274908942797 10000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337431703/625000000 : ℝ)^1049 ≤ (44247382407833/100000000000000 : ℝ)^793 := by
    have hnat : (337431703 : ℕ)^1049*100000000000000^793 ≤ 44247382407833^793*625000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337431703 625000000 44247382407833 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1069639503/5000000000 : ℝ), (5260126557/10000000000 : ℝ), (337431703/625000000 : ℝ)] ![(3250882036687/25000000000000 : ℝ), (4274908942797/10000000000000 : ℝ), (44247382407833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1069639503/5000000000 : ℝ)|^1049 ≤ (3250882036687/25000000000000 : ℝ)^793
        have hw : |(-1069639503/5000000000 : ℝ)|=(1069639503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260126557/10000000000 : ℝ)|^1049 ≤ (4274908942797/10000000000000 : ℝ)^793
        have hw : |(5260126557/10000000000 : ℝ)|=(5260126557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337431703/625000000 : ℝ)|^1049 ≤ (44247382407833/100000000000000 : ℝ)^793
        have hw : |(337431703/625000000 : ℝ)|=(337431703/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s4_5 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2655430391/5000000000 : ℝ)*x 0 + (-1035493573/5000000000 : ℝ)*x 1 + (5398906883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655430391/5000000000 : ℝ)^1049 ≤ (21647680210761/50000000000000 : ℝ)^793 := by
    have hnat : (2655430391 : ℕ)^1049*50000000000000^793 ≤ 21647680210761^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655430391 5000000000 21647680210761 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035493573/5000000000 : ℝ)^1049 ≤ (12457261112037/100000000000000 : ℝ)^793 := by
    have hnat : (1035493573 : ℕ)^1049*100000000000000^793 ≤ 12457261112037^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035493573 5000000000 12457261112037 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398906883/10000000000 : ℝ)^1049 ≤ (8849475690147/20000000000000 : ℝ)^793 := by
    have hnat : (5398906883 : ℕ)^1049*20000000000000^793 ≤ 8849475690147^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398906883 10000000000 8849475690147 20000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655430391/5000000000 : ℝ), (-1035493573/5000000000 : ℝ), (5398906883/10000000000 : ℝ)] ![(21647680210761/50000000000000 : ℝ), (12457261112037/100000000000000 : ℝ), (8849475690147/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655430391/5000000000 : ℝ)|^1049 ≤ (21647680210761/50000000000000 : ℝ)^793
        have hw : |(2655430391/5000000000 : ℝ)|=(2655430391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1035493573/5000000000 : ℝ)|^1049 ≤ (12457261112037/100000000000000 : ℝ)^793
        have hw : |(-1035493573/5000000000 : ℝ)|=(1035493573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398906883/10000000000 : ℝ)|^1049 ≤ (8849475690147/20000000000000 : ℝ)^793
        have hw : |(5398906883/10000000000 : ℝ)|=(5398906883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s4_6 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2655430309/5000000000 : ℝ)*x 0 + (2699453667/5000000000 : ℝ)*x 1 + (-1035493377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655430309/5000000000 : ℝ)^1049 ≤ (43295358652951/100000000000000 : ℝ)^793 := by
    have hnat : (2655430309 : ℕ)^1049*100000000000000^793 ≤ 43295358652951^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655430309 5000000000 43295358652951 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699453667/5000000000 : ℝ)^1049 ≤ (44247383340191/100000000000000 : ℝ)^793 := by
    have hnat : (2699453667 : ℕ)^1049*100000000000000^793 ≤ 44247383340191^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699453667 5000000000 44247383340191 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035493377/5000000000 : ℝ)^1049 ≤ (12457257992907/100000000000000 : ℝ)^793 := by
    have hnat : (1035493377 : ℕ)^1049*100000000000000^793 ≤ 12457257992907^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035493377 5000000000 12457257992907 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655430309/5000000000 : ℝ), (2699453667/5000000000 : ℝ), (-1035493377/5000000000 : ℝ)] ![(43295358652951/100000000000000 : ℝ), (44247383340191/100000000000000 : ℝ), (12457257992907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655430309/5000000000 : ℝ)|^1049 ≤ (43295358652951/100000000000000 : ℝ)^793
        have hw : |(2655430309/5000000000 : ℝ)|=(2655430309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699453667/5000000000 : ℝ)|^1049 ≤ (44247383340191/100000000000000 : ℝ)^793
        have hw : |(2699453667/5000000000 : ℝ)|=(2699453667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1035493377/5000000000 : ℝ)|^1049 ≤ (12457257992907/100000000000000 : ℝ)^793
        have hw : |(-1035493377/5000000000 : ℝ)|=(1035493377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s4_7 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1089084661/2500000000 : ℝ)*x 0 + (4498142717/10000000000 : ℝ)*x 1 + (421895159/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089084661/2500000000 : ℝ)^1049 ≤ (33313570032379/100000000000000 : ℝ)^793 := by
    have hnat : (1089084661 : ℕ)^1049*100000000000000^793 ≤ 33313570032379^793*2500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089084661 2500000000 33313570032379 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498142717/10000000000 : ℝ)^1049 ≤ (8688879821253/25000000000000 : ℝ)^793 := by
    have hnat : (4498142717 : ℕ)^1049*25000000000000^793 ≤ 8688879821253^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498142717 10000000000 8688879821253 25000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (421895159/1000000000 : ℝ)^1049 ≤ (15965455334691/50000000000000 : ℝ)^793 := by
    have hnat : (421895159 : ℕ)^1049*50000000000000^793 ≤ 15965455334691^793*1000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421895159 1000000000 15965455334691 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089084661/2500000000 : ℝ), (4498142717/10000000000 : ℝ), (421895159/1000000000 : ℝ)] ![(33313570032379/100000000000000 : ℝ), (8688879821253/25000000000000 : ℝ), (15965455334691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089084661/2500000000 : ℝ)|^1049 ≤ (33313570032379/100000000000000 : ℝ)^793
        have hw : |(1089084661/2500000000 : ℝ)|=(1089084661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498142717/10000000000 : ℝ)|^1049 ≤ (8688879821253/25000000000000 : ℝ)^793
        have hw : |(4498142717/10000000000 : ℝ)|=(4498142717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(421895159/1000000000 : ℝ)|^1049 ≤ (15965455334691/50000000000000 : ℝ)^793
        have hw : |(421895159/1000000000 : ℝ)|=(421895159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1199_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10797/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11279/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14743/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10797/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14743/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10797/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14743/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10797/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14743/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10797/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14743/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10797/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14743/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10797/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10797/100000 : ℝ) ^ (8391/2048 : ℝ) ≤ (27366574522973/250000000000000000 : ℝ) := by
    have hpowers : (10797/100000 : ℝ)^8391 ≤ (27366574522973/250000000000000000 : ℝ)^2048 := by
      have hnat : (10797 : ℕ)^8391*250000000000000000^2048 ≤ 27366574522973^2048*100000^8391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10797 100000 27366574522973 250000000000000000 8391 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10797/100000 : ℝ)) (X := (27366574522973/250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14743/100000 : ℝ) ^ (8391/2048 : ℝ) ≤ (39224429843578413/100000000000000000000 : ℝ) := by
    have hpowers : (14743/100000 : ℝ)^8391 ≤ (39224429843578413/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14743 : ℕ)^8391*100000000000000000000^2048 ≤ 39224429843578413^2048*100000^8391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14743 100000 39224429843578413 100000000000000000000 8391 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14743/100000 : ℝ)) (X := (39224429843578413/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (125027366574522973/125000000000000000 : ℝ) ≤ (10000534306827977/10000000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (125027366574522973/125000000000000000 : ℝ)^2048 ≤ (10000534306827977/10000000000000000 : ℝ)^8391 := by
      have hnat : (125027366574522973 : ℕ)^2048*10000000000000000^8391 ≤ 10000534306827977^8391*125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125027366574522973 125000000000000000 10000534306827977 10000000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000534306827977/10000000000000000 : ℝ)) (X := (125027366574522973/125000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050171059652767613/100000000000000000000 : ℝ) ≤ (10001224298074939/10000000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (100050171059652767613/100000000000000000000 : ℝ)^2048 ≤ (10001224298074939/10000000000000000 : ℝ)^8391 := by
      have hnat : (100050171059652767613 : ℕ)^2048*10000000000000000^8391 ≤ 10001224298074939^8391*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050171059652767613 100000000000000000000 10001224298074939 10000000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001224298074939/10000000000000000 : ℝ)) (X := (100050171059652767613/100000000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039224429843578413/50000000000000000000 : ℝ) ≤ (10001914289321901/10000000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (50039224429843578413/50000000000000000000 : ℝ)^2048 ≤ (10001914289321901/10000000000000000 : ℝ)^8391 := by
      have hnat : (50039224429843578413 : ℕ)^2048*10000000000000000^8391 ≤ 10001914289321901^8391*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039224429843578413 50000000000000000000 10001914289321901 10000000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001914289321901/10000000000000000 : ℝ)) (X := (50039224429843578413/50000000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(27366574522973/250000000000000000 : ℝ) ≤ ((19723604351878149907/19730000000000000000 : ℝ)+2*(344995623481/197300000000000 : ℝ)*(10797/100000 : ℝ))^(8391/2048 : ℝ) := by
    rw [show (19723604351878149907/19730000000000000000 : ℝ)+2*(344995623481/197300000000000 : ℝ)*(10797/100000 : ℝ)=(10000534306827977/10000000000000000 : ℝ) by norm_num, show 1+2*(27366574522973/250000000000000000 : ℝ)=(125027366574522973/125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39224429843578413/100000000000000000000 : ℝ)+(27366574522973/250000000000000000 : ℝ) ≤ ((19723604351878149907/19730000000000000000 : ℝ)+(344995623481/197300000000000 : ℝ)*((14743/100000 : ℝ)+(10797/100000 : ℝ)))^(8391/2048 : ℝ) := by
    rw [show (19723604351878149907/19730000000000000000 : ℝ)+(344995623481/197300000000000 : ℝ)*((14743/100000 : ℝ)+(10797/100000 : ℝ))=(10001224298074939/10000000000000000 : ℝ) by norm_num, show 1+(39224429843578413/100000000000000000000 : ℝ)+(27366574522973/250000000000000000 : ℝ)=(100050171059652767613/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39224429843578413/100000000000000000000 : ℝ) ≤ ((19723604351878149907/19730000000000000000 : ℝ)+2*(344995623481/197300000000000 : ℝ)*(14743/100000 : ℝ))^(8391/2048 : ℝ) := by
    rw [show (19723604351878149907/19730000000000000000 : ℝ)+2*(344995623481/197300000000000 : ℝ)*(14743/100000 : ℝ)=(10001914289321901/10000000000000000 : ℝ) by norm_num, show 1+2*(39224429843578413/100000000000000000000 : ℝ)=(50039224429843578413/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19723604351878149907/19730000000000000000 : ℝ)*(X 1 0+X 2 0)+(344995623481/197300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (10797/100000 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (19723604351878149907/19730000000000000000 : ℝ)) (alpha := (344995623481/197300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19723604351878149907/19730000000000000000 : ℝ)*(X 0 1+X 2 1)+(344995623481/197300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (10797/100000 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (19723604351878149907/19730000000000000000 : ℝ)) (alpha := (344995623481/197300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19723604351878149907/19730000000000000000 : ℝ)*(X 0 2+X 1 2)+(344995623481/197300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (10797/100000 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (19723604351878149907/19730000000000000000 : ℝ)) (alpha := (344995623481/197300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2139272569/10000000000 : ℝ)*X 0 0+(2699649873/5000000000 : ℝ)*X 0 1+(5259735551/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069272787/2000000000 : ℝ)*X 1 0+(-2210158113/10000000000 : ℝ)*X 1 1+(5259735739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673182009/5000000000 : ℝ)*X 2 0+(1051947113/2000000000 : ℝ)*X 2 1+(-276269779/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178162609/5000000000 : ℝ)*X 0 0+(843632499/2000000000 : ℝ)*X 0 1+(4498928899/10000000000 : ℝ)*X 0 2+(2178162609/5000000000 : ℝ)*X 1 0+(843632499/2000000000 : ℝ)*X 1 1+(4498928899/10000000000 : ℝ)*X 1 2+(2178162609/5000000000 : ℝ)*X 2 0+(843632499/2000000000 : ℝ)*X 2 1+(4498928899/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1069639503/5000000000 : ℝ)*X 0 0+(5260126557/10000000000 : ℝ)*X 0 1+(337431703/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655430391/5000000000 : ℝ)*X 1 0+(-1035493573/5000000000 : ℝ)*X 1 1+(5398906883/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655430309/5000000000 : ℝ)*X 2 0+(2699453667/5000000000 : ℝ)*X 2 1+(-1035493377/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089084661/2500000000 : ℝ)*X 0 0+(4498142717/10000000000 : ℝ)*X 0 1+(421895159/1000000000 : ℝ)*X 0 2+(1089084661/2500000000 : ℝ)*X 1 0+(4498142717/10000000000 : ℝ)*X 1 1+(421895159/1000000000 : ℝ)*X 1 2+(1089084661/2500000000 : ℝ)*X 2 0+(4498142717/10000000000 : ℝ)*X 2 1+(421895159/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5349653701554785463927742557/986500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (768099359/50000000000000 : ℝ)*(base19) + (317394497/20000000000000 : ℝ)*(base23) + (64646893/25000000000000 : ℝ)*(upper3) + (323261/1000000000000 : ℝ)*(upper4) + (59323957/100000000000000 : ℝ)*(upper5) + (5363486889561317/100000000000000 : ℝ)*(major0) + (5363486889561317/100000000000000 : ℝ)*(major1) + (5363486889561317/100000000000000 : ℝ)*(major2) + (7165211770574689/100000000000000 : ℝ)*(sp0) + (7165253656855259/100000000000000 : ℝ)*(sp1) + (1791313401520373/25000000000000 : ℝ)*(sp2) + (556515118623/15625000000 : ℝ)*(sp3) + (5427809911/12500000000000 : ℝ)*(sp4) + (10823059687/50000000000000 : ℝ)*(sp7) + (1780859202653287/50000000000000 : ℝ)*(f.failure) + (7165255193053977/100000000000000 : ℝ)*(f.sum) + (5534774826389/4932500000000000000000000000 : ℝ)*base66 + (607776445578047519/1973000000000000000000000000000000 : ℝ)*base67 + (16422966111636952481/1973000000000000000000000000000000 : ℝ)*base70 + (11675045594009047519/1973000000000000000000000000000000 : ℝ)*base71 + (8548833577381/4932500000000000000000000000 : ℝ)*base73 + (29376210947510952481/1973000000000000000000000000000000 : ℝ)*base76 + (13129255279333952481/1973000000000000000000000000000000 : ℝ)*base78 + (2504991265031952481/1973000000000000000000000000000000 : ℝ)*base80 + (30670225707863/9865000000000000000000000000 : ℝ)*base82 + (1753317/312500000000000000000 : ℝ)*base89 + (1753317/312500000000000000000 : ℝ)*base91 + (1753317/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1102807329364486239054959889/123312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (706458731/50000000000000 : ℝ)*(base19) + (1702469501/100000000000000 : ℝ)*(base23) + (279648621/100000000000000 : ℝ)*(upper3) + (8151007/5000000000000 : ℝ)*(lower4) + (98204099/50000000000000 : ℝ)*(upper5) + (1348422634494409/25000000000000 : ℝ)*(major0) + (1348422634494409/25000000000000 : ℝ)*(major1) + (1348422634494409/25000000000000 : ℝ)*(major2) + (7720226347/100000000000000 : ℝ)*(sp1) + (3840140673/10000000000000 : ℝ)*(sp2) + (180140127629809/2500000000000 : ℝ)*(sp4) + (900699496506069/12500000000000 : ℝ)*(sp5) + (225173906291129/3125000000000 : ℝ)*(sp6) + (3581775672656511/100000000000000 : ℝ)*(sp7) + (3581775672656511/100000000000000 : ℝ)*(f.failure) + (180140127629809/2500000000000 : ℝ)*(f.sum) + (3534581751957/1233125000000000000000000000 : ℝ)*base65 + (5537790799349480037/493250000000000000000000000000000 : ℝ)*base68 + (5441924141524230037/493250000000000000000000000000000 : ℝ)*base70 + (4144512104668980037/493250000000000000000000000000000 : ℝ)*base72 + (2379157787561/2466250000000000000000000000 : ℝ)*base74 + (9708572929433480037/493250000000000000000000000000000 : ℝ)*base76 + (1002943712492269963/493250000000000000000000000000000 : ℝ)*base77 + (8247474808245980037/493250000000000000000000000000000 : ℝ)*base80 + (1337918847173/4932500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (5670101/625000000000000000000 : ℝ)*base89 + (5670101/625000000000000000000 : ℝ)*base91 + (5670101/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1199_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10797/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1199_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1199_s5_0 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-106989751/500000000 : ℝ)*x 0 + (5393462557/10000000000 : ℝ)*x 1 + (5265229561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106989751/500000000 : ℝ)^1049 ≤ (13007677443213/100000000000000 : ℝ)^793 := by
    have hnat : (106989751 : ℕ)^1049*100000000000000^793 ≤ 13007677443213^793*500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106989751 500000000 13007677443213 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393462557/10000000000 : ℝ)^1049 ≤ (8837672825829/20000000000000 : ℝ)^793 := by
    have hnat : (5393462557 : ℕ)^1049*20000000000000^793 ≤ 8837672825829^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393462557 10000000000 8837672825829 20000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265229561/10000000000 : ℝ)^1049 ≤ (42803958405997/100000000000000 : ℝ)^793 := by
    have hnat : (5265229561 : ℕ)^1049*100000000000000^793 ≤ 42803958405997^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265229561 10000000000 42803958405997 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106989751/500000000 : ℝ), (5393462557/10000000000 : ℝ), (5265229561/10000000000 : ℝ)] ![(13007677443213/100000000000000 : ℝ), (8837672825829/20000000000000 : ℝ), (42803958405997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106989751/500000000 : ℝ)|^1049 ≤ (13007677443213/100000000000000 : ℝ)^793
        have hw : |(-106989751/500000000 : ℝ)|=(106989751/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393462557/10000000000 : ℝ)|^1049 ≤ (8837672825829/20000000000000 : ℝ)^793
        have hw : |(5393462557/10000000000 : ℝ)|=(5393462557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265229561/10000000000 : ℝ)|^1049 ≤ (42803958405997/100000000000000 : ℝ)^793
        have hw : |(5265229561/10000000000 : ℝ)|=(5265229561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s5_1 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (106897851/200000000 : ℝ)*x 0 + (-137802709/625000000 : ℝ)*x 1 + (658153699/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106897851/200000000 : ℝ)^1049 ≤ (43662737094339/100000000000000 : ℝ)^793 := by
    have hnat : (106897851 : ℕ)^1049*100000000000000^793 ≤ 43662737094339^793*200000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106897851 200000000 43662737094339 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137802709/625000000 : ℝ)^1049 ≤ (1353330415341/10000000000000 : ℝ)^793 := by
    have hnat : (137802709 : ℕ)^1049*10000000000000^793 ≤ 1353330415341^793*625000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137802709 625000000 1353330415341 10000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658153699/1250000000 : ℝ)^1049 ≤ (42803958739371/100000000000000 : ℝ)^793 := by
    have hnat : (658153699 : ℕ)^1049*100000000000000^793 ≤ 42803958739371^793*1250000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658153699 1250000000 42803958739371 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106897851/200000000 : ℝ), (-137802709/625000000 : ℝ), (658153699/1250000000 : ℝ)] ![(43662737094339/100000000000000 : ℝ), (1353330415341/10000000000000 : ℝ), (42803958739371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106897851/200000000 : ℝ)|^1049 ≤ (43662737094339/100000000000000 : ℝ)^793
        have hw : |(106897851/200000000 : ℝ)|=(106897851/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-137802709/625000000 : ℝ)|^1049 ≤ (1353330415341/10000000000000 : ℝ)^793
        have hw : |(-137802709/625000000 : ℝ)|=(137802709/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658153699/1250000000 : ℝ)|^1049 ≤ (42803958739371/100000000000000 : ℝ)^793
        have hw : |(658153699/1250000000 : ℝ)|=(658153699/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s5_2 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344892447/10000000000 : ℝ)*x 0 + (1053045933/2000000000 : ℝ)*x 1 + (-275605423/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344892447/10000000000 : ℝ)^1049 ≤ (43662735981297/100000000000000 : ℝ)^793 := by
    have hnat : (5344892447 : ℕ)^1049*100000000000000^793 ≤ 43662735981297^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344892447 10000000000 43662735981297 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053045933/2000000000 : ℝ)^1049 ≤ (42803959524411/100000000000000 : ℝ)^793 := by
    have hnat : (1053045933 : ℕ)^1049*100000000000000^793 ≤ 42803959524411^793*2000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053045933 2000000000 42803959524411 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275605423/1250000000 : ℝ)^1049 ≤ (13533304478189/100000000000000 : ℝ)^793 := by
    have hnat : (275605423 : ℕ)^1049*100000000000000^793 ≤ 13533304478189^793*1250000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275605423 1250000000 13533304478189 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344892447/10000000000 : ℝ), (1053045933/2000000000 : ℝ), (-275605423/1250000000 : ℝ)] ![(43662735981297/100000000000000 : ℝ), (42803959524411/100000000000000 : ℝ), (13533304478189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344892447/10000000000 : ℝ)|^1049 ≤ (43662735981297/100000000000000 : ℝ)^793
        have hw : |(5344892447/10000000000 : ℝ)|=(5344892447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053045933/2000000000 : ℝ)|^1049 ≤ (42803959524411/100000000000000 : ℝ)^793
        have hw : |(1053045933/2000000000 : ℝ)|=(1053045933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-275605423/1250000000 : ℝ)|^1049 ≤ (13533304478189/100000000000000 : ℝ)^793
        have hw : |(-275605423/1250000000 : ℝ)|=(275605423/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s5_3 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2178315751/5000000000 : ℝ)*x 0 + (4229520573/10000000000 : ℝ)*x 1 + (4487492013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178315751/5000000000 : ℝ)^1049 ≤ (2082283285529/6250000000000 : ℝ)^793 := by
    have hnat : (2178315751 : ℕ)^1049*6250000000000^793 ≤ 2082283285529^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178315751 5000000000 2082283285529 6250000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4229520573/10000000000 : ℝ)^1049 ≤ (16018383610027/50000000000000 : ℝ)^793 := by
    have hnat : (4229520573 : ℕ)^1049*50000000000000^793 ≤ 16018383610027^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229520573 10000000000 16018383610027 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487492013/10000000000 : ℝ)^1049 ≤ (17323350100917/50000000000000 : ℝ)^793 := by
    have hnat : (4487492013 : ℕ)^1049*50000000000000^793 ≤ 17323350100917^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487492013 10000000000 17323350100917 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178315751/5000000000 : ℝ), (4229520573/10000000000 : ℝ), (4487492013/10000000000 : ℝ)] ![(2082283285529/6250000000000 : ℝ), (16018383610027/50000000000000 : ℝ), (17323350100917/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178315751/5000000000 : ℝ)|^1049 ≤ (2082283285529/6250000000000 : ℝ)^793
        have hw : |(2178315751/5000000000 : ℝ)|=(2178315751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4229520573/10000000000 : ℝ)|^1049 ≤ (16018383610027/50000000000000 : ℝ)^793
        have hw : |(4229520573/10000000000 : ℝ)|=(4229520573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4487492013/10000000000 : ℝ)|^1049 ≤ (17323350100917/50000000000000 : ℝ)^793
        have hw : |(4487492013/10000000000 : ℝ)|=(4487492013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s5_4 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-267475013/1250000000 : ℝ)*x 0 + (5265559773/10000000000 : ℝ)*x 1 + (2696565561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267475013/1250000000 : ℝ)^1049 ≤ (13007718325539/100000000000000 : ℝ)^793 := by
    have hnat : (267475013 : ℕ)^1049*100000000000000^793 ≤ 13007718325539^793*1250000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267475013 1250000000 13007718325539 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265559773/10000000000 : ℝ)^1049 ≤ (21403754766363/50000000000000 : ℝ)^793 := by
    have hnat : (5265559773 : ℕ)^1049*50000000000000^793 ≤ 21403754766363^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265559773 10000000000 21403754766363 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696565561/5000000000 : ℝ)^1049 ≤ (44184772126749/100000000000000 : ℝ)^793 := by
    have hnat : (2696565561 : ℕ)^1049*100000000000000^793 ≤ 44184772126749^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696565561 5000000000 44184772126749 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-267475013/1250000000 : ℝ), (5265559773/10000000000 : ℝ), (2696565561/5000000000 : ℝ)] ![(13007718325539/100000000000000 : ℝ), (21403754766363/50000000000000 : ℝ), (44184772126749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-267475013/1250000000 : ℝ)|^1049 ≤ (13007718325539/100000000000000 : ℝ)^793
        have hw : |(-267475013/1250000000 : ℝ)|=(267475013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265559773/10000000000 : ℝ)|^1049 ≤ (21403754766363/50000000000000 : ℝ)^793
        have hw : |(5265559773/10000000000 : ℝ)|=(5265559773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696565561/5000000000 : ℝ)|^1049 ≤ (44184772126749/100000000000000 : ℝ)^793
        have hw : |(2696565561/5000000000 : ℝ)|=(2696565561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s5_5 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2656135219/5000000000 : ℝ)*x 0 + (-129808871/625000000 : ℝ)*x 1 + (5393131117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656135219/5000000000 : ℝ)^1049 ≤ (43310562763317/100000000000000 : ℝ)^793 := by
    have hnat : (2656135219 : ℕ)^1049*100000000000000^793 ≤ 43310562763317^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656135219 5000000000 43310562763317 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129808871/625000000 : ℝ)^1049 ≤ (6252332573013/50000000000000 : ℝ)^793 := by
    have hnat : (129808871 : ℕ)^1049*50000000000000^793 ≤ 6252332573013^793*625000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129808871 625000000 6252332573013 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393131117/10000000000 : ℝ)^1049 ≤ (44184772072561/100000000000000 : ℝ)^793 := by
    have hnat : (5393131117 : ℕ)^1049*100000000000000^793 ≤ 44184772072561^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393131117 10000000000 44184772072561 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656135219/5000000000 : ℝ), (-129808871/625000000 : ℝ), (5393131117/10000000000 : ℝ)] ![(43310562763317/100000000000000 : ℝ), (6252332573013/50000000000000 : ℝ), (44184772072561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656135219/5000000000 : ℝ)|^1049 ≤ (43310562763317/100000000000000 : ℝ)^793
        have hw : |(2656135219/5000000000 : ℝ)|=(2656135219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-129808871/625000000 : ℝ)|^1049 ≤ (6252332573013/50000000000000 : ℝ)^793
        have hw : |(-129808871/625000000 : ℝ)|=(129808871/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393131117/10000000000 : ℝ)|^1049 ≤ (44184772072561/100000000000000 : ℝ)^793
        have hw : |(5393131117/10000000000 : ℝ)|=(5393131117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s5_6 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (132806761/250000000 : ℝ)*x 0 + (5393131117/10000000000 : ℝ)*x 1 + (-1038470967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132806761/250000000 : ℝ)^1049 ≤ (43310562784887/100000000000000 : ℝ)^793 := by
    have hnat : (132806761 : ℕ)^1049*100000000000000^793 ≤ 43310562784887^793*250000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132806761 250000000 43310562784887 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393131117/10000000000 : ℝ)^1049 ≤ (44184772072561/100000000000000 : ℝ)^793 := by
    have hnat : (5393131117 : ℕ)^1049*100000000000000^793 ≤ 44184772072561^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393131117 10000000000 44184772072561 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038470967/5000000000 : ℝ)^1049 ≤ (12504665130097/100000000000000 : ℝ)^793 := by
    have hnat : (1038470967 : ℕ)^1049*100000000000000^793 ≤ 12504665130097^793*5000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038470967 5000000000 12504665130097 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132806761/250000000 : ℝ), (5393131117/10000000000 : ℝ), (-1038470967/5000000000 : ℝ)] ![(43310562784887/100000000000000 : ℝ), (44184772072561/100000000000000 : ℝ), (12504665130097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132806761/250000000 : ℝ)|^1049 ≤ (43310562784887/100000000000000 : ℝ)^793
        have hw : |(132806761/250000000 : ℝ)|=(132806761/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393131117/10000000000 : ℝ)|^1049 ≤ (44184772072561/100000000000000 : ℝ)^793
        have hw : |(5393131117/10000000000 : ℝ)|=(5393131117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1038470967/5000000000 : ℝ)|^1049 ≤ (12504665130097/100000000000000 : ℝ)^793
        have hw : |(-1038470967/5000000000 : ℝ)|=(1038470967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1199_s5_7 (p : ℝ) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4356641661/10000000000 : ℝ)*x 0 + (224341391/500000000 : ℝ)*x 1 + (4230187293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356641661/10000000000 : ℝ)^1049 ≤ (16658317668763/50000000000000 : ℝ)^793 := by
    have hnat : (4356641661 : ℕ)^1049*50000000000000^793 ≤ 16658317668763^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356641661 10000000000 16658317668763 50000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224341391/500000000 : ℝ)^1049 ≤ (34639916848981/100000000000000 : ℝ)^793 := by
    have hnat : (224341391 : ℕ)^1049*100000000000000^793 ≤ 34639916848981^793*500000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224341391 500000000 34639916848981 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230187293/10000000000 : ℝ)^1049 ≤ (32043447803263/100000000000000 : ℝ)^793 := by
    have hnat : (4230187293 : ℕ)^1049*100000000000000^793 ≤ 32043447803263^793*10000000000^1049 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230187293 10000000000 32043447803263 100000000000000 1049 793 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1049/256 : ℝ)) 1049 793 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356641661/10000000000 : ℝ), (224341391/500000000 : ℝ), (4230187293/10000000000 : ℝ)] ![(16658317668763/50000000000000 : ℝ), (34639916848981/100000000000000 : ℝ), (32043447803263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356641661/10000000000 : ℝ)|^1049 ≤ (16658317668763/50000000000000 : ℝ)^793
        have hw : |(4356641661/10000000000 : ℝ)|=(4356641661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224341391/500000000 : ℝ)|^1049 ≤ (34639916848981/100000000000000 : ℝ)^793
        have hw : |(224341391/500000000 : ℝ)|=(224341391/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230187293/10000000000 : ℝ)|^1049 ≤ (32043447803263/100000000000000 : ℝ)^793
        have hw : |(4230187293/10000000000 : ℝ)|=(4230187293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1199_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2849/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (441/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11279/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11279/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11279/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11279/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11279/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11279/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11279/100000 : ℝ) ^ (8391/2048 : ℝ) ≤ (13091621648296309/100000000000000000000 : ℝ) := by
    have hpowers : (11279/100000 : ℝ)^8391 ≤ (13091621648296309/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11279 : ℕ)^8391*100000000000000000000^2048 ≤ 13091621648296309^2048*100000^8391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11279 100000 13091621648296309 100000000000000000000 8391 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11279/100000 : ℝ)) (X := (13091621648296309/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8391/2048 : ℝ) ≤ (33975303986736591/100000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8391 ≤ (33975303986736591/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8391*100000000000000000000^2048 ≤ 33975303986736591^2048*20000^8391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 33975303986736591 100000000000000000000 8391 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (33975303986736591/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013091621648296309/50000000000000000000 : ℝ) ≤ (10000638993878493/10000000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (50013091621648296309/50000000000000000000 : ℝ)^2048 ≤ (10000638993878493/10000000000000000 : ℝ)^8391 := by
      have hnat : (50013091621648296309 : ℕ)^2048*10000000000000000^8391 ≤ 10000638993878493^8391*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013091621648296309 50000000000000000000 10000638993878493 10000000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000638993878493/10000000000000000 : ℝ)) (X := (50013091621648296309/50000000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (1000470669256350329/1000000000000000000 : ℝ) ≤ (10001148562989599/10000000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (1000470669256350329/1000000000000000000 : ℝ)^2048 ≤ (10001148562989599/10000000000000000 : ℝ)^8391 := by
      have hnat : (1000470669256350329 : ℕ)^2048*10000000000000000^8391 ≤ 10001148562989599^8391*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000470669256350329 1000000000000000000 10001148562989599 10000000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001148562989599/10000000000000000 : ℝ)) (X := (1000470669256350329/1000000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033975303986736591/50000000000000000000 : ℝ) ≤ (2000331626420141/2000000000000000 : ℝ) ^ (8391/2048 : ℝ) := by
    have hpowers : (50033975303986736591/50000000000000000000 : ℝ)^2048 ≤ (2000331626420141/2000000000000000 : ℝ)^8391 := by
      have hnat : (50033975303986736591 : ℕ)^2048*2000000000000000^8391 ≤ 2000331626420141^8391*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033975303986736591 50000000000000000000 2000331626420141 2000000000000000 2048 8391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000331626420141/2000000000000000 : ℝ)) (X := (50033975303986736591/50000000000000000000 : ℝ)) (by norm_num) 8391 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13091621648296309/100000000000000000000 : ℝ) ≤ ((184689962536853101/184750000000000000 : ℝ)+2*(254784555553/147800000000000 : ℝ)*(11279/100000 : ℝ))^(8391/2048 : ℝ) := by
    rw [show (184689962536853101/184750000000000000 : ℝ)+2*(254784555553/147800000000000 : ℝ)*(11279/100000 : ℝ)=(10000638993878493/10000000000000000 : ℝ) by norm_num, show 1+2*(13091621648296309/100000000000000000000 : ℝ)=(50013091621648296309/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33975303986736591/100000000000000000000 : ℝ)+(13091621648296309/100000000000000000000 : ℝ) ≤ ((184689962536853101/184750000000000000 : ℝ)+(254784555553/147800000000000 : ℝ)*((2847/20000 : ℝ)+(11279/100000 : ℝ)))^(8391/2048 : ℝ) := by
    rw [show (184689962536853101/184750000000000000 : ℝ)+(254784555553/147800000000000 : ℝ)*((2847/20000 : ℝ)+(11279/100000 : ℝ))=(10001148562989599/10000000000000000 : ℝ) by norm_num, show 1+(33975303986736591/100000000000000000000 : ℝ)+(13091621648296309/100000000000000000000 : ℝ)=(1000470669256350329/1000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33975303986736591/100000000000000000000 : ℝ) ≤ ((184689962536853101/184750000000000000 : ℝ)+2*(254784555553/147800000000000 : ℝ)*(2847/20000 : ℝ))^(8391/2048 : ℝ) := by
    rw [show (184689962536853101/184750000000000000 : ℝ)+2*(254784555553/147800000000000 : ℝ)*(2847/20000 : ℝ)=(2000331626420141/2000000000000000 : ℝ) by norm_num, show 1+2*(33975303986736591/100000000000000000000 : ℝ)=(50033975303986736591/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (184689962536853101/184750000000000000 : ℝ)*(X 1 0+X 2 0)+(254784555553/147800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (184689962536853101/184750000000000000 : ℝ)) (alpha := (254784555553/147800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (184689962536853101/184750000000000000 : ℝ)*(X 0 1+X 2 1)+(254784555553/147800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (184689962536853101/184750000000000000 : ℝ)) (alpha := (254784555553/147800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (184689962536853101/184750000000000000 : ℝ)*(X 0 2+X 1 2)+(254784555553/147800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8391/2048 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (184689962536853101/184750000000000000 : ℝ)) (alpha := (254784555553/147800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-106989751/500000000 : ℝ)*X 0 0+(5393462557/10000000000 : ℝ)*X 0 1+(5265229561/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((106897851/200000000 : ℝ)*X 1 0+(-137802709/625000000 : ℝ)*X 1 1+(658153699/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344892447/10000000000 : ℝ)*X 2 0+(1053045933/2000000000 : ℝ)*X 2 1+(-275605423/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178315751/5000000000 : ℝ)*X 0 0+(4229520573/10000000000 : ℝ)*X 0 1+(4487492013/10000000000 : ℝ)*X 0 2+(2178315751/5000000000 : ℝ)*X 1 0+(4229520573/10000000000 : ℝ)*X 1 1+(4487492013/10000000000 : ℝ)*X 1 2+(2178315751/5000000000 : ℝ)*X 2 0+(4229520573/10000000000 : ℝ)*X 2 1+(4487492013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-267475013/1250000000 : ℝ)*X 0 0+(5265559773/10000000000 : ℝ)*X 0 1+(2696565561/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656135219/5000000000 : ℝ)*X 1 0+(-129808871/625000000 : ℝ)*X 1 1+(5393131117/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132806761/250000000 : ℝ)*X 2 0+(5393131117/10000000000 : ℝ)*X 2 1+(-1038470967/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4356641661/10000000000 : ℝ)*X 0 0+(224341391/500000000 : ℝ)*X 0 1+(4230187293/10000000000 : ℝ)*X 0 2+(4356641661/10000000000 : ℝ)*X 1 0+(224341391/500000000 : ℝ)*X 1 1+(4230187293/10000000000 : ℝ)*X 1 2+(4356641661/10000000000 : ℝ)*X 2 0+(224341391/500000000 : ℝ)*X 2 1+(4230187293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1199_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (985341194117504882581269/144335937500000000000000000000 : ℝ) := by norm_num
    linear_combination (1670928171/100000000000000 : ℝ)*(base19) + (275859391/20000000000000 : ℝ)*(base23) + (37775111/50000000000000 : ℝ)*(lower2) + (248830879/100000000000000 : ℝ)*(upper3) + (52801299/100000000000000 : ℝ)*(upper5) + (2918711687097843/50000000000000 : ℝ)*(major0) + (2918711687097843/50000000000000 : ℝ)*(major1) + (2918711687097843/50000000000000 : ℝ)*(major2) + (7798357912885983/100000000000000 : ℝ)*(sp0) + (1949600133268611/25000000000000 : ℝ)*(sp1) + (7798400824705659/100000000000000 : ℝ)*(sp2) + (3876419195279111/100000000000000 : ℝ)*(sp3) + (5536389579/12500000000000 : ℝ)*(sp4) + (6280388067/25000000000000 : ℝ)*(sp7) + (3876444316831379/100000000000000 : ℝ)*(f.failure) + (1559680440800523/20000000000000 : ℝ)*(f.sum) + (22631277576189/3695000000000000000000000000 : ℝ)*base65 + (41765205939440107/9237500000000000000000000000000 : ℝ)*base68 + (161292046075140107/9237500000000000000000000000000 : ℝ)*base70 + (57353068176440107/9237500000000000000000000000000 : ℝ)*base72 + (4579306190207/1847500000000000000000000000 : ℝ)*base73 + (17891600104122393/9237500000000000000000000000000 : ℝ)*base75 + (89280319559527607/9237500000000000000000000000000 : ℝ)*base78 + (86373935603840107/9237500000000000000000000000000 : ℝ)*base80 + (2931548546983/1847500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (751889/625000000000000000000 : ℝ)*base89 + (751889/625000000000000000000 : ℝ)*base91 + (751889/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1234191488532353403954243/461875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (241189371/50000000000000 : ℝ)*(base19) + (528615749/100000000000000 : ℝ)*(base23) + (5268499/10000000000000 : ℝ)*(upper3) + (9643599/50000000000000 : ℝ)*(lower4) + (54112117/100000000000000 : ℝ)*(upper5) + (293381272520519/5000000000000 : ℝ)*(major0) + (293381272520519/5000000000000 : ℝ)*(major1) + (293381272520519/5000000000000 : ℝ)*(major2) + (2589823647/20000000000000 : ℝ)*(sp1) + (14085631931/100000000000000 : ℝ)*(sp2) + (7838750271616651/100000000000000 : ℝ)*(sp4) + (3919368420059837/50000000000000 : ℝ)*(sp5) + (7838735657368971/100000000000000 : ℝ)*(sp6) + (1948250270066499/50000000000000 : ℝ)*(sp7) + (1948250270066499/50000000000000 : ℝ)*(f.failure) + (7838750271616651/100000000000000 : ℝ)*(f.sum) + (870672754693/184750000000000000000000000 : ℝ)*base66 + (5703276182258081/923750000000000000000000000000 : ℝ)*base68 + (12160365511533169/923750000000000000000000000000 : ℝ)*base69 + (2040804991963169/923750000000000000000000000000 : ℝ)*base71 + (283139530377/73900000000000000000000000 : ℝ)*base74 + (16482967214178169/923750000000000000000000000000 : ℝ)*base75 + (9294647997006919/923750000000000000000000000000 : ℝ)*base77 + (5740432639459331/923750000000000000000000000000 : ℝ)*base80 + (101078924303/73900000000000000000000000 : ℝ)*base82 + (539809/312500000000000000000 : ℝ)*base89 + (539809/312500000000000000000 : ℝ)*base91 + (539809/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1199_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (441/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1199_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1199_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16339/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (233/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (441/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1199_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1199_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1199_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8391/2048 : ℝ) ≤ p) (hpb : p ≤ (1049/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9411691/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16339/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (233/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (441/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1199_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

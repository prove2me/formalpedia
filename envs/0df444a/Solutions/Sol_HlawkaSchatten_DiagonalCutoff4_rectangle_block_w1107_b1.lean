-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1107_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:03:59.292988+00:00
-- url     : https://prove2.me/submissions/8c7399e7-a2c9-4101-ac64-0eb02bc6ead4

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
theorem support_rectangle_w1107_s3_0 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-544882371/2500000000 : ℝ)*x 0 + (5432892801/10000000000 : ℝ)*x 1 + (65358467/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544882371/2500000000 : ℝ)^2075 ≤ (6616020064311/50000000000000 : ℝ)^1563 := by
    have hnat : (544882371 : ℕ)^2075*50000000000000^1563 ≤ 6616020064311^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544882371 2500000000 6616020064311 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432892801/10000000000 : ℝ)^2075 ≤ (44487081297887/100000000000000 : ℝ)^1563 := by
    have hnat : (5432892801 : ℕ)^2075*100000000000000^1563 ≤ 44487081297887^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432892801 10000000000 44487081297887 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65358467/125000000 : ℝ)^2075 ≤ (21140439277627/50000000000000 : ℝ)^1563 := by
    have hnat : (65358467 : ℕ)^2075*50000000000000^1563 ≤ 21140439277627^1563*125000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65358467 125000000 21140439277627 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-544882371/2500000000 : ℝ), (5432892801/10000000000 : ℝ), (65358467/125000000 : ℝ)] ![(6616020064311/50000000000000 : ℝ), (44487081297887/100000000000000 : ℝ), (21140439277627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-544882371/2500000000 : ℝ)|^2075 ≤ (6616020064311/50000000000000 : ℝ)^1563
        have hw : |(-544882371/2500000000 : ℝ)|=(544882371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432892801/10000000000 : ℝ)|^2075 ≤ (44487081297887/100000000000000 : ℝ)^1563
        have hw : |(5432892801/10000000000 : ℝ)|=(5432892801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65358467/125000000 : ℝ)|^2075 ≤ (21140439277627/50000000000000 : ℝ)^1563
        have hw : |(65358467/125000000 : ℝ)|=(65358467/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s3_1 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5354649883/10000000000 : ℝ)*x 0 + (-570999997/2500000000 : ℝ)*x 1 + (5228677453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354649883/10000000000 : ℝ)^2075 ≤ (43638530254517/100000000000000 : ℝ)^1563 := by
    have hnat : (5354649883 : ℕ)^2075*100000000000000^1563 ≤ 43638530254517^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354649883 10000000000 43638530254517 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (570999997/2500000000 : ℝ)^2075 ≤ (14080590184317/100000000000000 : ℝ)^1563 := by
    have hnat : (570999997 : ℕ)^2075*100000000000000^1563 ≤ 14080590184317^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570999997 2500000000 14080590184317 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228677453/10000000000 : ℝ)^2075 ≤ (4228087955363/10000000000000 : ℝ)^1563 := by
    have hnat : (5228677453 : ℕ)^2075*10000000000000^1563 ≤ 4228087955363^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228677453 10000000000 4228087955363 10000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354649883/10000000000 : ℝ), (-570999997/2500000000 : ℝ), (5228677453/10000000000 : ℝ)] ![(43638530254517/100000000000000 : ℝ), (14080590184317/100000000000000 : ℝ), (4228087955363/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354649883/10000000000 : ℝ)|^2075 ≤ (43638530254517/100000000000000 : ℝ)^1563
        have hw : |(5354649883/10000000000 : ℝ)|=(5354649883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-570999997/2500000000 : ℝ)|^2075 ≤ (14080590184317/100000000000000 : ℝ)^1563
        have hw : |(-570999997/2500000000 : ℝ)|=(570999997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228677453/10000000000 : ℝ)|^2075 ≤ (4228087955363/10000000000000 : ℝ)^1563
        have hw : |(5228677453/10000000000 : ℝ)|=(5228677453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s3_2 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (167332813/312500000 : ℝ)*x 0 + (104573551/200000000 : ℝ)*x 1 + (-570999921/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167332813/312500000 : ℝ)^2075 ≤ (1090963292337/2500000000000 : ℝ)^1563 := by
    have hnat : (167332813 : ℕ)^2075*2500000000000^1563 ≤ 1090963292337^1563*312500000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167332813 312500000 1090963292337 2500000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104573551/200000000 : ℝ)^2075 ≤ (42280880594947/100000000000000 : ℝ)^1563 := by
    have hnat : (104573551 : ℕ)^2075*100000000000000^1563 ≤ 42280880594947^1563*200000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104573551 200000000 42280880594947 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (570999921/2500000000 : ℝ)^2075 ≤ (3520146924069/25000000000000 : ℝ)^1563 := by
    have hnat : (570999921 : ℕ)^2075*25000000000000^1563 ≤ 3520146924069^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570999921 2500000000 3520146924069 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167332813/312500000 : ℝ), (104573551/200000000 : ℝ), (-570999921/2500000000 : ℝ)] ![(1090963292337/2500000000000 : ℝ), (42280880594947/100000000000000 : ℝ), (3520146924069/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167332813/312500000 : ℝ)|^2075 ≤ (1090963292337/2500000000000 : ℝ)^1563
        have hw : |(167332813/312500000 : ℝ)|=(167332813/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104573551/200000000 : ℝ)|^2075 ≤ (42280880594947/100000000000000 : ℝ)^1563
        have hw : |(104573551/200000000 : ℝ)|=(104573551/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-570999921/2500000000 : ℝ)|^2075 ≤ (3520146924069/25000000000000 : ℝ)^1563
        have hw : |(-570999921/2500000000 : ℝ)|=(570999921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s3_3 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2183567071/5000000000 : ℝ)*x 0 + (2085027953/5000000000 : ℝ)*x 1 + (1143387263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183567071/5000000000 : ℝ)^2075 ≤ (104036053513/312500000000 : ℝ)^1563 := by
    have hnat : (2183567071 : ℕ)^2075*312500000000^1563 ≤ 104036053513^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183567071 5000000000 104036053513 312500000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085027953/5000000000 : ℝ)^2075 ≤ (31311926296459/100000000000000 : ℝ)^1563 := by
    have hnat : (2085027953 : ℕ)^2075*100000000000000^1563 ≤ 31311926296459^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085027953 5000000000 31311926296459 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1143387263/2500000000 : ℝ)^2075 ≤ (35396536565973/100000000000000 : ℝ)^1563 := by
    have hnat : (1143387263 : ℕ)^2075*100000000000000^1563 ≤ 35396536565973^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143387263 2500000000 35396536565973 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183567071/5000000000 : ℝ), (2085027953/5000000000 : ℝ), (1143387263/2500000000 : ℝ)] ![(104036053513/312500000000 : ℝ), (31311926296459/100000000000000 : ℝ), (35396536565973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183567071/5000000000 : ℝ)|^2075 ≤ (104036053513/312500000000 : ℝ)^1563
        have hw : |(2183567071/5000000000 : ℝ)|=(2183567071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085027953/5000000000 : ℝ)|^2075 ≤ (31311926296459/100000000000000 : ℝ)^1563
        have hw : |(2085027953/5000000000 : ℝ)|=(2085027953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1143387263/2500000000 : ℝ)|^2075 ≤ (35396536565973/100000000000000 : ℝ)^1563
        have hw : |(1143387263/2500000000 : ℝ)|=(1143387263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s3_4 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1089774653/5000000000 : ℝ)*x 0 + (2614744923/5000000000 : ℝ)*x 1 + (5432075711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089774653/5000000000 : ℝ)^2075 ≤ (6616099944909/50000000000000 : ℝ)^1563 := by
    have hnat : (1089774653 : ℕ)^2075*50000000000000^1563 ≤ 6616099944909^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089774653 5000000000 6616099944909 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614744923/5000000000 : ℝ)^2075 ≤ (42289600999877/100000000000000 : ℝ)^1563 := by
    have hnat : (2614744923 : ℕ)^2075*100000000000000^1563 ≤ 42289600999877^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614744923 5000000000 42289600999877 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432075711/10000000000 : ℝ)^2075 ≤ (22239099543323/50000000000000 : ℝ)^1563 := by
    have hnat : (5432075711 : ℕ)^2075*50000000000000^1563 ≤ 22239099543323^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432075711 10000000000 22239099543323 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1089774653/5000000000 : ℝ), (2614744923/5000000000 : ℝ), (5432075711/10000000000 : ℝ)] ![(6616099944909/50000000000000 : ℝ), (42289600999877/100000000000000 : ℝ), (22239099543323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1089774653/5000000000 : ℝ)|^2075 ≤ (6616099944909/50000000000000 : ℝ)^1563
        have hw : |(-1089774653/5000000000 : ℝ)|=(1089774653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614744923/5000000000 : ℝ)|^2075 ≤ (42289600999877/100000000000000 : ℝ)^1563
        have hw : |(2614744923/5000000000 : ℝ)|=(2614744923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432075711/10000000000 : ℝ)|^2075 ≤ (22239099543323/50000000000000 : ℝ)^1563
        have hw : |(5432075711/10000000000 : ℝ)|=(5432075711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s3_5 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (212121877/400000000 : ℝ)*x 0 + (-2080601561/10000000000 : ℝ)*x 1 + (543207591/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212121877/400000000 : ℝ)^2075 ≤ (21540553409919/50000000000000 : ℝ)^1563 := by
    have hnat : (212121877 : ℕ)^2075*50000000000000^1563 ≤ 21540553409919^1563*400000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212121877 400000000 21540553409919 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080601561/10000000000 : ℝ)^2075 ≤ (12440691922817/100000000000000 : ℝ)^1563 := by
    have hnat : (2080601561 : ℕ)^2075*100000000000000^1563 ≤ 12440691922817^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080601561 10000000000 12440691922817 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543207591/1000000000 : ℝ)^2075 ≤ (4447820124983/10000000000000 : ℝ)^1563 := by
    have hnat : (543207591 : ℕ)^2075*10000000000000^1563 ≤ 4447820124983^1563*1000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543207591 1000000000 4447820124983 10000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212121877/400000000 : ℝ), (-2080601561/10000000000 : ℝ), (543207591/1000000000 : ℝ)] ![(21540553409919/50000000000000 : ℝ), (12440691922817/100000000000000 : ℝ), (4447820124983/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212121877/400000000 : ℝ)|^2075 ≤ (21540553409919/50000000000000 : ℝ)^1563
        have hw : |(212121877/400000000 : ℝ)|=(212121877/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2080601561/10000000000 : ℝ)|^2075 ≤ (12440691922817/100000000000000 : ℝ)^1563
        have hw : |(-2080601561/10000000000 : ℝ)|=(2080601561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543207591/1000000000 : ℝ)|^2075 ≤ (4447820124983/10000000000000 : ℝ)^1563
        have hw : |(543207591/1000000000 : ℝ)|=(543207591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s3_6 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1060609397/2000000000 : ℝ)*x 0 + (5432075727/10000000000 : ℝ)*x 1 + (-2080601729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060609397/2000000000 : ℝ)^2075 ≤ (43081107466939/100000000000000 : ℝ)^1563 := by
    have hnat : (1060609397 : ℕ)^2075*100000000000000^1563 ≤ 43081107466939^1563*2000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060609397 2000000000 43081107466939 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432075727/10000000000 : ℝ)^2075 ≤ (4447819926057/10000000000000 : ℝ)^1563 := by
    have hnat : (5432075727 : ℕ)^2075*10000000000000^1563 ≤ 4447819926057^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432075727 10000000000 4447819926057 10000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2080601729/10000000000 : ℝ)^2075 ≤ (12440693256413/100000000000000 : ℝ)^1563 := by
    have hnat : (2080601729 : ℕ)^2075*100000000000000^1563 ≤ 12440693256413^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080601729 10000000000 12440693256413 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060609397/2000000000 : ℝ), (5432075727/10000000000 : ℝ), (-2080601729/10000000000 : ℝ)] ![(43081107466939/100000000000000 : ℝ), (4447819926057/10000000000000 : ℝ), (12440693256413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060609397/2000000000 : ℝ)|^2075 ≤ (43081107466939/100000000000000 : ℝ)^1563
        have hw : |(1060609397/2000000000 : ℝ)|=(1060609397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432075727/10000000000 : ℝ)|^2075 ≤ (4447819926057/10000000000000 : ℝ)^1563
        have hw : |(5432075727/10000000000 : ℝ)|=(5432075727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2080601729/10000000000 : ℝ)|^2075 ≤ (12440693256413/100000000000000 : ℝ)^1563
        have hw : |(-2080601729/10000000000 : ℝ)|=(2080601729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s3_7 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4367173269/10000000000 : ℝ)*x 0 + (2285972283/5000000000 : ℝ)*x 1 + (1042917439/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367173269/10000000000 : ℝ)^2075 ≤ (16645966552251/50000000000000 : ℝ)^1563 := by
    have hnat : (4367173269 : ℕ)^2075*50000000000000^1563 ≤ 16645966552251^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367173269 10000000000 16645966552251 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2285972283/5000000000 : ℝ)^2075 ≤ (35380051999641/100000000000000 : ℝ)^1563 := by
    have hnat : (2285972283 : ℕ)^2075*100000000000000^1563 ≤ 35380051999641^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285972283 5000000000 35380051999641 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042917439/2500000000 : ℝ)^2075 ≤ (15664007438403/50000000000000 : ℝ)^1563 := by
    have hnat : (1042917439 : ℕ)^2075*50000000000000^1563 ≤ 15664007438403^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042917439 2500000000 15664007438403 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367173269/10000000000 : ℝ), (2285972283/5000000000 : ℝ), (1042917439/2500000000 : ℝ)] ![(16645966552251/50000000000000 : ℝ), (35380051999641/100000000000000 : ℝ), (15664007438403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367173269/10000000000 : ℝ)|^2075 ≤ (16645966552251/50000000000000 : ℝ)^1563
        have hw : |(4367173269/10000000000 : ℝ)|=(4367173269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2285972283/5000000000 : ℝ)|^2075 ≤ (35380051999641/100000000000000 : ℝ)^1563
        have hw : |(2285972283/5000000000 : ℝ)|=(2285972283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042917439/2500000000 : ℝ)|^2075 ≤ (15664007438403/50000000000000 : ℝ)^1563
        have hw : |(1042917439/2500000000 : ℝ)|=(1042917439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1107_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16609/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8909/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (329/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14849/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16609/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8909/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16609/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8909/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16609/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8909/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16609/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8909/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16609/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8909/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16609/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8909/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8909/100000 : ℝ) ^ (8299/2048 : ℝ) ≤ (5551987773817907/100000000000000000000 : ℝ) := by
    have hpowers : (8909/100000 : ℝ)^8299 ≤ (5551987773817907/100000000000000000000 : ℝ)^2048 := by
      have hnat : (8909 : ℕ)^8299*100000000000000000000^2048 ≤ 5551987773817907^2048*100000^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8909 100000 5551987773817907 100000000000000000000 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8909/100000 : ℝ)) (X := (5551987773817907/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16609/100000 : ℝ) ^ (8299/2048 : ℝ) ≤ (6928511354335317/10000000000000000000 : ℝ) := by
    have hpowers : (16609/100000 : ℝ)^8299 ≤ (6928511354335317/10000000000000000000 : ℝ)^2048 := by
      have hnat : (16609 : ℕ)^8299*10000000000000000000^2048 ≤ 6928511354335317^2048*100000^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16609 100000 6928511354335317 10000000000000000000 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16609/100000 : ℝ)) (X := (6928511354335317/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005551987773817907/50000000000000000000 : ℝ) ≤ (2000054801761617/2000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (50005551987773817907/50000000000000000000 : ℝ)^2048 ≤ (2000054801761617/2000000000000000 : ℝ)^8299 := by
      have hnat : (50005551987773817907 : ℕ)^2048*2000000000000000^8299 ≤ 2000054801761617^8299*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005551987773817907 50000000000000000000 2000054801761617 2000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000054801761617/2000000000000000 : ℝ)) (X := (50005551987773817907/50000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100074837101317171077/100000000000000000000 : ℝ) ≤ (2500461571288651/2500000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (100074837101317171077/100000000000000000000 : ℝ)^2048 ≤ (2500461571288651/2500000000000000 : ℝ)^8299 := by
      have hnat : (100074837101317171077 : ℕ)^2048*2500000000000000^8299 ≤ 2500461571288651^8299*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100074837101317171077 100000000000000000000 2500461571288651 2500000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500461571288651/2500000000000000 : ℝ)) (X := (100074837101317171077/100000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5006928511354335317/5000000000000000000 : ℝ) ≤ (10003418561501123/10000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (5006928511354335317/5000000000000000000 : ℝ)^2048 ≤ (10003418561501123/10000000000000000 : ℝ)^8299 := by
      have hnat : (5006928511354335317 : ℕ)^2048*10000000000000000^8299 ≤ 10003418561501123^8299*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5006928511354335317 5000000000000000000 10003418561501123 10000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003418561501123/10000000000000000 : ℝ)) (X := (5006928511354335317/5000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5551987773817907/100000000000000000000 : ℝ) ≤ ((38487047523939989479/38500000000000000000 : ℝ)+2*(1572276346519/770000000000000 : ℝ)*(8909/100000 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (38487047523939989479/38500000000000000000 : ℝ)+2*(1572276346519/770000000000000 : ℝ)*(8909/100000 : ℝ)=(2000054801761617/2000000000000000 : ℝ) by norm_num, show 1+2*(5551987773817907/100000000000000000000 : ℝ)=(50005551987773817907/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6928511354335317/10000000000000000000 : ℝ)+(5551987773817907/100000000000000000000 : ℝ) ≤ ((38487047523939989479/38500000000000000000 : ℝ)+(1572276346519/770000000000000 : ℝ)*((16609/100000 : ℝ)+(8909/100000 : ℝ)))^(8299/2048 : ℝ) := by
    rw [show (38487047523939989479/38500000000000000000 : ℝ)+(1572276346519/770000000000000 : ℝ)*((16609/100000 : ℝ)+(8909/100000 : ℝ))=(2500461571288651/2500000000000000 : ℝ) by norm_num, show 1+(6928511354335317/10000000000000000000 : ℝ)+(5551987773817907/100000000000000000000 : ℝ)=(100074837101317171077/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6928511354335317/10000000000000000000 : ℝ) ≤ ((38487047523939989479/38500000000000000000 : ℝ)+2*(1572276346519/770000000000000 : ℝ)*(16609/100000 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (38487047523939989479/38500000000000000000 : ℝ)+2*(1572276346519/770000000000000 : ℝ)*(16609/100000 : ℝ)=(10003418561501123/10000000000000000 : ℝ) by norm_num, show 1+2*(6928511354335317/10000000000000000000 : ℝ)=(5006928511354335317/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38487047523939989479/38500000000000000000 : ℝ)*(X 1 0+X 2 0)+(1572276346519/770000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (8909/100000 : ℝ)) (hi := (16609/100000 : ℝ)) (c := (38487047523939989479/38500000000000000000 : ℝ)) (alpha := (1572276346519/770000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38487047523939989479/38500000000000000000 : ℝ)*(X 0 1+X 2 1)+(1572276346519/770000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (8909/100000 : ℝ)) (hi := (16609/100000 : ℝ)) (c := (38487047523939989479/38500000000000000000 : ℝ)) (alpha := (1572276346519/770000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38487047523939989479/38500000000000000000 : ℝ)*(X 0 2+X 1 2)+(1572276346519/770000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (8909/100000 : ℝ)) (hi := (16609/100000 : ℝ)) (c := (38487047523939989479/38500000000000000000 : ℝ)) (alpha := (1572276346519/770000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-544882371/2500000000 : ℝ)*X 0 0+(5432892801/10000000000 : ℝ)*X 0 1+(65358467/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354649883/10000000000 : ℝ)*X 1 0+(-570999997/2500000000 : ℝ)*X 1 1+(5228677453/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167332813/312500000 : ℝ)*X 2 0+(104573551/200000000 : ℝ)*X 2 1+(-570999921/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2183567071/5000000000 : ℝ)*X 0 0+(2085027953/5000000000 : ℝ)*X 0 1+(1143387263/2500000000 : ℝ)*X 0 2+(2183567071/5000000000 : ℝ)*X 1 0+(2085027953/5000000000 : ℝ)*X 1 1+(1143387263/2500000000 : ℝ)*X 1 2+(2183567071/5000000000 : ℝ)*X 2 0+(2085027953/5000000000 : ℝ)*X 2 1+(1143387263/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1089774653/5000000000 : ℝ)*X 0 0+(2614744923/5000000000 : ℝ)*X 0 1+(5432075711/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212121877/400000000 : ℝ)*X 1 0+(-2080601561/10000000000 : ℝ)*X 1 1+(543207591/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060609397/2000000000 : ℝ)*X 2 0+(5432075727/10000000000 : ℝ)*X 2 1+(-2080601729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4367173269/10000000000 : ℝ)*X 0 0+(2285972283/5000000000 : ℝ)*X 0 1+(1042917439/2500000000 : ℝ)*X 0 2+(4367173269/10000000000 : ℝ)*X 1 0+(2285972283/5000000000 : ℝ)*X 1 1+(1042917439/2500000000 : ℝ)*X 1 2+(4367173269/10000000000 : ℝ)*X 2 0+(2285972283/5000000000 : ℝ)*X 2 1+(1042917439/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (197260527525205358023107909/25000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (523371067/25000000000000 : ℝ)*(base19) + (981652497/50000000000000 : ℝ)*(base23) + (33708703/25000000000000 : ℝ)*(lower2) + (63053293/50000000000000 : ℝ)*(upper3) + (265847367/100000000000000 : ℝ)*(upper5) + (3687632482948611/100000000000000 : ℝ)*(major0) + (3687632482948611/100000000000000 : ℝ)*(major1) + (3687632482948611/100000000000000 : ℝ)*(major2) + (1224206649010221/25000000000000 : ℝ)*(sp0) + (1224217412643029/25000000000000 : ℝ)*(sp1) + (489686978075139/10000000000000 : ℝ)*(sp2) + (619593771410747/25000000000000 : ℝ)*(sp3) + (90296031/200000000000 : ℝ)*(sp4) + (3574636761/20000000000000 : ℝ)*(sp7) + (1239196479413397/50000000000000 : ℝ)*(f.failure) + (76513621000881/1562500000000 : ℝ)*(f.sum) + (198760406687391/38500000000000000000000000000 : ℝ)*base66 + (36990356289293113669/3850000000000000000000000000000000 : ℝ)*base67 + (17868846751393113669/3850000000000000000000000000000000 : ℝ)*base69 + (32866882804656886331/3850000000000000000000000000000000 : ℝ)*base72 + (271672318960109/38500000000000000000000000000 : ℝ)*base73 + (24517820590593113669/3850000000000000000000000000000000 : ℝ)*base75 + (14129163080856886331/3850000000000000000000000000000000 : ℝ)*base78 + (10277495437693113669/3850000000000000000000000000000000 : ℝ)*base79 + (267280160189109/38500000000000000000000000000 : ℝ)*base81 + (1668447/200000000000000000000 : ℝ)*base89 + (1668447/200000000000000000000 : ℝ)*base91 + (1668447/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (139608897112968514881753/38500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78829521/12500000000000 : ℝ)*(base19) + (441133643/50000000000000 : ℝ)*(base23) + (117600167/100000000000000 : ℝ)*(upper3) + (95050137/100000000000000 : ℝ)*(lower4) + (8677593/50000000000000 : ℝ)*(upper5) + (3717229350748171/100000000000000 : ℝ)*(major0) + (3717229350748171/100000000000000 : ℝ)*(major1) + (3717229350748171/100000000000000 : ℝ)*(major2) + (13210499011/100000000000000 : ℝ)*(sp1) + (7455382757/50000000000000 : ℝ)*(sp2) + (2468087043648037/50000000000000 : ℝ)*(sp4) + (987232049232179/20000000000000 : ℝ)*(sp5) + (2468079147131637/50000000000000 : ℝ)*(sp6) + (624571123331689/25000000000000 : ℝ)*(sp7) + (624571123331689/25000000000000 : ℝ)*(f.failure) + (2468087043648037/50000000000000 : ℝ)*(f.sum) + (59325636253251/38500000000000000000000000000 : ℝ)*base66 + (38222874662855942909/3850000000000000000000000000000000 : ℝ)*base67 + (12338319289644057091/3850000000000000000000000000000000 : ℝ)*base70 + (22713240322655942909/3850000000000000000000000000000000 : ℝ)*base71 + (164668202546249/38500000000000000000000000000 : ℝ)*base73 + (20681191592794057091/3850000000000000000000000000000000 : ℝ)*base76 + (2745163247555942909/3850000000000000000000000000000000 : ℝ)*base77 + (15023766069044057091/3850000000000000000000000000000000 : ℝ)*base80 + (140542012727749/38500000000000000000000000000 : ℝ)*base81 + (831461/100000000000000000000 : ℝ)*base90 + (831461/100000000000000000000 : ℝ)*base92 + (831461/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1107_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16609/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8909/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (329/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14849/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1107_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1107_s4_0 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2182827543/10000000000 : ℝ)*x 0 + (5403626047/10000000000 : ℝ)*x 1 + (16424337/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182827543/10000000000 : ℝ)^2075 ≤ (13258628344211/100000000000000 : ℝ)^1563 := by
    have hnat : (2182827543 : ℕ)^2075*100000000000000^1563 ≤ 13258628344211^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182827543 10000000000 13258628344211 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403626047/10000000000 : ℝ)^2075 ≤ (1380287782211/3125000000000 : ℝ)^1563 := by
    have hnat : (5403626047 : ℕ)^2075*3125000000000^1563 ≤ 1380287782211^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403626047 10000000000 1380287782211 3125000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16424337/31250000 : ℝ)^2075 ≤ (21286081308443/50000000000000 : ℝ)^1563 := by
    have hnat : (16424337 : ℕ)^2075*50000000000000^1563 ≤ 21286081308443^1563*31250000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16424337 31250000 21286081308443 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2182827543/10000000000 : ℝ), (5403626047/10000000000 : ℝ), (16424337/31250000 : ℝ)] ![(13258628344211/100000000000000 : ℝ), (1380287782211/3125000000000 : ℝ), (21286081308443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2182827543/10000000000 : ℝ)|^2075 ≤ (13258628344211/100000000000000 : ℝ)^1563
        have hw : |(-2182827543/10000000000 : ℝ)|=(2182827543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403626047/10000000000 : ℝ)|^2075 ≤ (1380287782211/3125000000000 : ℝ)^1563
        have hw : |(5403626047/10000000000 : ℝ)|=(5403626047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16424337/31250000 : ℝ)|^2075 ≤ (21286081308443/50000000000000 : ℝ)^1563
        have hw : |(16424337/31250000 : ℝ)|=(16424337/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s4_1 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347366847/10000000000 : ℝ)*x 0 + (-282248333/1250000000 : ℝ)*x 1 + (2627893937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347366847/10000000000 : ℝ)^2075 ≤ (21779875322303/50000000000000 : ℝ)^1563 := by
    have hnat : (5347366847 : ℕ)^2075*50000000000000^1563 ≤ 21779875322303^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347366847 10000000000 21779875322303 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282248333/1250000000 : ℝ)^2075 ≤ (6934043180883/50000000000000 : ℝ)^1563 := by
    have hnat : (282248333 : ℕ)^2075*50000000000000^1563 ≤ 6934043180883^1563*1250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282248333 1250000000 6934043180883 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627893937/5000000000 : ℝ)^2075 ≤ (21286081491251/50000000000000 : ℝ)^1563 := by
    have hnat : (2627893937 : ℕ)^2075*50000000000000^1563 ≤ 21286081491251^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627893937 5000000000 21286081491251 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347366847/10000000000 : ℝ), (-282248333/1250000000 : ℝ), (2627893937/5000000000 : ℝ)] ![(21779875322303/50000000000000 : ℝ), (6934043180883/50000000000000 : ℝ), (21286081491251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347366847/10000000000 : ℝ)|^2075 ≤ (21779875322303/50000000000000 : ℝ)^1563
        have hw : |(5347366847/10000000000 : ℝ)|=(5347366847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-282248333/1250000000 : ℝ)|^2075 ≤ (6934043180883/50000000000000 : ℝ)^1563
        have hw : |(-282248333/1250000000 : ℝ)|=(282248333/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627893937/5000000000 : ℝ)|^2075 ≤ (21286081491251/50000000000000 : ℝ)^1563
        have hw : |(2627893937/5000000000 : ℝ)|=(2627893937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s4_2 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673683587/5000000000 : ℝ)*x 0 + (5255787699/10000000000 : ℝ)*x 1 + (-2257986461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673683587/5000000000 : ℝ)^2075 ≤ (10889938545233/25000000000000 : ℝ)^1563 := by
    have hnat : (2673683587 : ℕ)^2075*25000000000000^1563 ≤ 10889938545233^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673683587 5000000000 10889938545233 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255787699/10000000000 : ℝ)^2075 ≤ (10643040275163/25000000000000 : ℝ)^1563 := by
    have hnat : (5255787699 : ℕ)^2075*25000000000000^1563 ≤ 10643040275163^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255787699 10000000000 10643040275163 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257986461/10000000000 : ℝ)^2075 ≤ (13868084706567/100000000000000 : ℝ)^1563 := by
    have hnat : (2257986461 : ℕ)^2075*100000000000000^1563 ≤ 13868084706567^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257986461 10000000000 13868084706567 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673683587/5000000000 : ℝ), (5255787699/10000000000 : ℝ), (-2257986461/10000000000 : ℝ)] ![(10889938545233/25000000000000 : ℝ), (10643040275163/25000000000000 : ℝ), (13868084706567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673683587/5000000000 : ℝ)|^2075 ≤ (10889938545233/25000000000000 : ℝ)^1563
        have hw : |(2673683587/5000000000 : ℝ)|=(2673683587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255787699/10000000000 : ℝ)|^2075 ≤ (10643040275163/25000000000000 : ℝ)^1563
        have hw : |(5255787699/10000000000 : ℝ)|=(5255787699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2257986461/10000000000 : ℝ)|^2075 ≤ (13868084706567/100000000000000 : ℝ)^1563
        have hw : |(-2257986461/10000000000 : ℝ)|=(2257986461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s4_3 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4369098573/10000000000 : ℝ)*x 0 + (105637371/250000000 : ℝ)*x 1 + (2258799013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369098573/10000000000 : ℝ)^2075 ≤ (6662283871899/20000000000000 : ℝ)^1563 := by
    have hnat : (4369098573 : ℕ)^2075*20000000000000^1563 ≤ 6662283871899^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369098573 10000000000 6662283871899 20000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105637371/250000000 : ℝ)^2075 ≤ (31865765565357/100000000000000 : ℝ)^1563 := by
    have hnat : (105637371 : ℕ)^2075*100000000000000^1563 ≤ 31865765565357^1563*250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105637371 250000000 31865765565357 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2258799013/5000000000 : ℝ)^2075 ≤ (34822815061993/100000000000000 : ℝ)^1563 := by
    have hnat : (2258799013 : ℕ)^2075*100000000000000^1563 ≤ 34822815061993^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258799013 5000000000 34822815061993 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369098573/10000000000 : ℝ), (105637371/250000000 : ℝ), (2258799013/5000000000 : ℝ)] ![(6662283871899/20000000000000 : ℝ), (31865765565357/100000000000000 : ℝ), (34822815061993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369098573/10000000000 : ℝ)|^2075 ≤ (6662283871899/20000000000000 : ℝ)^1563
        have hw : |(4369098573/10000000000 : ℝ)|=(4369098573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105637371/250000000 : ℝ)|^2075 ≤ (31865765565357/100000000000000 : ℝ)^1563
        have hw : |(105637371/250000000 : ℝ)|=(105637371/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2258799013/5000000000 : ℝ)|^2075 ≤ (34822815061993/100000000000000 : ℝ)^1563
        have hw : |(2258799013/5000000000 : ℝ)|=(2258799013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s4_4 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-272854469/1250000000 : ℝ)*x 0 + (5256213891/10000000000 : ℝ)*x 1 + (2701598869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272854469/1250000000 : ℝ)^2075 ≤ (3314673634941/25000000000000 : ℝ)^1563 := by
    have hnat : (272854469 : ℕ)^2075*25000000000000^1563 ≤ 3314673634941^1563*1250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272854469 1250000000 3314673634941 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5256213891/10000000000 : ℝ)^2075 ≤ (4257674418729/10000000000000 : ℝ)^1563 := by
    have hnat : (5256213891 : ℕ)^2075*10000000000000^1563 ≤ 4257674418729^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256213891 10000000000 4257674418729 10000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701598869/5000000000 : ℝ)^2075 ≤ (22082280628277/50000000000000 : ℝ)^1563 := by
    have hnat : (2701598869 : ℕ)^2075*50000000000000^1563 ≤ 22082280628277^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701598869 5000000000 22082280628277 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-272854469/1250000000 : ℝ), (5256213891/10000000000 : ℝ), (2701598869/5000000000 : ℝ)] ![(3314673634941/25000000000000 : ℝ), (4257674418729/10000000000000 : ℝ), (22082280628277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-272854469/1250000000 : ℝ)|^2075 ≤ (3314673634941/25000000000000 : ℝ)^1563
        have hw : |(-272854469/1250000000 : ℝ)|=(272854469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5256213891/10000000000 : ℝ)|^2075 ≤ (4257674418729/10000000000000 : ℝ)^1563
        have hw : |(5256213891/10000000000 : ℝ)|=(5256213891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701598869/5000000000 : ℝ)|^2075 ≤ (22082280628277/50000000000000 : ℝ)^1563
        have hw : |(2701598869/5000000000 : ℝ)|=(2701598869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s4_5 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2655006109/5000000000 : ℝ)*x 0 + (-42211527/200000000 : ℝ)*x 1 + (2701598941/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655006109/5000000000 : ℝ)^2075 ≤ (43156243722163/100000000000000 : ℝ)^1563 := by
    have hnat : (2655006109 : ℕ)^2075*100000000000000^1563 ≤ 43156243722163^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655006109 5000000000 43156243722163 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42211527/200000000 : ℝ)^2075 ≤ (1267919345247/10000000000000 : ℝ)^1563 := by
    have hnat : (42211527 : ℕ)^2075*10000000000000^1563 ≤ 1267919345247^1563*200000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42211527 200000000 1267919345247 10000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701598941/5000000000 : ℝ)^2075 ≤ (44164562819143/100000000000000 : ℝ)^1563 := by
    have hnat : (2701598941 : ℕ)^2075*100000000000000^1563 ≤ 44164562819143^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701598941 5000000000 44164562819143 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655006109/5000000000 : ℝ), (-42211527/200000000 : ℝ), (2701598941/5000000000 : ℝ)] ![(43156243722163/100000000000000 : ℝ), (1267919345247/10000000000000 : ℝ), (44164562819143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655006109/5000000000 : ℝ)|^2075 ≤ (43156243722163/100000000000000 : ℝ)^1563
        have hw : |(2655006109/5000000000 : ℝ)|=(2655006109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-42211527/200000000 : ℝ)|^2075 ≤ (1267919345247/10000000000000 : ℝ)^1563
        have hw : |(-42211527/200000000 : ℝ)|=(42211527/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701598941/5000000000 : ℝ)|^2075 ≤ (44164562819143/100000000000000 : ℝ)^1563
        have hw : |(2701598941/5000000000 : ℝ)|=(2701598941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s4_6 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2655006213/5000000000 : ℝ)*x 0 + (2701598879/5000000000 : ℝ)*x 1 + (-1055288119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655006213/5000000000 : ℝ)^2075 ≤ (4315624596641/10000000000000 : ℝ)^1563 := by
    have hnat : (2655006213 : ℕ)^2075*10000000000000^1563 ≤ 4315624596641^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655006213 5000000000 4315624596641 10000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701598879/5000000000 : ℝ)^2075 ≤ (2208228073679/5000000000000 : ℝ)^1563 := by
    have hnat : (2701598879 : ℕ)^2075*5000000000000^1563 ≤ 2208228073679^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701598879 5000000000 2208228073679 5000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055288119/5000000000 : ℝ)^2075 ≤ (12679192559231/100000000000000 : ℝ)^1563 := by
    have hnat : (1055288119 : ℕ)^2075*100000000000000^1563 ≤ 12679192559231^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055288119 5000000000 12679192559231 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655006213/5000000000 : ℝ), (2701598879/5000000000 : ℝ), (-1055288119/5000000000 : ℝ)] ![(4315624596641/10000000000000 : ℝ), (2208228073679/5000000000000 : ℝ), (12679192559231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655006213/5000000000 : ℝ)|^2075 ≤ (4315624596641/10000000000000 : ℝ)^1563
        have hw : |(2655006213/5000000000 : ℝ)|=(2655006213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701598879/5000000000 : ℝ)|^2075 ≤ (2208228073679/5000000000000 : ℝ)^1563
        have hw : |(2701598879/5000000000 : ℝ)|=(2701598879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1055288119/5000000000 : ℝ)|^2075 ≤ (12679192559231/100000000000000 : ℝ)^1563
        have hw : |(-1055288119/5000000000 : ℝ)|=(1055288119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s4_7 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1092278373/2500000000 : ℝ)*x 0 + (4516755257/10000000000 : ℝ)*x 1 + (528292641/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092278373/2500000000 : ℝ)^2075 ≤ (832789259191/2500000000000 : ℝ)^1563 := by
    have hnat : (1092278373 : ℕ)^2075*2500000000000^1563 ≤ 832789259191^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092278373 2500000000 832789259191 2500000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4516755257/10000000000 : ℝ)^2075 ≤ (34814191023303/100000000000000 : ℝ)^1563 := by
    have hnat : (4516755257 : ℕ)^2075*100000000000000^1563 ≤ 34814191023303^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516755257 10000000000 34814191023303 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528292641/1250000000 : ℝ)^2075 ≤ (1274969543493/4000000000000 : ℝ)^1563 := by
    have hnat : (528292641 : ℕ)^2075*4000000000000^1563 ≤ 1274969543493^1563*1250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528292641 1250000000 1274969543493 4000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092278373/2500000000 : ℝ), (4516755257/10000000000 : ℝ), (528292641/1250000000 : ℝ)] ![(832789259191/2500000000000 : ℝ), (34814191023303/100000000000000 : ℝ), (1274969543493/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092278373/2500000000 : ℝ)|^2075 ≤ (832789259191/2500000000000 : ℝ)^1563
        have hw : |(1092278373/2500000000 : ℝ)|=(1092278373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4516755257/10000000000 : ℝ)|^2075 ≤ (34814191023303/100000000000000 : ℝ)^1563
        have hw : |(4516755257/10000000000 : ℝ)|=(4516755257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528292641/1250000000 : ℝ)|^2075 ≤ (1274969543493/4000000000000 : ℝ)^1563
        have hw : |(528292641/1250000000 : ℝ)|=(528292641/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1107_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14849/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (329/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11107/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7119/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14849/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (329/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14849/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (329/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14849/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (329/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14849/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (329/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14849/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (329/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14849/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (329/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (329/3125 : ℝ) ^ (8299/2048 : ℝ) ≤ (436882740101371/4000000000000000000 : ℝ) := by
    have hpowers : (329/3125 : ℝ)^8299 ≤ (436882740101371/4000000000000000000 : ℝ)^2048 := by
      have hnat : (329 : ℕ)^8299*4000000000000000000^2048 ≤ 436882740101371^2048*3125^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        329 3125 436882740101371 4000000000000000000 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (329/3125 : ℝ)) (X := (436882740101371/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14849/100000 : ℝ) ^ (8299/2048 : ℝ) ≤ (8801227342441019/20000000000000000000 : ℝ) := by
    have hpowers : (14849/100000 : ℝ)^8299 ≤ (8801227342441019/20000000000000000000 : ℝ)^2048 := by
      have hnat : (14849 : ℕ)^8299*20000000000000000000^2048 ≤ 8801227342441019^2048*100000^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14849 100000 8801227342441019 20000000000000000000 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14849/100000 : ℝ)) (X := (8801227342441019/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000436882740101371/2000000000000000000 : ℝ) ≤ (10000539018106631/10000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (2000436882740101371/2000000000000000000 : ℝ)^2048 ≤ (10000539018106631/10000000000000000 : ℝ)^8299 := by
      have hnat : (2000436882740101371 : ℕ)^2048*10000000000000000^8299 ≤ 10000539018106631^8299*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000436882740101371 2000000000000000000 10000539018106631 10000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000539018106631/10000000000000000 : ℝ)) (X := (2000436882740101371/2000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005492820521473937/10000000000000000000 : ℝ) ≤ (5000677609957681/5000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (10005492820521473937/10000000000000000000 : ℝ)^2048 ≤ (5000677609957681/5000000000000000 : ℝ)^8299 := by
      have hnat : (10005492820521473937 : ℕ)^2048*5000000000000000^8299 ≤ 5000677609957681^8299*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005492820521473937 10000000000000000000 5000677609957681 5000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000677609957681/5000000000000000 : ℝ)) (X := (10005492820521473937/10000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10008801227342441019/10000000000000000000 : ℝ) ≤ (10002171421724093/10000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (10008801227342441019/10000000000000000000 : ℝ)^2048 ≤ (10002171421724093/10000000000000000 : ℝ)^8299 := by
      have hnat : (10008801227342441019 : ℕ)^2048*10000000000000000^8299 ≤ 10002171421724093^8299*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10008801227342441019 10000000000000000000 10002171421724093 10000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002171421724093/10000000000000000 : ℝ)) (X := (10008801227342441019/10000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(436882740101371/4000000000000000000 : ℝ) ≤ ((8639028630390822523/8642000000000000000 : ℝ)+2*(816201808731/432100000000000 : ℝ)*(329/3125 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (8639028630390822523/8642000000000000000 : ℝ)+2*(816201808731/432100000000000 : ℝ)*(329/3125 : ℝ)=(10000539018106631/10000000000000000 : ℝ) by norm_num, show 1+2*(436882740101371/4000000000000000000 : ℝ)=(2000436882740101371/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8801227342441019/20000000000000000000 : ℝ)+(436882740101371/4000000000000000000 : ℝ) ≤ ((8639028630390822523/8642000000000000000 : ℝ)+(816201808731/432100000000000 : ℝ)*((14849/100000 : ℝ)+(329/3125 : ℝ)))^(8299/2048 : ℝ) := by
    rw [show (8639028630390822523/8642000000000000000 : ℝ)+(816201808731/432100000000000 : ℝ)*((14849/100000 : ℝ)+(329/3125 : ℝ))=(5000677609957681/5000000000000000 : ℝ) by norm_num, show 1+(8801227342441019/20000000000000000000 : ℝ)+(436882740101371/4000000000000000000 : ℝ)=(10005492820521473937/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8801227342441019/20000000000000000000 : ℝ) ≤ ((8639028630390822523/8642000000000000000 : ℝ)+2*(816201808731/432100000000000 : ℝ)*(14849/100000 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (8639028630390822523/8642000000000000000 : ℝ)+2*(816201808731/432100000000000 : ℝ)*(14849/100000 : ℝ)=(10002171421724093/10000000000000000 : ℝ) by norm_num, show 1+2*(8801227342441019/20000000000000000000 : ℝ)=(10008801227342441019/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8639028630390822523/8642000000000000000 : ℝ)*(X 1 0+X 2 0)+(816201808731/432100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (329/3125 : ℝ)) (hi := (14849/100000 : ℝ)) (c := (8639028630390822523/8642000000000000000 : ℝ)) (alpha := (816201808731/432100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8639028630390822523/8642000000000000000 : ℝ)*(X 0 1+X 2 1)+(816201808731/432100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (329/3125 : ℝ)) (hi := (14849/100000 : ℝ)) (c := (8639028630390822523/8642000000000000000 : ℝ)) (alpha := (816201808731/432100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8639028630390822523/8642000000000000000 : ℝ)*(X 0 2+X 1 2)+(816201808731/432100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (329/3125 : ℝ)) (hi := (14849/100000 : ℝ)) (c := (8639028630390822523/8642000000000000000 : ℝ)) (alpha := (816201808731/432100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2182827543/10000000000 : ℝ)*X 0 0+(5403626047/10000000000 : ℝ)*X 0 1+(16424337/31250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347366847/10000000000 : ℝ)*X 1 0+(-282248333/1250000000 : ℝ)*X 1 1+(2627893937/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673683587/5000000000 : ℝ)*X 2 0+(5255787699/10000000000 : ℝ)*X 2 1+(-2257986461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4369098573/10000000000 : ℝ)*X 0 0+(105637371/250000000 : ℝ)*X 0 1+(2258799013/5000000000 : ℝ)*X 0 2+(4369098573/10000000000 : ℝ)*X 1 0+(105637371/250000000 : ℝ)*X 1 1+(2258799013/5000000000 : ℝ)*X 1 2+(4369098573/10000000000 : ℝ)*X 2 0+(105637371/250000000 : ℝ)*X 2 1+(2258799013/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-272854469/1250000000 : ℝ)*X 0 0+(5256213891/10000000000 : ℝ)*X 0 1+(2701598869/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655006109/5000000000 : ℝ)*X 1 0+(-42211527/200000000 : ℝ)*X 1 1+(2701598941/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655006213/5000000000 : ℝ)*X 2 0+(2701598879/5000000000 : ℝ)*X 2 1+(-1055288119/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1092278373/2500000000 : ℝ)*X 0 0+(4516755257/10000000000 : ℝ)*X 0 1+(528292641/1250000000 : ℝ)*X 0 2+(1092278373/2500000000 : ℝ)*X 1 0+(4516755257/10000000000 : ℝ)*X 1 1+(528292641/1250000000 : ℝ)*X 1 2+(1092278373/2500000000 : ℝ)*X 2 0+(4516755257/10000000000 : ℝ)*X 2 1+(528292641/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1135327434870295292415632091/108025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (438209041/100000000000000 : ℝ)*(base19) + (24882481/20000000000000 : ℝ)*(base23) + (459441953/100000000000000 : ℝ)*(lower2) + (93853587/50000000000000 : ℝ)*(upper3) + (70455623/100000000000000 : ℝ)*(lower4) + (2546902084934861/50000000000000 : ℝ)*(major0) + (2546902084934861/50000000000000 : ℝ)*(major1) + (2546902084934861/50000000000000 : ℝ)*(major2) + (6764148832279061/100000000000000 : ℝ)*(sp0) + (27056605295061/400000000000 : ℝ)*(sp1) + (3382075818780943/50000000000000 : ℝ)*(sp2) + (1711723811003547/50000000000000 : ℝ)*(sp3) + (2929695231/100000000000000 : ℝ)*(sp4) + (4302714721/50000000000000 : ℝ)*(sp7) + (427932028429567/12500000000000 : ℝ)*(f.failure) + (6764151761974291/100000000000000 : ℝ)*(f.sum) + (147275668825273/21605000000000000000000000000 : ℝ)*base66 + (1561589462826294303/432100000000000000000000000000000 : ℝ)*base67 + (2646747157995305697/432100000000000000000000000000000 : ℝ)*base70 + (6792182503754894303/432100000000000000000000000000000 : ℝ)*base71 + (1635245262847/5401250000000000000000000000 : ℝ)*base74 + (3612838042902494303/432100000000000000000000000000000 : ℝ)*base75 + (946187782565494303/432100000000000000000000000000000 : ℝ)*base77 + (10713862995931694303/432100000000000000000000000000000 : ℝ)*base79 + (2183704536359/675156250000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (134883/50000000000000000000 : ℝ)*base90 + (134883/50000000000000000000 : ℝ)*base92 + (134883/50000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4647475449026587176027997881/432100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45573777/2500000000000 : ℝ)*(base19) + (576594189/25000000000000 : ℝ)*(base23) + (134580739/50000000000000 : ℝ)*(upper3) + (21621143/25000000000000 : ℝ)*(lower4) + (11363823/3125000000000 : ℝ)*(upper5) + (5123415709632317/100000000000000 : ℝ)*(major0) + (5123415709632317/100000000000000 : ℝ)*(major1) + (5123415709632317/100000000000000 : ℝ)*(major2) + (5654153737/12500000000000 : ℝ)*(sp1) + (52916942169/100000000000000 : ℝ)*(sp2) + (850434179755151/12500000000000 : ℝ)*(sp4) + (6803426381860231/100000000000000 : ℝ)*(sp5) + (1700854553680571/25000000000000 : ℝ)*(sp6) + (430419702838113/12500000000000 : ℝ)*(sp7) + (430419702838113/12500000000000 : ℝ)*(f.failure) + (850434179755151/12500000000000 : ℝ)*(f.sum) + (29881922674767/21605000000000000000000000000 : ℝ)*base65 + (9660742987811615791/864200000000000000000000000000000 : ℝ)*base67 + (1939480196259615791/864200000000000000000000000000000 : ℝ)*base69 + (4441472436887215791/864200000000000000000000000000000 : ℝ)*base71 + (150780474042657/21605000000000000000000000000 : ℝ)*base73 + (6784250779903215791/864200000000000000000000000000000 : ℝ)*base75 + (5851759448983215791/864200000000000000000000000000000 : ℝ)*base77 + (7322219451396615791/864200000000000000000000000000000 : ℝ)*base79 + (1495933010173/337578125000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (425437/50000000000000000000 : ℝ)*base90 + (425437/50000000000000000000 : ℝ)*base92 + (425437/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1107_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14849/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (329/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1107_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1107_s5_0 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2183543537/10000000000 : ℝ)*x 0 + (5395853423/10000000000 : ℝ)*x 1 + (657886371/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183543537/10000000000 : ℝ)^2075 ≤ (6632201133737/50000000000000 : ℝ)^1563 := by
    have hnat : (2183543537 : ℕ)^2075*50000000000000^1563 ≤ 6632201133737^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183543537 10000000000 6632201133737 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395853423/10000000000 : ℝ)^2075 ≤ (22042441781789/50000000000000 : ℝ)^1563 := by
    have hnat : (5395853423 : ℕ)^2075*50000000000000^1563 ≤ 22042441781789^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395853423 10000000000 22042441781789 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657886371/1250000000 : ℝ)^2075 ≤ (42650714159991/100000000000000 : ℝ)^1563 := by
    have hnat : (657886371 : ℕ)^2075*100000000000000^1563 ≤ 42650714159991^1563*1250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657886371 1250000000 42650714159991 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2183543537/10000000000 : ℝ), (5395853423/10000000000 : ℝ), (657886371/1250000000 : ℝ)] ![(6632201133737/50000000000000 : ℝ), (22042441781789/50000000000000 : ℝ), (42650714159991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2183543537/10000000000 : ℝ)|^2075 ≤ (6632201133737/50000000000000 : ℝ)^1563
        have hw : |(-2183543537/10000000000 : ℝ)|=(2183543537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395853423/10000000000 : ℝ)|^2075 ≤ (22042441781789/50000000000000 : ℝ)^1563
        have hw : |(5395853423/10000000000 : ℝ)|=(5395853423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657886371/1250000000 : ℝ)|^2075 ≤ (42650714159991/100000000000000 : ℝ)^1563
        have hw : |(657886371/1250000000 : ℝ)|=(657886371/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s5_1 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (267271273/500000000 : ℝ)*x 0 + (-2250924569/10000000000 : ℝ)*x 1 + (210523621/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267271273/500000000 : ℝ)^2075 ≤ (43538756856073/100000000000000 : ℝ)^1563 := by
    have hnat : (267271273 : ℕ)^2075*100000000000000^1563 ≤ 43538756856073^1563*500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267271273 500000000 43538756856073 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250924569/10000000000 : ℝ)^2075 ≤ (13810533734079/100000000000000 : ℝ)^1563 := by
    have hnat : (2250924569 : ℕ)^2075*100000000000000^1563 ≤ 13810533734079^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250924569 10000000000 13810533734079 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210523621/400000000 : ℝ)^2075 ≤ (21325354697027/50000000000000 : ℝ)^1563 := by
    have hnat : (210523621 : ℕ)^2075*50000000000000^1563 ≤ 21325354697027^1563*400000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210523621 400000000 21325354697027 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267271273/500000000 : ℝ), (-2250924569/10000000000 : ℝ), (210523621/400000000 : ℝ)] ![(43538756856073/100000000000000 : ℝ), (13810533734079/100000000000000 : ℝ), (21325354697027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267271273/500000000 : ℝ)|^2075 ≤ (43538756856073/100000000000000 : ℝ)^1563
        have hw : |(267271273/500000000 : ℝ)|=(267271273/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2250924569/10000000000 : ℝ)|^2075 ≤ (13810533734079/100000000000000 : ℝ)^1563
        have hw : |(-2250924569/10000000000 : ℝ)|=(2250924569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210523621/400000000 : ℝ)|^2075 ≤ (21325354697027/50000000000000 : ℝ)^1563
        have hw : |(210523621/400000000 : ℝ)|=(210523621/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s5_2 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345424899/10000000000 : ℝ)*x 0 + (5263090737/10000000000 : ℝ)*x 1 + (-1125462517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345424899/10000000000 : ℝ)^2075 ≤ (43538750789887/100000000000000 : ℝ)^1563 := by
    have hnat : (5345424899 : ℕ)^2075*100000000000000^1563 ≤ 43538750789887^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345424899 10000000000 43538750789887 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263090737/10000000000 : ℝ)^2075 ≤ (21325355837409/50000000000000 : ℝ)^1563 := by
    have hnat : (5263090737 : ℕ)^2075*50000000000000^1563 ≤ 21325355837409^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263090737 10000000000 21325355837409 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125462517/5000000000 : ℝ)^2075 ≤ (6905268760829/50000000000000 : ℝ)^1563 := by
    have hnat : (1125462517 : ℕ)^2075*50000000000000^1563 ≤ 6905268760829^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125462517 5000000000 6905268760829 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345424899/10000000000 : ℝ), (5263090737/10000000000 : ℝ), (-1125462517/5000000000 : ℝ)] ![(43538750789887/100000000000000 : ℝ), (21325355837409/50000000000000 : ℝ), (6905268760829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345424899/10000000000 : ℝ)|^2075 ≤ (43538750789887/100000000000000 : ℝ)^1563
        have hw : |(5345424899/10000000000 : ℝ)|=(5345424899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263090737/10000000000 : ℝ)|^2075 ≤ (21325355837409/50000000000000 : ℝ)^1563
        have hw : |(5263090737/10000000000 : ℝ)|=(5263090737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1125462517/5000000000 : ℝ)|^2075 ≤ (6905268760829/50000000000000 : ℝ)^1563
        have hw : |(-1125462517/5000000000 : ℝ)|=(1125462517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s5_3 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4369517011/10000000000 : ℝ)*x 0 + (4240333739/10000000000 : ℝ)*x 1 + (70353909/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369517011/10000000000 : ℝ)^2075 ≤ (33315654797679/100000000000000 : ℝ)^1563 := by
    have hnat : (4369517011 : ℕ)^2075*100000000000000^1563 ≤ 33315654797679^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369517011 10000000000 33315654797679 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4240333739/10000000000 : ℝ)^2075 ≤ (32014412895461/100000000000000 : ℝ)^1563 := by
    have hnat : (4240333739 : ℕ)^2075*100000000000000^1563 ≤ 32014412895461^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240333739 10000000000 32014412895461 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70353909/156250000 : ℝ)^2075 ≤ (17334966145653/50000000000000 : ℝ)^1563 := by
    have hnat : (70353909 : ℕ)^2075*50000000000000^1563 ≤ 17334966145653^1563*156250000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70353909 156250000 17334966145653 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369517011/10000000000 : ℝ), (4240333739/10000000000 : ℝ), (70353909/156250000 : ℝ)] ![(33315654797679/100000000000000 : ℝ), (32014412895461/100000000000000 : ℝ), (17334966145653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369517011/10000000000 : ℝ)|^2075 ≤ (33315654797679/100000000000000 : ℝ)^1563
        have hw : |(4369517011/10000000000 : ℝ)|=(4369517011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4240333739/10000000000 : ℝ)|^2075 ≤ (32014412895461/100000000000000 : ℝ)^1563
        have hw : |(4240333739/10000000000 : ℝ)|=(4240333739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70353909/156250000 : ℝ)|^2075 ≤ (17334966145653/50000000000000 : ℝ)^1563
        have hw : |(70353909/156250000 : ℝ)|=(70353909/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s5_4 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2183549029/10000000000 : ℝ)*x 0 + (210537399/400000000 : ℝ)*x 1 + (5395508121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183549029/10000000000 : ℝ)^2075 ≤ (13264446558491/100000000000000 : ℝ)^1563 := by
    have hnat : (2183549029 : ℕ)^2075*100000000000000^1563 ≤ 13264446558491^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183549029 10000000000 13264446558491 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210537399/400000000 : ℝ)^2075 ≤ (21327207568909/50000000000000 : ℝ)^1563 := by
    have hnat : (210537399 : ℕ)^2075*50000000000000^1563 ≤ 21327207568909^1563*400000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210537399 400000000 21327207568909 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395508121/10000000000 : ℝ)^2075 ≤ (1763245531713/4000000000000 : ℝ)^1563 := by
    have hnat : (5395508121 : ℕ)^2075*4000000000000^1563 ≤ 1763245531713^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395508121 10000000000 1763245531713 4000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2183549029/10000000000 : ℝ), (210537399/400000000 : ℝ), (5395508121/10000000000 : ℝ)] ![(13264446558491/100000000000000 : ℝ), (21327207568909/50000000000000 : ℝ), (1763245531713/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2183549029/10000000000 : ℝ)|^2075 ≤ (13264446558491/100000000000000 : ℝ)^1563
        have hw : |(-2183549029/10000000000 : ℝ)|=(2183549029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210537399/400000000 : ℝ)|^2075 ≤ (21327207568909/50000000000000 : ℝ)^1563
        have hw : |(210537399/400000000 : ℝ)|=(210537399/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395508121/10000000000 : ℝ)|^2075 ≤ (1763245531713/4000000000000 : ℝ)^1563
        have hw : |(5395508121/10000000000 : ℝ)|=(5395508121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s5_5 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (265593907/500000000 : ℝ)*x 0 + (-264813431/1250000000 : ℝ)*x 1 + (1348876997/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265593907/500000000 : ℝ)^2075 ≤ (8635275504133/20000000000000 : ℝ)^1563 := by
    have hnat : (265593907 : ℕ)^2075*20000000000000^1563 ≤ 8635275504133^1563*500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265593907 500000000 8635275504133 20000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264813431/1250000000 : ℝ)^2075 ≤ (12742485623401/100000000000000 : ℝ)^1563 := by
    have hnat : (264813431 : ℕ)^2075*100000000000000^1563 ≤ 12742485623401^1563*1250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264813431 1250000000 12742485623401 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348876997/2500000000 : ℝ)^2075 ≤ (22040568425137/50000000000000 : ℝ)^1563 := by
    have hnat : (1348876997 : ℕ)^2075*50000000000000^1563 ≤ 22040568425137^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348876997 2500000000 22040568425137 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265593907/500000000 : ℝ), (-264813431/1250000000 : ℝ), (1348876997/2500000000 : ℝ)] ![(8635275504133/20000000000000 : ℝ), (12742485623401/100000000000000 : ℝ), (22040568425137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265593907/500000000 : ℝ)|^2075 ≤ (8635275504133/20000000000000 : ℝ)^1563
        have hw : |(265593907/500000000 : ℝ)|=(265593907/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-264813431/1250000000 : ℝ)|^2075 ≤ (12742485623401/100000000000000 : ℝ)^1563
        have hw : |(-264813431/1250000000 : ℝ)|=(264813431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348876997/2500000000 : ℝ)|^2075 ≤ (22040568425137/50000000000000 : ℝ)^1563
        have hw : |(1348876997/2500000000 : ℝ)|=(1348876997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s5_6 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (531187807/1000000000 : ℝ)*x 0 + (2697754087/5000000000 : ℝ)*x 1 + (-2118507289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531187807/1000000000 : ℝ)^2075 ≤ (21588188382651/50000000000000 : ℝ)^1563 := by
    have hnat : (531187807 : ℕ)^2075*50000000000000^1563 ≤ 21588188382651^1563*1000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531187807 1000000000 21588188382651 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697754087/5000000000 : ℝ)^2075 ≤ (11020284716919/25000000000000 : ℝ)^1563 := by
    have hnat : (2697754087 : ℕ)^2075*25000000000000^1563 ≤ 11020284716919^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697754087 5000000000 11020284716919 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2118507289/10000000000 : ℝ)^2075 ≤ (6371242176881/50000000000000 : ℝ)^1563 := by
    have hnat : (2118507289 : ℕ)^2075*50000000000000^1563 ≤ 6371242176881^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118507289 10000000000 6371242176881 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531187807/1000000000 : ℝ), (2697754087/5000000000 : ℝ), (-2118507289/10000000000 : ℝ)] ![(21588188382651/50000000000000 : ℝ), (11020284716919/25000000000000 : ℝ), (6371242176881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531187807/1000000000 : ℝ)|^2075 ≤ (21588188382651/50000000000000 : ℝ)^1563
        have hw : |(531187807/1000000000 : ℝ)|=(531187807/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697754087/5000000000 : ℝ)|^2075 ≤ (11020284716919/25000000000000 : ℝ)^1563
        have hw : |(2697754087/5000000000 : ℝ)|=(2697754087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2118507289/10000000000 : ℝ)|^2075 ≤ (6371242176881/50000000000000 : ℝ)^1563
        have hw : |(-2118507289/10000000000 : ℝ)|=(2118507289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s5_7 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4369527759/10000000000 : ℝ)*x 0 + (4501970209/10000000000 : ℝ)*x 1 + (4241016319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369527759/10000000000 : ℝ)^2075 ≤ (3331576359091/10000000000000 : ℝ)^1563 := by
    have hnat : (4369527759 : ℕ)^2075*10000000000000^1563 ≤ 3331576359091^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369527759 10000000000 3331576359091 10000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501970209/10000000000 : ℝ)^2075 ≤ (4332872713999/12500000000000 : ℝ)^1563 := by
    have hnat : (4501970209 : ℕ)^2075*12500000000000^1563 ≤ 4332872713999^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501970209 10000000000 4332872713999 12500000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4241016319/10000000000 : ℝ)^2075 ≤ (8005313670949/25000000000000 : ℝ)^1563 := by
    have hnat : (4241016319 : ℕ)^2075*25000000000000^1563 ≤ 8005313670949^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241016319 10000000000 8005313670949 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369527759/10000000000 : ℝ), (4501970209/10000000000 : ℝ), (4241016319/10000000000 : ℝ)] ![(3331576359091/10000000000000 : ℝ), (4332872713999/12500000000000 : ℝ), (8005313670949/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369527759/10000000000 : ℝ)|^2075 ≤ (3331576359091/10000000000000 : ℝ)^1563
        have hw : |(4369527759/10000000000 : ℝ)|=(4369527759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501970209/10000000000 : ℝ)|^2075 ≤ (4332872713999/12500000000000 : ℝ)^1563
        have hw : |(4501970209/10000000000 : ℝ)|=(4501970209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4241016319/10000000000 : ℝ)|^2075 ≤ (8005313670949/25000000000000 : ℝ)^1563
        have hw : |(4241016319/10000000000 : ℝ)|=(4241016319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1107_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11263/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (563/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11107/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11107/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11107/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11107/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11107/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11107/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11107/100000 : ℝ) ^ (8299/2048 : ℝ) ≤ (2713646312915571/20000000000000000000 : ℝ) := by
    have hpowers : (11107/100000 : ℝ)^8299 ≤ (2713646312915571/20000000000000000000 : ℝ)^2048 := by
      have hnat : (11107 : ℕ)^8299*20000000000000000000^2048 ≤ 2713646312915571^2048*100000^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11107 100000 2713646312915571 20000000000000000000 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11107/100000 : ℝ)) (X := (2713646312915571/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7119/50000 : ℝ) ^ (8299/2048 : ℝ) ≤ (9279124025382301/25000000000000000000 : ℝ) := by
    have hpowers : (7119/50000 : ℝ)^8299 ≤ (9279124025382301/25000000000000000000 : ℝ)^2048 := by
      have hnat : (7119 : ℕ)^8299*25000000000000000000^2048 ≤ 9279124025382301^2048*50000^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7119 50000 9279124025382301 25000000000000000000 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7119/50000 : ℝ)) (X := (9279124025382301/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002713646312915571/10000000000000000000 : ℝ) ≤ (1000066959630831/1000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (10002713646312915571/10000000000000000000 : ℝ)^2048 ≤ (1000066959630831/1000000000000000 : ℝ)^8299 := by
      have hnat : (10002713646312915571 : ℕ)^2048*1000000000000000^8299 ≤ 1000066959630831^8299*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002713646312915571 10000000000000000000 1000066959630831 1000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000066959630831/1000000000000000 : ℝ)) (X := (10002713646312915571/10000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050684727666107059/100000000000000000000 : ℝ) ≤ (5000625271200531/5000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (100050684727666107059/100000000000000000000 : ℝ)^2048 ≤ (5000625271200531/5000000000000000 : ℝ)^8299 := by
      have hnat : (100050684727666107059 : ℕ)^2048*5000000000000000^8299 ≤ 5000625271200531^8299*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050684727666107059 100000000000000000000 5000625271200531 5000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000625271200531/5000000000000000 : ℝ)) (X := (100050684727666107059/100000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509279124025382301/12500000000000000000 : ℝ) ≤ (5000915744246907/5000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (12509279124025382301/12500000000000000000 : ℝ)^2048 ≤ (5000915744246907/5000000000000000 : ℝ)^8299 := by
      have hnat : (12509279124025382301 : ℕ)^2048*5000000000000000^8299 ≤ 5000915744246907^8299*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509279124025382301 12500000000000000000 5000915744246907 5000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000915744246907/5000000000000000 : ℝ)) (X := (12509279124025382301/12500000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2713646312915571/20000000000000000000 : ℝ) ≤ ((15649595684768462841/15655000000000000000 : ℝ)+2*(36309130797/19568750000000 : ℝ)*(11107/100000 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (15649595684768462841/15655000000000000000 : ℝ)+2*(36309130797/19568750000000 : ℝ)*(11107/100000 : ℝ)=(1000066959630831/1000000000000000 : ℝ) by norm_num, show 1+2*(2713646312915571/20000000000000000000 : ℝ)=(10002713646312915571/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9279124025382301/25000000000000000000 : ℝ)+(2713646312915571/20000000000000000000 : ℝ) ≤ ((15649595684768462841/15655000000000000000 : ℝ)+(36309130797/19568750000000 : ℝ)*((7119/50000 : ℝ)+(11107/100000 : ℝ)))^(8299/2048 : ℝ) := by
    rw [show (15649595684768462841/15655000000000000000 : ℝ)+(36309130797/19568750000000 : ℝ)*((7119/50000 : ℝ)+(11107/100000 : ℝ))=(5000625271200531/5000000000000000 : ℝ) by norm_num, show 1+(9279124025382301/25000000000000000000 : ℝ)+(2713646312915571/20000000000000000000 : ℝ)=(100050684727666107059/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9279124025382301/25000000000000000000 : ℝ) ≤ ((15649595684768462841/15655000000000000000 : ℝ)+2*(36309130797/19568750000000 : ℝ)*(7119/50000 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (15649595684768462841/15655000000000000000 : ℝ)+2*(36309130797/19568750000000 : ℝ)*(7119/50000 : ℝ)=(5000915744246907/5000000000000000 : ℝ) by norm_num, show 1+2*(9279124025382301/25000000000000000000 : ℝ)=(12509279124025382301/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15649595684768462841/15655000000000000000 : ℝ)*(X 1 0+X 2 0)+(36309130797/19568750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (11107/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (15649595684768462841/15655000000000000000 : ℝ)) (alpha := (36309130797/19568750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15649595684768462841/15655000000000000000 : ℝ)*(X 0 1+X 2 1)+(36309130797/19568750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (11107/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (15649595684768462841/15655000000000000000 : ℝ)) (alpha := (36309130797/19568750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15649595684768462841/15655000000000000000 : ℝ)*(X 0 2+X 1 2)+(36309130797/19568750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (11107/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (15649595684768462841/15655000000000000000 : ℝ)) (alpha := (36309130797/19568750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2183543537/10000000000 : ℝ)*X 0 0+(5395853423/10000000000 : ℝ)*X 0 1+(657886371/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267271273/500000000 : ℝ)*X 1 0+(-2250924569/10000000000 : ℝ)*X 1 1+(210523621/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345424899/10000000000 : ℝ)*X 2 0+(5263090737/10000000000 : ℝ)*X 2 1+(-1125462517/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4369517011/10000000000 : ℝ)*X 0 0+(4240333739/10000000000 : ℝ)*X 0 1+(70353909/156250000 : ℝ)*X 0 2+(4369517011/10000000000 : ℝ)*X 1 0+(4240333739/10000000000 : ℝ)*X 1 1+(70353909/156250000 : ℝ)*X 1 2+(4369517011/10000000000 : ℝ)*X 2 0+(4240333739/10000000000 : ℝ)*X 2 1+(70353909/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2183549029/10000000000 : ℝ)*X 0 0+(210537399/400000000 : ℝ)*X 0 1+(5395508121/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265593907/500000000 : ℝ)*X 1 0+(-264813431/1250000000 : ℝ)*X 1 1+(1348876997/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531187807/1000000000 : ℝ)*X 2 0+(2697754087/5000000000 : ℝ)*X 2 1+(-2118507289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4369527759/10000000000 : ℝ)*X 0 0+(4501970209/10000000000 : ℝ)*X 0 1+(4241016319/10000000000 : ℝ)*X 0 2+(4369527759/10000000000 : ℝ)*X 1 0+(4501970209/10000000000 : ℝ)*X 1 1+(4241016319/10000000000 : ℝ)*X 1 2+(4369527759/10000000000 : ℝ)*X 2 0+(4501970209/10000000000 : ℝ)*X 2 1+(4241016319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (998875487988047802400141947/195687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (527672621/100000000000000 : ℝ)*(base19) + (22296473/25000000000000 : ℝ)*(base23) + (262331/10000000000000 : ℝ)*(lower2) + (41862747/50000000000000 : ℝ)*(lower3) + (53378203/20000000000000 : ℝ)*(lower4) + (2836118357659111/50000000000000 : ℝ)*(major0) + (2836118357659111/50000000000000 : ℝ)*(major1) + (2836118357659111/50000000000000 : ℝ)*(major2) + (7532262688787701/100000000000000 : ℝ)*(sp0) + (7532262161115079/100000000000000 : ℝ)*(sp1) + (1506447983122759/20000000000000 : ℝ)*(sp2) + (953051127806199/25000000000000 : ℝ)*(sp3) + (11341994007/50000000000000 : ℝ)*(sp6) + (3030237939/50000000000000 : ℝ)*(sp7) + (1906105285850337/50000000000000 : ℝ)*(f.failure) + (7532262688787701/100000000000000 : ℝ)*(f.sum) + (17966209174689/15655000000000000000000000000 : ℝ)*base65 + (855060333412444351/782750000000000000000000000000000 : ℝ)*base67 + (3221595000040694351/782750000000000000000000000000000 : ℝ)*base69 + (3011061073837305649/782750000000000000000000000000000 : ℝ)*base72 + (24295575988781/15655000000000000000000000000 : ℝ)*base74 + (1877658722336444351/782750000000000000000000000000000 : ℝ)*base75 + (829248702863944351/782750000000000000000000000000000 : ℝ)*base77 + (5216705497295444351/782750000000000000000000000000000 : ℝ)*base79 + (9408330542567/7827500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (56387/200000000000000000000 : ℝ)*base89 + (56387/200000000000000000000 : ℝ)*base91 + (56387/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8824404728985865061789719671/782750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1094630521/100000000000000 : ℝ)*(base19) + (337487059/20000000000000 : ℝ)*(base23) + (127041879/100000000000000 : ℝ)*(upper3) + (69015467/25000000000000 : ℝ)*(lower4) + (15268733/100000000000000 : ℝ)*(upper5) + (5701822186195877/100000000000000 : ℝ)*(major0) + (5701822186195877/100000000000000 : ℝ)*(major1) + (5701822186195877/100000000000000 : ℝ)*(major2) + (20864186273/100000000000000 : ℝ)*(sp1) + (12059514823/25000000000000 : ℝ)*(sp2) + (302861982003021/4000000000000 : ℝ)*(sp4) + (1892881897814683/25000000000000 : ℝ)*(sp5) + (7571499624580939/100000000000000 : ℝ)*(sp6) + (958023611632449/25000000000000 : ℝ)*(sp7) + (958023611632449/25000000000000 : ℝ)*(f.failure) + (302861982003021/4000000000000 : ℝ)*(f.sum) + (103414882821541/15655000000000000000000000000 : ℝ)*base66 + (2298224769357393443/1565500000000000000000000000000000 : ℝ)*base68 + (7220570654387606557/1565500000000000000000000000000000 : ℝ)*base69 + (9241376926874893443/1565500000000000000000000000000000 : ℝ)*base72 + (19549222208899/15655000000000000000000000000 : ℝ)*base73 + (4964253051339606557/1565500000000000000000000000000000 : ℝ)*base75 + (12744324350533893443/1565500000000000000000000000000000 : ℝ)*base78 + (11854955271689893443/1565500000000000000000000000000000 : ℝ)*base80 + (90355369899129/15655000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (276701/100000000000000000000 : ℝ)*base90 + (276701/100000000000000000000 : ℝ)*base92 + (276701/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1107_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (563/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1107_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1107_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16609/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8909/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (563/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1107_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1107_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1107_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16609/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8909/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (563/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1107_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

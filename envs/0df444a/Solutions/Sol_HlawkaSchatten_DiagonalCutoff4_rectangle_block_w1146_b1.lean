-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1146_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:33:37.479539+00:00
-- url     : https://prove2.me/submissions/dc4fb2ed-b777-4086-a5a9-73358c420ecc

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
theorem support_rectangle_w1146_s3_0 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2161215063/10000000000 : ℝ)*x 0 + (1357193733/2500000000 : ℝ)*x 1 + (5232452129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161215063/10000000000 : ℝ)^8339 ≤ (13125402243261/100000000000000 : ℝ)^6291 := by
    have hnat : (2161215063 : ℕ)^8339*100000000000000^6291 ≤ 13125402243261^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161215063 10000000000 13125402243261 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357193733/2500000000 : ℝ)^8339 ≤ (44497488347299/100000000000000 : ℝ)^6291 := by
    have hnat : (1357193733 : ℕ)^8339*100000000000000^6291 ≤ 44497488347299^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357193733 2500000000 44497488347299 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5232452129/10000000000 : ℝ)^8339 ≤ (21188554699167/50000000000000 : ℝ)^6291 := by
    have hnat : (5232452129 : ℕ)^8339*50000000000000^6291 ≤ 21188554699167^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232452129 10000000000 21188554699167 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2161215063/10000000000 : ℝ), (1357193733/2500000000 : ℝ), (5232452129/10000000000 : ℝ)] ![(13125402243261/100000000000000 : ℝ), (44497488347299/100000000000000 : ℝ), (21188554699167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2161215063/10000000000 : ℝ)|^8339 ≤ (13125402243261/100000000000000 : ℝ)^6291
        have hw : |(-2161215063/10000000000 : ℝ)|=(2161215063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357193733/2500000000 : ℝ)|^8339 ≤ (44497488347299/100000000000000 : ℝ)^6291
        have hw : |(1357193733/2500000000 : ℝ)|=(1357193733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5232452129/10000000000 : ℝ)|^8339 ≤ (21188554699167/50000000000000 : ℝ)^6291
        have hw : |(5232452129/10000000000 : ℝ)|=(5232452129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s3_1 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2676850111/5000000000 : ℝ)*x 0 + (-2261559993/10000000000 : ℝ)*x 1 + (2616225979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676850111/5000000000 : ℝ)^8339 ≤ (43683646798679/100000000000000 : ℝ)^6291 := by
    have hnat : (2676850111 : ℕ)^8339*100000000000000^6291 ≤ 43683646798679^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676850111 5000000000 43683646798679 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2261559993/10000000000 : ℝ)^8339 ≤ (13939245625049/100000000000000 : ℝ)^6291 := by
    have hnat : (2261559993 : ℕ)^8339*100000000000000^6291 ≤ 13939245625049^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261559993 10000000000 13939245625049 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2616225979/5000000000 : ℝ)^8339 ≤ (10594276890643/25000000000000 : ℝ)^6291 := by
    have hnat : (2616225979 : ℕ)^8339*25000000000000^6291 ≤ 10594276890643^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616225979 5000000000 10594276890643 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676850111/5000000000 : ℝ), (-2261559993/10000000000 : ℝ), (2616225979/5000000000 : ℝ)] ![(43683646798679/100000000000000 : ℝ), (13939245625049/100000000000000 : ℝ), (10594276890643/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676850111/5000000000 : ℝ)|^8339 ≤ (43683646798679/100000000000000 : ℝ)^6291
        have hw : |(2676850111/5000000000 : ℝ)|=(2676850111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2261559993/10000000000 : ℝ)|^8339 ≤ (13939245625049/100000000000000 : ℝ)^6291
        have hw : |(-2261559993/10000000000 : ℝ)|=(2261559993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2616225979/5000000000 : ℝ)|^8339 ≤ (10594276890643/25000000000000 : ℝ)^6291
        have hw : |(2616225979/5000000000 : ℝ)|=(2616225979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s3_2 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5353700303/10000000000 : ℝ)*x 0 + (5232452027/10000000000 : ℝ)*x 1 + (-452311959/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353700303/10000000000 : ℝ)^8339 ≤ (43683647674759/100000000000000 : ℝ)^6291 := by
    have hnat : (5353700303 : ℕ)^8339*100000000000000^6291 ≤ 43683647674759^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353700303 10000000000 43683647674759 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5232452027/10000000000 : ℝ)^8339 ≤ (21188554151659/50000000000000 : ℝ)^6291 := by
    have hnat : (5232452027 : ℕ)^8339*50000000000000^6291 ≤ 21188554151659^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232452027 10000000000 21188554151659 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (452311959/2000000000 : ℝ)^8339 ≤ (871202750461/6250000000000 : ℝ)^6291 := by
    have hnat : (452311959 : ℕ)^8339*6250000000000^6291 ≤ 871202750461^6291*2000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452311959 2000000000 871202750461 6250000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353700303/10000000000 : ℝ), (5232452027/10000000000 : ℝ), (-452311959/2000000000 : ℝ)] ![(43683647674759/100000000000000 : ℝ), (21188554151659/50000000000000 : ℝ), (871202750461/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353700303/10000000000 : ℝ)|^8339 ≤ (43683647674759/100000000000000 : ℝ)^6291
        have hw : |(5353700303/10000000000 : ℝ)|=(5353700303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5232452027/10000000000 : ℝ)|^8339 ≤ (21188554151659/50000000000000 : ℝ)^6291
        have hw : |(5232452027/10000000000 : ℝ)|=(5232452027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-452311959/2000000000 : ℝ)|^8339 ≤ (871202750461/6250000000000 : ℝ)^6291
        have hw : |(-452311959/2000000000 : ℝ)|=(452311959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s3_3 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (27261733/62500000 : ℝ)*x 0 + (130336927/312500000 : ℝ)*x 1 + (4561667071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27261733/62500000 : ℝ)^8339 ≤ (33294395908469/100000000000000 : ℝ)^6291 := by
    have hnat : (27261733 : ℕ)^8339*100000000000000^6291 ≤ 33294395908469^6291*62500000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27261733 62500000 33294395908469 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130336927/312500000 : ℝ)^8339 ≤ (15687414380779/50000000000000 : ℝ)^6291 := by
    have hnat : (130336927 : ℕ)^8339*50000000000000^6291 ≤ 15687414380779^6291*312500000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130336927 312500000 15687414380779 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4561667071/10000000000 : ℝ)^8339 ≤ (35330775320201/100000000000000 : ℝ)^6291 := by
    have hnat : (4561667071 : ℕ)^8339*100000000000000^6291 ≤ 35330775320201^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4561667071 10000000000 35330775320201 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(27261733/62500000 : ℝ), (130336927/312500000 : ℝ), (4561667071/10000000000 : ℝ)] ![(33294395908469/100000000000000 : ℝ), (15687414380779/50000000000000 : ℝ), (35330775320201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(27261733/62500000 : ℝ)|^8339 ≤ (33294395908469/100000000000000 : ℝ)^6291
        have hw : |(27261733/62500000 : ℝ)|=(27261733/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130336927/312500000 : ℝ)|^8339 ≤ (15687414380779/50000000000000 : ℝ)^6291
        have hw : |(130336927/312500000 : ℝ)|=(130336927/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4561667071/10000000000 : ℝ)|^8339 ≤ (35330775320201/100000000000000 : ℝ)^6291
        have hw : |(4561667071/10000000000 : ℝ)|=(4561667071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s3_4 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1080616477/5000000000 : ℝ)*x 0 + (1308302989/2500000000 : ℝ)*x 1 + (542801087/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080616477/5000000000 : ℝ)^8339 ≤ (13125546270331/100000000000000 : ℝ)^6291 := by
    have hnat : (1080616477 : ℕ)^8339*100000000000000^6291 ≤ 13125546270331^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080616477 5000000000 13125546270331 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1308302989/2500000000 : ℝ)^8339 ≤ (21192633338899/50000000000000 : ℝ)^6291 := by
    have hnat : (1308302989 : ℕ)^8339*50000000000000^6291 ≤ 21192633338899^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308302989 2500000000 21192633338899 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542801087/1000000000 : ℝ)^8339 ≤ (44489187037897/100000000000000 : ℝ)^6291 := by
    have hnat : (542801087 : ℕ)^8339*100000000000000^6291 ≤ 44489187037897^6291*1000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542801087 1000000000 44489187037897 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1080616477/5000000000 : ℝ), (1308302989/2500000000 : ℝ), (542801087/1000000000 : ℝ)] ![(13125546270331/100000000000000 : ℝ), (21192633338899/50000000000000 : ℝ), (44489187037897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1080616477/5000000000 : ℝ)|^8339 ≤ (13125546270331/100000000000000 : ℝ)^6291
        have hw : |(-1080616477/5000000000 : ℝ)|=(1080616477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1308302989/2500000000 : ℝ)|^8339 ≤ (21192633338899/50000000000000 : ℝ)^6291
        have hw : |(1308302989/2500000000 : ℝ)|=(1308302989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542801087/1000000000 : ℝ)|^8339 ≤ (44489187037897/100000000000000 : ℝ)^6291
        have hw : |(542801087/1000000000 : ℝ)|=(542801087/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s3_5 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1325987043/2500000000 : ℝ)*x 0 + (-129125063/625000000 : ℝ)*x 1 + (169625343/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325987043/2500000000 : ℝ)^8339 ≤ (43146353658841/100000000000000 : ℝ)^6291 := by
    have hnat : (1325987043 : ℕ)^8339*100000000000000^6291 ≤ 43146353658841^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325987043 2500000000 43146353658841 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129125063/625000000 : ℝ)^8339 ≤ (12364458138279/100000000000000 : ℝ)^6291 := by
    have hnat : (129125063 : ℕ)^8339*100000000000000^6291 ≤ 12364458138279^6291*625000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129125063 625000000 12364458138279 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169625343/312500000 : ℝ)^8339 ≤ (44489188189529/100000000000000 : ℝ)^6291 := by
    have hnat : (169625343 : ℕ)^8339*100000000000000^6291 ≤ 44489188189529^6291*312500000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169625343 312500000 44489188189529 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325987043/2500000000 : ℝ), (-129125063/625000000 : ℝ), (169625343/312500000 : ℝ)] ![(43146353658841/100000000000000 : ℝ), (12364458138279/100000000000000 : ℝ), (44489188189529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325987043/2500000000 : ℝ)|^8339 ≤ (43146353658841/100000000000000 : ℝ)^6291
        have hw : |(1325987043/2500000000 : ℝ)|=(1325987043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-129125063/625000000 : ℝ)|^8339 ≤ (12364458138279/100000000000000 : ℝ)^6291
        have hw : |(-129125063/625000000 : ℝ)|=(129125063/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169625343/312500000 : ℝ)|^8339 ≤ (44489188189529/100000000000000 : ℝ)^6291
        have hw : |(169625343/312500000 : ℝ)|=(169625343/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s3_6 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2651974027/5000000000 : ℝ)*x 0 + (542801117/1000000000 : ℝ)*x 1 + (-2066000903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651974027/5000000000 : ℝ)^8339 ≤ (43146352386449/100000000000000 : ℝ)^6291 := by
    have hnat : (2651974027 : ℕ)^8339*100000000000000^6291 ≤ 43146352386449^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651974027 5000000000 43146352386449 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542801117/1000000000 : ℝ)^8339 ≤ (22244595148617/50000000000000 : ℝ)^6291 := by
    have hnat : (542801117 : ℕ)^8339*50000000000000^6291 ≤ 22244595148617^6291*1000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542801117 1000000000 22244595148617 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066000903/10000000000 : ℝ)^8339 ≤ (12364457305311/100000000000000 : ℝ)^6291 := by
    have hnat : (2066000903 : ℕ)^8339*100000000000000^6291 ≤ 12364457305311^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066000903 10000000000 12364457305311 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651974027/5000000000 : ℝ), (542801117/1000000000 : ℝ), (-2066000903/10000000000 : ℝ)] ![(43146352386449/100000000000000 : ℝ), (22244595148617/50000000000000 : ℝ), (12364457305311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651974027/5000000000 : ℝ)|^8339 ≤ (43146352386449/100000000000000 : ℝ)^6291
        have hw : |(2651974027/5000000000 : ℝ)|=(2651974027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542801117/1000000000 : ℝ)|^8339 ≤ (22244595148617/50000000000000 : ℝ)^6291
        have hw : |(542801117/1000000000 : ℝ)|=(542801117/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2066000903/10000000000 : ℝ)|^8339 ≤ (12364457305311/100000000000000 : ℝ)^6291
        have hw : |(-2066000903/10000000000 : ℝ)|=(2066000903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s3_7 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436191291/1000000000 : ℝ)*x 0 + (4560154449/10000000000 : ℝ)*x 1 + (4172302721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436191291/1000000000 : ℝ)^8339 ≤ (2080922275691/6250000000000 : ℝ)^6291 := by
    have hnat : (436191291 : ℕ)^8339*6250000000000^6291 ≤ 2080922275691^6291*1000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436191291 1000000000 2080922275691 6250000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4560154449/10000000000 : ℝ)^8339 ≤ (2207202923281/6250000000000 : ℝ)^6291 := by
    have hnat : (4560154449 : ℕ)^8339*6250000000000^6291 ≤ 2207202923281^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4560154449 10000000000 2207202923281 6250000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172302721/10000000000 : ℝ)^8339 ≤ (6277999360303/20000000000000 : ℝ)^6291 := by
    have hnat : (4172302721 : ℕ)^8339*20000000000000^6291 ≤ 6277999360303^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172302721 10000000000 6277999360303 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436191291/1000000000 : ℝ), (4560154449/10000000000 : ℝ), (4172302721/10000000000 : ℝ)] ![(2080922275691/6250000000000 : ℝ), (2207202923281/6250000000000 : ℝ), (6277999360303/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436191291/1000000000 : ℝ)|^8339 ≤ (2080922275691/6250000000000 : ℝ)^6291
        have hw : |(436191291/1000000000 : ℝ)|=(436191291/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4560154449/10000000000 : ℝ)|^8339 ≤ (2207202923281/6250000000000 : ℝ)^6291
        have hw : |(4560154449/10000000000 : ℝ)|=(4560154449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172302721/10000000000 : ℝ)|^8339 ≤ (6277999360303/20000000000000 : ℝ)^6291
        have hw : |(4172302721/10000000000 : ℝ)|=(4172302721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1146_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16491/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (284/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (10647/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14801/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16491/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (284/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16491/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (284/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16491/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (284/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16491/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (284/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16491/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (284/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16491/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (284/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (284/3125 : ℝ) ^ (4169/1024 : ℝ) ≤ (5749412334044263/100000000000000000000 : ℝ) := by
    have hpowers : (284/3125 : ℝ)^4169 ≤ (5749412334044263/100000000000000000000 : ℝ)^1024 := by
      have hnat : (284 : ℕ)^4169*100000000000000000000^1024 ≤ 5749412334044263^1024*3125^4169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        284 3125 5749412334044263 100000000000000000000 4169 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (284/3125 : ℝ)) (X := (5749412334044263/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16491/100000 : ℝ) ^ (4169/1024 : ℝ) ≤ (65040854540498769/100000000000000000000 : ℝ) := by
    have hpowers : (16491/100000 : ℝ)^4169 ≤ (65040854540498769/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16491 : ℕ)^4169*100000000000000000000^1024 ≤ 65040854540498769^1024*100000^4169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16491 100000 65040854540498769 100000000000000000000 4169 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16491/100000 : ℝ)) (X := (65040854540498769/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005749412334044263/50000000000000000000 : ℝ) ≤ (5000141212350621/5000000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (50005749412334044263/50000000000000000000 : ℝ)^1024 ≤ (5000141212350621/5000000000000000 : ℝ)^4169 := by
      have hnat : (50005749412334044263 : ℕ)^1024*5000000000000000^4169 ≤ 5000141212350621^4169*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005749412334044263 50000000000000000000 5000141212350621 5000000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000141212350621/5000000000000000 : ℝ)) (X := (50005749412334044263/50000000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12508848783359317879/12500000000000000000 : ℝ) ≤ (1000173830380727/1000000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (12508848783359317879/12500000000000000000 : ℝ)^1024 ≤ (1000173830380727/1000000000000000 : ℝ)^4169 := by
      have hnat : (12508848783359317879 : ℕ)^1024*1000000000000000^4169 ≤ 1000173830380727^4169*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508848783359317879 12500000000000000000 1000173830380727 1000000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000173830380727/1000000000000000 : ℝ)) (X := (12508848783359317879/12500000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50065040854540498769/50000000000000000000 : ℝ) ≤ (5001597091456649/5000000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (50065040854540498769/50000000000000000000 : ℝ)^1024 ≤ (5001597091456649/5000000000000000 : ℝ)^4169 := by
      have hnat : (50065040854540498769 : ℕ)^1024*5000000000000000^4169 ≤ 5001597091456649^4169*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50065040854540498769 50000000000000000000 5001597091456649 5000000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001597091456649/5000000000000000 : ℝ)) (X := (50065040854540498769/50000000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5749412334044263/100000000000000000000 : ℝ) ≤ ((37002814365716064799/37015000000000000000 : ℝ)+2*(363969776507/185075000000000 : ℝ)*(284/3125 : ℝ))^(4169/1024 : ℝ) := by
    rw [show (37002814365716064799/37015000000000000000 : ℝ)+2*(363969776507/185075000000000 : ℝ)*(284/3125 : ℝ)=(5000141212350621/5000000000000000 : ℝ) by norm_num, show 1+2*(5749412334044263/100000000000000000000 : ℝ)=(50005749412334044263/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(65040854540498769/100000000000000000000 : ℝ)+(5749412334044263/100000000000000000000 : ℝ) ≤ ((37002814365716064799/37015000000000000000 : ℝ)+(363969776507/185075000000000 : ℝ)*((16491/100000 : ℝ)+(284/3125 : ℝ)))^(4169/1024 : ℝ) := by
    rw [show (37002814365716064799/37015000000000000000 : ℝ)+(363969776507/185075000000000 : ℝ)*((16491/100000 : ℝ)+(284/3125 : ℝ))=(1000173830380727/1000000000000000 : ℝ) by norm_num, show 1+(65040854540498769/100000000000000000000 : ℝ)+(5749412334044263/100000000000000000000 : ℝ)=(12508848783359317879/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(65040854540498769/100000000000000000000 : ℝ) ≤ ((37002814365716064799/37015000000000000000 : ℝ)+2*(363969776507/185075000000000 : ℝ)*(16491/100000 : ℝ))^(4169/1024 : ℝ) := by
    rw [show (37002814365716064799/37015000000000000000 : ℝ)+2*(363969776507/185075000000000 : ℝ)*(16491/100000 : ℝ)=(5001597091456649/5000000000000000 : ℝ) by norm_num, show 1+2*(65040854540498769/100000000000000000000 : ℝ)=(50065040854540498769/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37002814365716064799/37015000000000000000 : ℝ)*(X 1 0+X 2 0)+(363969776507/185075000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (284/3125 : ℝ)) (hi := (16491/100000 : ℝ)) (c := (37002814365716064799/37015000000000000000 : ℝ)) (alpha := (363969776507/185075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37002814365716064799/37015000000000000000 : ℝ)*(X 0 1+X 2 1)+(363969776507/185075000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (284/3125 : ℝ)) (hi := (16491/100000 : ℝ)) (c := (37002814365716064799/37015000000000000000 : ℝ)) (alpha := (363969776507/185075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37002814365716064799/37015000000000000000 : ℝ)*(X 0 2+X 1 2)+(363969776507/185075000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (284/3125 : ℝ)) (hi := (16491/100000 : ℝ)) (c := (37002814365716064799/37015000000000000000 : ℝ)) (alpha := (363969776507/185075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2161215063/10000000000 : ℝ)*X 0 0+(1357193733/2500000000 : ℝ)*X 0 1+(5232452129/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676850111/5000000000 : ℝ)*X 1 0+(-2261559993/10000000000 : ℝ)*X 1 1+(2616225979/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353700303/10000000000 : ℝ)*X 2 0+(5232452027/10000000000 : ℝ)*X 2 1+(-452311959/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((27261733/62500000 : ℝ)*X 0 0+(130336927/312500000 : ℝ)*X 0 1+(4561667071/10000000000 : ℝ)*X 0 2+(27261733/62500000 : ℝ)*X 1 0+(130336927/312500000 : ℝ)*X 1 1+(4561667071/10000000000 : ℝ)*X 1 2+(27261733/62500000 : ℝ)*X 2 0+(130336927/312500000 : ℝ)*X 2 1+(4561667071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1080616477/5000000000 : ℝ)*X 0 0+(1308302989/2500000000 : ℝ)*X 0 1+(542801087/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325987043/2500000000 : ℝ)*X 1 0+(-129125063/625000000 : ℝ)*X 1 1+(169625343/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651974027/5000000000 : ℝ)*X 2 0+(542801117/1000000000 : ℝ)*X 2 1+(-2066000903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436191291/1000000000 : ℝ)*X 0 0+(4560154449/10000000000 : ℝ)*X 0 1+(4172302721/10000000000 : ℝ)*X 0 2+(436191291/1000000000 : ℝ)*X 1 0+(4560154449/10000000000 : ℝ)*X 1 1+(4172302721/10000000000 : ℝ)*X 1 2+(436191291/1000000000 : ℝ)*X 2 0+(4560154449/10000000000 : ℝ)*X 2 1+(4172302721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4464418180066103491339631763/1850750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4119651/500000000000 : ℝ)*(base19) + (49968653/6250000000000 : ℝ)*(base23) + (11305393/20000000000000 : ℝ)*(lower2) + (127846339/100000000000000 : ℝ)*(upper5) + (3825992304054907/100000000000000 : ℝ)*(major0) + (3825992304054907/100000000000000 : ℝ)*(major1) + (3825992304054907/100000000000000 : ℝ)*(major2) + (1018732400042527/20000000000000 : ℝ)*(sp0) + (1273419202241591/25000000000000 : ℝ)*(sp1) + (5093677273209431/100000000000000 : ℝ)*(sp2) + (2558300999093107/100000000000000 : ℝ)*(sp3) + (4018123811/25000000000000 : ℝ)*(sp4) + (87962263/20000000000000 : ℝ)*(sp5) + (1363975363/25000000000000 : ℝ)*(sp7) + (3997353835929/156250000000 : ℝ)*(f.failure) + (5093678072707879/100000000000000 : ℝ)*(f.sum) + (25746147278911/37015000000000000000000000000 : ℝ)*base65 + (29388713587215718693/3701500000000000000000000000000000 : ℝ)*base67 + (14323869158009718693/3701500000000000000000000000000000 : ℝ)*base69 + (7181193491333718693/3701500000000000000000000000000000 : ℝ)*base71 + (43852102560991/9253750000000000000000000000 : ℝ)*base74 + (30820781144174218693/3701500000000000000000000000000000 : ℝ)*base75 + (8030100664926218693/3701500000000000000000000000000000 : ℝ)*base77 + (11547988645786218693/3701500000000000000000000000000000 : ℝ)*base79 + (12011453049217/4626875000000000000000000000 : ℝ)*base81 + (130361/15625000000000000000 : ℝ)*base89 + (130361/15625000000000000000 : ℝ)*base91 + (130361/15625000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (112719183212756295054939/18507500000000000000000000000 : ℝ) := by norm_num
    linear_combination (236954241/20000000000000 : ℝ)*(base19) + (323490703/25000000000000 : ℝ)*(base23) + (82442897/50000000000000 : ℝ)*(upper3) + (10688007/12500000000000 : ℝ)*(lower4) + (7228861/6250000000000 : ℝ)*(upper5) + (1927950067865353/50000000000000 : ℝ)*(major0) + (1927950067865353/50000000000000 : ℝ)*(major1) + (1927950067865353/50000000000000 : ℝ)*(major2) + (22049883203/100000000000000 : ℝ)*(sp1) + (28679814209/100000000000000 : ℝ)*(sp2) + (5133495298569917/100000000000000 : ℝ)*(sp4) + (5133472063915509/100000000000000 : ℝ)*(sp5) + (80210395699889/1562500000000 : ℝ)*(sp6) + (644576192469041/25000000000000 : ℝ)*(sp7) + (644576192469041/25000000000000 : ℝ)*(f.failure) + (5133495298569917/100000000000000 : ℝ)*(f.sum) + (30467719097719/18507500000000000000000000000 : ℝ)*base65 + (12491165798983209047/1850750000000000000000000000000000 : ℝ)*base67 + (848778775176290953/1850750000000000000000000000000000 : ℝ)*base70 + (8703667801958709047/1850750000000000000000000000000000 : ℝ)*base71 + (22591949005993/37015000000000000000000000000 : ℝ)*base73 + (2081915858827290953/1850750000000000000000000000000000 : ℝ)*base76 + (8510267321814040953/1850750000000000000000000000000000 : ℝ)*base78 + (31102729194399959047/1850750000000000000000000000000000 : ℝ)*base79 + (128943187308753/37015000000000000000000000000 : ℝ)*base81 + (15406881/2500000000000000000000 : ℝ)*base90 + (15406881/2500000000000000000000 : ℝ)*base92 + (15406881/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1146_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16491/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (284/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10647/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14801/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1146_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1146_s4_0 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2164184867/10000000000 : ℝ)*x 0 + (2700850679/5000000000 : ℝ)*x 1 + (5257582923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164184867/10000000000 : ℝ)^8339 ≤ (821832201833/6250000000000 : ℝ)^6291 := by
    have hnat : (2164184867 : ℕ)^8339*6250000000000^6291 ≤ 821832201833^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164184867 10000000000 821832201833 6250000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700850679/5000000000 : ℝ)^8339 ≤ (5525446777511/12500000000000 : ℝ)^6291 := by
    have hnat : (2700850679 : ℕ)^8339*12500000000000^6291 ≤ 5525446777511^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700850679 5000000000 5525446777511 12500000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5257582923/10000000000 : ℝ)^8339 ≤ (42647110531341/100000000000000 : ℝ)^6291 := by
    have hnat : (5257582923 : ℕ)^8339*100000000000000^6291 ≤ 42647110531341^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257582923 10000000000 42647110531341 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2164184867/10000000000 : ℝ), (2700850679/5000000000 : ℝ), (5257582923/10000000000 : ℝ)] ![(821832201833/6250000000000 : ℝ), (5525446777511/12500000000000 : ℝ), (42647110531341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2164184867/10000000000 : ℝ)|^8339 ≤ (821832201833/6250000000000 : ℝ)^6291
        have hw : |(-2164184867/10000000000 : ℝ)|=(2164184867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700850679/5000000000 : ℝ)|^8339 ≤ (5525446777511/12500000000000 : ℝ)^6291
        have hw : |(2700850679/5000000000 : ℝ)|=(2700850679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5257582923/10000000000 : ℝ)|^8339 ≤ (42647110531341/100000000000000 : ℝ)^6291
        have hw : |(5257582923/10000000000 : ℝ)|=(5257582923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s4_1 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346936117/10000000000 : ℝ)*x 0 + (-279677737/1250000000 : ℝ)*x 1 + (328598977/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346936117/10000000000 : ℝ)^8339 ≤ (43610502561003/100000000000000 : ℝ)^6291 := by
    have hnat : (5346936117 : ℕ)^8339*100000000000000^6291 ≤ 43610502561003^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346936117 10000000000 43610502561003 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (279677737/1250000000 : ℝ)^8339 ≤ (1374237927179/10000000000000 : ℝ)^6291 := by
    have hnat : (279677737 : ℕ)^8339*10000000000000^6291 ≤ 1374237927179^6291*1250000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279677737 1250000000 1374237927179 10000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328598977/625000000 : ℝ)^8339 ≤ (21323559077329/50000000000000 : ℝ)^6291 := by
    have hnat : (328598977 : ℕ)^8339*50000000000000^6291 ≤ 21323559077329^6291*625000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328598977 625000000 21323559077329 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346936117/10000000000 : ℝ), (-279677737/1250000000 : ℝ), (328598977/625000000 : ℝ)] ![(43610502561003/100000000000000 : ℝ), (1374237927179/10000000000000 : ℝ), (21323559077329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346936117/10000000000 : ℝ)|^8339 ≤ (43610502561003/100000000000000 : ℝ)^6291
        have hw : |(5346936117/10000000000 : ℝ)|=(5346936117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-279677737/1250000000 : ℝ)|^8339 ≤ (1374237927179/10000000000000 : ℝ)^6291
        have hw : |(-279677737/1250000000 : ℝ)|=(279677737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328598977/625000000 : ℝ)|^8339 ≤ (21323559077329/50000000000000 : ℝ)^6291
        have hw : |(328598977/625000000 : ℝ)|=(328598977/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s4_2 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346936499/10000000000 : ℝ)*x 0 + (5257582691/10000000000 : ℝ)*x 1 + (-279677829/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346936499/10000000000 : ℝ)^8339 ≤ (43610506690943/100000000000000 : ℝ)^6291 := by
    have hnat : (5346936499 : ℕ)^8339*100000000000000^6291 ≤ 43610506690943^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346936499 10000000000 43610506690943 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5257582691/10000000000 : ℝ)^8339 ≤ (10661777009207/25000000000000 : ℝ)^6291 := by
    have hnat : (5257582691 : ℕ)^8339*25000000000000^6291 ≤ 10661777009207^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257582691 10000000000 10661777009207 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279677829/1250000000 : ℝ)^8339 ≤ (3435596315997/25000000000000 : ℝ)^6291 := by
    have hnat : (279677829 : ℕ)^8339*25000000000000^6291 ≤ 3435596315997^6291*1250000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279677829 1250000000 3435596315997 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346936499/10000000000 : ℝ), (5257582691/10000000000 : ℝ), (-279677829/1250000000 : ℝ)] ![(43610506690943/100000000000000 : ℝ), (10661777009207/25000000000000 : ℝ), (3435596315997/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346936499/10000000000 : ℝ)|^8339 ≤ (43610506690943/100000000000000 : ℝ)^6291
        have hw : |(5346936499/10000000000 : ℝ)|=(5346936499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5257582691/10000000000 : ℝ)|^8339 ≤ (10661777009207/25000000000000 : ℝ)^6291
        have hw : |(5257582691/10000000000 : ℝ)|=(5257582691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-279677829/1250000000 : ℝ)|^8339 ≤ (3435596315997/25000000000000 : ℝ)^6291
        have hw : |(-279677829/1250000000 : ℝ)|=(279677829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s4_3 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4363650709/10000000000 : ℝ)*x 0 + (4222521319/10000000000 : ℝ)*x 1 + (2254734003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363650709/10000000000 : ℝ)^8339 ≤ (16656170269669/50000000000000 : ℝ)^6291 := by
    have hnat : (4363650709 : ℕ)^8339*50000000000000^6291 ≤ 16656170269669^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363650709 10000000000 16656170269669 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4222521319/10000000000 : ℝ)^8339 ≤ (31891786873987/100000000000000 : ℝ)^6291 := by
    have hnat : (4222521319 : ℕ)^8339*100000000000000^6291 ≤ 31891786873987^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222521319 10000000000 31891786873987 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254734003/5000000000 : ℝ)^8339 ≤ (34795872571981/100000000000000 : ℝ)^6291 := by
    have hnat : (2254734003 : ℕ)^8339*100000000000000^6291 ≤ 34795872571981^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254734003 5000000000 34795872571981 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363650709/10000000000 : ℝ), (4222521319/10000000000 : ℝ), (2254734003/5000000000 : ℝ)] ![(16656170269669/50000000000000 : ℝ), (31891786873987/100000000000000 : ℝ), (34795872571981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363650709/10000000000 : ℝ)|^8339 ≤ (16656170269669/50000000000000 : ℝ)^6291
        have hw : |(4363650709/10000000000 : ℝ)|=(4363650709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4222521319/10000000000 : ℝ)|^8339 ≤ (31891786873987/100000000000000 : ℝ)^6291
        have hw : |(4222521319/10000000000 : ℝ)|=(4222521319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2254734003/5000000000 : ℝ)|^8339 ≤ (34795872571981/100000000000000 : ℝ)^6291
        have hw : |(2254734003/5000000000 : ℝ)|=(2254734003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s4_4 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1082096331/5000000000 : ℝ)*x 0 + (328624533/625000000 : ℝ)*x 1 + (2700644773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082096331/5000000000 : ℝ)^8339 ≤ (6574689004529/50000000000000 : ℝ)^6291 := by
    have hnat : (1082096331 : ℕ)^8339*50000000000000^6291 ≤ 6574689004529^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082096331 5000000000 6574689004529 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328624533/625000000 : ℝ)^8339 ≤ (10662878686621/25000000000000 : ℝ)^6291 := by
    have hnat : (328624533 : ℕ)^8339*25000000000000^6291 ≤ 10662878686621^6291*625000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328624533 625000000 10662878686621 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700644773/5000000000 : ℝ)^8339 ≤ (22099553616413/50000000000000 : ℝ)^6291 := by
    have hnat : (2700644773 : ℕ)^8339*50000000000000^6291 ≤ 22099553616413^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700644773 5000000000 22099553616413 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1082096331/5000000000 : ℝ), (328624533/625000000 : ℝ), (2700644773/5000000000 : ℝ)] ![(6574689004529/50000000000000 : ℝ), (10662878686621/25000000000000 : ℝ), (22099553616413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1082096331/5000000000 : ℝ)|^8339 ≤ (6574689004529/50000000000000 : ℝ)^6291
        have hw : |(-1082096331/5000000000 : ℝ)|=(1082096331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328624533/625000000 : ℝ)|^8339 ≤ (10662878686621/25000000000000 : ℝ)^6291
        have hw : |(328624533/625000000 : ℝ)|=(328624533/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700644773/5000000000 : ℝ)|^8339 ≤ (22099553616413/50000000000000 : ℝ)^6291
        have hw : |(2700644773/5000000000 : ℝ)|=(2700644773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s4_5 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310415167/10000000000 : ℝ)*x 0 + (-209371497/1000000000 : ℝ)*x 1 + (1350322373/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310415167/10000000000 : ℝ)^8339 ≤ (43216101023223/100000000000000 : ℝ)^6291 := by
    have hnat : (5310415167 : ℕ)^8339*100000000000000^6291 ≤ 43216101023223^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310415167 10000000000 43216101023223 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209371497/1000000000 : ℝ)^8339 ≤ (1573099039257/12500000000000 : ℝ)^6291 := by
    have hnat : (209371497 : ℕ)^8339*12500000000000^6291 ≤ 1573099039257^6291*1000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209371497 1000000000 1573099039257 12500000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350322373/2500000000 : ℝ)^8339 ≤ (2762444165443/6250000000000 : ℝ)^6291 := by
    have hnat : (1350322373 : ℕ)^8339*6250000000000^6291 ≤ 2762444165443^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350322373 2500000000 2762444165443 6250000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310415167/10000000000 : ℝ), (-209371497/1000000000 : ℝ), (1350322373/2500000000 : ℝ)] ![(43216101023223/100000000000000 : ℝ), (1573099039257/12500000000000 : ℝ), (2762444165443/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310415167/10000000000 : ℝ)|^8339 ≤ (43216101023223/100000000000000 : ℝ)^6291
        have hw : |(5310415167/10000000000 : ℝ)|=(5310415167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-209371497/1000000000 : ℝ)|^8339 ≤ (1573099039257/12500000000000 : ℝ)^6291
        have hw : |(-209371497/1000000000 : ℝ)|=(209371497/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350322373/2500000000 : ℝ)|^8339 ≤ (2762444165443/6250000000000 : ℝ)^6291
        have hw : |(1350322373/2500000000 : ℝ)|=(1350322373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s4_6 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310415121/10000000000 : ℝ)*x 0 + (5401289459/10000000000 : ℝ)*x 1 + (-2093715077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310415121/10000000000 : ℝ)^8339 ≤ (43216100527009/100000000000000 : ℝ)^6291 := by
    have hnat : (5310415121 : ℕ)^8339*100000000000000^6291 ≤ 43216100527009^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310415121 10000000000 43216100527009 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401289459/10000000000 : ℝ)^8339 ≤ (2762444143071/6250000000000 : ℝ)^6291 := by
    have hnat : (5401289459 : ℕ)^8339*6250000000000^6291 ≤ 2762444143071^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401289459 10000000000 2762444143071 6250000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2093715077/10000000000 : ℝ)^8339 ≤ (629239658329/5000000000000 : ℝ)^6291 := by
    have hnat : (2093715077 : ℕ)^8339*5000000000000^6291 ≤ 629239658329^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093715077 10000000000 629239658329 5000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310415121/10000000000 : ℝ), (5401289459/10000000000 : ℝ), (-2093715077/10000000000 : ℝ)] ![(43216100527009/100000000000000 : ℝ), (2762444143071/6250000000000 : ℝ), (629239658329/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310415121/10000000000 : ℝ)|^8339 ≤ (43216100527009/100000000000000 : ℝ)^6291
        have hw : |(5310415121/10000000000 : ℝ)|=(5310415121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401289459/10000000000 : ℝ)|^8339 ≤ (2762444143071/6250000000000 : ℝ)^6291
        have hw : |(5401289459/10000000000 : ℝ)|=(5401289459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2093715077/10000000000 : ℝ)|^8339 ≤ (629239658329/5000000000000 : ℝ)^6291
        have hw : |(-2093715077/10000000000 : ℝ)|=(2093715077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s4_7 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1090916187/2500000000 : ℝ)*x 0 + (4508650787/10000000000 : ℝ)*x 1 + (527917747/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090916187/2500000000 : ℝ)^8339 ≤ (33312482603933/100000000000000 : ℝ)^6291 := by
    have hnat : (1090916187 : ℕ)^8339*100000000000000^6291 ≤ 33312482603933^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090916187 2500000000 33312482603933 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508650787/10000000000 : ℝ)^8339 ≤ (17393757093659/50000000000000 : ℝ)^6291 := by
    have hnat : (4508650787 : ℕ)^8339*50000000000000^6291 ≤ 17393757093659^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508650787 10000000000 17393757093659 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527917747/1250000000 : ℝ)^8339 ≤ (7975000795479/25000000000000 : ℝ)^6291 := by
    have hnat : (527917747 : ℕ)^8339*25000000000000^6291 ≤ 7975000795479^6291*1250000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527917747 1250000000 7975000795479 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090916187/2500000000 : ℝ), (4508650787/10000000000 : ℝ), (527917747/1250000000 : ℝ)] ![(33312482603933/100000000000000 : ℝ), (17393757093659/50000000000000 : ℝ), (7975000795479/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090916187/2500000000 : ℝ)|^8339 ≤ (33312482603933/100000000000000 : ℝ)^6291
        have hw : |(1090916187/2500000000 : ℝ)|=(1090916187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508650787/10000000000 : ℝ)|^8339 ≤ (17393757093659/50000000000000 : ℝ)^6291
        have hw : |(4508650787/10000000000 : ℝ)|=(4508650787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(527917747/1250000000 : ℝ)|^8339 ≤ (7975000795479/25000000000000 : ℝ)^6291
        have hw : |(527917747/1250000000 : ℝ)|=(527917747/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1146_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14801/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10647/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11183/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14801/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10647/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14801/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10647/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14801/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10647/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14801/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10647/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14801/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10647/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14801/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10647/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (10647/100000 : ℝ) ^ (4169/1024 : ℝ) ≤ (10953702948182261/100000000000000000000 : ℝ) := by
    have hpowers : (10647/100000 : ℝ)^4169 ≤ (10953702948182261/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10647 : ℕ)^4169*100000000000000000000^1024 ≤ 10953702948182261^1024*100000^4169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10647 100000 10953702948182261 100000000000000000000 4169 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10647/100000 : ℝ)) (X := (10953702948182261/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14801/100000 : ℝ) ^ (4169/1024 : ℝ) ≤ (41880808970002397/100000000000000000000 : ℝ) := by
    have hpowers : (14801/100000 : ℝ)^4169 ≤ (41880808970002397/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14801 : ℕ)^4169*100000000000000000000^1024 ≤ 41880808970002397^1024*100000^4169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14801 100000 41880808970002397 100000000000000000000 4169 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14801/100000 : ℝ)) (X := (41880808970002397/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010953702948182261/50000000000000000000 : ℝ) ≤ (10000538050615743/10000000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (50010953702948182261/50000000000000000000 : ℝ)^1024 ≤ (10000538050615743/10000000000000000 : ℝ)^4169 := by
      have hnat : (50010953702948182261 : ℕ)^1024*10000000000000000^4169 ≤ 10000538050615743^4169*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010953702948182261 50000000000000000000 10000538050615743 10000000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538050615743/10000000000000000 : ℝ)) (X := (50010953702948182261/50000000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026417255959092329/50000000000000000000 : ℝ) ≤ (10001297475693541/10000000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (50026417255959092329/50000000000000000000 : ℝ)^1024 ≤ (10001297475693541/10000000000000000 : ℝ)^4169 := by
      have hnat : (50026417255959092329 : ℕ)^1024*10000000000000000^4169 ≤ 10001297475693541^4169*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026417255959092329 50000000000000000000 10001297475693541 10000000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001297475693541/10000000000000000 : ℝ)) (X := (50026417255959092329/50000000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50041880808970002397/50000000000000000000 : ℝ) ≤ (10002056900771339/10000000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (50041880808970002397/50000000000000000000 : ℝ)^1024 ≤ (10002056900771339/10000000000000000 : ℝ)^4169 := by
      have hnat : (50041880808970002397 : ℕ)^1024*10000000000000000^4169 ≤ 10002056900771339^4169*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50041880808970002397 50000000000000000000 10002056900771339 10000000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002056900771339/10000000000000000 : ℝ)) (X := (50041880808970002397/50000000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10953702948182261/100000000000000000000 : ℝ) ≤ ((4152606386465116581/4154000000000000000 : ℝ)+2*(379712538899/207700000000000 : ℝ)*(10647/100000 : ℝ))^(4169/1024 : ℝ) := by
    rw [show (4152606386465116581/4154000000000000000 : ℝ)+2*(379712538899/207700000000000 : ℝ)*(10647/100000 : ℝ)=(10000538050615743/10000000000000000 : ℝ) by norm_num, show 1+2*(10953702948182261/100000000000000000000 : ℝ)=(50010953702948182261/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(41880808970002397/100000000000000000000 : ℝ)+(10953702948182261/100000000000000000000 : ℝ) ≤ ((4152606386465116581/4154000000000000000 : ℝ)+(379712538899/207700000000000 : ℝ)*((14801/100000 : ℝ)+(10647/100000 : ℝ)))^(4169/1024 : ℝ) := by
    rw [show (4152606386465116581/4154000000000000000 : ℝ)+(379712538899/207700000000000 : ℝ)*((14801/100000 : ℝ)+(10647/100000 : ℝ))=(10001297475693541/10000000000000000 : ℝ) by norm_num, show 1+(41880808970002397/100000000000000000000 : ℝ)+(10953702948182261/100000000000000000000 : ℝ)=(50026417255959092329/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(41880808970002397/100000000000000000000 : ℝ) ≤ ((4152606386465116581/4154000000000000000 : ℝ)+2*(379712538899/207700000000000 : ℝ)*(14801/100000 : ℝ))^(4169/1024 : ℝ) := by
    rw [show (4152606386465116581/4154000000000000000 : ℝ)+2*(379712538899/207700000000000 : ℝ)*(14801/100000 : ℝ)=(10002056900771339/10000000000000000 : ℝ) by norm_num, show 1+2*(41880808970002397/100000000000000000000 : ℝ)=(50041880808970002397/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4152606386465116581/4154000000000000000 : ℝ)*(X 1 0+X 2 0)+(379712538899/207700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (10647/100000 : ℝ)) (hi := (14801/100000 : ℝ)) (c := (4152606386465116581/4154000000000000000 : ℝ)) (alpha := (379712538899/207700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4152606386465116581/4154000000000000000 : ℝ)*(X 0 1+X 2 1)+(379712538899/207700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (10647/100000 : ℝ)) (hi := (14801/100000 : ℝ)) (c := (4152606386465116581/4154000000000000000 : ℝ)) (alpha := (379712538899/207700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4152606386465116581/4154000000000000000 : ℝ)*(X 0 2+X 1 2)+(379712538899/207700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (10647/100000 : ℝ)) (hi := (14801/100000 : ℝ)) (c := (4152606386465116581/4154000000000000000 : ℝ)) (alpha := (379712538899/207700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2164184867/10000000000 : ℝ)*X 0 0+(2700850679/5000000000 : ℝ)*X 0 1+(5257582923/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346936117/10000000000 : ℝ)*X 1 0+(-279677737/1250000000 : ℝ)*X 1 1+(328598977/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346936499/10000000000 : ℝ)*X 2 0+(5257582691/10000000000 : ℝ)*X 2 1+(-279677829/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4363650709/10000000000 : ℝ)*X 0 0+(4222521319/10000000000 : ℝ)*X 0 1+(2254734003/5000000000 : ℝ)*X 0 2+(4363650709/10000000000 : ℝ)*X 1 0+(4222521319/10000000000 : ℝ)*X 1 1+(2254734003/5000000000 : ℝ)*X 1 2+(4363650709/10000000000 : ℝ)*X 2 0+(4222521319/10000000000 : ℝ)*X 2 1+(2254734003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1082096331/5000000000 : ℝ)*X 0 0+(328624533/625000000 : ℝ)*X 0 1+(2700644773/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310415167/10000000000 : ℝ)*X 1 0+(-209371497/1000000000 : ℝ)*X 1 1+(1350322373/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310415121/10000000000 : ℝ)*X 2 0+(5401289459/10000000000 : ℝ)*X 2 1+(-2093715077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1090916187/2500000000 : ℝ)*X 0 0+(4508650787/10000000000 : ℝ)*X 0 1+(527917747/1250000000 : ℝ)*X 0 2+(1090916187/2500000000 : ℝ)*X 1 0+(4508650787/10000000000 : ℝ)*X 1 1+(527917747/1250000000 : ℝ)*X 1 2+(1090916187/2500000000 : ℝ)*X 2 0+(4508650787/10000000000 : ℝ)*X 2 1+(527917747/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (93064401778527979494819/10385000000000000000000000000 : ℝ) := by norm_num
    linear_combination (159666151/20000000000000 : ℝ)*(base15) + (2568769/25000000000000 : ℝ)*(base29) + (21478661/20000000000000 : ℝ)*(lower2) + (13369073/20000000000000 : ℝ)*(upper3) + (20422233/6250000000000 : ℝ)*(lower4) + (5211878465381981/100000000000000 : ℝ)*(major0) + (5211878475657057/100000000000000 : ℝ)*(major1) + (5211878475657057/100000000000000 : ℝ)*(major2) + (6938756870245597/100000000000000 : ℝ)*(sp0) + (1387751212327953/20000000000000 : ℝ)*(sp1) + (6938725931635263/100000000000000 : ℝ)*(sp2) + (871246729497293/25000000000000 : ℝ)*(sp3) + (30928335259/100000000000000 : ℝ)*(sp6) + (3216091287/25000000000000 : ℝ)*(sp7) + (43562497279429/1250000000000 : ℝ)*(f.failure) + (6938756870245597/100000000000000 : ℝ)*(f.sum) + (11953785507581/5192500000000000000000000000 : ℝ)*base66 + (2433626107792777883/415400000000000000000000000000000 : ℝ)*base68 + (13367827064815822117/415400000000000000000000000000000 : ℝ)*base69 + (20201018515351213039/415400000000000000000000000000000 : ℝ)*base72 + (19503525208459/10385000000000000000000000000 : ℝ)*base74 + (654751410274742117/415400000000000000000000000000000 : ℝ)*base75 + (6584254680955386961/415400000000000000000000000000000 : ℝ)*base77 + (3465305008694457883/415400000000000000000000000000000 : ℝ)*base80 + (165561761425249/2596250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (215611/125000000000000000000 : ℝ)*base89 + (215611/125000000000000000000 : ℝ)*base91 + (215611/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (59301805858618909499601/10385000000000000000000000000 : ℝ) := by norm_num
    linear_combination (115830773/6250000000000 : ℝ)*(base19) + (970356723/50000000000000 : ℝ)*(base23) + (13291581/12500000000000 : ℝ)*(upper2) + (25441453/25000000000000 : ℝ)*(upper3) + (58831031/20000000000000 : ℝ)*(upper5) + (2620871575994243/50000000000000 : ℝ)*(major0) + (2620871575994243/50000000000000 : ℝ)*(major1) + (2620871575994243/50000000000000 : ℝ)*(major2) + (49603106343/100000000000000 : ℝ)*(sp1) + (41988558213/100000000000000 : ℝ)*(sp2) + (3489258436428593/50000000000000 : ℝ)*(sp4) + (279138616658339/4000000000000 : ℝ)*(sp5) + (6978472943585527/100000000000000 : ℝ)*(sp6) + (1752484620387677/50000000000000 : ℝ)*(sp7) + (1752484620387677/50000000000000 : ℝ)*(f.failure) + (3489258436428593/50000000000000 : ℝ)*(f.sum) + (30377477186093/5192500000000000000000000000 : ℝ)*base66 + (1961531543557216817/207700000000000000000000000000000 : ℝ)*base68 + (809949285786983183/207700000000000000000000000000000 : ℝ)*base69 + (429908426060616817/207700000000000000000000000000000 : ℝ)*base72 + (29572093746643/5192500000000000000000000000 : ℝ)*base74 + (749457715902983183/207700000000000000000000000000000 : ℝ)*base75 + (3372869875565216817/207700000000000000000000000000000 : ℝ)*base78 + (247224017359183183/207700000000000000000000000000000 : ℝ)*base79 + (26256406512051/10385000000000000000000000000 : ℝ)*base82 + (57273843/5000000000000000000000 : ℝ)*base89 + (57273843/5000000000000000000000 : ℝ)*base91 + (57273843/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1146_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14801/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10647/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11183/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1146_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1146_s5_0 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-135300883/625000000 : ℝ)*x 0 + (2697404697/5000000000 : ℝ)*x 1 + (5264061721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135300883/625000000 : ℝ)^8339 ≤ (6577191718711/50000000000000 : ℝ)^6291 := by
    have hnat : (135300883 : ℕ)^8339*50000000000000^6291 ≤ 6577191718711^6291*625000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135300883 625000000 6577191718711 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697404697/5000000000 : ℝ)^8339 ≤ (44128830643267/100000000000000 : ℝ)^6291 := by
    have hnat : (2697404697 : ℕ)^8339*100000000000000^6291 ≤ 44128830643267^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697404697 5000000000 44128830643267 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264061721/10000000000 : ℝ)^8339 ≤ (8543357180371/20000000000000 : ℝ)^6291 := by
    have hnat : (5264061721 : ℕ)^8339*20000000000000^6291 ≤ 8543357180371^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264061721 10000000000 8543357180371 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-135300883/625000000 : ℝ), (2697404697/5000000000 : ℝ), (5264061721/10000000000 : ℝ)] ![(6577191718711/50000000000000 : ℝ), (44128830643267/100000000000000 : ℝ), (8543357180371/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-135300883/625000000 : ℝ)|^8339 ≤ (6577191718711/50000000000000 : ℝ)^6291
        have hw : |(-135300883/625000000 : ℝ)|=(135300883/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697404697/5000000000 : ℝ)|^8339 ≤ (44128830643267/100000000000000 : ℝ)^6291
        have hw : |(2697404697/5000000000 : ℝ)|=(2697404697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264061721/10000000000 : ℝ)|^8339 ≤ (8543357180371/20000000000000 : ℝ)^6291
        have hw : |(5264061721/10000000000 : ℝ)|=(5264061721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s5_1 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267260383/500000000 : ℝ)*x 0 + (-1115578567/5000000000 : ℝ)*x 1 + (5264061721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267260383/500000000 : ℝ)^8339 ≤ (43591816571069/100000000000000 : ℝ)^6291 := by
    have hnat : (267260383 : ℕ)^8339*100000000000000^6291 ≤ 43591816571069^6291*500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267260383 500000000 43591816571069 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115578567/5000000000 : ℝ)^8339 ≤ (1711424689219/12500000000000 : ℝ)^6291 := by
    have hnat : (1115578567 : ℕ)^8339*12500000000000^6291 ≤ 1711424689219^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115578567 5000000000 1711424689219 12500000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264061721/10000000000 : ℝ)^8339 ≤ (8543357180371/20000000000000 : ℝ)^6291 := by
    have hnat : (5264061721 : ℕ)^8339*20000000000000^6291 ≤ 8543357180371^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264061721 10000000000 8543357180371 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267260383/500000000 : ℝ), (-1115578567/5000000000 : ℝ), (5264061721/10000000000 : ℝ)] ![(43591816571069/100000000000000 : ℝ), (1711424689219/12500000000000 : ℝ), (8543357180371/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267260383/500000000 : ℝ)|^8339 ≤ (43591816571069/100000000000000 : ℝ)^6291
        have hw : |(267260383/500000000 : ℝ)|=(267260383/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1115578567/5000000000 : ℝ)|^8339 ≤ (1711424689219/12500000000000 : ℝ)^6291
        have hw : |(-1115578567/5000000000 : ℝ)|=(1115578567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264061721/10000000000 : ℝ)|^8339 ≤ (8543357180371/20000000000000 : ℝ)^6291
        have hw : |(5264061721/10000000000 : ℝ)|=(5264061721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s5_2 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267260383/500000000 : ℝ)*x 0 + (5264061721/10000000000 : ℝ)*x 1 + (-1115578567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267260383/500000000 : ℝ)^8339 ≤ (43591816571069/100000000000000 : ℝ)^6291 := by
    have hnat : (267260383 : ℕ)^8339*100000000000000^6291 ≤ 43591816571069^6291*500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267260383 500000000 43591816571069 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264061721/10000000000 : ℝ)^8339 ≤ (8543357180371/20000000000000 : ℝ)^6291 := by
    have hnat : (5264061721 : ℕ)^8339*20000000000000^6291 ≤ 8543357180371^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264061721 10000000000 8543357180371 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1115578567/5000000000 : ℝ)^8339 ≤ (1711424689219/12500000000000 : ℝ)^6291 := by
    have hnat : (1115578567 : ℕ)^8339*12500000000000^6291 ≤ 1711424689219^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115578567 5000000000 1711424689219 12500000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267260383/500000000 : ℝ), (5264061721/10000000000 : ℝ), (-1115578567/5000000000 : ℝ)] ![(43591816571069/100000000000000 : ℝ), (8543357180371/20000000000000 : ℝ), (1711424689219/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267260383/500000000 : ℝ)|^8339 ≤ (43591816571069/100000000000000 : ℝ)^6291
        have hw : |(267260383/500000000 : ℝ)|=(267260383/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264061721/10000000000 : ℝ)|^8339 ≤ (8543357180371/20000000000000 : ℝ)^6291
        have hw : |(5264061721/10000000000 : ℝ)|=(5264061721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1115578567/5000000000 : ℝ)|^8339 ≤ (1711424689219/12500000000000 : ℝ)^6291
        have hw : |(-1115578567/5000000000 : ℝ)|=(1115578567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s5_3 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364017479/10000000000 : ℝ)*x 0 + (52947319/125000000 : ℝ)*x 1 + (4496108737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364017479/10000000000 : ℝ)^8339 ≤ (33316052037099/100000000000000 : ℝ)^6291 := by
    have hnat : (4364017479 : ℕ)^8339*100000000000000^6291 ≤ 33316052037099^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364017479 10000000000 33316052037099 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52947319/125000000 : ℝ)^8339 ≤ (32024649928829/100000000000000 : ℝ)^6291 := by
    have hnat : (52947319 : ℕ)^8339*100000000000000^6291 ≤ 32024649928829^6291*125000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52947319 125000000 32024649928829 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4496108737/10000000000 : ℝ)^8339 ≤ (4332412252163/12500000000000 : ℝ)^6291 := by
    have hnat : (4496108737 : ℕ)^8339*12500000000000^6291 ≤ 4332412252163^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496108737 10000000000 4332412252163 12500000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364017479/10000000000 : ℝ), (52947319/125000000 : ℝ), (4496108737/10000000000 : ℝ)] ![(33316052037099/100000000000000 : ℝ), (32024649928829/100000000000000 : ℝ), (4332412252163/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364017479/10000000000 : ℝ)|^8339 ≤ (33316052037099/100000000000000 : ℝ)^6291
        have hw : |(4364017479/10000000000 : ℝ)|=(4364017479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52947319/125000000 : ℝ)|^8339 ≤ (32024649928829/100000000000000 : ℝ)^6291
        have hw : |(52947319/125000000 : ℝ)|=(52947319/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4496108737/10000000000 : ℝ)|^8339 ≤ (4332412252163/12500000000000 : ℝ)^6291
        have hw : |(4496108737/10000000000 : ℝ)|=(4496108737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s5_4 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2164819429/10000000000 : ℝ)*x 0 + (41128121/78125000 : ℝ)*x 1 + (5394470369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164819429/10000000000 : ℝ)^8339 ≤ (3288606533723/25000000000000 : ℝ)^6291 := by
    have hnat : (2164819429 : ℕ)^8339*25000000000000^6291 ≤ 3288606533723^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164819429 10000000000 3288606533723 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41128121/78125000 : ℝ)^8339 ≤ (8544083827617/20000000000000 : ℝ)^6291 := by
    have hnat : (41128121 : ℕ)^8339*20000000000000^6291 ≤ 8544083827617^6291*78125000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41128121 78125000 8544083827617 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394470369/10000000000 : ℝ)^8339 ≤ (8825030941549/20000000000000 : ℝ)^6291 := by
    have hnat : (5394470369 : ℕ)^8339*20000000000000^6291 ≤ 8825030941549^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394470369 10000000000 8825030941549 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2164819429/10000000000 : ℝ), (41128121/78125000 : ℝ), (5394470369/10000000000 : ℝ)] ![(3288606533723/25000000000000 : ℝ), (8544083827617/20000000000000 : ℝ), (8825030941549/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2164819429/10000000000 : ℝ)|^8339 ≤ (3288606533723/25000000000000 : ℝ)^6291
        have hw : |(-2164819429/10000000000 : ℝ)|=(2164819429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41128121/78125000 : ℝ)|^8339 ≤ (8544083827617/20000000000000 : ℝ)^6291
        have hw : |(41128121/78125000 : ℝ)|=(41128121/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394470369/10000000000 : ℝ)|^8339 ≤ (8825030941549/20000000000000 : ℝ)^6291
        have hw : |(5394470369/10000000000 : ℝ)|=(5394470369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s5_5 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (332004547/625000000 : ℝ)*x 0 + (-262593561/1250000000 : ℝ)*x 1 + (1078894073/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332004547/625000000 : ℝ)^8339 ≤ (172935930969/400000000000 : ℝ)^6291 := by
    have hnat : (332004547 : ℕ)^8339*400000000000^6291 ≤ 172935930969^6291*625000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332004547 625000000 172935930969 400000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262593561/1250000000 : ℝ)^8339 ≤ (3160215645081/25000000000000 : ℝ)^6291 := by
    have hnat : (262593561 : ℕ)^8339*25000000000000^6291 ≤ 3160215645081^6291*1250000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262593561 1250000000 3160215645081 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078894073/2000000000 : ℝ)^8339 ≤ (70600247463/160000000000 : ℝ)^6291 := by
    have hnat : (1078894073 : ℕ)^8339*160000000000^6291 ≤ 70600247463^6291*2000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078894073 2000000000 70600247463 160000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332004547/625000000 : ℝ), (-262593561/1250000000 : ℝ), (1078894073/2000000000 : ℝ)] ![(172935930969/400000000000 : ℝ), (3160215645081/25000000000000 : ℝ), (70600247463/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332004547/625000000 : ℝ)|^8339 ≤ (172935930969/400000000000 : ℝ)^6291
        have hw : |(332004547/625000000 : ℝ)|=(332004547/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-262593561/1250000000 : ℝ)|^8339 ≤ (3160215645081/25000000000000 : ℝ)^6291
        have hw : |(-262593561/1250000000 : ℝ)|=(262593561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078894073/2000000000 : ℝ)|^8339 ≤ (70600247463/160000000000 : ℝ)^6291
        have hw : |(1078894073/2000000000 : ℝ)|=(1078894073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s5_6 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328018189/2500000000 : ℝ)*x 0 + (5394470363/10000000000 : ℝ)*x 1 + (-420149697/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328018189/2500000000 : ℝ)^8339 ≤ (10808495696351/25000000000000 : ℝ)^6291 := by
    have hnat : (1328018189 : ℕ)^8339*25000000000000^6291 ≤ 10808495696351^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328018189 2500000000 10808495696351 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394470363/10000000000 : ℝ)^8339 ≤ (44125154642689/100000000000000 : ℝ)^6291 := by
    have hnat : (5394470363 : ℕ)^8339*100000000000000^6291 ≤ 44125154642689^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394470363 10000000000 44125154642689 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (420149697/2000000000 : ℝ)^8339 ≤ (2528172511279/20000000000000 : ℝ)^6291 := by
    have hnat : (420149697 : ℕ)^8339*20000000000000^6291 ≤ 2528172511279^6291*2000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420149697 2000000000 2528172511279 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328018189/2500000000 : ℝ), (5394470363/10000000000 : ℝ), (-420149697/2000000000 : ℝ)] ![(10808495696351/25000000000000 : ℝ), (44125154642689/100000000000000 : ℝ), (2528172511279/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328018189/2500000000 : ℝ)|^8339 ≤ (10808495696351/25000000000000 : ℝ)^6291
        have hw : |(1328018189/2500000000 : ℝ)|=(1328018189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394470363/10000000000 : ℝ)|^8339 ≤ (44125154642689/100000000000000 : ℝ)^6291
        have hw : |(5394470363/10000000000 : ℝ)|=(5394470363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-420149697/2000000000 : ℝ)|^8339 ≤ (2528172511279/20000000000000 : ℝ)^6291
        have hw : |(-420149697/2000000000 : ℝ)|=(420149697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s5_7 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364028027/10000000000 : ℝ)*x 0 + (1123859057/2500000000 : ℝ)*x 1 + (4236460529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364028027/10000000000 : ℝ)^8339 ≤ (33316158778189/100000000000000 : ℝ)^6291 := by
    have hnat : (4364028027 : ℕ)^8339*100000000000000^6291 ≤ 33316158778189^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364028027 10000000000 33316158778189 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123859057/2500000000 : ℝ)^8339 ≤ (17326213154059/50000000000000 : ℝ)^6291 := by
    have hnat : (1123859057 : ℕ)^8339*50000000000000^6291 ≤ 17326213154059^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123859057 2500000000 17326213154059 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4236460529/10000000000 : ℝ)^8339 ≤ (3203141489371/10000000000000 : ℝ)^6291 := by
    have hnat : (4236460529 : ℕ)^8339*10000000000000^6291 ≤ 3203141489371^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236460529 10000000000 3203141489371 10000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364028027/10000000000 : ℝ), (1123859057/2500000000 : ℝ), (4236460529/10000000000 : ℝ)] ![(33316158778189/100000000000000 : ℝ), (17326213154059/50000000000000 : ℝ), (3203141489371/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364028027/10000000000 : ℝ)|^8339 ≤ (33316158778189/100000000000000 : ℝ)^6291
        have hw : |(4364028027/10000000000 : ℝ)|=(4364028027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123859057/2500000000 : ℝ)|^8339 ≤ (17326213154059/50000000000000 : ℝ)^6291
        have hw : |(1123859057/2500000000 : ℝ)|=(1123859057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4236460529/10000000000 : ℝ)|^8339 ≤ (3203141489371/10000000000000 : ℝ)^6291
        have hw : |(4236460529/10000000000 : ℝ)|=(4236460529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1146_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11183/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11321/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1409/10000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (11183/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11183/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11183/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11183/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11183/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11183/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11183/100000 : ℝ) ^ (4169/1024 : ℝ) ≤ (6532448014043/48828125000000000 : ℝ) := by
    have hpowers : (11183/100000 : ℝ)^4169 ≤ (6532448014043/48828125000000000 : ℝ)^1024 := by
      have hnat : (11183 : ℕ)^4169*48828125000000000^1024 ≤ 6532448014043^1024*100000^4169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11183 100000 6532448014043 48828125000000000 4169 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11183/100000 : ℝ)) (X := (6532448014043/48828125000000000 : ℝ)) (by norm_num) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (4169/1024 : ℝ) ≤ (35733333593680557/100000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^4169 ≤ (35733333593680557/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2847 : ℕ)^4169*100000000000000000000^1024 ≤ 35733333593680557^1024*20000^4169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 35733333593680557 100000000000000000000 4169 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (35733333593680557/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (24420594948014043/24414062500000000 : ℝ) ≤ (2500164285848179/2500000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (24420594948014043/24414062500000000 : ℝ)^1024 ≤ (2500164285848179/2500000000000000 : ℝ)^4169 := by
      have hnat : (24420594948014043 : ℕ)^1024*2500000000000000^4169 ≤ 2500164285848179^4169*24414062500000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24420594948014043 24414062500000000 2500164285848179 2500000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500164285848179/2500000000000000 : ℝ)) (X := (24420594948014043/24414062500000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049111787126440621/100000000000000000000 : ℝ) ≤ (2500301518089931/2500000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (100049111787126440621/100000000000000000000 : ℝ)^1024 ≤ (2500301518089931/2500000000000000 : ℝ)^4169 := by
      have hnat : (100049111787126440621 : ℕ)^1024*2500000000000000^4169 ≤ 2500301518089931^4169*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049111787126440621 100000000000000000000 2500301518089931 2500000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500301518089931/2500000000000000 : ℝ)) (X := (100049111787126440621/100000000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035733333593680557/50000000000000000000 : ℝ) ≤ (2500438750331683/2500000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (50035733333593680557/50000000000000000000 : ℝ)^1024 ≤ (2500438750331683/2500000000000000 : ℝ)^4169 := by
      have hnat : (50035733333593680557 : ℕ)^1024*2500000000000000^4169 ≤ 2500438750331683^4169*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035733333593680557 50000000000000000000 2500438750331683 2500000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500438750331683/2500000000000000 : ℝ)) (X := (50035733333593680557/50000000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6532448014043/48828125000000000 : ℝ) ≤ ((1906858016022404269/1907500000000000000 : ℝ)+2*(17154030219/9537500000000 : ℝ)*(11183/100000 : ℝ))^(4169/1024 : ℝ) := by
    rw [show (1906858016022404269/1907500000000000000 : ℝ)+2*(17154030219/9537500000000 : ℝ)*(11183/100000 : ℝ)=(2500164285848179/2500000000000000 : ℝ) by norm_num, show 1+2*(6532448014043/48828125000000000 : ℝ)=(24420594948014043/24414062500000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35733333593680557/100000000000000000000 : ℝ)+(6532448014043/48828125000000000 : ℝ) ≤ ((1906858016022404269/1907500000000000000 : ℝ)+(17154030219/9537500000000 : ℝ)*((2847/20000 : ℝ)+(11183/100000 : ℝ)))^(4169/1024 : ℝ) := by
    rw [show (1906858016022404269/1907500000000000000 : ℝ)+(17154030219/9537500000000 : ℝ)*((2847/20000 : ℝ)+(11183/100000 : ℝ))=(2500301518089931/2500000000000000 : ℝ) by norm_num, show 1+(35733333593680557/100000000000000000000 : ℝ)+(6532448014043/48828125000000000 : ℝ)=(100049111787126440621/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35733333593680557/100000000000000000000 : ℝ) ≤ ((1906858016022404269/1907500000000000000 : ℝ)+2*(17154030219/9537500000000 : ℝ)*(2847/20000 : ℝ))^(4169/1024 : ℝ) := by
    rw [show (1906858016022404269/1907500000000000000 : ℝ)+2*(17154030219/9537500000000 : ℝ)*(2847/20000 : ℝ)=(2500438750331683/2500000000000000 : ℝ) by norm_num, show 1+2*(35733333593680557/100000000000000000000 : ℝ)=(50035733333593680557/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1906858016022404269/1907500000000000000 : ℝ)*(X 1 0+X 2 0)+(17154030219/9537500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (11183/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1906858016022404269/1907500000000000000 : ℝ)) (alpha := (17154030219/9537500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1906858016022404269/1907500000000000000 : ℝ)*(X 0 1+X 2 1)+(17154030219/9537500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (11183/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1906858016022404269/1907500000000000000 : ℝ)) (alpha := (17154030219/9537500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1906858016022404269/1907500000000000000 : ℝ)*(X 0 2+X 1 2)+(17154030219/9537500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (11183/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1906858016022404269/1907500000000000000 : ℝ)) (alpha := (17154030219/9537500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-135300883/625000000 : ℝ)*X 0 0+(2697404697/5000000000 : ℝ)*X 0 1+(5264061721/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267260383/500000000 : ℝ)*X 1 0+(-1115578567/5000000000 : ℝ)*X 1 1+(5264061721/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267260383/500000000 : ℝ)*X 2 0+(5264061721/10000000000 : ℝ)*X 2 1+(-1115578567/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364017479/10000000000 : ℝ)*X 0 0+(52947319/125000000 : ℝ)*X 0 1+(4496108737/10000000000 : ℝ)*X 0 2+(4364017479/10000000000 : ℝ)*X 1 0+(52947319/125000000 : ℝ)*X 1 1+(4496108737/10000000000 : ℝ)*X 1 2+(4364017479/10000000000 : ℝ)*X 2 0+(52947319/125000000 : ℝ)*X 2 1+(4496108737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2164819429/10000000000 : ℝ)*X 0 0+(41128121/78125000 : ℝ)*X 0 1+(5394470369/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((332004547/625000000 : ℝ)*X 1 0+(-262593561/1250000000 : ℝ)*X 1 1+(1078894073/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328018189/2500000000 : ℝ)*X 2 0+(5394470363/10000000000 : ℝ)*X 2 1+(-420149697/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4364028027/10000000000 : ℝ)*X 0 0+(1123859057/2500000000 : ℝ)*X 0 1+(4236460529/10000000000 : ℝ)*X 0 2+(4364028027/10000000000 : ℝ)*X 1 0+(1123859057/2500000000 : ℝ)*X 1 1+(4236460529/10000000000 : ℝ)*X 1 2+(4364028027/10000000000 : ℝ)*X 2 0+(1123859057/2500000000 : ℝ)*X 2 1+(4236460529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13392049774290663108909/1907500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1390205387/100000000000000 : ℝ)*(base19) + (647335301/50000000000000 : ℝ)*(base23) + (25532663/50000000000000 : ℝ)*(lower2) + (178262329/100000000000000 : ℝ)*(upper3) + (53656693/50000000000000 : ℝ)*(upper5) + (22441038640239/390625000000 : ℝ)*(major0) + (22441038640239/390625000000 : ℝ)*(major1) + (22441038640239/390625000000 : ℝ)*(major2) + (7648358268758639/100000000000000 : ℝ)*(sp0) + (3824196847962257/50000000000000 : ℝ)*(sp1) + (7648393791459299/100000000000000 : ℝ)*(sp2) + (3841396459774309/100000000000000 : ℝ)*(sp3) + (18408685631/50000000000000 : ℝ)*(sp4) + (10001936847/50000000000000 : ℝ)*(sp7) + (3841416463648003/100000000000000 : ℝ)*(f.failure) + (7648395086129901/100000000000000 : ℝ)*(f.sum) + (10042095296783/3815000000000000000000000000 : ℝ)*base65 + (7693178501451703/5960937500000000000000000000000 : ℝ)*base67 + (4306634326757457/1490234375000000000000000000000 : ℝ)*base69 + (16734894469075281/11921875000000000000000000000000 : ℝ)*base71 + (2419591890507/953750000000000000000000000 : ℝ)*base73 + (70147491875174719/11921875000000000000000000000000 : ℝ)*base76 + (37848851082487219/11921875000000000000000000000000 : ℝ)*base78 + (92158790531330969/11921875000000000000000000000000 : ℝ)*base80 + (11572271829073/3815000000000000000000000000 : ℝ)*base81 + (5487277/10000000000000000000000 : ℝ)*base89 + (5487277/10000000000000000000000 : ℝ)*base91 + (5487277/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25872820398630282875909493/11921875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16806889/4000000000000 : ℝ)*(base19) + (457061049/100000000000000 : ℝ)*(base23) + (454139/1000000000000 : ℝ)*(upper3) + (13562973/100000000000000 : ℝ)*(lower4) + (23122007/50000000000000 : ℝ)*(upper5) + (180460652254003/3125000000000 : ℝ)*(major0) + (180460652254003/3125000000000 : ℝ)*(major1) + (180460652254003/3125000000000 : ℝ)*(major2) + (11120613679/100000000000000 : ℝ)*(sp1) + (12013146131/100000000000000 : ℝ)*(sp2) + (7688115606587617/100000000000000 : ℝ)*(sp4) + (7688104065801713/100000000000000 : ℝ)*(sp5) + (3844051568190219/50000000000000 : ℝ)*(sp6) + (1930683032664329/50000000000000 : ℝ)*(sp7) + (1930683032664329/50000000000000 : ℝ)*(f.failure) + (7688115606587617/100000000000000 : ℝ)*(f.sum) + (6265475719303/3815000000000000000000000000 : ℝ)*base66 + (27824907791248693/5960937500000000000000000000000 : ℝ)*base68 + (23502463371638011/11921875000000000000000000000000 : ℝ)*base70 + (8130558250697429/745117187500000000000000000000 : ℝ)*base71 + (13895881042209/1907500000000000000000000000 : ℝ)*base74 + (69326207436475909/2980468750000000000000000000000 : ℝ)*base76 + (1201308737933267/1490234375000000000000000000000 : ℝ)*base78 + (133122574586981761/11921875000000000000000000000000 : ℝ)*base80 + (3073565132661/1907500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (58504711/5000000000000000000000 : ℝ)*base89 + (58504711/5000000000000000000000 : ℝ)*base91 + (58504711/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1146_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11183/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11321/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1146_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1146_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16491/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (284/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11321/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1146_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1146_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1146_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16491/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (284/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11321/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1146_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

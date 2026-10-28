-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1083_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:51:20.58911+00:00
-- url     : https://prove2.me/submissions/f4573bf8-f784-40dc-9d11-29fc7183e207

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
theorem support_rectangle_w1083_s0_0 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-955312573/5000000000 : ℝ)*x 0 + (3034033847/5000000000 : ℝ)*x 1 + (19091861/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (955312573/5000000000 : ℝ)^2069 ≤ (11086616587759/100000000000000 : ℝ)^1557 := by
    have hnat : (955312573 : ℕ)^2069*100000000000000^1557 ≤ 11086616587759^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955312573 5000000000 11086616587759 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3034033847/5000000000 : ℝ)^2069 ≤ (51488383455439/100000000000000 : ℝ)^1557 := by
    have hnat : (3034033847 : ℕ)^2069*100000000000000^1557 ≤ 51488383455439^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3034033847 5000000000 51488383455439 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19091861/40000000 : ℝ)^2069 ≤ (37424999949029/100000000000000 : ℝ)^1557 := by
    have hnat : (19091861 : ℕ)^2069*100000000000000^1557 ≤ 37424999949029^1557*40000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19091861 40000000 37424999949029 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-955312573/5000000000 : ℝ), (3034033847/5000000000 : ℝ), (19091861/40000000 : ℝ)] ![(11086616587759/100000000000000 : ℝ), (51488383455439/100000000000000 : ℝ), (37424999949029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-955312573/5000000000 : ℝ)|^2069 ≤ (11086616587759/100000000000000 : ℝ)^1557
        have hw : |(-955312573/5000000000 : ℝ)|=(955312573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3034033847/5000000000 : ℝ)|^2069 ≤ (51488383455439/100000000000000 : ℝ)^1557
        have hw : |(3034033847/5000000000 : ℝ)|=(3034033847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(19091861/40000000 : ℝ)|^2069 ≤ (37424999949029/100000000000000 : ℝ)^1557
        have hw : |(19091861/40000000 : ℝ)|=(19091861/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s0_1 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1104023241/2000000000 : ℝ)*x 0 + (-2655590041/10000000000 : ℝ)*x 1 + (238648251/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104023241/2000000000 : ℝ)^2069 ≤ (45403686469961/100000000000000 : ℝ)^1557 := by
    have hnat : (1104023241 : ℕ)^2069*100000000000000^1557 ≤ 45403686469961^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104023241 2000000000 45403686469961 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2655590041/10000000000 : ℝ)^2069 ≤ (17171315971017/100000000000000 : ℝ)^1557 := by
    have hnat : (2655590041 : ℕ)^2069*100000000000000^1557 ≤ 17171315971017^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655590041 10000000000 17171315971017 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (238648251/500000000 : ℝ)^2069 ≤ (4678124694069/12500000000000 : ℝ)^1557 := by
    have hnat : (238648251 : ℕ)^2069*12500000000000^1557 ≤ 4678124694069^1557*500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238648251 500000000 4678124694069 12500000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1104023241/2000000000 : ℝ), (-2655590041/10000000000 : ℝ), (238648251/500000000 : ℝ)] ![(45403686469961/100000000000000 : ℝ), (17171315971017/100000000000000 : ℝ), (4678124694069/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1104023241/2000000000 : ℝ)|^2069 ≤ (45403686469961/100000000000000 : ℝ)^1557
        have hw : |(1104023241/2000000000 : ℝ)|=(1104023241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2655590041/10000000000 : ℝ)|^2069 ≤ (17171315971017/100000000000000 : ℝ)^1557
        have hw : |(-2655590041/10000000000 : ℝ)|=(2655590041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(238648251/500000000 : ℝ)|^2069 ≤ (4678124694069/12500000000000 : ℝ)^1557
        have hw : |(238648251/500000000 : ℝ)|=(238648251/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s0_2 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1104023253/2000000000 : ℝ)*x 0 + (4772965209/10000000000 : ℝ)*x 1 + (-1327794867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104023253/2000000000 : ℝ)^2069 ≤ (5675460890719/12500000000000 : ℝ)^1557 := by
    have hnat : (1104023253 : ℕ)^2069*12500000000000^1557 ≤ 5675460890719^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104023253 2000000000 5675460890719 12500000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4772965209/10000000000 : ℝ)^2069 ≤ (37424999521831/100000000000000 : ℝ)^1557 := by
    have hnat : (4772965209 : ℕ)^2069*100000000000000^1557 ≤ 37424999521831^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4772965209 10000000000 37424999521831 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1327794867/5000000000 : ℝ)^2069 ≤ (17171313333151/100000000000000 : ℝ)^1557 := by
    have hnat : (1327794867 : ℕ)^2069*100000000000000^1557 ≤ 17171313333151^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327794867 5000000000 17171313333151 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1104023253/2000000000 : ℝ), (4772965209/10000000000 : ℝ), (-1327794867/5000000000 : ℝ)] ![(5675460890719/12500000000000 : ℝ), (37424999521831/100000000000000 : ℝ), (17171313333151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1104023253/2000000000 : ℝ)|^2069 ≤ (5675460890719/12500000000000 : ℝ)^1557
        have hw : |(1104023253/2000000000 : ℝ)|=(1104023253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4772965209/10000000000 : ℝ)|^2069 ≤ (37424999521831/100000000000000 : ℝ)^1557
        have hw : |(4772965209/10000000000 : ℝ)|=(4772965209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1327794867/5000000000 : ℝ)|^2069 ≤ (17171313333151/100000000000000 : ℝ)^1557
        have hw : |(-1327794867/5000000000 : ℝ)|=(1327794867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s0_3 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4205805771/10000000000 : ℝ)*x 0 + (624794521/2000000000 : ℝ)*x 1 + (226830411/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4205805771/10000000000 : ℝ)^2069 ≤ (3163419045723/10000000000000 : ℝ)^1557 := by
    have hnat : (4205805771 : ℕ)^2069*10000000000000^1557 ≤ 3163419045723^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4205805771 10000000000 3163419045723 10000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (624794521/2000000000 : ℝ)^2069 ≤ (5327065119859/25000000000000 : ℝ)^1557 := by
    have hnat : (624794521 : ℕ)^2069*25000000000000^1557 ≤ 5327065119859^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624794521 2000000000 5327065119859 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226830411/400000000 : ℝ)^2069 ≤ (47057549045259/100000000000000 : ℝ)^1557 := by
    have hnat : (226830411 : ℕ)^2069*100000000000000^1557 ≤ 47057549045259^1557*400000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226830411 400000000 47057549045259 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4205805771/10000000000 : ℝ), (624794521/2000000000 : ℝ), (226830411/400000000 : ℝ)] ![(3163419045723/10000000000000 : ℝ), (5327065119859/25000000000000 : ℝ), (47057549045259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4205805771/10000000000 : ℝ)|^2069 ≤ (3163419045723/10000000000000 : ℝ)^1557
        have hw : |(4205805771/10000000000 : ℝ)|=(4205805771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(624794521/2000000000 : ℝ)|^2069 ≤ (5327065119859/25000000000000 : ℝ)^1557
        have hw : |(624794521/2000000000 : ℝ)|=(624794521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(226830411/400000000 : ℝ)|^2069 ≤ (47057549045259/100000000000000 : ℝ)^1557
        have hw : |(226830411/400000000 : ℝ)|=(226830411/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s0_4 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1915947449/10000000000 : ℝ)*x 0 + (4806399759/10000000000 : ℝ)*x 1 + (188545681/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1915947449/10000000000 : ℝ)^2069 ≤ (5563837103121/50000000000000 : ℝ)^1557 := by
    have hnat : (1915947449 : ℕ)^2069*50000000000000^1557 ≤ 5563837103121^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915947449 10000000000 5563837103121 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4806399759/10000000000 : ℝ)^2069 ≤ (7554754049621/20000000000000 : ℝ)^1557 := by
    have hnat : (4806399759 : ℕ)^2069*20000000000000^1557 ≤ 7554754049621^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4806399759 10000000000 7554754049621 20000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188545681/312500000 : ℝ)^2069 ≤ (51098555524197/100000000000000 : ℝ)^1557 := by
    have hnat : (188545681 : ℕ)^2069*100000000000000^1557 ≤ 51098555524197^1557*312500000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188545681 312500000 51098555524197 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1915947449/10000000000 : ℝ), (4806399759/10000000000 : ℝ), (188545681/312500000 : ℝ)] ![(5563837103121/50000000000000 : ℝ), (7554754049621/20000000000000 : ℝ), (51098555524197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1915947449/10000000000 : ℝ)|^2069 ≤ (5563837103121/50000000000000 : ℝ)^1557
        have hw : |(-1915947449/10000000000 : ℝ)|=(1915947449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4806399759/10000000000 : ℝ)|^2069 ≤ (7554754049621/20000000000000 : ℝ)^1557
        have hw : |(4806399759/10000000000 : ℝ)|=(4806399759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(188545681/312500000 : ℝ)|^2069 ≤ (51098555524197/100000000000000 : ℝ)^1557
        have hw : |(188545681/312500000 : ℝ)|=(188545681/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s0_5 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2584256453/5000000000 : ℝ)*x 0 + (-1395096249/10000000000 : ℝ)*x 1 + (3016730083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584256453/5000000000 : ℝ)^2069 ≤ (10400386373163/25000000000000 : ℝ)^1557 := by
    have hnat : (2584256453 : ℕ)^2069*25000000000000^1557 ≤ 10400386373163^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584256453 5000000000 10400386373163 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1395096249/10000000000 : ℝ)^2069 ≤ (1459983453877/20000000000000 : ℝ)^1557 := by
    have hnat : (1395096249 : ℕ)^2069*20000000000000^1557 ≤ 1459983453877^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1395096249 10000000000 1459983453877 20000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3016730083/5000000000 : ℝ)^2069 ≤ (51098537224897/100000000000000 : ℝ)^1557 := by
    have hnat : (3016730083 : ℕ)^2069*100000000000000^1557 ≤ 51098537224897^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3016730083 5000000000 51098537224897 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2584256453/5000000000 : ℝ), (-1395096249/10000000000 : ℝ), (3016730083/5000000000 : ℝ)] ![(10400386373163/25000000000000 : ℝ), (1459983453877/20000000000000 : ℝ), (51098537224897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2584256453/5000000000 : ℝ)|^2069 ≤ (10400386373163/25000000000000 : ℝ)^1557
        have hw : |(2584256453/5000000000 : ℝ)|=(2584256453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1395096249/10000000000 : ℝ)|^2069 ≤ (1459983453877/20000000000000 : ℝ)^1557
        have hw : |(-1395096249/10000000000 : ℝ)|=(1395096249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3016730083/5000000000 : ℝ)|^2069 ≤ (51098537224897/100000000000000 : ℝ)^1557
        have hw : |(3016730083/5000000000 : ℝ)|=(3016730083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s0_6 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (161516029/312500000 : ℝ)*x 0 + (6033461561/10000000000 : ℝ)*x 1 + (-697546979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (161516029/312500000 : ℝ)^2069 ≤ (41601545727961/100000000000000 : ℝ)^1557 := by
    have hnat : (161516029 : ℕ)^2069*100000000000000^1557 ≤ 41601545727961^1557*312500000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161516029 312500000 41601545727961 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6033461561/10000000000 : ℝ)^2069 ≤ (51098552924481/100000000000000 : ℝ)^1557 := by
    have hnat : (6033461561 : ℕ)^2069*100000000000000^1557 ≤ 51098552924481^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6033461561 10000000000 51098552924481 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (697546979/5000000000 : ℝ)^2069 ≤ (3649950669787/50000000000000 : ℝ)^1557 := by
    have hnat : (697546979 : ℕ)^2069*50000000000000^1557 ≤ 3649950669787^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      697546979 5000000000 3649950669787 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(161516029/312500000 : ℝ), (6033461561/10000000000 : ℝ), (-697546979/5000000000 : ℝ)] ![(41601545727961/100000000000000 : ℝ), (51098552924481/100000000000000 : ℝ), (3649950669787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(161516029/312500000 : ℝ)|^2069 ≤ (41601545727961/100000000000000 : ℝ)^1557
        have hw : |(161516029/312500000 : ℝ)|=(161516029/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6033461561/10000000000 : ℝ)|^2069 ≤ (51098552924481/100000000000000 : ℝ)^1557
        have hw : |(6033461561/10000000000 : ℝ)|=(6033461561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-697546979/5000000000 : ℝ)|^2069 ≤ (3649950669787/50000000000000 : ℝ)^1557
        have hw : |(-697546979/5000000000 : ℝ)|=(697546979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s0_7 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4216269267/10000000000 : ℝ)*x 0 + (1121002127/2000000000 : ℝ)*x 1 + (1596012497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4216269267/10000000000 : ℝ)^2069 ≤ (7934703758687/25000000000000 : ℝ)^1557 := by
    have hnat : (4216269267 : ℕ)^2069*25000000000000^1557 ≤ 7934703758687^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216269267 10000000000 7934703758687 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121002127/2000000000 : ℝ)^2069 ≤ (46333909317763/100000000000000 : ℝ)^1557 := by
    have hnat : (1121002127 : ℕ)^2069*100000000000000^1557 ≤ 46333909317763^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121002127 2000000000 46333909317763 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1596012497/5000000000 : ℝ)^2069 ≤ (5481818906523/25000000000000 : ℝ)^1557 := by
    have hnat : (1596012497 : ℕ)^2069*25000000000000^1557 ≤ 5481818906523^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596012497 5000000000 5481818906523 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4216269267/10000000000 : ℝ), (1121002127/2000000000 : ℝ), (1596012497/5000000000 : ℝ)] ![(7934703758687/25000000000000 : ℝ), (46333909317763/100000000000000 : ℝ), (5481818906523/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4216269267/10000000000 : ℝ)|^2069 ≤ (7934703758687/25000000000000 : ℝ)^1557
        have hw : |(4216269267/10000000000 : ℝ)|=(4216269267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121002127/2000000000 : ℝ)|^2069 ≤ (46333909317763/100000000000000 : ℝ)^1557
        have hw : |(1121002127/2000000000 : ℝ)|=(1121002127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1596012497/5000000000 : ℝ)|^2069 ≤ (5481818906523/25000000000000 : ℝ)^1557
        have hw : |(1596012497/5000000000 : ℝ)|=(1596012497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1083_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (21/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (28043/100000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (8275/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8275 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8275*1^2048 ≤ 0^2048*1^8275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8275 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8275/2048 : ℝ) ≤ (2466678303154286737/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8275 ≤ (2466678303154286737/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8275*100000000000000000000^2048 ≤ 2466678303154286737^2048*5^8275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2466678303154286737 100000000000000000000 8275 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2466678303154286737/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8275 := by
      have hnat : (1 : ℕ)^2048*1^8275 ≤ 1^8275*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102466678303154286737/100000000000000000000 : ℝ) ≤ (5030244932286737/5000000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (102466678303154286737/100000000000000000000 : ℝ)^2048 ≤ (5030244932286737/5000000000000000 : ℝ)^8275 := by
      have hnat : (102466678303154286737 : ℕ)^2048*5000000000000000^8275 ≤ 5030244932286737^8275*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102466678303154286737 100000000000000000000 5030244932286737 5000000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5030244932286737/5000000000000000 : ℝ)) (X := (102466678303154286737/100000000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52466678303154286737/50000000000000000000 : ℝ) ≤ (2530244932286737/2500000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (52466678303154286737/50000000000000000000 : ℝ)^2048 ≤ (2530244932286737/2500000000000000 : ℝ)^8275 := by
      have hnat : (52466678303154286737 : ℕ)^2048*2500000000000000^8275 ≤ 2530244932286737^8275*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52466678303154286737 50000000000000000000 2530244932286737 2500000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2530244932286737/2500000000000000 : ℝ)) (X := (52466678303154286737/50000000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(30244932286737/2000000000000000 : ℝ)*(0 : ℝ))^(8275/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(30244932286737/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2466678303154286737/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(30244932286737/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8275/2048 : ℝ) := by
    rw [show (1 : ℝ)+(30244932286737/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5030244932286737/5000000000000000 : ℝ) by norm_num, show 1+(2466678303154286737/100000000000000000000 : ℝ)+(0 : ℝ)=(102466678303154286737/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2466678303154286737/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(30244932286737/2000000000000000 : ℝ)*(2/5 : ℝ))^(8275/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(30244932286737/2000000000000000 : ℝ)*(2/5 : ℝ)=(2530244932286737/2500000000000000 : ℝ) by norm_num, show 1+2*(2466678303154286737/100000000000000000000 : ℝ)=(52466678303154286737/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(30244932286737/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30244932286737/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(30244932286737/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30244932286737/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(30244932286737/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30244932286737/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-955312573/5000000000 : ℝ)*X 0 0+(3034033847/5000000000 : ℝ)*X 0 1+(19091861/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1104023241/2000000000 : ℝ)*X 1 0+(-2655590041/10000000000 : ℝ)*X 1 1+(238648251/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1104023253/2000000000 : ℝ)*X 2 0+(4772965209/10000000000 : ℝ)*X 2 1+(-1327794867/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4205805771/10000000000 : ℝ)*X 0 0+(624794521/2000000000 : ℝ)*X 0 1+(226830411/400000000 : ℝ)*X 0 2+(4205805771/10000000000 : ℝ)*X 1 0+(624794521/2000000000 : ℝ)*X 1 1+(226830411/400000000 : ℝ)*X 1 2+(4205805771/10000000000 : ℝ)*X 2 0+(624794521/2000000000 : ℝ)*X 2 1+(226830411/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1915947449/10000000000 : ℝ)*X 0 0+(4806399759/10000000000 : ℝ)*X 0 1+(188545681/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2584256453/5000000000 : ℝ)*X 1 0+(-1395096249/10000000000 : ℝ)*X 1 1+(3016730083/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((161516029/312500000 : ℝ)*X 2 0+(6033461561/10000000000 : ℝ)*X 2 1+(-697546979/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4216269267/10000000000 : ℝ)*X 0 0+(1121002127/2000000000 : ℝ)*X 0 1+(1596012497/5000000000 : ℝ)*X 0 2+(4216269267/10000000000 : ℝ)*X 1 0+(1121002127/2000000000 : ℝ)*X 1 1+(1596012497/5000000000 : ℝ)*X 1 2+(4216269267/10000000000 : ℝ)*X 2 0+(1121002127/2000000000 : ℝ)*X 2 1+(1596012497/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5689016250101241111/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6000153/6250000000000 : ℝ)*(base1) + (127640043/10000000000000 : ℝ)*(base19) + (1178294423/100000000000000 : ℝ)*(base23) + (26624677/25000000000000 : ℝ)*(base24) + (28013897/10000000000000 : ℝ)*(upper3) + (582400425675969/100000000000000 : ℝ)*(major0) + (582400425675969/100000000000000 : ℝ)*(major1) + (582400425675969/100000000000000 : ℝ)*(major2) + (772143608895773/100000000000000 : ℝ)*(sp0) + (193036200654149/25000000000000 : ℝ)*(sp1) + (154428958844779/20000000000000 : ℝ)*(sp2) + (392652550918019/100000000000000 : ℝ)*(sp3) + (25661237/1000000000000 : ℝ)*(sp4) + (483945141/25000000000000 : ℝ)*(sp7) + (39265458270103/10000000000000 : ℝ)*(f.failure) + (386073039508513/50000000000000 : ℝ)*(f.sum) + (41390349576847/100000000000000000000000000000 : ℝ)*base66 + (166933478923153/200000000000000000000000000000 : ℝ)*base67 + (114877939876847/200000000000000000000000000000 : ℝ)*base70 + (170454325076847/200000000000000000000000000000 : ℝ)*base72 + (74871438423153/100000000000000000000000000000 : ℝ)*base73 + (971460593876847/200000000000000000000000000000 : ℝ)*base76 + (742377124076847/200000000000000000000000000000 : ℝ)*base78 + (48368820323153/200000000000000000000000000000 : ℝ)*base79 + (281814367223153/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (3491313/500000000000000000000 : ℝ)*base90 + (3491313/500000000000000000000 : ℝ)*base92 + (3491313/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (310227071135690586071301/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1159378951/100000000000000 : ℝ)*(base19) + (1439863483/100000000000000 : ℝ)*(base23) + (236410881/100000000000000 : ℝ)*(base39) + (118143163/50000000000000 : ℝ)*(base45) + (3642987/4000000000000 : ℝ)*(upper3) + (331639953/100000000000000 : ℝ)*(upper5) + (614687871888809/100000000000000 : ℝ)*(major0) + (614687871888809/100000000000000 : ℝ)*(major1) + (614687635477929/100000000000000 : ℝ)*(major2) + (698564091/100000000000000 : ℝ)*(sp2) + (814952509652287/100000000000000 : ℝ)*(sp4) + (814951350273337/100000000000000 : ℝ)*(sp5) + (407475303817797/50000000000000 : ℝ)*(sp6) + (414422790896397/100000000000000 : ℝ)*(sp7) + (414422790896397/100000000000000 : ℝ)*(f.failure) + (12733636657237/1562500000000 : ℝ)*(f.sum) + (77617302576953/100000000000000000000000000000 : ℝ)*base65 + (317116322672327/200000000000000000000000000000 : ℝ)*base68 + (1954394785026233/200000000000000000000000000000 : ℝ)*base69 + (554223801272327/200000000000000000000000000000 : ℝ)*base72 + (87886897976953/100000000000000000000000000000 : ℝ)*base73 + (518099657426233/200000000000000000000000000000 : ℝ)*base75 + (509538299773767/200000000000000000000000000000 : ℝ)*base78 + (196371100173767/200000000000000000000000000000 : ℝ)*base80 + (452811392226233/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (9330187/5000000000000000000000 : ℝ)*base90 + (9330187/5000000000000000000000 : ℝ)*base92 + (59330187/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1083_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (21/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (28043/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1083_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1083_s1_0 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2119538893/10000000000 : ℝ)*x 0 + (571758091/1000000000 : ℝ)*x 1 + (2494837163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119538893/10000000000 : ℝ)^2069 ≤ (6362888196563/50000000000000 : ℝ)^1557 := by
    have hnat : (2119538893 : ℕ)^2069*50000000000000^1557 ≤ 6362888196563^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119538893 10000000000 6362888196563 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (571758091/1000000000 : ℝ)^2069 ≤ (47574542772911/100000000000000 : ℝ)^1557 := by
    have hnat : (571758091 : ℕ)^2069*100000000000000^1557 ≤ 47574542772911^1557*1000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571758091 1000000000 47574542772911 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2494837163/5000000000 : ℝ)^2069 ≤ (39699680816987/100000000000000 : ℝ)^1557 := by
    have hnat : (2494837163 : ℕ)^2069*100000000000000^1557 ≤ 39699680816987^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2494837163 5000000000 39699680816987 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2119538893/10000000000 : ℝ), (571758091/1000000000 : ℝ), (2494837163/5000000000 : ℝ)] ![(6362888196563/50000000000000 : ℝ), (47574542772911/100000000000000 : ℝ), (39699680816987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2119538893/10000000000 : ℝ)|^2069 ≤ (6362888196563/50000000000000 : ℝ)^1557
        have hw : |(-2119538893/10000000000 : ℝ)|=(2119538893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(571758091/1000000000 : ℝ)|^2069 ≤ (47574542772911/100000000000000 : ℝ)^1557
        have hw : |(571758091/1000000000 : ℝ)|=(571758091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2494837163/5000000000 : ℝ)|^2069 ≤ (39699680816987/100000000000000 : ℝ)^1557
        have hw : |(2494837163/5000000000 : ℝ)|=(2494837163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s1_1 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (677796697/1250000000 : ℝ)*x 0 + (-1256781233/5000000000 : ℝ)*x 1 + (4989674589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (677796697/1250000000 : ℝ)^2069 ≤ (1773539815381/4000000000000 : ℝ)^1557 := by
    have hnat : (677796697 : ℕ)^2069*4000000000000^1557 ≤ 1773539815381^1557*1250000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677796697 1250000000 1773539815381 4000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1256781233/5000000000 : ℝ)^2069 ≤ (15961821003009/100000000000000 : ℝ)^1557 := by
    have hnat : (1256781233 : ℕ)^2069*100000000000000^1557 ≤ 15961821003009^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1256781233 5000000000 15961821003009 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4989674589/10000000000 : ℝ)^2069 ≤ (9924920899403/25000000000000 : ℝ)^1557 := by
    have hnat : (4989674589 : ℕ)^2069*25000000000000^1557 ≤ 9924920899403^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4989674589 10000000000 9924920899403 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(677796697/1250000000 : ℝ), (-1256781233/5000000000 : ℝ), (4989674589/10000000000 : ℝ)] ![(1773539815381/4000000000000 : ℝ), (15961821003009/100000000000000 : ℝ), (9924920899403/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(677796697/1250000000 : ℝ)|^2069 ≤ (1773539815381/4000000000000 : ℝ)^1557
        have hw : |(677796697/1250000000 : ℝ)|=(677796697/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1256781233/5000000000 : ℝ)|^2069 ≤ (15961821003009/100000000000000 : ℝ)^1557
        have hw : |(-1256781233/5000000000 : ℝ)|=(1256781233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4989674589/10000000000 : ℝ)|^2069 ≤ (9924920899403/25000000000000 : ℝ)^1557
        have hw : |(4989674589/10000000000 : ℝ)|=(4989674589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s1_2 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2711187181/5000000000 : ℝ)*x 0 + (4989673759/10000000000 : ℝ)*x 1 + (-2513562493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711187181/5000000000 : ℝ)^2069 ≤ (44338503925077/100000000000000 : ℝ)^1557 := by
    have hnat : (2711187181 : ℕ)^2069*100000000000000^1557 ≤ 44338503925077^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711187181 5000000000 44338503925077 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4989673759/10000000000 : ℝ)^2069 ≤ (7939934964451/20000000000000 : ℝ)^1557 := by
    have hnat : (4989673759 : ℕ)^2069*20000000000000^1557 ≤ 7939934964451^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4989673759 10000000000 7939934964451 20000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2513562493/10000000000 : ℝ)^2069 ≤ (62350864183/390625000000 : ℝ)^1557 := by
    have hnat : (2513562493 : ℕ)^2069*390625000000^1557 ≤ 62350864183^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2513562493 10000000000 62350864183 390625000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711187181/5000000000 : ℝ), (4989673759/10000000000 : ℝ), (-2513562493/10000000000 : ℝ)] ![(44338503925077/100000000000000 : ℝ), (7939934964451/20000000000000 : ℝ), (62350864183/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711187181/5000000000 : ℝ)|^2069 ≤ (44338503925077/100000000000000 : ℝ)^1557
        have hw : |(2711187181/5000000000 : ℝ)|=(2711187181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4989673759/10000000000 : ℝ)|^2069 ≤ (7939934964451/20000000000000 : ℝ)^1557
        have hw : |(4989673759/10000000000 : ℝ)|=(4989673759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2513562493/10000000000 : ℝ)|^2069 ≤ (62350864183/390625000000 : ℝ)^1557
        have hw : |(-2513562493/10000000000 : ℝ)|=(2513562493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s1_3 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1080597753/2500000000 : ℝ)*x 0 + (3665817647/10000000000 : ℝ)*x 1 + (5097227867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080597753/2500000000 : ℝ)^2069 ≤ (410059114299/1250000000000 : ℝ)^1557 := by
    have hnat : (1080597753 : ℕ)^2069*1250000000000^1557 ≤ 410059114299^1557*2500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080597753 2500000000 410059114299 1250000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3665817647/10000000000 : ℝ)^2069 ≤ (26354445826007/100000000000000 : ℝ)^1557 := by
    have hnat : (3665817647 : ℕ)^2069*100000000000000^1557 ≤ 26354445826007^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3665817647 10000000000 26354445826007 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5097227867/10000000000 : ℝ)^2069 ≤ (40840825024923/100000000000000 : ℝ)^1557 := by
    have hnat : (5097227867 : ℕ)^2069*100000000000000^1557 ≤ 40840825024923^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5097227867 10000000000 40840825024923 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080597753/2500000000 : ℝ), (3665817647/10000000000 : ℝ), (5097227867/10000000000 : ℝ)] ![(410059114299/1250000000000 : ℝ), (26354445826007/100000000000000 : ℝ), (40840825024923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080597753/2500000000 : ℝ)|^2069 ≤ (410059114299/1250000000000 : ℝ)^1557
        have hw : |(1080597753/2500000000 : ℝ)|=(1080597753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3665817647/10000000000 : ℝ)|^2069 ≤ (26354445826007/100000000000000 : ℝ)^1557
        have hw : |(3665817647/10000000000 : ℝ)|=(3665817647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5097227867/10000000000 : ℝ)|^2069 ≤ (40840825024923/100000000000000 : ℝ)^1557
        have hw : |(5097227867/10000000000 : ℝ)|=(5097227867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s1_4 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2120434879/10000000000 : ℝ)*x 0 + (4999838669/10000000000 : ℝ)*x 1 + (5707208767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120434879/10000000000 : ℝ)^2069 ≤ (12732925407677/100000000000000 : ℝ)^1557 := by
    have hnat : (2120434879 : ℕ)^2069*100000000000000^1557 ≤ 12732925407677^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120434879 10000000000 12732925407677 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4999838669/10000000000 : ℝ)^2069 ≤ (19903590768627/50000000000000 : ℝ)^1557 := by
    have hnat : (4999838669 : ℕ)^2069*50000000000000^1557 ≤ 19903590768627^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999838669 10000000000 19903590768627 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5707208767/10000000000 : ℝ)^2069 ≤ (949197860683/2000000000000 : ℝ)^1557 := by
    have hnat : (5707208767 : ℕ)^2069*2000000000000^1557 ≤ 949197860683^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5707208767 10000000000 949197860683 2000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2120434879/10000000000 : ℝ), (4999838669/10000000000 : ℝ), (5707208767/10000000000 : ℝ)] ![(12732925407677/100000000000000 : ℝ), (19903590768627/50000000000000 : ℝ), (949197860683/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2120434879/10000000000 : ℝ)|^2069 ≤ (12732925407677/100000000000000 : ℝ)^1557
        have hw : |(-2120434879/10000000000 : ℝ)|=(2120434879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4999838669/10000000000 : ℝ)|^2069 ≤ (19903590768627/50000000000000 : ℝ)^1557
        have hw : |(4999838669/10000000000 : ℝ)|=(4999838669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5707208767/10000000000 : ℝ)|^2069 ≤ (949197860683/2000000000000 : ℝ)^1557
        have hw : |(5707208767/10000000000 : ℝ)|=(5707208767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s1_5 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5236312331/10000000000 : ℝ)*x 0 + (-1796025527/10000000000 : ℝ)*x 1 + (5707210971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5236312331/10000000000 : ℝ)^2069 ≤ (42328278192901/100000000000000 : ℝ)^1557 := by
    have hnat : (5236312331 : ℕ)^2069*100000000000000^1557 ≤ 42328278192901^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236312331 10000000000 42328278192901 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1796025527/10000000000 : ℝ)^2069 ≤ (10211804395413/100000000000000 : ℝ)^1557 := by
    have hnat : (1796025527 : ℕ)^2069*100000000000000^1557 ≤ 10211804395413^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1796025527 10000000000 10211804395413 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5707210971/10000000000 : ℝ)^2069 ≤ (23729958694529/50000000000000 : ℝ)^1557 := by
    have hnat : (5707210971 : ℕ)^2069*50000000000000^1557 ≤ 23729958694529^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5707210971 10000000000 23729958694529 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5236312331/10000000000 : ℝ), (-1796025527/10000000000 : ℝ), (5707210971/10000000000 : ℝ)] ![(42328278192901/100000000000000 : ℝ), (10211804395413/100000000000000 : ℝ), (23729958694529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5236312331/10000000000 : ℝ)|^2069 ≤ (42328278192901/100000000000000 : ℝ)^1557
        have hw : |(5236312331/10000000000 : ℝ)|=(5236312331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1796025527/10000000000 : ℝ)|^2069 ≤ (10211804395413/100000000000000 : ℝ)^1557
        have hw : |(-1796025527/10000000000 : ℝ)|=(1796025527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5707210971/10000000000 : ℝ)|^2069 ≤ (23729958694529/50000000000000 : ℝ)^1557
        have hw : |(5707210971/10000000000 : ℝ)|=(5707210971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s1_6 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5236310243/10000000000 : ℝ)*x 0 + (2853606653/5000000000 : ℝ)*x 1 + (-1796025083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5236310243/10000000000 : ℝ)^2069 ≤ (42328255764031/100000000000000 : ℝ)^1557 := by
    have hnat : (5236310243 : ℕ)^2069*100000000000000^1557 ≤ 42328255764031^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236310243 10000000000 42328255764031 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2853606653/5000000000 : ℝ)^2069 ≤ (47459943191561/100000000000000 : ℝ)^1557 := by
    have hnat : (2853606653 : ℕ)^2069*100000000000000^1557 ≤ 47459943191561^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2853606653 5000000000 47459943191561 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1796025083/10000000000 : ℝ)^2069 ≤ (5105900520391/50000000000000 : ℝ)^1557 := by
    have hnat : (1796025083 : ℕ)^2069*50000000000000^1557 ≤ 5105900520391^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1796025083 10000000000 5105900520391 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5236310243/10000000000 : ℝ), (2853606653/5000000000 : ℝ), (-1796025083/10000000000 : ℝ)] ![(42328255764031/100000000000000 : ℝ), (47459943191561/100000000000000 : ℝ), (5105900520391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5236310243/10000000000 : ℝ)|^2069 ≤ (42328255764031/100000000000000 : ℝ)^1557
        have hw : |(5236310243/10000000000 : ℝ)|=(5236310243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2853606653/5000000000 : ℝ)|^2069 ≤ (47459943191561/100000000000000 : ℝ)^1557
        have hw : |(2853606653/5000000000 : ℝ)|=(2853606653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1796025083/10000000000 : ℝ)|^2069 ≤ (5105900520391/50000000000000 : ℝ)^1557
        have hw : |(-1796025083/10000000000 : ℝ)|=(1796025083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s1_7 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4324148037/10000000000 : ℝ)*x 0 + (1015447317/2000000000 : ℝ)*x 1 + (1843104909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324148037/10000000000 : ℝ)^2069 ≤ (32822450267183/100000000000000 : ℝ)^1557 := by
    have hnat : (4324148037 : ℕ)^2069*100000000000000^1557 ≤ 32822450267183^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324148037 10000000000 32822450267183 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1015447317/2000000000 : ℝ)^2069 ≤ (20314056365651/50000000000000 : ℝ)^1557 := by
    have hnat : (1015447317 : ℕ)^2069*50000000000000^1557 ≤ 20314056365651^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015447317 2000000000 20314056365651 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1843104909/5000000000 : ℝ)^2069 ≤ (6637359245769/25000000000000 : ℝ)^1557 := by
    have hnat : (1843104909 : ℕ)^2069*25000000000000^1557 ≤ 6637359245769^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1843104909 5000000000 6637359245769 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324148037/10000000000 : ℝ), (1015447317/2000000000 : ℝ), (1843104909/5000000000 : ℝ)] ![(32822450267183/100000000000000 : ℝ), (20314056365651/50000000000000 : ℝ), (6637359245769/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324148037/10000000000 : ℝ)|^2069 ≤ (32822450267183/100000000000000 : ℝ)^1557
        have hw : |(4324148037/10000000000 : ℝ)|=(4324148037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1015447317/2000000000 : ℝ)|^2069 ≤ (20314056365651/50000000000000 : ℝ)^1557
        have hw : |(1015447317/2000000000 : ℝ)|=(1015447317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1843104909/5000000000 : ℝ)|^2069 ≤ (6637359245769/25000000000000 : ℝ)^1557
        have hw : |(1843104909/5000000000 : ℝ)|=(1843104909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s1_8 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4035329/5000000000 : ℝ)*x 0 + (1097982753/2000000000 : ℝ)*x 1 + (318491433/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4035329/5000000000 : ℝ)^2069 ≤ (7758621923/100000000000000 : ℝ)^1557 := by
    have hnat : (4035329 : ℕ)^2069*100000000000000^1557 ≤ 7758621923^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035329 5000000000 7758621923 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097982753/2000000000 : ℝ)^2069 ≤ (9014775044667/20000000000000 : ℝ)^1557 := by
    have hnat : (1097982753 : ℕ)^2069*20000000000000^1557 ≤ 9014775044667^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097982753 2000000000 9014775044667 20000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (318491433/500000000 : ℝ)^2069 ≤ (27459183066769/50000000000000 : ℝ)^1557 := by
    have hnat : (318491433 : ℕ)^2069*50000000000000^1557 ≤ 27459183066769^1557*500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318491433 500000000 27459183066769 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4035329/5000000000 : ℝ), (1097982753/2000000000 : ℝ), (318491433/500000000 : ℝ)] ![(7758621923/100000000000000 : ℝ), (9014775044667/20000000000000 : ℝ), (27459183066769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4035329/5000000000 : ℝ)|^2069 ≤ (7758621923/100000000000000 : ℝ)^1557
        have hw : |(4035329/5000000000 : ℝ)|=(4035329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097982753/2000000000 : ℝ)|^2069 ≤ (9014775044667/20000000000000 : ℝ)^1557
        have hw : |(1097982753/2000000000 : ℝ)|=(1097982753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(318491433/500000000 : ℝ)|^2069 ≤ (27459183066769/50000000000000 : ℝ)^1557
        have hw : |(318491433/500000000 : ℝ)|=(318491433/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s1_9 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (60469781/625000000 : ℝ)*x 0 + (-4447877703/10000000000 : ℝ)*x 1 + (277227257/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (60469781/625000000 : ℝ)^2069 ≤ (2244268488377/50000000000000 : ℝ)^1557 := by
    have hnat : (60469781 : ℕ)^2069*50000000000000^1557 ≤ 2244268488377^1557*625000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60469781 625000000 2244268488377 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4447877703/10000000000 : ℝ)^2069 ≤ (2129768065571/6250000000000 : ℝ)^1557 := by
    have hnat : (4447877703 : ℕ)^2069*6250000000000^1557 ≤ 2129768065571^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4447877703 10000000000 2129768065571 6250000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277227257/400000000 : ℝ)^2069 ≤ (61435173956069/100000000000000 : ℝ)^1557 := by
    have hnat : (277227257 : ℕ)^2069*100000000000000^1557 ≤ 61435173956069^1557*400000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277227257 400000000 61435173956069 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(60469781/625000000 : ℝ), (-4447877703/10000000000 : ℝ), (277227257/400000000 : ℝ)] ![(2244268488377/50000000000000 : ℝ), (2129768065571/6250000000000 : ℝ), (61435173956069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(60469781/625000000 : ℝ)|^2069 ≤ (2244268488377/50000000000000 : ℝ)^1557
        have hw : |(60469781/625000000 : ℝ)|=(60469781/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4447877703/10000000000 : ℝ)|^2069 ≤ (2129768065571/6250000000000 : ℝ)^1557
        have hw : |(-4447877703/10000000000 : ℝ)|=(4447877703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(277227257/400000000 : ℝ)|^2069 ≤ (61435173956069/100000000000000 : ℝ)^1557
        have hw : |(277227257/400000000 : ℝ)|=(277227257/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s1_10 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (967509719/10000000000 : ℝ)*x 0 + (3465333307/5000000000 : ℝ)*x 1 + (-69498421/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (967509719/10000000000 : ℝ)^2069 ≤ (4488495198019/100000000000000 : ℝ)^1557 := by
    have hnat : (967509719 : ℕ)^2069*100000000000000^1557 ≤ 4488495198019^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967509719 10000000000 4488495198019 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3465333307/5000000000 : ℝ)^2069 ≤ (61434999495509/100000000000000 : ℝ)^1557 := by
    have hnat : (3465333307 : ℕ)^2069*100000000000000^1557 ≤ 61434999495509^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3465333307 5000000000 61434999495509 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69498421/156250000 : ℝ)^2069 ≤ (17038252647207/50000000000000 : ℝ)^1557 := by
    have hnat : (69498421 : ℕ)^2069*50000000000000^1557 ≤ 17038252647207^1557*156250000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69498421 156250000 17038252647207 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(967509719/10000000000 : ℝ), (3465333307/5000000000 : ℝ), (-69498421/156250000 : ℝ)] ![(4488495198019/100000000000000 : ℝ), (61434999495509/100000000000000 : ℝ), (17038252647207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(967509719/10000000000 : ℝ)|^2069 ≤ (4488495198019/100000000000000 : ℝ)^1557
        have hw : |(967509719/10000000000 : ℝ)|=(967509719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3465333307/5000000000 : ℝ)|^2069 ≤ (61434999495509/100000000000000 : ℝ)^1557
        have hw : |(3465333307/5000000000 : ℝ)|=(3465333307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-69498421/156250000 : ℝ)|^2069 ≤ (17038252647207/50000000000000 : ℝ)^1557
        have hw : |(-69498421/156250000 : ℝ)|=(69498421/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s1_11 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1923011761/10000000000 : ℝ)*x 0 + (1456588639/2500000000 : ℝ)*x 1 + (5021524953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1923011761/10000000000 : ℝ)^2069 ≤ (2236445614759/20000000000000 : ℝ)^1557 := by
    have hnat : (1923011761 : ℕ)^2069*20000000000000^1557 ≤ 2236445614759^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923011761 10000000000 2236445614759 20000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1456588639/2500000000 : ℝ)^2069 ≤ (4878099044553/10000000000000 : ℝ)^1557 := by
    have hnat : (1456588639 : ℕ)^2069*10000000000000^1557 ≤ 4878099044553^1557*2500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1456588639 2500000000 4878099044553 10000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5021524953/10000000000 : ℝ)^2069 ≤ (40036781473953/100000000000000 : ℝ)^1557 := by
    have hnat : (5021524953 : ℕ)^2069*100000000000000^1557 ≤ 40036781473953^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5021524953 10000000000 40036781473953 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1923011761/10000000000 : ℝ), (1456588639/2500000000 : ℝ), (5021524953/10000000000 : ℝ)] ![(2236445614759/20000000000000 : ℝ), (4878099044553/10000000000000 : ℝ), (40036781473953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1923011761/10000000000 : ℝ)|^2069 ≤ (2236445614759/20000000000000 : ℝ)^1557
        have hw : |(1923011761/10000000000 : ℝ)|=(1923011761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1456588639/2500000000 : ℝ)|^2069 ≤ (4878099044553/10000000000000 : ℝ)^1557
        have hw : |(1456588639/2500000000 : ℝ)|=(1456588639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5021524953/10000000000 : ℝ)|^2069 ≤ (40036781473953/100000000000000 : ℝ)^1557
        have hw : |(5021524953/10000000000 : ℝ)|=(5021524953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1083_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (21/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5313/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2071/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (28043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (21/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (28043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (21/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (28043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (21/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (28043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (21/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (28043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (21/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (28043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (21/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (21/12500 : ℝ) ^ (8275/2048 : ℝ) ≤ (614874217/100000000000000000000 : ℝ) := by
    have hpowers : (21/12500 : ℝ)^8275 ≤ (614874217/100000000000000000000 : ℝ)^2048 := by
      have hnat : (21 : ℕ)^8275*100000000000000000000^2048 ≤ 614874217^2048*12500^8275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21 12500 614874217 100000000000000000000 8275 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21/12500 : ℝ)) (X := (614874217/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (28043/100000 : ℝ) ^ (8275/2048 : ℝ) ≤ (587380710827721419/100000000000000000000 : ℝ) := by
    have hpowers : (28043/100000 : ℝ)^8275 ≤ (587380710827721419/100000000000000000000 : ℝ)^2048 := by
      have hnat : (28043 : ℕ)^8275*100000000000000000000^2048 ≤ 587380710827721419^2048*100000^8275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28043 100000 587380710827721419 100000000000000000000 8275 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28043/100000 : ℝ)) (X := (587380710827721419/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000000614874217/50000000000000000000 : ℝ) ≤ (2500000000007609/2500000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (50000000000614874217/50000000000000000000 : ℝ)^2048 ≤ (2500000000007609/2500000000000000 : ℝ)^8275 := by
      have hnat : (50000000000614874217 : ℕ)^2048*2500000000000000^8275 ≤ 2500000000007609^8275*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000000614874217 50000000000000000000 2500000000007609 2500000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000000007609/2500000000000000 : ℝ)) (X := (50000000000614874217/50000000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25146845177860648909/25000000000000000000 : ℝ) ≤ (5007252605437861/5000000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (25146845177860648909/25000000000000000000 : ℝ)^2048 ≤ (5007252605437861/5000000000000000 : ℝ)^8275 := by
      have hnat : (25146845177860648909 : ℕ)^2048*5000000000000000^8275 ≤ 5007252605437861^8275*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25146845177860648909 25000000000000000000 5007252605437861 5000000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007252605437861/5000000000000000 : ℝ)) (X := (25146845177860648909/25000000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50587380710827721419/50000000000000000000 : ℝ) ≤ (626813151357563/625000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (50587380710827721419/50000000000000000000 : ℝ)^2048 ≤ (626813151357563/625000000000000 : ℝ)^8275 := by
      have hnat : (50587380710827721419 : ℕ)^2048*625000000000000^8275 ≤ 626813151357563^8275*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50587380710827721419 50000000000000000000 626813151357563 625000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (626813151357563/625000000000000 : ℝ)) (X := (50587380710827721419/50000000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(614874217/100000000000000000000 : ℝ) ≤ ((69686281562501096851/69687500000000000000 : ℝ)+2*(7252605422643/1393750000000000 : ℝ)*(21/12500 : ℝ))^(8275/2048 : ℝ) := by
    rw [show (69686281562501096851/69687500000000000000 : ℝ)+2*(7252605422643/1393750000000000 : ℝ)*(21/12500 : ℝ)=(2500000000007609/2500000000000000 : ℝ) by norm_num, show 1+2*(614874217/100000000000000000000 : ℝ)=(50000000000614874217/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(587380710827721419/100000000000000000000 : ℝ)+(614874217/100000000000000000000 : ℝ) ≤ ((69686281562501096851/69687500000000000000 : ℝ)+(7252605422643/1393750000000000 : ℝ)*((28043/100000 : ℝ)+(21/12500 : ℝ)))^(8275/2048 : ℝ) := by
    rw [show (69686281562501096851/69687500000000000000 : ℝ)+(7252605422643/1393750000000000 : ℝ)*((28043/100000 : ℝ)+(21/12500 : ℝ))=(5007252605437861/5000000000000000 : ℝ) by norm_num, show 1+(587380710827721419/100000000000000000000 : ℝ)+(614874217/100000000000000000000 : ℝ)=(25146845177860648909/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(587380710827721419/100000000000000000000 : ℝ) ≤ ((69686281562501096851/69687500000000000000 : ℝ)+2*(7252605422643/1393750000000000 : ℝ)*(28043/100000 : ℝ))^(8275/2048 : ℝ) := by
    rw [show (69686281562501096851/69687500000000000000 : ℝ)+2*(7252605422643/1393750000000000 : ℝ)*(28043/100000 : ℝ)=(626813151357563/625000000000000 : ℝ) by norm_num, show 1+2*(587380710827721419/100000000000000000000 : ℝ)=(50587380710827721419/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (69686281562501096851/69687500000000000000 : ℝ)*(X 1 0+X 2 0)+(7252605422643/1393750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (21/12500 : ℝ)) (hi := (28043/100000 : ℝ)) (c := (69686281562501096851/69687500000000000000 : ℝ)) (alpha := (7252605422643/1393750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (69686281562501096851/69687500000000000000 : ℝ)*(X 0 1+X 2 1)+(7252605422643/1393750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (21/12500 : ℝ)) (hi := (28043/100000 : ℝ)) (c := (69686281562501096851/69687500000000000000 : ℝ)) (alpha := (7252605422643/1393750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (69686281562501096851/69687500000000000000 : ℝ)*(X 0 2+X 1 2)+(7252605422643/1393750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (21/12500 : ℝ)) (hi := (28043/100000 : ℝ)) (c := (69686281562501096851/69687500000000000000 : ℝ)) (alpha := (7252605422643/1393750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2119538893/10000000000 : ℝ)*X 0 0+(571758091/1000000000 : ℝ)*X 0 1+(2494837163/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((677796697/1250000000 : ℝ)*X 1 0+(-1256781233/5000000000 : ℝ)*X 1 1+(4989674589/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2711187181/5000000000 : ℝ)*X 2 0+(4989673759/10000000000 : ℝ)*X 2 1+(-2513562493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1080597753/2500000000 : ℝ)*X 0 0+(3665817647/10000000000 : ℝ)*X 0 1+(5097227867/10000000000 : ℝ)*X 0 2+(1080597753/2500000000 : ℝ)*X 1 0+(3665817647/10000000000 : ℝ)*X 1 1+(5097227867/10000000000 : ℝ)*X 1 2+(1080597753/2500000000 : ℝ)*X 2 0+(3665817647/10000000000 : ℝ)*X 2 1+(5097227867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2120434879/10000000000 : ℝ)*X 0 0+(4999838669/10000000000 : ℝ)*X 0 1+(5707208767/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5236312331/10000000000 : ℝ)*X 1 0+(-1796025527/10000000000 : ℝ)*X 1 1+(5707210971/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5236310243/10000000000 : ℝ)*X 2 0+(2853606653/5000000000 : ℝ)*X 2 1+(-1796025083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4324148037/10000000000 : ℝ)*X 0 0+(1015447317/2000000000 : ℝ)*X 0 1+(1843104909/5000000000 : ℝ)*X 0 2+(4324148037/10000000000 : ℝ)*X 1 0+(1015447317/2000000000 : ℝ)*X 1 1+(1843104909/5000000000 : ℝ)*X 1 2+(4324148037/10000000000 : ℝ)*X 2 0+(1015447317/2000000000 : ℝ)*X 2 1+(1843104909/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((4035329/5000000000 : ℝ)*X 0 0+(1097982753/2000000000 : ℝ)*X 0 1+(318491433/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((60469781/625000000 : ℝ)*X 1 0+(-4447877703/10000000000 : ℝ)*X 1 1+(277227257/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((967509719/10000000000 : ℝ)*X 2 0+(3465333307/5000000000 : ℝ)*X 2 1+(-69498421/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1923011761/10000000000 : ℝ)*X 0 0+(1456588639/2500000000 : ℝ)*X 0 1+(5021524953/10000000000 : ℝ)*X 0 2+(1923011761/10000000000 : ℝ)*X 1 0+(1456588639/2500000000 : ℝ)*X 1 1+(5021524953/10000000000 : ℝ)*X 1 2+(1923011761/10000000000 : ℝ)*X 2 0+(1456588639/2500000000 : ℝ)*X 2 1+(5021524953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (487007169318225575761238661/108886718750000000000000000000000 : ℝ) := by norm_num
    linear_combination (64763072193001/6250000000000 : ℝ)*(major0) + (64763072193001/6250000000000 : ℝ)*(major1) + (64763072193001/6250000000000 : ℝ)*(major2) + (686902011955987/50000000000000 : ℝ)*(sp0) + (343451157676373/25000000000000 : ℝ)*(sp1) + (42931362596703/3125000000000 : ℝ)*(sp2) + (69861198880107/10000000000000 : ℝ)*(sp3) + (1237989359/100000000000000 : ℝ)*(sp4) + (141911757/20000000000000 : ℝ)*(sp5) + (9556293/625000000000 : ℝ)*(sp6) + (303034943/100000000000000 : ℝ)*(sp8) + (112335999/50000000000000 : ℝ)*(sp9) + (432834899/100000000000000 : ℝ)*(sp10) + (15183797/2500000000000 : ℝ)*(sp11) + (698612596152951/100000000000000 : ℝ)*(f.failure) + (343451391234069/25000000000000 : ℝ)*(f.sum) + (574549042671951/139375000000000000000000000000 : ℝ)*base65 + (975041232882197649/435546875000000000000000000000000 : ℝ)*base68 + (405236689442075387/217773437500000000000000000000000 : ℝ)*base70 + (831619707565737113/217773437500000000000000000000000 : ℝ)*base71 + (128544814313201/139375000000000000000000000000 : ℝ)*base73 + (1040636530022768363/217773437500000000000000000000000 : ℝ)*base75 + (409055552037751369/108886718750000000000000000000000 : ℝ)*base77 + (2330669031274052351/435546875000000000000000000000000 : ℝ)*base79 + (133548465396913/69687500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (25202479/5000000000000000000000 : ℝ)*base89 + (25202479/5000000000000000000000 : ℝ)*base91 + (25202479/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9184800232082749760002135173/1742187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (161453777/100000000000000 : ℝ)*(lower4) + (1066290379432541/100000000000000 : ℝ)*(major0) + (1066290379432541/100000000000000 : ℝ)*(major1) + (1066290379432541/100000000000000 : ℝ)*(major2) + (1172613009/100000000000000 : ℝ)*(sp0) + (479237401/20000000000000 : ℝ)*(sp1) + (2658476459/50000000000000 : ℝ)*(sp2) + (353420580305381/25000000000000 : ℝ)*(sp4) + (1413684632246967/100000000000000 : ℝ)*(sp5) + (706840948715753/50000000000000 : ℝ)*(sp6) + (718891844488469/100000000000000 : ℝ)*(sp7) + (3720549891/100000000000000 : ℝ)*(sp8) + (46487613/25000000000000 : ℝ)*(sp9) + (1524259087/100000000000000 : ℝ)*(sp11) + (179723342186889/25000000000000 : ℝ)*(f.failure) + (176710901798053/12500000000000 : ℝ)*(f.sum) + (706210938154851/139375000000000000000000000000 : ℝ)*base65 + (35569821528182321609/6968750000000000000000000000000000 : ℝ)*base68 + (33133284203526071609/6968750000000000000000000000000000 : ℝ)*base70 + (3305450620161428391/6968750000000000000000000000000000 : ℝ)*base71 + (13189065437753/17421875000000000000000000000 : ℝ)*base74 + (29765016244151071609/6968750000000000000000000000000000 : ℝ)*base76 + (27554391313432321609/6968750000000000000000000000000000 : ℝ)*base78 + (42492426117276071609/6968750000000000000000000000000000 : ℝ)*base80 + (1745179375149/139375000000000000000000000000 : ℝ)*base82 + (4248881/1250000000000000000000 : ℝ)*base89 + (4248881/1250000000000000000000 : ℝ)*base91 + (4248881/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1083_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (21/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5313/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2071/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1083_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1083_s2_0 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2176006193/10000000000 : ℝ)*x 0 + (1380602571/2500000000 : ℝ)*x 1 + (321812583/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176006193/10000000000 : ℝ)^2069 ≤ (6589127907239/50000000000000 : ℝ)^1557 := by
    have hnat : (2176006193 : ℕ)^2069*50000000000000^1557 ≤ 6589127907239^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176006193 10000000000 6589127907239 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1380602571/2500000000 : ℝ)^2069 ≤ (9085752431099/20000000000000 : ℝ)^1557 := by
    have hnat : (1380602571 : ℕ)^2069*20000000000000^1557 ≤ 9085752431099^1557*2500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380602571 2500000000 9085752431099 20000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (321812583/625000000 : ℝ)^2069 ≤ (5174122752093/12500000000000 : ℝ)^1557 := by
    have hnat : (321812583 : ℕ)^2069*12500000000000^1557 ≤ 5174122752093^1557*625000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321812583 625000000 5174122752093 12500000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2176006193/10000000000 : ℝ), (1380602571/2500000000 : ℝ), (321812583/625000000 : ℝ)] ![(6589127907239/50000000000000 : ℝ), (9085752431099/20000000000000 : ℝ), (5174122752093/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2176006193/10000000000 : ℝ)|^2069 ≤ (6589127907239/50000000000000 : ℝ)^1557
        have hw : |(-2176006193/10000000000 : ℝ)|=(2176006193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1380602571/2500000000 : ℝ)|^2069 ≤ (9085752431099/20000000000000 : ℝ)^1557
        have hw : |(1380602571/2500000000 : ℝ)|=(1380602571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(321812583/625000000 : ℝ)|^2069 ≤ (5174122752093/12500000000000 : ℝ)^1557
        have hw : |(321812583/625000000 : ℝ)|=(321812583/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s2_1 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5376442407/10000000000 : ℝ)*x 0 + (-1185302341/5000000000 : ℝ)*x 1 + (1029800371/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376442407/10000000000 : ℝ)^2069 ≤ (21920055480049/50000000000000 : ℝ)^1557 := by
    have hnat : (5376442407 : ℕ)^2069*50000000000000^1557 ≤ 21920055480049^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376442407 10000000000 21920055480049 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1185302341/5000000000 : ℝ)^2069 ≤ (7383450690711/50000000000000 : ℝ)^1557 := by
    have hnat : (1185302341 : ℕ)^2069*50000000000000^1557 ≤ 7383450690711^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1185302341 5000000000 7383450690711 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1029800371/2000000000 : ℝ)^2069 ≤ (41392987646457/100000000000000 : ℝ)^1557 := by
    have hnat : (1029800371 : ℕ)^2069*100000000000000^1557 ≤ 41392987646457^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029800371 2000000000 41392987646457 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376442407/10000000000 : ℝ), (-1185302341/5000000000 : ℝ), (1029800371/2000000000 : ℝ)] ![(21920055480049/50000000000000 : ℝ), (7383450690711/50000000000000 : ℝ), (41392987646457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376442407/10000000000 : ℝ)|^2069 ≤ (21920055480049/50000000000000 : ℝ)^1557
        have hw : |(5376442407/10000000000 : ℝ)|=(5376442407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1185302341/5000000000 : ℝ)|^2069 ≤ (7383450690711/50000000000000 : ℝ)^1557
        have hw : |(-1185302341/5000000000 : ℝ)|=(1185302341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1029800371/2000000000 : ℝ)|^2069 ≤ (41392987646457/100000000000000 : ℝ)^1557
        have hw : |(1029800371/2000000000 : ℝ)|=(1029800371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s2_2 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1344110639/2500000000 : ℝ)*x 0 + (5149001689/10000000000 : ℝ)*x 1 + (-2370604701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344110639/2500000000 : ℝ)^2069 ≤ (21920056287293/50000000000000 : ℝ)^1557 := by
    have hnat : (1344110639 : ℕ)^2069*50000000000000^1557 ≤ 21920056287293^1557*2500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344110639 2500000000 21920056287293 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5149001689/10000000000 : ℝ)^2069 ≤ (41392985873151/100000000000000 : ℝ)^1557 := by
    have hnat : (5149001689 : ℕ)^2069*100000000000000^1557 ≤ 41392985873151^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149001689 10000000000 41392985873151 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2370604701/10000000000 : ℝ)^2069 ≤ (1845862692337/12500000000000 : ℝ)^1557 := by
    have hnat : (2370604701 : ℕ)^2069*12500000000000^1557 ≤ 1845862692337^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2370604701 10000000000 1845862692337 12500000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344110639/2500000000 : ℝ), (5149001689/10000000000 : ℝ), (-2370604701/10000000000 : ℝ)] ![(21920056287293/50000000000000 : ℝ), (41392985873151/100000000000000 : ℝ), (1845862692337/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344110639/2500000000 : ℝ)|^2069 ≤ (21920056287293/50000000000000 : ℝ)^1557
        have hw : |(1344110639/2500000000 : ℝ)|=(1344110639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5149001689/10000000000 : ℝ)|^2069 ≤ (41392985873151/100000000000000 : ℝ)^1557
        have hw : |(5149001689/10000000000 : ℝ)|=(5149001689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2370604701/10000000000 : ℝ)|^2069 ≤ (1845862692337/12500000000000 : ℝ)^1557
        have hw : |(-2370604701/10000000000 : ℝ)|=(2370604701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s2_3 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2180485073/5000000000 : ℝ)*x 0 + (4009345119/10000000000 : ℝ)*x 1 + (4743644213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180485073/5000000000 : ℝ)^2069 ≤ (8298594264121/25000000000000 : ℝ)^1557 := by
    have hnat : (2180485073 : ℕ)^2069*25000000000000^1557 ≤ 8298594264121^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180485073 5000000000 8298594264121 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4009345119/10000000000 : ℝ)^2069 ≤ (7421455873967/25000000000000 : ℝ)^1557 := by
    have hnat : (4009345119 : ℕ)^2069*25000000000000^1557 ≤ 7421455873967^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4009345119 10000000000 7421455873967 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4743644213/10000000000 : ℝ)^2069 ≤ (9279949859819/25000000000000 : ℝ)^1557 := by
    have hnat : (4743644213 : ℕ)^2069*25000000000000^1557 ≤ 9279949859819^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4743644213 10000000000 9279949859819 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180485073/5000000000 : ℝ), (4009345119/10000000000 : ℝ), (4743644213/10000000000 : ℝ)] ![(8298594264121/25000000000000 : ℝ), (7421455873967/25000000000000 : ℝ), (9279949859819/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180485073/5000000000 : ℝ)|^2069 ≤ (8298594264121/25000000000000 : ℝ)^1557
        have hw : |(2180485073/5000000000 : ℝ)|=(2180485073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4009345119/10000000000 : ℝ)|^2069 ≤ (7421455873967/25000000000000 : ℝ)^1557
        have hw : |(4009345119/10000000000 : ℝ)|=(4009345119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4743644213/10000000000 : ℝ)|^2069 ≤ (9279949859819/25000000000000 : ℝ)^1557
        have hw : |(4743644213/10000000000 : ℝ)|=(4743644213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s2_4 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1088063237/5000000000 : ℝ)*x 0 + (160990159/312500000 : ℝ)*x 1 + (551969861/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088063237/5000000000 : ℝ)^2069 ≤ (3294805951003/25000000000000 : ℝ)^1557 := by
    have hnat : (1088063237 : ℕ)^2069*25000000000000^1557 ≤ 3294805951003^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088063237 5000000000 3294805951003 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160990159/312500000 : ℝ)^2069 ≤ (10355413479249/25000000000000 : ℝ)^1557 := by
    have hnat : (160990159 : ℕ)^2069*25000000000000^1557 ≤ 10355413479249^1557*312500000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160990159 312500000 10355413479249 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (551969861/1000000000 : ℝ)^2069 ≤ (45399122270009/100000000000000 : ℝ)^1557 := by
    have hnat : (551969861 : ℕ)^2069*100000000000000^1557 ≤ 45399122270009^1557*1000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551969861 1000000000 45399122270009 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1088063237/5000000000 : ℝ), (160990159/312500000 : ℝ), (551969861/1000000000 : ℝ)] ![(3294805951003/25000000000000 : ℝ), (10355413479249/25000000000000 : ℝ), (45399122270009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1088063237/5000000000 : ℝ)|^2069 ≤ (3294805951003/25000000000000 : ℝ)^1557
        have hw : |(-1088063237/5000000000 : ℝ)|=(1088063237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160990159/312500000 : ℝ)|^2069 ≤ (10355413479249/25000000000000 : ℝ)^1557
        have hw : |(160990159/312500000 : ℝ)|=(160990159/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(551969861/1000000000 : ℝ)|^2069 ≤ (45399122270009/100000000000000 : ℝ)^1557
        have hw : |(551969861/1000000000 : ℝ)|=(551969861/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s2_5 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2641039073/5000000000 : ℝ)*x 0 + (-999953917/5000000000 : ℝ)*x 1 + (1103939741/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641039073/5000000000 : ℝ)^2069 ≤ (42820590363601/100000000000000 : ℝ)^1557 := by
    have hnat : (2641039073 : ℕ)^2069*100000000000000^1557 ≤ 42820590363601^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641039073 5000000000 42820590363601 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (999953917/5000000000 : ℝ)^2069 ≤ (2945071578063/25000000000000 : ℝ)^1557 := by
    have hnat : (999953917 : ℕ)^2069*25000000000000^1557 ≤ 2945071578063^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999953917 5000000000 2945071578063 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103939741/2000000000 : ℝ)^2069 ≤ (45399123308321/100000000000000 : ℝ)^1557 := by
    have hnat : (1103939741 : ℕ)^2069*100000000000000^1557 ≤ 45399123308321^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103939741 2000000000 45399123308321 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641039073/5000000000 : ℝ), (-999953917/5000000000 : ℝ), (1103939741/2000000000 : ℝ)] ![(42820590363601/100000000000000 : ℝ), (2945071578063/25000000000000 : ℝ), (45399123308321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641039073/5000000000 : ℝ)|^2069 ≤ (42820590363601/100000000000000 : ℝ)^1557
        have hw : |(2641039073/5000000000 : ℝ)|=(2641039073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-999953917/5000000000 : ℝ)|^2069 ≤ (2945071578063/25000000000000 : ℝ)^1557
        have hw : |(-999953917/5000000000 : ℝ)|=(999953917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1103939741/2000000000 : ℝ)|^2069 ≤ (45399123308321/100000000000000 : ℝ)^1557
        have hw : |(1103939741/2000000000 : ℝ)|=(1103939741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s2_6 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2641039189/5000000000 : ℝ)*x 0 + (1103939711/2000000000 : ℝ)*x 1 + (-79996309/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641039189/5000000000 : ℝ)^2069 ≤ (1070514821571/2500000000000 : ℝ)^1557 := by
    have hnat : (2641039189 : ℕ)^2069*2500000000000^1557 ≤ 1070514821571^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641039189 5000000000 1070514821571 2500000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103939711/2000000000 : ℝ)^2069 ≤ (22699560834441/50000000000000 : ℝ)^1557 := by
    have hnat : (1103939711 : ℕ)^2069*50000000000000^1557 ≤ 22699560834441^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103939711 2000000000 22699560834441 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79996309/400000000 : ℝ)^2069 ≤ (2356057091813/20000000000000 : ℝ)^1557 := by
    have hnat : (79996309 : ℕ)^2069*20000000000000^1557 ≤ 2356057091813^1557*400000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79996309 400000000 2356057091813 20000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641039189/5000000000 : ℝ), (1103939711/2000000000 : ℝ), (-79996309/400000000 : ℝ)] ![(1070514821571/2500000000000 : ℝ), (22699560834441/50000000000000 : ℝ), (2356057091813/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641039189/5000000000 : ℝ)|^2069 ≤ (1070514821571/2500000000000 : ℝ)^1557
        have hw : |(2641039189/5000000000 : ℝ)|=(2641039189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1103939711/2000000000 : ℝ)|^2069 ≤ (22699560834441/50000000000000 : ℝ)^1557
        have hw : |(1103939711/2000000000 : ℝ)|=(1103939711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-79996309/400000000 : ℝ)|^2069 ≤ (2356057091813/20000000000000 : ℝ)^1557
        have hw : |(-79996309/400000000 : ℝ)|=(79996309/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s2_7 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4361206843/10000000000 : ℝ)*x 0 + (4738367233/10000000000 : ℝ)*x 1 + (501834579/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361206843/10000000000 : ℝ)^2069 ≤ (6639354239709/20000000000000 : ℝ)^1557 := by
    have hnat : (4361206843 : ℕ)^2069*20000000000000^1557 ≤ 6639354239709^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361206843 10000000000 6639354239709 20000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4738367233/10000000000 : ℝ)^2069 ≤ (370649374719/1000000000000 : ℝ)^1557 := by
    have hnat : (4738367233 : ℕ)^2069*1000000000000^1557 ≤ 370649374719^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4738367233 10000000000 370649374719 1000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501834579/1250000000 : ℝ)^2069 ≤ (29738291304451/100000000000000 : ℝ)^1557 := by
    have hnat : (501834579 : ℕ)^2069*100000000000000^1557 ≤ 29738291304451^1557*1250000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501834579 1250000000 29738291304451 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361206843/10000000000 : ℝ), (4738367233/10000000000 : ℝ), (501834579/1250000000 : ℝ)] ![(6639354239709/20000000000000 : ℝ), (370649374719/1000000000000 : ℝ), (29738291304451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361206843/10000000000 : ℝ)|^2069 ≤ (6639354239709/20000000000000 : ℝ)^1557
        have hw : |(4361206843/10000000000 : ℝ)|=(4361206843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4738367233/10000000000 : ℝ)|^2069 ≤ (370649374719/1000000000000 : ℝ)^1557
        have hw : |(4738367233/10000000000 : ℝ)|=(4738367233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(501834579/1250000000 : ℝ)|^2069 ≤ (29738291304451/100000000000000 : ℝ)^1557
        have hw : |(501834579/1250000000 : ℝ)|=(501834579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1083_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2071/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5313/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1759/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3337/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2071/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5313/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2071/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5313/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2071/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5313/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2071/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5313/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2071/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5313/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2071/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5313/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5313/100000 : ℝ) ^ (8275/2048 : ℝ) ≤ (353729008309471/50000000000000000000 : ℝ) := by
    have hpowers : (5313/100000 : ℝ)^8275 ≤ (353729008309471/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5313 : ℕ)^8275*50000000000000000000^2048 ≤ 353729008309471^2048*100000^8275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5313 100000 353729008309471 50000000000000000000 8275 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5313/100000 : ℝ)) (X := (353729008309471/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2071/10000 : ℝ) ^ (8275/2048 : ℝ) ≤ (4314664187933673/2500000000000000000 : ℝ) := by
    have hpowers : (2071/10000 : ℝ)^8275 ≤ (4314664187933673/2500000000000000000 : ℝ)^2048 := by
      have hnat : (2071 : ℕ)^8275*2500000000000000000^2048 ≤ 4314664187933673^2048*10000^8275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2071 10000 4314664187933673 2500000000000000000 8275 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2071/10000 : ℝ)) (X := (4314664187933673/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000353729008309471/25000000000000000000 : ℝ) ≤ (2500008754479183/2500000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (25000353729008309471/25000000000000000000 : ℝ)^2048 ≤ (2500008754479183/2500000000000000 : ℝ)^8275 := by
      have hnat : (25000353729008309471 : ℕ)^2048*2500000000000000^8275 ≤ 2500008754479183^8275*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000353729008309471 25000000000000000000 2500008754479183 2500000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500008754479183/2500000000000000 : ℝ)) (X := (25000353729008309471/25000000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50086647012766982931/50000000000000000000 : ℝ) ≤ (2501071525650973/2500000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (50086647012766982931/50000000000000000000 : ℝ)^2048 ≤ (2501071525650973/2500000000000000 : ℝ)^8275 := by
      have hnat : (50086647012766982931 : ℕ)^2048*2500000000000000^8275 ≤ 2501071525650973^8275*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50086647012766982931 50000000000000000000 2501071525650973 2500000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501071525650973/2500000000000000 : ℝ)) (X := (50086647012766982931/50000000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1254314664187933673/1250000000000000000 : ℝ) ≤ (2502134296822763/2500000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (1254314664187933673/1250000000000000000 : ℝ)^2048 ≤ (2502134296822763/2500000000000000 : ℝ)^8275 := by
      have hnat : (1254314664187933673 : ℕ)^2048*2500000000000000^8275 ≤ 2502134296822763^8275*1250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1254314664187933673 1250000000000000000 2502134296822763 2500000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502134296822763/2500000000000000 : ℝ)) (X := (1254314664187933673/1250000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(353729008309471/50000000000000000000 : ℝ) ≤ ((38481341786244540111/38492500000000000000 : ℝ)+2*(106277117179/38492500000000 : ℝ)*(5313/100000 : ℝ))^(8275/2048 : ℝ) := by
    rw [show (38481341786244540111/38492500000000000000 : ℝ)+2*(106277117179/38492500000000 : ℝ)*(5313/100000 : ℝ)=(2500008754479183/2500000000000000 : ℝ) by norm_num, show 1+2*(353729008309471/50000000000000000000 : ℝ)=(25000353729008309471/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4314664187933673/2500000000000000000 : ℝ)+(353729008309471/50000000000000000000 : ℝ) ≤ ((38481341786244540111/38492500000000000000 : ℝ)+(106277117179/38492500000000 : ℝ)*((2071/10000 : ℝ)+(5313/100000 : ℝ)))^(8275/2048 : ℝ) := by
    rw [show (38481341786244540111/38492500000000000000 : ℝ)+(106277117179/38492500000000 : ℝ)*((2071/10000 : ℝ)+(5313/100000 : ℝ))=(2501071525650973/2500000000000000 : ℝ) by norm_num, show 1+(4314664187933673/2500000000000000000 : ℝ)+(353729008309471/50000000000000000000 : ℝ)=(50086647012766982931/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4314664187933673/2500000000000000000 : ℝ) ≤ ((38481341786244540111/38492500000000000000 : ℝ)+2*(106277117179/38492500000000 : ℝ)*(2071/10000 : ℝ))^(8275/2048 : ℝ) := by
    rw [show (38481341786244540111/38492500000000000000 : ℝ)+2*(106277117179/38492500000000 : ℝ)*(2071/10000 : ℝ)=(2502134296822763/2500000000000000 : ℝ) by norm_num, show 1+2*(4314664187933673/2500000000000000000 : ℝ)=(1254314664187933673/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38481341786244540111/38492500000000000000 : ℝ)*(X 1 0+X 2 0)+(106277117179/38492500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (5313/100000 : ℝ)) (hi := (2071/10000 : ℝ)) (c := (38481341786244540111/38492500000000000000 : ℝ)) (alpha := (106277117179/38492500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38481341786244540111/38492500000000000000 : ℝ)*(X 0 1+X 2 1)+(106277117179/38492500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (5313/100000 : ℝ)) (hi := (2071/10000 : ℝ)) (c := (38481341786244540111/38492500000000000000 : ℝ)) (alpha := (106277117179/38492500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38481341786244540111/38492500000000000000 : ℝ)*(X 0 2+X 1 2)+(106277117179/38492500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (5313/100000 : ℝ)) (hi := (2071/10000 : ℝ)) (c := (38481341786244540111/38492500000000000000 : ℝ)) (alpha := (106277117179/38492500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2176006193/10000000000 : ℝ)*X 0 0+(1380602571/2500000000 : ℝ)*X 0 1+(321812583/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5376442407/10000000000 : ℝ)*X 1 0+(-1185302341/5000000000 : ℝ)*X 1 1+(1029800371/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1344110639/2500000000 : ℝ)*X 2 0+(5149001689/10000000000 : ℝ)*X 2 1+(-2370604701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180485073/5000000000 : ℝ)*X 0 0+(4009345119/10000000000 : ℝ)*X 0 1+(4743644213/10000000000 : ℝ)*X 0 2+(2180485073/5000000000 : ℝ)*X 1 0+(4009345119/10000000000 : ℝ)*X 1 1+(4743644213/10000000000 : ℝ)*X 1 2+(2180485073/5000000000 : ℝ)*X 2 0+(4009345119/10000000000 : ℝ)*X 2 1+(4743644213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1088063237/5000000000 : ℝ)*X 0 0+(160990159/312500000 : ℝ)*X 0 1+(551969861/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2641039073/5000000000 : ℝ)*X 1 0+(-999953917/5000000000 : ℝ)*X 1 1+(1103939741/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2641039189/5000000000 : ℝ)*X 2 0+(1103939711/2000000000 : ℝ)*X 2 1+(-79996309/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4361206843/10000000000 : ℝ)*X 0 0+(4738367233/10000000000 : ℝ)*X 0 1+(501834579/1250000000 : ℝ)*X 0 2+(4361206843/10000000000 : ℝ)*X 1 0+(4738367233/10000000000 : ℝ)*X 1 1+(501834579/1250000000 : ℝ)*X 1 2+(4361206843/10000000000 : ℝ)*X 2 0+(4738367233/10000000000 : ℝ)*X 2 1+(501834579/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2710267807309412912213479539/962312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (403460099/100000000000000 : ℝ)*(base19) + (453197739/100000000000000 : ℝ)*(base23) + (12616963/25000000000000 : ℝ)*(upper3) + (2632339/20000000000000 : ℝ)*(upper4) + (36721513/100000000000000 : ℝ)*(upper5) + (2019946425050617/100000000000000 : ℝ)*(major0) + (2019946425050617/100000000000000 : ℝ)*(major1) + (2019946425050617/100000000000000 : ℝ)*(major2) + (1339018201382923/50000000000000 : ℝ)*(sp0) + (535608744968203/20000000000000 : ℝ)*(sp1) + (167377729693961/6250000000000 : ℝ)*(sp2) + (136184559762709/10000000000000 : ℝ)*(sp3) + (1931383817/25000000000000 : ℝ)*(sp4) + (1515146323/50000000000000 : ℝ)*(sp7) + (170231078489967/12500000000000 : ℝ)*(f.failure) + (1339022064150557/50000000000000 : ℝ)*(f.sum) + (7422579018777/962312500000000000000000000 : ℝ)*base66 + (26462914489461798487/3849250000000000000000000000000000 : ℝ)*base67 + (43723670013562298487/3849250000000000000000000000000000 : ℝ)*base69 + (13450260240072048487/3849250000000000000000000000000000 : ℝ)*base71 + (23952501521831/7698500000000000000000000000 : ℝ)*base74 + (37555393710505048487/3849250000000000000000000000000000 : ℝ)*base75 + (9825176611814701513/3849250000000000000000000000000000 : ℝ)*base78 + (29135994526523798487/3849250000000000000000000000000000 : ℝ)*base79 + (17578612841371/7698500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3616343/625000000000000000000 : ℝ)*base89 + (3616343/625000000000000000000 : ℝ)*base91 + (3616343/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1526116769069485489773475191/481156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18954997/3125000000000 : ℝ)*(base19) + (97878643/12500000000000 : ℝ)*(base23) + (26388631/25000000000000 : ℝ)*(upper3) + (6022369/50000000000000 : ℝ)*(lower4) + (11061473/20000000000000 : ℝ)*(upper5) + (512387210028573/25000000000000 : ℝ)*(major0) + (512387210028573/25000000000000 : ℝ)*(major1) + (512387210028573/25000000000000 : ℝ)*(major2) + (5179888999/100000000000000 : ℝ)*(sp1) + (3550404521/50000000000000 : ℝ)*(sp2) + (1358645493691537/50000000000000 : ℝ)*(sp4) + (271728520093417/10000000000000 : ℝ)*(sp5) + (2717283103544887/100000000000000 : ℝ)*(sp6) + (27636131742397/2000000000000 : ℝ)*(sp7) + (27636131742397/2000000000000 : ℝ)*(f.failure) + (1358645493691537/50000000000000 : ℝ)*(f.sum) + (6906988212017/7698500000000000000000000000 : ℝ)*base66 + (2535511338135533397/962312500000000000000000000000000 : ℝ)*base68 + (7451770337564658397/962312500000000000000000000000000 : ℝ)*base70 + (2228043892289654103/962312500000000000000000000000000 : ℝ)*base71 + (112395169001/19246250000000000000000000 : ℝ)*base74 + (5646249842470654103/962312500000000000000000000000000 : ℝ)*base75 + (19040897331841603/962312500000000000000000000000000 : ℝ)*base77 + (6888790554347779103/962312500000000000000000000000000 : ℝ)*base79 + (99175779080007/15397000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (603813/100000000000000000000 : ℝ)*base89 + (603813/100000000000000000000 : ℝ)*base91 + (603813/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1083_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2071/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5313/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1759/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3337/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1083_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1083_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1759/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3337/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1083_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1083_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1083_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1759/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3337/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1083_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

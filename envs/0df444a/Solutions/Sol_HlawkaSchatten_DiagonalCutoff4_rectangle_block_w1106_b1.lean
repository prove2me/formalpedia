-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1106_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:03:16.538701+00:00
-- url     : https://prove2.me/submissions/41051bc7-cf0b-425c-a8f0-197e27166cfc

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
theorem support_rectangle_w1106_s3_0 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2179998763/10000000000 : ℝ)*x 0 + (5433014879/10000000000 : ℝ)*x 1 + (5228566137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179998763/10000000000 : ℝ)^8299 ≤ (13234766047841/100000000000000 : ℝ)^6251 := by
    have hnat : (2179998763 : ℕ)^8299*100000000000000^6251 ≤ 13234766047841^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179998763 10000000000 13234766047841 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433014879/10000000000 : ℝ)^8299 ≤ (44486986073983/100000000000000 : ℝ)^6251 := by
    have hnat : (5433014879 : ℕ)^8299*100000000000000^6251 ≤ 44486986073983^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433014879 10000000000 44486986073983 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228566137/10000000000 : ℝ)^8299 ≤ (42278247871943/100000000000000 : ℝ)^6251 := by
    have hnat : (5228566137 : ℕ)^8299*100000000000000^6251 ≤ 42278247871943^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228566137 10000000000 42278247871943 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2179998763/10000000000 : ℝ), (5433014879/10000000000 : ℝ), (5228566137/10000000000 : ℝ)] ![(13234766047841/100000000000000 : ℝ), (44486986073983/100000000000000 : ℝ), (42278247871943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2179998763/10000000000 : ℝ)|^8299 ≤ (13234766047841/100000000000000 : ℝ)^6251
        have hw : |(-2179998763/10000000000 : ℝ)|=(2179998763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433014879/10000000000 : ℝ)|^8299 ≤ (44486986073983/100000000000000 : ℝ)^6251
        have hw : |(5433014879/10000000000 : ℝ)|=(5433014879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228566137/10000000000 : ℝ)|^8299 ≤ (42278247871943/100000000000000 : ℝ)^6251
        have hw : |(5228566137/10000000000 : ℝ)|=(5228566137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s3_1 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2677339211/5000000000 : ℝ)*x 0 + (-2284591321/10000000000 : ℝ)*x 1 + (5228566241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677339211/5000000000 : ℝ)^8299 ≤ (43637410659803/100000000000000 : ℝ)^6251 := by
    have hnat : (2677339211 : ℕ)^8299*100000000000000^6251 ≤ 43637410659803^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677339211 5000000000 43637410659803 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2284591321/10000000000 : ℝ)^8299 ≤ (2816868066807/20000000000000 : ℝ)^6251 := by
    have hnat : (2284591321 : ℕ)^8299*20000000000000^6251 ≤ 2816868066807^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284591321 10000000000 2816868066807 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228566241/10000000000 : ℝ)^8299 ≤ (8455649797681/20000000000000 : ℝ)^6251 := by
    have hnat : (5228566241 : ℕ)^8299*20000000000000^6251 ≤ 8455649797681^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228566241 10000000000 8455649797681 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677339211/5000000000 : ℝ), (-2284591321/10000000000 : ℝ), (5228566241/10000000000 : ℝ)] ![(43637410659803/100000000000000 : ℝ), (2816868066807/20000000000000 : ℝ), (8455649797681/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677339211/5000000000 : ℝ)|^8299 ≤ (43637410659803/100000000000000 : ℝ)^6251
        have hw : |(2677339211/5000000000 : ℝ)|=(2677339211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2284591321/10000000000 : ℝ)|^8299 ≤ (2816868066807/20000000000000 : ℝ)^6251
        have hw : |(-2284591321/10000000000 : ℝ)|=(2284591321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228566241/10000000000 : ℝ)|^8299 ≤ (8455649797681/20000000000000 : ℝ)^6251
        have hw : |(5228566241/10000000000 : ℝ)|=(5228566241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s3_2 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2677339279/5000000000 : ℝ)*x 0 + (2614283169/5000000000 : ℝ)*x 1 + (-1142295507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677339279/5000000000 : ℝ)^8299 ≤ (43637412131237/100000000000000 : ℝ)^6251 := by
    have hnat : (2677339279 : ℕ)^8299*100000000000000^6251 ≤ 43637412131237^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677339279 5000000000 43637412131237 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614283169/5000000000 : ℝ)^8299 ≤ (42278250029721/100000000000000 : ℝ)^6251 := by
    have hnat : (2614283169 : ℕ)^8299*100000000000000^6251 ≤ 42278250029721^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614283169 5000000000 42278250029721 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1142295507/5000000000 : ℝ)^8299 ≤ (14084337821323/100000000000000 : ℝ)^6251 := by
    have hnat : (1142295507 : ℕ)^8299*100000000000000^6251 ≤ 14084337821323^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142295507 5000000000 14084337821323 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677339279/5000000000 : ℝ), (2614283169/5000000000 : ℝ), (-1142295507/5000000000 : ℝ)] ![(43637412131237/100000000000000 : ℝ), (42278250029721/100000000000000 : ℝ), (14084337821323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677339279/5000000000 : ℝ)|^8299 ≤ (43637412131237/100000000000000 : ℝ)^6251
        have hw : |(2677339279/5000000000 : ℝ)|=(2677339279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614283169/5000000000 : ℝ)|^8299 ≤ (42278250029721/100000000000000 : ℝ)^6251
        have hw : |(2614283169/5000000000 : ℝ)|=(2614283169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1142295507/5000000000 : ℝ)|^8299 ≤ (14084337821323/100000000000000 : ℝ)^6251
        have hw : |(-1142295507/5000000000 : ℝ)|=(1142295507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s3_3 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2183634183/5000000000 : ℝ)*x 0 + (4170009259/10000000000 : ℝ)*x 1 + (571735459/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183634183/5000000000 : ℝ)^8299 ≤ (33291450192601/100000000000000 : ℝ)^6251 := by
    have hnat : (2183634183 : ℕ)^8299*100000000000000^6251 ≤ 33291450192601^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183634183 5000000000 33291450192601 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170009259/10000000000 : ℝ)^8299 ≤ (31310026148901/100000000000000 : ℝ)^6251 := by
    have hnat : (4170009259 : ℕ)^8299*100000000000000^6251 ≤ 31310026148901^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170009259 10000000000 31310026148901 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (571735459/1250000000 : ℝ)^8299 ≤ (35398523645279/100000000000000 : ℝ)^6251 := by
    have hnat : (571735459 : ℕ)^8299*100000000000000^6251 ≤ 35398523645279^6251*1250000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571735459 1250000000 35398523645279 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183634183/5000000000 : ℝ), (4170009259/10000000000 : ℝ), (571735459/1250000000 : ℝ)] ![(33291450192601/100000000000000 : ℝ), (31310026148901/100000000000000 : ℝ), (35398523645279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183634183/5000000000 : ℝ)|^8299 ≤ (33291450192601/100000000000000 : ℝ)^6251
        have hw : |(2183634183/5000000000 : ℝ)|=(2183634183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170009259/10000000000 : ℝ)|^8299 ≤ (31310026148901/100000000000000 : ℝ)^6251
        have hw : |(4170009259/10000000000 : ℝ)|=(4170009259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(571735459/1250000000 : ℝ)|^8299 ≤ (35398523645279/100000000000000 : ℝ)^6251
        have hw : |(571735459/1250000000 : ℝ)|=(571735459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s3_4 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-272502331/1250000000 : ℝ)*x 0 + (5229380237/10000000000 : ℝ)*x 1 + (5432196161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272502331/1250000000 : ℝ)^8299 ≤ (330873158041/2500000000000 : ℝ)^6251 := by
    have hnat : (272502331 : ℕ)^8299*2500000000000^6251 ≤ 330873158041^6251*1250000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272502331 1250000000 330873158041 2500000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5229380237/10000000000 : ℝ)^8299 ≤ (42286987631241/100000000000000 : ℝ)^6251 := by
    have hnat : (5229380237 : ℕ)^8299*100000000000000^6251 ≤ 42286987631241^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229380237 10000000000 42286987631241 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432196161/10000000000 : ℝ)^8299 ≤ (8895617206739/20000000000000 : ℝ)^6251 := by
    have hnat : (5432196161 : ℕ)^8299*20000000000000^6251 ≤ 8895617206739^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432196161 10000000000 8895617206739 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-272502331/1250000000 : ℝ), (5229380237/10000000000 : ℝ), (5432196161/10000000000 : ℝ)] ![(330873158041/2500000000000 : ℝ), (42286987631241/100000000000000 : ℝ), (8895617206739/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-272502331/1250000000 : ℝ)|^8299 ≤ (330873158041/2500000000000 : ℝ)^6251
        have hw : |(-272502331/1250000000 : ℝ)|=(272502331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5229380237/10000000000 : ℝ)|^8299 ≤ (42286987631241/100000000000000 : ℝ)^6251
        have hw : |(5229380237/10000000000 : ℝ)|=(5229380237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432196161/10000000000 : ℝ)|^8299 ≤ (8895617206739/20000000000000 : ℝ)^6251
        have hw : |(5432196161/10000000000 : ℝ)|=(5432196161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s3_5 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5303020353/10000000000 : ℝ)*x 0 + (-1040480613/5000000000 : ℝ)*x 1 + (2716098183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303020353/10000000000 : ℝ)^8299 ≤ (5384923531841/12500000000000 : ℝ)^6251 := by
    have hnat : (5303020353 : ℕ)^8299*12500000000000^6251 ≤ 5384923531841^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303020353 10000000000 5384923531841 12500000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040480613/5000000000 : ℝ)^8299 ≤ (1244252347321/10000000000000 : ℝ)^6251 := by
    have hnat : (1040480613 : ℕ)^8299*10000000000000^6251 ≤ 1244252347321^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040480613 5000000000 1244252347321 10000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716098183/5000000000 : ℝ)^8299 ≤ (22239044131067/50000000000000 : ℝ)^6251 := by
    have hnat : (2716098183 : ℕ)^8299*50000000000000^6251 ≤ 22239044131067^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716098183 5000000000 22239044131067 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303020353/10000000000 : ℝ), (-1040480613/5000000000 : ℝ), (2716098183/5000000000 : ℝ)] ![(5384923531841/12500000000000 : ℝ), (1244252347321/10000000000000 : ℝ), (22239044131067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303020353/10000000000 : ℝ)|^8299 ≤ (5384923531841/12500000000000 : ℝ)^6251
        have hw : |(5303020353/10000000000 : ℝ)|=(5303020353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1040480613/5000000000 : ℝ)|^8299 ≤ (1244252347321/10000000000000 : ℝ)^6251
        have hw : |(-1040480613/5000000000 : ℝ)|=(1040480613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716098183/5000000000 : ℝ)|^8299 ≤ (22239044131067/50000000000000 : ℝ)^6251
        have hw : |(2716098183/5000000000 : ℝ)|=(2716098183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s3_6 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5303020419/10000000000 : ℝ)*x 0 + (5432196177/10000000000 : ℝ)*x 1 + (-1040480697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303020419/10000000000 : ℝ)^8299 ≤ (21539694483271/50000000000000 : ℝ)^6251 := by
    have hnat : (5303020419 : ℕ)^8299*50000000000000^6251 ≤ 21539694483271^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303020419 10000000000 21539694483271 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432196177/10000000000 : ℝ)^8299 ≤ (22239043103811/50000000000000 : ℝ)^6251 := by
    have hnat : (5432196177 : ℕ)^8299*50000000000000^6251 ≤ 22239043103811^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432196177 10000000000 22239043103811 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040480697/5000000000 : ℝ)^8299 ≤ (1555315600853/12500000000000 : ℝ)^6251 := by
    have hnat : (1040480697 : ℕ)^8299*12500000000000^6251 ≤ 1555315600853^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040480697 5000000000 1555315600853 12500000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303020419/10000000000 : ℝ), (5432196177/10000000000 : ℝ), (-1040480697/5000000000 : ℝ)] ![(21539694483271/50000000000000 : ℝ), (22239043103811/50000000000000 : ℝ), (1555315600853/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303020419/10000000000 : ℝ)|^8299 ≤ (21539694483271/50000000000000 : ℝ)^6251
        have hw : |(5303020419/10000000000 : ℝ)|=(5303020419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432196177/10000000000 : ℝ)|^8299 ≤ (22239043103811/50000000000000 : ℝ)^6251
        have hw : |(5432196177/10000000000 : ℝ)|=(5432196177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1040480697/5000000000 : ℝ)|^8299 ≤ (1555315600853/12500000000000 : ℝ)^6251
        have hw : |(-1040480697/5000000000 : ℝ)|=(1040480697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s3_7 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (10918269/25000000 : ℝ)*x 0 + (4572276341/10000000000 : ℝ)*x 1 + (834325197/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10918269/25000000 : ℝ)^8299 ≤ (16645923629129/50000000000000 : ℝ)^6251 := by
    have hnat : (10918269 : ℕ)^8299*50000000000000^6251 ≤ 16645923629129^6251*25000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10918269 25000000 16645923629129 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4572276341/10000000000 : ℝ)^8299 ≤ (35382009480357/100000000000000 : ℝ)^6251 := by
    have hnat : (4572276341 : ℕ)^8299*100000000000000^6251 ≤ 35382009480357^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4572276341 10000000000 35382009480357 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (834325197/2000000000 : ℝ)^8299 ≤ (15663071620333/50000000000000 : ℝ)^6251 := by
    have hnat : (834325197 : ℕ)^8299*50000000000000^6251 ≤ 15663071620333^6251*2000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834325197 2000000000 15663071620333 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10918269/25000000 : ℝ), (4572276341/10000000000 : ℝ), (834325197/2000000000 : ℝ)] ![(16645923629129/50000000000000 : ℝ), (35382009480357/100000000000000 : ℝ), (15663071620333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10918269/25000000 : ℝ)|^8299 ≤ (16645923629129/50000000000000 : ℝ)^6251
        have hw : |(10918269/25000000 : ℝ)|=(10918269/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4572276341/10000000000 : ℝ)|^8299 ≤ (35382009480357/100000000000000 : ℝ)^6251
        have hw : |(4572276341/10000000000 : ℝ)|=(4572276341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(834325197/2000000000 : ℝ)|^8299 ≤ (15663071620333/50000000000000 : ℝ)^6251
        have hw : |(834325197/2000000000 : ℝ)|=(834325197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1106_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16613/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1113/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (421/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14851/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16613/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1113/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16613/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1113/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16613/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1113/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16613/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1113/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16613/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1113/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16613/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1113/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1113/12500 : ℝ) ^ (4149/1024 : ℝ) ≤ (5545917828352169/100000000000000000000 : ℝ) := by
    have hpowers : (1113/12500 : ℝ)^4149 ≤ (5545917828352169/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1113 : ℕ)^4149*100000000000000000000^1024 ≤ 5545917828352169^1024*12500^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1113 12500 5545917828352169 100000000000000000000 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1113/12500 : ℝ)) (X := (5545917828352169/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16613/100000 : ℝ) ^ (4149/1024 : ℝ) ≤ (34706783104505387/50000000000000000000 : ℝ) := by
    have hpowers : (16613/100000 : ℝ)^4149 ≤ (34706783104505387/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16613 : ℕ)^4149*50000000000000000000^1024 ≤ 34706783104505387^1024*100000^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16613 100000 34706783104505387 50000000000000000000 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16613/100000 : ℝ)) (X := (34706783104505387/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005545917828352169/50000000000000000000 : ℝ) ≤ (1250034217779287/1250000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (50005545917828352169/50000000000000000000 : ℝ)^1024 ≤ (1250034217779287/1250000000000000 : ℝ)^4149 := by
      have hnat : (50005545917828352169 : ℕ)^1024*1250000000000000^4149 ≤ 1250034217779287^4149*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005545917828352169 50000000000000000000 1250034217779287 1250000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250034217779287/1250000000000000 : ℝ)) (X := (50005545917828352169/50000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100074959484037362943/100000000000000000000 : ℝ) ≤ (2000369905290903/2000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (100074959484037362943/100000000000000000000 : ℝ)^1024 ≤ (2000369905290903/2000000000000000 : ℝ)^4149 := by
      have hnat : (100074959484037362943 : ℕ)^1024*2000000000000000^4149 ≤ 2000369905290903^4149*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100074959484037362943 100000000000000000000 2000369905290903 2000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000369905290903/2000000000000000 : ℝ)) (X := (100074959484037362943/100000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25034706783104505387/25000000000000000000 : ℝ) ≤ (5001712655337367/5000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (25034706783104505387/25000000000000000000 : ℝ)^1024 ≤ (5001712655337367/5000000000000000 : ℝ)^4149 := by
      have hnat : (25034706783104505387 : ℕ)^1024*5000000000000000^4149 ≤ 5001712655337367^4149*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25034706783104505387 25000000000000000000 5001712655337367 5000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001712655337367/5000000000000000 : ℝ)) (X := (25034706783104505387/25000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5545917828352169/100000000000000000000 : ℝ) ≤ ((9633006089186315989/9636250000000000000 : ℝ)+2*(1575784220219/770900000000000 : ℝ)*(1113/12500 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (9633006089186315989/9636250000000000000 : ℝ)+2*(1575784220219/770900000000000 : ℝ)*(1113/12500 : ℝ)=(1250034217779287/1250000000000000 : ℝ) by norm_num, show 1+2*(5545917828352169/100000000000000000000 : ℝ)=(50005545917828352169/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34706783104505387/50000000000000000000 : ℝ)+(5545917828352169/100000000000000000000 : ℝ) ≤ ((9633006089186315989/9636250000000000000 : ℝ)+(1575784220219/770900000000000 : ℝ)*((16613/100000 : ℝ)+(1113/12500 : ℝ)))^(4149/1024 : ℝ) := by
    rw [show (9633006089186315989/9636250000000000000 : ℝ)+(1575784220219/770900000000000 : ℝ)*((16613/100000 : ℝ)+(1113/12500 : ℝ))=(2000369905290903/2000000000000000 : ℝ) by norm_num, show 1+(34706783104505387/50000000000000000000 : ℝ)+(5545917828352169/100000000000000000000 : ℝ)=(100074959484037362943/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34706783104505387/50000000000000000000 : ℝ) ≤ ((9633006089186315989/9636250000000000000 : ℝ)+2*(1575784220219/770900000000000 : ℝ)*(16613/100000 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (9633006089186315989/9636250000000000000 : ℝ)+2*(1575784220219/770900000000000 : ℝ)*(16613/100000 : ℝ)=(5001712655337367/5000000000000000 : ℝ) by norm_num, show 1+2*(34706783104505387/50000000000000000000 : ℝ)=(25034706783104505387/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9633006089186315989/9636250000000000000 : ℝ)*(X 1 0+X 2 0)+(1575784220219/770900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (1113/12500 : ℝ)) (hi := (16613/100000 : ℝ)) (c := (9633006089186315989/9636250000000000000 : ℝ)) (alpha := (1575784220219/770900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9633006089186315989/9636250000000000000 : ℝ)*(X 0 1+X 2 1)+(1575784220219/770900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (1113/12500 : ℝ)) (hi := (16613/100000 : ℝ)) (c := (9633006089186315989/9636250000000000000 : ℝ)) (alpha := (1575784220219/770900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9633006089186315989/9636250000000000000 : ℝ)*(X 0 2+X 1 2)+(1575784220219/770900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (1113/12500 : ℝ)) (hi := (16613/100000 : ℝ)) (c := (9633006089186315989/9636250000000000000 : ℝ)) (alpha := (1575784220219/770900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2179998763/10000000000 : ℝ)*X 0 0+(5433014879/10000000000 : ℝ)*X 0 1+(5228566137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677339211/5000000000 : ℝ)*X 1 0+(-2284591321/10000000000 : ℝ)*X 1 1+(5228566241/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677339279/5000000000 : ℝ)*X 2 0+(2614283169/5000000000 : ℝ)*X 2 1+(-1142295507/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2183634183/5000000000 : ℝ)*X 0 0+(4170009259/10000000000 : ℝ)*X 0 1+(571735459/1250000000 : ℝ)*X 0 2+(2183634183/5000000000 : ℝ)*X 1 0+(4170009259/10000000000 : ℝ)*X 1 1+(571735459/1250000000 : ℝ)*X 1 2+(2183634183/5000000000 : ℝ)*X 2 0+(4170009259/10000000000 : ℝ)*X 2 1+(571735459/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-272502331/1250000000 : ℝ)*X 0 0+(5229380237/10000000000 : ℝ)*X 0 1+(5432196161/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303020353/10000000000 : ℝ)*X 1 0+(-1040480613/5000000000 : ℝ)*X 1 1+(2716098183/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303020419/10000000000 : ℝ)*X 2 0+(5432196177/10000000000 : ℝ)*X 2 1+(-1040480697/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((10918269/25000000 : ℝ)*X 0 0+(4572276341/10000000000 : ℝ)*X 0 1+(834325197/2000000000 : ℝ)*X 0 2+(10918269/25000000 : ℝ)*X 1 0+(4572276341/10000000000 : ℝ)*X 1 1+(834325197/2000000000 : ℝ)*X 1 2+(10918269/25000000 : ℝ)*X 2 0+(4572276341/10000000000 : ℝ)*X 2 1+(834325197/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (141670836364079530756077441/30113281250000000000000000000000 : ℝ) := by norm_num
    linear_combination (721958603/50000000000000 : ℝ)*(base19) + (1356506127/100000000000000 : ℝ)*(base23) + (113326959/100000000000000 : ℝ)*(lower2) + (8446439/20000000000000 : ℝ)*(upper3) + (43468701/20000000000000 : ℝ)*(upper5) + (3597316131459/97656250000 : ℝ)*(major0) + (3597316131459/97656250000 : ℝ)*(major1) + (3597316131459/97656250000 : ℝ)*(major2) + (2445613615705749/50000000000000 : ℝ)*(sp0) + (2445630022666541/50000000000000 : ℝ)*(sp1) + (4891260132744161/100000000000000 : ℝ)*(sp2) + (154751875816167/6250000000000 : ℝ)*(sp3) + (34257838791/100000000000000 : ℝ)*(sp4) + (588904959/5000000000000 : ℝ)*(sp7) + (619010447789463/25000000000000 : ℝ)*(f.failure) + (4891261489250289/100000000000000 : ℝ)*(f.sum) + (66216007908027/19272500000000000000000000000 : ℝ)*base65 + (921234615982502897/120453125000000000000000000000000 : ℝ)*base68 + (836065200279747103/120453125000000000000000000000000 : ℝ)*base69 + (428130348513862557/30113281250000000000000000000000 : ℝ)*base71 + (79691785965633/19272500000000000000000000000 : ℝ)*base74 + (34789290247959489/60226562500000000000000000000000 : ℝ)*base75 + (457666657255021989/60226562500000000000000000000000 : ℝ)*base77 + (1287302066921396989/60226562500000000000000000000000 : ℝ)*base79 + (68165609768077/19272500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1438233/2500000000000000000000 : ℝ)*base89 + (1438233/2500000000000000000000 : ℝ)*base91 + (1438233/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11233773345629644872957/1482500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1378209279/100000000000000 : ℝ)*(base19) + (212343541/12500000000000 : ℝ)*(base23) + (40520817/20000000000000 : ℝ)*(upper3) + (122996653/100000000000000 : ℝ)*(lower4) + (19480567/20000000000000 : ℝ)*(upper5) + (1856629310084497/50000000000000 : ℝ)*(major0) + (1856629310084497/50000000000000 : ℝ)*(major1) + (1856629310084497/50000000000000 : ℝ)*(major2) + (25929936563/100000000000000 : ℝ)*(sp1) + (5745198161/20000000000000 : ℝ)*(sp2) + (4930574312591631/100000000000000 : ℝ)*(sp4) + (493054700444579/10000000000000 : ℝ)*(sp5) + (4930543887852497/100000000000000 : ℝ)*(sp6) + (2495942675160101/100000000000000 : ℝ)*(sp7) + (2495942675160101/100000000000000 : ℝ)*(f.failure) + (4930574312591631/100000000000000 : ℝ)*(f.sum) + (4862217603629/1482500000000000000000000000 : ℝ)*base66 + (167989028260531541/37062500000000000000000000000000 : ℝ)*base67 + (58443799875968459/37062500000000000000000000000000 : ℝ)*base70 + (451407183259718459/37062500000000000000000000000000 : ℝ)*base72 + (4874036356513/741250000000000000000000000 : ℝ)*base73 + (761758115974468459/37062500000000000000000000000000 : ℝ)*base76 + (107877506092719041/37062500000000000000000000000000 : ℝ)*base77 + (380697034472031541/37062500000000000000000000000000 : ℝ)*base79 + (6083863501717/2965000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (37510891/10000000000000000000000 : ℝ)*base89 + (37510891/10000000000000000000000 : ℝ)*base91 + (37510891/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1106_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16613/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1113/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (421/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14851/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1106_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1106_s4_0 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2183307319/10000000000 : ℝ)*x 0 + (5403682229/10000000000 : ℝ)*x 1 + (2627867819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183307319/10000000000 : ℝ)^8299 ≤ (13261439713323/100000000000000 : ℝ)^6251 := by
    have hnat : (2183307319 : ℕ)^8299*100000000000000^6251 ≤ 13261439713323^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183307319 10000000000 13261439713323 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403682229/10000000000 : ℝ)^8299 ≤ (8833678807133/20000000000000 : ℝ)^6251 := by
    have hnat : (5403682229 : ℕ)^8299*20000000000000^6251 ≤ 8833678807133^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403682229 10000000000 8833678807133 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627867819/5000000000 : ℝ)^8299 ≤ (42570166226787/100000000000000 : ℝ)^6251 := by
    have hnat : (2627867819 : ℕ)^8299*100000000000000^6251 ≤ 42570166226787^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627867819 5000000000 42570166226787 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2183307319/10000000000 : ℝ), (5403682229/10000000000 : ℝ), (2627867819/5000000000 : ℝ)] ![(13261439713323/100000000000000 : ℝ), (8833678807133/20000000000000 : ℝ), (42570166226787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2183307319/10000000000 : ℝ)|^8299 ≤ (13261439713323/100000000000000 : ℝ)^6251
        have hw : |(-2183307319/10000000000 : ℝ)|=(2183307319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403682229/10000000000 : ℝ)|^8299 ≤ (8833678807133/20000000000000 : ℝ)^6251
        have hw : |(5403682229/10000000000 : ℝ)|=(5403682229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627867819/5000000000 : ℝ)|^8299 ≤ (42570166226787/100000000000000 : ℝ)^6251
        have hw : |(2627867819/5000000000 : ℝ)|=(2627867819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s4_1 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668422617/1250000000 : ℝ)*x 0 + (-2258519793/10000000000 : ℝ)*x 1 + (5255736357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668422617/1250000000 : ℝ)^8299 ≤ (2177923705699/5000000000000 : ℝ)^6251 := by
    have hnat : (668422617 : ℕ)^8299*5000000000000^6251 ≤ 2177923705699^6251*1250000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668422617 1250000000 2177923705699 5000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2258519793/10000000000 : ℝ)^8299 ≤ (1387135190659/10000000000000 : ℝ)^6251 := by
    have hnat : (2258519793 : ℕ)^8299*10000000000000^6251 ≤ 1387135190659^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258519793 10000000000 1387135190659 10000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255736357/10000000000 : ℝ)^8299 ≤ (42570173958523/100000000000000 : ℝ)^6251 := by
    have hnat : (5255736357 : ℕ)^8299*100000000000000^6251 ≤ 42570173958523^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255736357 10000000000 42570173958523 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668422617/1250000000 : ℝ), (-2258519793/10000000000 : ℝ), (5255736357/10000000000 : ℝ)] ![(2177923705699/5000000000000 : ℝ), (1387135190659/10000000000000 : ℝ), (42570173958523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668422617/1250000000 : ℝ)|^8299 ≤ (2177923705699/5000000000000 : ℝ)^6251
        have hw : |(668422617/1250000000 : ℝ)|=(668422617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2258519793/10000000000 : ℝ)|^8299 ≤ (1387135190659/10000000000000 : ℝ)^6251
        have hw : |(-2258519793/10000000000 : ℝ)|=(2258519793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255736357/10000000000 : ℝ)|^8299 ≤ (42570173958523/100000000000000 : ℝ)^6251
        have hw : |(5255736357/10000000000 : ℝ)|=(5255736357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s4_2 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347380313/10000000000 : ℝ)*x 0 + (5255736493/10000000000 : ℝ)*x 1 + (-1129260221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347380313/10000000000 : ℝ)^8299 ≤ (21779233688263/50000000000000 : ℝ)^6251 := by
    have hnat : (5347380313 : ℕ)^8299*50000000000000^6251 ≤ 21779233688263^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347380313 10000000000 21779233688263 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255736493/10000000000 : ℝ)^8299 ≤ (42570175420993/100000000000000 : ℝ)^6251 := by
    have hnat : (5255736493 : ℕ)^8299*100000000000000^6251 ≤ 42570175420993^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255736493 10000000000 42570175420993 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129260221/5000000000 : ℝ)^8299 ≤ (6935678599271/50000000000000 : ℝ)^6251 := by
    have hnat : (1129260221 : ℕ)^8299*50000000000000^6251 ≤ 6935678599271^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129260221 5000000000 6935678599271 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347380313/10000000000 : ℝ), (5255736493/10000000000 : ℝ), (-1129260221/5000000000 : ℝ)] ![(21779233688263/50000000000000 : ℝ), (42570175420993/100000000000000 : ℝ), (6935678599271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347380313/10000000000 : ℝ)|^8299 ≤ (21779233688263/50000000000000 : ℝ)^6251
        have hw : |(5347380313/10000000000 : ℝ)|=(5347380313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255736493/10000000000 : ℝ)|^8299 ≤ (42570175420993/100000000000000 : ℝ)^6251
        have hw : |(5255736493/10000000000 : ℝ)|=(5255736493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1129260221/5000000000 : ℝ)|^8299 ≤ (6935678599271/50000000000000 : ℝ)^6251
        have hw : |(-1129260221/5000000000 : ℝ)|=(1129260221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s4_3 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1092309713/2500000000 : ℝ)*x 0 + (264097503/625000000 : ℝ)*x 1 + (2258909493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092309713/2500000000 : ℝ)^8299 ≤ (16655696919101/50000000000000 : ℝ)^6251 := by
    have hnat : (1092309713 : ℕ)^8299*50000000000000^6251 ≤ 16655696919101^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092309713 2500000000 16655696919101 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264097503/625000000 : ℝ)^8299 ≤ (199156124487/625000000000 : ℝ)^6251 := by
    have hnat : (264097503 : ℕ)^8299*625000000000^6251 ≤ 199156124487^6251*625000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264097503 625000000 199156124487 625000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2258909493/5000000000 : ℝ)^8299 ≤ (17411813112799/50000000000000 : ℝ)^6251 := by
    have hnat : (2258909493 : ℕ)^8299*50000000000000^6251 ≤ 17411813112799^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258909493 5000000000 17411813112799 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092309713/2500000000 : ℝ), (264097503/625000000 : ℝ), (2258909493/5000000000 : ℝ)] ![(16655696919101/50000000000000 : ℝ), (199156124487/625000000000 : ℝ), (17411813112799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092309713/2500000000 : ℝ)|^8299 ≤ (16655696919101/50000000000000 : ℝ)^6251
        have hw : |(1092309713/2500000000 : ℝ)|=(1092309713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264097503/625000000 : ℝ)|^8299 ≤ (199156124487/625000000000 : ℝ)^6251
        have hw : |(264097503/625000000 : ℝ)|=(264097503/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2258909493/5000000000 : ℝ)|^8299 ≤ (17411813112799/50000000000000 : ℝ)^6251
        have hw : |(2258909493/5000000000 : ℝ)|=(2258909493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s4_4 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2183313893/10000000000 : ℝ)*x 0 + (262808159/500000000 : ℝ)*x 1 + (2701626831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183313893/10000000000 : ℝ)^8299 ≤ (530459709051/4000000000000 : ℝ)^6251 := by
    have hnat : (2183313893 : ℕ)^8299*4000000000000^6251 ≤ 530459709051^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183313893 10000000000 530459709051 4000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262808159/500000000 : ℝ)^8299 ≤ (4257476384253/10000000000000 : ℝ)^6251 := by
    have hnat : (262808159 : ℕ)^8299*10000000000000^6251 ≤ 4257476384253^6251*500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262808159 500000000 4257476384253 10000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701626831/5000000000 : ℝ)^8299 ≤ (2760233963277/6250000000000 : ℝ)^6251 := by
    have hnat : (2701626831 : ℕ)^8299*6250000000000^6251 ≤ 2760233963277^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701626831 5000000000 2760233963277 6250000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2183313893/10000000000 : ℝ), (262808159/500000000 : ℝ), (2701626831/5000000000 : ℝ)] ![(530459709051/4000000000000 : ℝ), (4257476384253/10000000000000 : ℝ), (2760233963277/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2183313893/10000000000 : ℝ)|^8299 ≤ (530459709051/4000000000000 : ℝ)^6251
        have hw : |(-2183313893/10000000000 : ℝ)|=(2183313893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262808159/500000000 : ℝ)|^8299 ≤ (4257476384253/10000000000000 : ℝ)^6251
        have hw : |(262808159/500000000 : ℝ)|=(262808159/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701626831/5000000000 : ℝ)|^8299 ≤ (2760233963277/6250000000000 : ℝ)^6251
        have hw : |(2701626831/5000000000 : ℝ)|=(2701626831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s4_5 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310001343/10000000000 : ℝ)*x 0 + (-2111002913/10000000000 : ℝ)*x 1 + (5403253649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310001343/10000000000 : ℝ)^8299 ≤ (5394336858829/12500000000000 : ℝ)^6251 := by
    have hnat : (5310001343 : ℕ)^8299*12500000000000^6251 ≤ 5394336858829^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310001343 10000000000 5394336858829 12500000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111002913/10000000000 : ℝ)^8299 ≤ (6340780920183/50000000000000 : ℝ)^6251 := by
    have hnat : (2111002913 : ℕ)^8299*50000000000000^6251 ≤ 6340780920183^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111002913 10000000000 6340780920183 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403253649/10000000000 : ℝ)^8299 ≤ (44163743271363/100000000000000 : ℝ)^6251 := by
    have hnat : (5403253649 : ℕ)^8299*100000000000000^6251 ≤ 44163743271363^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403253649 10000000000 44163743271363 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310001343/10000000000 : ℝ), (-2111002913/10000000000 : ℝ), (5403253649/10000000000 : ℝ)] ![(5394336858829/12500000000000 : ℝ), (6340780920183/50000000000000 : ℝ), (44163743271363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310001343/10000000000 : ℝ)|^8299 ≤ (5394336858829/12500000000000 : ℝ)^6251
        have hw : |(5310001343/10000000000 : ℝ)|=(5310001343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2111002913/10000000000 : ℝ)|^8299 ≤ (6340780920183/50000000000000 : ℝ)^6251
        have hw : |(-2111002913/10000000000 : ℝ)|=(2111002913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403253649/10000000000 : ℝ)|^8299 ≤ (44163743271363/100000000000000 : ℝ)^6251
        have hw : |(5403253649/10000000000 : ℝ)|=(5403253649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s4_6 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655000667/5000000000 : ℝ)*x 0 + (5403253633/10000000000 : ℝ)*x 1 + (-2111002947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655000667/5000000000 : ℝ)^8299 ≤ (10788673693381/25000000000000 : ℝ)^6251 := by
    have hnat : (2655000667 : ℕ)^8299*25000000000000^6251 ≤ 10788673693381^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655000667 5000000000 10788673693381 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403253633/10000000000 : ℝ)^8299 ≤ (2208187154887/5000000000000 : ℝ)^6251 := by
    have hnat : (5403253633 : ℕ)^8299*5000000000000^6251 ≤ 2208187154887^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403253633 10000000000 2208187154887 5000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111002947/10000000000 : ℝ)^8299 ≤ (6340781055767/50000000000000 : ℝ)^6251 := by
    have hnat : (2111002947 : ℕ)^8299*50000000000000^6251 ≤ 6340781055767^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111002947 10000000000 6340781055767 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655000667/5000000000 : ℝ), (5403253633/10000000000 : ℝ), (-2111002947/10000000000 : ℝ)] ![(10788673693381/25000000000000 : ℝ), (2208187154887/5000000000000 : ℝ), (6340781055767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655000667/5000000000 : ℝ)|^8299 ≤ (10788673693381/25000000000000 : ℝ)^6251
        have hw : |(2655000667/5000000000 : ℝ)|=(2655000667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403253633/10000000000 : ℝ)|^8299 ≤ (2208187154887/5000000000000 : ℝ)^6251
        have hw : |(5403253633/10000000000 : ℝ)|=(5403253633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2111002947/10000000000 : ℝ)|^8299 ≤ (6340781055767/50000000000000 : ℝ)^6251
        have hw : |(-2111002947/10000000000 : ℝ)|=(2111002947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s4_7 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4369253239/10000000000 : ℝ)*x 0 + (451697549/1000000000 : ℝ)*x 1 + (4226407631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369253239/10000000000 : ℝ)^8299 ≤ (4163942432809/12500000000000 : ℝ)^6251 := by
    have hnat : (4369253239 : ℕ)^8299*12500000000000^6251 ≤ 4163942432809^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369253239 10000000000 4163942432809 12500000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451697549/1000000000 : ℝ)^8299 ≤ (34814994628187/100000000000000 : ℝ)^6251 := by
    have hnat : (451697549 : ℕ)^8299*100000000000000^6251 ≤ 34814994628187^6251*1000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451697549 1000000000 34814994628187 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4226407631/10000000000 : ℝ)^8299 ≤ (31873465900657/100000000000000 : ℝ)^6251 := by
    have hnat : (4226407631 : ℕ)^8299*100000000000000^6251 ≤ 31873465900657^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226407631 10000000000 31873465900657 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369253239/10000000000 : ℝ), (451697549/1000000000 : ℝ), (4226407631/10000000000 : ℝ)] ![(4163942432809/12500000000000 : ℝ), (34814994628187/100000000000000 : ℝ), (31873465900657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369253239/10000000000 : ℝ)|^8299 ≤ (4163942432809/12500000000000 : ℝ)^6251
        have hw : |(4369253239/10000000000 : ℝ)|=(4369253239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(451697549/1000000000 : ℝ)|^8299 ≤ (34814994628187/100000000000000 : ℝ)^6251
        have hw : |(451697549/1000000000 : ℝ)|=(451697549/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4226407631/10000000000 : ℝ)|^8299 ≤ (31873465900657/100000000000000 : ℝ)^6251
        have hw : |(4226407631/10000000000 : ℝ)|=(4226407631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1106_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14851/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (421/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (2221/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7119/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14851/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (421/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14851/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (421/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14851/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (421/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14851/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (421/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14851/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (421/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14851/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (421/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (421/4000 : ℝ) ^ (4149/1024 : ℝ) ≤ (10921461849573079/100000000000000000000 : ℝ) := by
    have hpowers : (421/4000 : ℝ)^4149 ≤ (10921461849573079/100000000000000000000 : ℝ)^1024 := by
      have hnat : (421 : ℕ)^4149*100000000000000000000^1024 ≤ 10921461849573079^1024*4000^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        421 4000 10921461849573079 100000000000000000000 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (421/4000 : ℝ)) (X := (10921461849573079/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14851/100000 : ℝ) ^ (4149/1024 : ℝ) ≤ (2754448751443881/6250000000000000000 : ℝ) := by
    have hpowers : (14851/100000 : ℝ)^4149 ≤ (2754448751443881/6250000000000000000 : ℝ)^1024 := by
      have hnat : (14851 : ℕ)^4149*6250000000000000000^1024 ≤ 2754448751443881^1024*100000^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14851 100000 2754448751443881 6250000000000000000 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14851/100000 : ℝ)) (X := (2754448751443881/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010921461849573079/50000000000000000000 : ℝ) ≤ (10000539053125727/10000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (50010921461849573079/50000000000000000000 : ℝ)^1024 ≤ (10000539053125727/10000000000000000 : ℝ)^4149 := by
      have hnat : (50010921461849573079 : ℕ)^1024*10000000000000000^4149 ≤ 10000539053125727^4149*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010921461849573079 50000000000000000000 10000539053125727 10000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000539053125727/10000000000000000 : ℝ)) (X := (50010921461849573079/50000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4002199705674907007/4000000000000000000 : ℝ) ≤ (2000271394585123/2000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (4002199705674907007/4000000000000000000 : ℝ)^1024 ≤ (2000271394585123/2000000000000000 : ℝ)^4149 := by
      have hnat : (4002199705674907007 : ℕ)^1024*2000000000000000^4149 ≤ 2000271394585123^4149*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4002199705674907007 4000000000000000000 2000271394585123 2000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000271394585123/2000000000000000 : ℝ)) (X := (4002199705674907007/4000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127754448751443881/3125000000000000000 : ℝ) ≤ (10002174892725503/10000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (3127754448751443881/3125000000000000000 : ℝ)^1024 ≤ (10002174892725503/10000000000000000 : ℝ)^4149 := by
      have hnat : (3127754448751443881 : ℕ)^1024*10000000000000000^4149 ≤ 10002174892725503^4149*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127754448751443881 3125000000000000000 10002174892725503 10000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002174892725503/10000000000000000 : ℝ)) (X := (3127754448751443881/3125000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10921461849573079/100000000000000000000 : ℝ) ≤ ((7207519122005708767/7210000000000000000 : ℝ)+2*(17039995831/9012500000000 : ℝ)*(421/4000 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (7207519122005708767/7210000000000000000 : ℝ)+2*(17039995831/9012500000000 : ℝ)*(421/4000 : ℝ)=(10000539053125727/10000000000000000 : ℝ) by norm_num, show 1+2*(10921461849573079/100000000000000000000 : ℝ)=(50010921461849573079/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2754448751443881/6250000000000000000 : ℝ)+(10921461849573079/100000000000000000000 : ℝ) ≤ ((7207519122005708767/7210000000000000000 : ℝ)+(17039995831/9012500000000 : ℝ)*((14851/100000 : ℝ)+(421/4000 : ℝ)))^(4149/1024 : ℝ) := by
    rw [show (7207519122005708767/7210000000000000000 : ℝ)+(17039995831/9012500000000 : ℝ)*((14851/100000 : ℝ)+(421/4000 : ℝ))=(2000271394585123/2000000000000000 : ℝ) by norm_num, show 1+(2754448751443881/6250000000000000000 : ℝ)+(10921461849573079/100000000000000000000 : ℝ)=(4002199705674907007/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2754448751443881/6250000000000000000 : ℝ) ≤ ((7207519122005708767/7210000000000000000 : ℝ)+2*(17039995831/9012500000000 : ℝ)*(14851/100000 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (7207519122005708767/7210000000000000000 : ℝ)+2*(17039995831/9012500000000 : ℝ)*(14851/100000 : ℝ)=(10002174892725503/10000000000000000 : ℝ) by norm_num, show 1+2*(2754448751443881/6250000000000000000 : ℝ)=(3127754448751443881/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7207519122005708767/7210000000000000000 : ℝ)*(X 1 0+X 2 0)+(17039995831/9012500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (421/4000 : ℝ)) (hi := (14851/100000 : ℝ)) (c := (7207519122005708767/7210000000000000000 : ℝ)) (alpha := (17039995831/9012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7207519122005708767/7210000000000000000 : ℝ)*(X 0 1+X 2 1)+(17039995831/9012500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (421/4000 : ℝ)) (hi := (14851/100000 : ℝ)) (c := (7207519122005708767/7210000000000000000 : ℝ)) (alpha := (17039995831/9012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7207519122005708767/7210000000000000000 : ℝ)*(X 0 2+X 1 2)+(17039995831/9012500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (421/4000 : ℝ)) (hi := (14851/100000 : ℝ)) (c := (7207519122005708767/7210000000000000000 : ℝ)) (alpha := (17039995831/9012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2183307319/10000000000 : ℝ)*X 0 0+(5403682229/10000000000 : ℝ)*X 0 1+(2627867819/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668422617/1250000000 : ℝ)*X 1 0+(-2258519793/10000000000 : ℝ)*X 1 1+(5255736357/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347380313/10000000000 : ℝ)*X 2 0+(5255736493/10000000000 : ℝ)*X 2 1+(-1129260221/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1092309713/2500000000 : ℝ)*X 0 0+(264097503/625000000 : ℝ)*X 0 1+(2258909493/5000000000 : ℝ)*X 0 2+(1092309713/2500000000 : ℝ)*X 1 0+(264097503/625000000 : ℝ)*X 1 1+(2258909493/5000000000 : ℝ)*X 1 2+(1092309713/2500000000 : ℝ)*X 2 0+(264097503/625000000 : ℝ)*X 2 1+(2258909493/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2183313893/10000000000 : ℝ)*X 0 0+(262808159/500000000 : ℝ)*X 0 1+(2701626831/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310001343/10000000000 : ℝ)*X 1 0+(-2111002913/10000000000 : ℝ)*X 1 1+(5403253649/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655000667/5000000000 : ℝ)*X 2 0+(5403253633/10000000000 : ℝ)*X 2 1+(-2111002947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4369253239/10000000000 : ℝ)*X 0 0+(451697549/1000000000 : ℝ)*X 0 1+(4226407631/10000000000 : ℝ)*X 0 2+(4369253239/10000000000 : ℝ)*X 1 0+(451697549/1000000000 : ℝ)*X 1 1+(4226407631/10000000000 : ℝ)*X 1 2+(4369253239/10000000000 : ℝ)*X 2 0+(451697549/1000000000 : ℝ)*X 2 1+(4226407631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57290459725449502637023917/90125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (670920269/25000000000000 : ℝ)*(base19) + (2129764007/100000000000000 : ℝ)*(base23) + (149996161/50000000000000 : ℝ)*(upper2) + (7076549/800000000000 : ℝ)*(upper3) + (175084733/100000000000000 : ℝ)*(upper4) + (2545267349911817/50000000000000 : ℝ)*(major0) + (2545267349911817/50000000000000 : ℝ)*(major1) + (2545267349911817/50000000000000 : ℝ)*(major2) + (3379651573274329/50000000000000 : ℝ)*(sp0) + (3379679876577039/50000000000000 : ℝ)*(sp1) + (6759360307071147/100000000000000 : ℝ)*(sp2) + (342165950946151/10000000000000 : ℝ)*(sp3) + (59290286497/100000000000000 : ℝ)*(sp4) + (23716080669/50000000000000 : ℝ)*(sp7) + (3421706941622847/100000000000000 : ℝ)*(f.failure) + (3379681218417577/50000000000000 : ℝ)*(f.sum) + (18582395473463/3605000000000000000000000000 : ℝ)*base66 + (1934729589765600361/360500000000000000000000000000000 : ℝ)*base68 + (2275668035662600361/360500000000000000000000000000000 : ℝ)*base70 + (3972592854279600361/360500000000000000000000000000000 : ℝ)*base72 + (9856214193999/1802500000000000000000000000 : ℝ)*base74 + (1808314605243399639/360500000000000000000000000000000 : ℝ)*base75 + (1661885911361100361/360500000000000000000000000000000 : ℝ)*base78 + (1983140532370100361/360500000000000000000000000000000 : ℝ)*base80 + (5678866298097/901250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (5291023/10000000000000000000000 : ℝ)*base90 + (5291023/10000000000000000000000 : ℝ)*base92 + (5291023/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (115202895018596391487993341/12875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (406652159/25000000000000 : ℝ)*(base19) + (1749376307/100000000000000 : ℝ)*(base23) + (40638051/25000000000000 : ℝ)*(upper3) + (32294379/50000000000000 : ℝ)*(lower4) + (149046579/100000000000000 : ℝ)*(upper5) + (1280008879006571/25000000000000 : ℝ)*(major0) + (1280008879006571/25000000000000 : ℝ)*(major1) + (1280008879006571/25000000000000 : ℝ)*(major2) + (1562719663/4000000000000 : ℝ)*(sp1) + (5108290111/12500000000000 : ℝ)*(sp2) + (6798534215605339/100000000000000 : ℝ)*(sp4) + (849811690125641/12500000000000 : ℝ)*(sp5) + (424905724994259/6250000000000 : ℝ)*(sp6) + (1720768259093649/50000000000000 : ℝ)*(sp7) + (1720768259093649/50000000000000 : ℝ)*(f.failure) + (6798534215605339/100000000000000 : ℝ)*(f.sum) + (236896196651/515000000000000000000000000 : ℝ)*base65 + (457063237556586851/25750000000000000000000000000000 : ℝ)*base67 + (328907330844586851/25750000000000000000000000000000 : ℝ)*base69 + (504687468942086851/25750000000000000000000000000000 : ℝ)*base71 + (1600018443361/515000000000000000000000000 : ℝ)*base73 + (168937955422836851/25750000000000000000000000000000 : ℝ)*base75 + (97944564840086851/25750000000000000000000000000000 : ℝ)*base77 + (380306738469586851/25750000000000000000000000000000 : ℝ)*base79 + (1506348718483/257500000000000000000000000 : ℝ)*base81 + (1544641/5000000000000000000000 : ℝ)*base90 + (1544641/5000000000000000000000 : ℝ)*base92 + (1544641/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1106_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14851/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (421/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2221/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1106_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1106_s5_0 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-273003487/1250000000 : ℝ)*x 0 + (5395879411/10000000000 : ℝ)*x 1 + (263153291/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273003487/1250000000 : ℝ)^8299 ≤ (6633625390571/50000000000000 : ℝ)^6251 := by
    have hnat : (273003487 : ℕ)^8299*50000000000000^6251 ≤ 6633625390571^6251*1250000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273003487 1250000000 6633625390571 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395879411/10000000000 : ℝ)^8299 ≤ (11020935043489/25000000000000 : ℝ)^6251 := by
    have hnat : (5395879411 : ℕ)^8299*25000000000000^6251 ≤ 11020935043489^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395879411 10000000000 11020935043489 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263153291/500000000 : ℝ)^8299 ≤ (21324504513349/50000000000000 : ℝ)^6251 := by
    have hnat : (263153291 : ℕ)^8299*50000000000000^6251 ≤ 21324504513349^6251*500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263153291 500000000 21324504513349 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-273003487/1250000000 : ℝ), (5395879411/10000000000 : ℝ), (263153291/500000000 : ℝ)] ![(6633625390571/50000000000000 : ℝ), (11020935043489/25000000000000 : ℝ), (21324504513349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-273003487/1250000000 : ℝ)|^8299 ≤ (6633625390571/50000000000000 : ℝ)^6251
        have hw : |(-273003487/1250000000 : ℝ)|=(273003487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395879411/10000000000 : ℝ)|^8299 ≤ (11020935043489/25000000000000 : ℝ)^6251
        have hw : |(5395879411/10000000000 : ℝ)|=(5395879411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263153291/500000000 : ℝ)|^8299 ≤ (21324504513349/50000000000000 : ℝ)^6251
        have hw : |(263153291/500000000 : ℝ)|=(263153291/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s5_1 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672715179/5000000000 : ℝ)*x 0 + (-2251435171/10000000000 : ℝ)*x 1 + (2631532753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672715179/5000000000 : ℝ)^8299 ≤ (43537380782991/100000000000000 : ℝ)^6251 := by
    have hnat : (2672715179 : ℕ)^8299*100000000000000^6251 ≤ 43537380782991^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672715179 5000000000 43537380782991 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251435171/10000000000 : ℝ)^8299 ≤ (17267016931/125000000000 : ℝ)^6251 := by
    have hnat : (2251435171 : ℕ)^8299*125000000000^6251 ≤ 17267016931^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251435171 10000000000 17267016931 125000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631532753/5000000000 : ℝ)^8299 ≤ (4264900564857/10000000000000 : ℝ)^6251 := by
    have hnat : (2631532753 : ℕ)^8299*10000000000000^6251 ≤ 4264900564857^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631532753 5000000000 4264900564857 10000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672715179/5000000000 : ℝ), (-2251435171/10000000000 : ℝ), (2631532753/5000000000 : ℝ)] ![(43537380782991/100000000000000 : ℝ), (17267016931/125000000000 : ℝ), (4264900564857/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672715179/5000000000 : ℝ)|^8299 ≤ (43537380782991/100000000000000 : ℝ)^6251
        have hw : |(2672715179/5000000000 : ℝ)|=(2672715179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2251435171/10000000000 : ℝ)|^8299 ≤ (17267016931/125000000000 : ℝ)^6251
        have hw : |(-2251435171/10000000000 : ℝ)|=(2251435171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631532753/5000000000 : ℝ)|^8299 ≤ (4264900564857/10000000000000 : ℝ)^6251
        have hw : |(2631532753/5000000000 : ℝ)|=(2631532753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s5_2 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672715013/5000000000 : ℝ)*x 0 + (5263065639/10000000000 : ℝ)*x 1 + (-1125717719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672715013/5000000000 : ℝ)^8299 ≤ (8707475438599/20000000000000 : ℝ)^6251 := by
    have hnat : (2672715013 : ℕ)^8299*20000000000000^6251 ≤ 8707475438599^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672715013 5000000000 8707475438599 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263065639/10000000000 : ℝ)^8299 ≤ (42649007079433/100000000000000 : ℝ)^6251 := by
    have hnat : (5263065639 : ℕ)^8299*100000000000000^6251 ≤ 42649007079433^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263065639 10000000000 42649007079433 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125717719/5000000000 : ℝ)^8299 ≤ (10791887281/78125000000 : ℝ)^6251 := by
    have hnat : (1125717719 : ℕ)^8299*78125000000^6251 ≤ 10791887281^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125717719 5000000000 10791887281 78125000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672715013/5000000000 : ℝ), (5263065639/10000000000 : ℝ), (-1125717719/5000000000 : ℝ)] ![(8707475438599/20000000000000 : ℝ), (42649007079433/100000000000000 : ℝ), (10791887281/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672715013/5000000000 : ℝ)|^8299 ≤ (8707475438599/20000000000000 : ℝ)^6251
        have hw : |(2672715013/5000000000 : ℝ)|=(2672715013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263065639/10000000000 : ℝ)|^8299 ≤ (42649007079433/100000000000000 : ℝ)^6251
        have hw : |(5263065639/10000000000 : ℝ)|=(5263065639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1125717719/5000000000 : ℝ)|^8299 ≤ (10791887281/78125000000 : ℝ)^6251
        have hw : |(-1125717719/5000000000 : ℝ)|=(1125717719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s5_3 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4369658763/10000000000 : ℝ)*x 0 + (424045227/1000000000 : ℝ)*x 1 + (1125704401/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369658763/10000000000 : ℝ)^8299 ≤ (16657822107209/50000000000000 : ℝ)^6251 := by
    have hnat : (4369658763 : ℕ)^8299*50000000000000^6251 ≤ 16657822107209^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369658763 10000000000 16657822107209 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424045227/1000000000 : ℝ)^8299 ≤ (32014161634773/100000000000000 : ℝ)^6251 := by
    have hnat : (424045227 : ℕ)^8299*100000000000000^6251 ≤ 32014161634773^6251*1000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424045227 1000000000 32014161634773 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125704401/2500000000 : ℝ)^8299 ≤ (34670194125017/100000000000000 : ℝ)^6251 := by
    have hnat : (1125704401 : ℕ)^8299*100000000000000^6251 ≤ 34670194125017^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125704401 2500000000 34670194125017 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369658763/10000000000 : ℝ), (424045227/1000000000 : ℝ), (1125704401/2500000000 : ℝ)] ![(16657822107209/50000000000000 : ℝ), (32014161634773/100000000000000 : ℝ), (34670194125017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369658763/10000000000 : ℝ)|^8299 ≤ (16657822107209/50000000000000 : ℝ)^6251
        have hw : |(4369658763/10000000000 : ℝ)|=(4369658763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(424045227/1000000000 : ℝ)|^8299 ≤ (32014161634773/100000000000000 : ℝ)^6251
        have hw : |(424045227/1000000000 : ℝ)|=(424045227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125704401/2500000000 : ℝ)|^8299 ≤ (34670194125017/100000000000000 : ℝ)^6251
        have hw : |(1125704401/2500000000 : ℝ)|=(1125704401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s5_4 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2184033289/10000000000 : ℝ)*x 0 + (2631705053/5000000000 : ℝ)*x 1 + (5395533907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184033289/10000000000 : ℝ)^8299 ≤ (13267294275169/100000000000000 : ℝ)^6251 := by
    have hnat : (2184033289 : ℕ)^8299*100000000000000^6251 ≤ 13267294275169^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184033289 10000000000 13267294275169 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631705053/5000000000 : ℝ)^8299 ≤ (42652713021987/100000000000000 : ℝ)^6251 := by
    have hnat : (2631705053 : ℕ)^8299*100000000000000^6251 ≤ 42652713021987^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631705053 5000000000 42652713021987 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395533907/10000000000 : ℝ)^8299 ≤ (4407999267959/10000000000000 : ℝ)^6251 := by
    have hnat : (5395533907 : ℕ)^8299*10000000000000^6251 ≤ 4407999267959^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395533907 10000000000 4407999267959 10000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2184033289/10000000000 : ℝ), (2631705053/5000000000 : ℝ), (5395533907/10000000000 : ℝ)] ![(13267294275169/100000000000000 : ℝ), (42652713021987/100000000000000 : ℝ), (4407999267959/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2184033289/10000000000 : ℝ)|^8299 ≤ (13267294275169/100000000000000 : ℝ)^6251
        have hw : |(-2184033289/10000000000 : ℝ)|=(2184033289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631705053/5000000000 : ℝ)|^8299 ≤ (42652713021987/100000000000000 : ℝ)^6251
        have hw : |(2631705053/5000000000 : ℝ)|=(2631705053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395533907/10000000000 : ℝ)|^8299 ≤ (4407999267959/10000000000000 : ℝ)^6251
        have hw : |(5395533907/10000000000 : ℝ)|=(5395533907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s5_5 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311872787/10000000000 : ℝ)*x 0 + (-529741787/2500000000 : ℝ)*x 1 + (1079106759/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311872787/10000000000 : ℝ)^8299 ≤ (21587444185159/50000000000000 : ℝ)^6251 := by
    have hnat : (5311872787 : ℕ)^8299*50000000000000^6251 ≤ 21587444185159^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311872787 10000000000 21587444185159 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529741787/2500000000 : ℝ)^8299 ≤ (12745120150003/100000000000000 : ℝ)^6251 := by
    have hnat : (529741787 : ℕ)^8299*100000000000000^6251 ≤ 12745120150003^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529741787 2500000000 12745120150003 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079106759/2000000000 : ℝ)^8299 ≤ (55099989331/125000000000 : ℝ)^6251 := by
    have hnat : (1079106759 : ℕ)^8299*125000000000^6251 ≤ 55099989331^6251*2000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079106759 2000000000 55099989331 125000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311872787/10000000000 : ℝ), (-529741787/2500000000 : ℝ), (1079106759/2000000000 : ℝ)] ![(21587444185159/50000000000000 : ℝ), (12745120150003/100000000000000 : ℝ), (55099989331/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311872787/10000000000 : ℝ)|^8299 ≤ (21587444185159/50000000000000 : ℝ)^6251
        have hw : |(5311872787/10000000000 : ℝ)|=(5311872787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-529741787/2500000000 : ℝ)|^8299 ≤ (12745120150003/100000000000000 : ℝ)^6251
        have hw : |(-529741787/2500000000 : ℝ)|=(529741787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079106759/2000000000 : ℝ)|^8299 ≤ (55099989331/125000000000 : ℝ)^6251
        have hw : |(1079106759/2000000000 : ℝ)|=(1079106759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s5_6 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311872711/10000000000 : ℝ)*x 0 + (2697766989/5000000000 : ℝ)*x 1 + (-1059483501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311872711/10000000000 : ℝ)^8299 ≤ (8634977510041/20000000000000 : ℝ)^6251 := by
    have hnat : (5311872711 : ℕ)^8299*20000000000000^6251 ≤ 8634977510041^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311872711 10000000000 8634977510041 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697766989/5000000000 : ℝ)^8299 ≤ (44079993449681/100000000000000 : ℝ)^6251 := by
    have hnat : (2697766989 : ℕ)^8299*100000000000000^6251 ≤ 44079993449681^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697766989 5000000000 44079993449681 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1059483501/5000000000 : ℝ)^8299 ≤ (12745118984137/100000000000000 : ℝ)^6251 := by
    have hnat : (1059483501 : ℕ)^8299*100000000000000^6251 ≤ 12745118984137^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059483501 5000000000 12745118984137 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311872711/10000000000 : ℝ), (2697766989/5000000000 : ℝ), (-1059483501/5000000000 : ℝ)] ![(8634977510041/20000000000000 : ℝ), (44079993449681/100000000000000 : ℝ), (12745118984137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311872711/10000000000 : ℝ)|^8299 ≤ (8634977510041/20000000000000 : ℝ)^6251
        have hw : |(5311872711/10000000000 : ℝ)|=(5311872711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697766989/5000000000 : ℝ)|^8299 ≤ (44079993449681/100000000000000 : ℝ)^6251
        have hw : |(2697766989/5000000000 : ℝ)|=(2697766989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1059483501/5000000000 : ℝ)|^8299 ≤ (12745118984137/100000000000000 : ℝ)^6251
        have hw : |(-1059483501/5000000000 : ℝ)|=(1059483501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s5_7 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1092417377/2500000000 : ℝ)*x 0 + (4502137503/10000000000 : ℝ)*x 1 + (848226999/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092417377/2500000000 : ℝ)^8299 ≤ (8328938244503/25000000000000 : ℝ)^6251 := by
    have hnat : (1092417377 : ℕ)^8299*25000000000000^6251 ≤ 8328938244503^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092417377 2500000000 8328938244503 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502137503/10000000000 : ℝ)^8299 ≤ (8665810526901/25000000000000 : ℝ)^6251 := by
    have hnat : (4502137503 : ℕ)^8299*25000000000000^6251 ≤ 8665810526901^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502137503 10000000000 8665810526901 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848226999/2000000000 : ℝ)^8299 ≤ (32021004901689/100000000000000 : ℝ)^6251 := by
    have hnat : (848226999 : ℕ)^8299*100000000000000^6251 ≤ 32021004901689^6251*2000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848226999 2000000000 32021004901689 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092417377/2500000000 : ℝ), (4502137503/10000000000 : ℝ), (848226999/2000000000 : ℝ)] ![(8328938244503/25000000000000 : ℝ), (8665810526901/25000000000000 : ℝ), (32021004901689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092417377/2500000000 : ℝ)|^8299 ≤ (8328938244503/25000000000000 : ℝ)^6251
        have hw : |(1092417377/2500000000 : ℝ)|=(1092417377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502137503/10000000000 : ℝ)|^8299 ≤ (8665810526901/25000000000000 : ℝ)^6251
        have hw : |(4502137503/10000000000 : ℝ)|=(4502137503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848226999/2000000000 : ℝ)|^8299 ≤ (32021004901689/100000000000000 : ℝ)^6251
        have hw : |(848226999/2000000000 : ℝ)|=(848226999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1106_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2221/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11261/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7037/50000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (2221/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2221/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2221/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2221/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2221/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2221/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2221/20000 : ℝ) ^ (4149/1024 : ℝ) ≤ (424152862178021/3125000000000000000 : ℝ) := by
    have hpowers : (2221/20000 : ℝ)^4149 ≤ (424152862178021/3125000000000000000 : ℝ)^1024 := by
      have hnat : (2221 : ℕ)^4149*3125000000000000000^1024 ≤ 424152862178021^1024*20000^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2221 20000 424152862178021 3125000000000000000 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2221/20000 : ℝ)) (X := (424152862178021/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7119/50000 : ℝ) ^ (4149/1024 : ℝ) ≤ (37151839844000359/100000000000000000000 : ℝ) := by
    have hpowers : (7119/50000 : ℝ)^4149 ≤ (37151839844000359/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7119 : ℕ)^4149*100000000000000000000^1024 ≤ 37151839844000359^1024*50000^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7119 50000 37151839844000359 100000000000000000000 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7119/50000 : ℝ)) (X := (37151839844000359/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562924152862178021/1562500000000000000 : ℝ) ≤ (5000334953491279/5000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (1562924152862178021/1562500000000000000 : ℝ)^1024 ≤ (5000334953491279/5000000000000000 : ℝ)^4149 := by
      have hnat : (1562924152862178021 : ℕ)^1024*5000000000000000^4149 ≤ 5000334953491279^4149*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562924152862178021 1562500000000000000 5000334953491279 5000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000334953491279/5000000000000000 : ℝ)) (X := (1562924152862178021/1562500000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050724731433697031/100000000000000000000 : ℝ) ≤ (10001251680056489/10000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (100050724731433697031/100000000000000000000 : ℝ)^1024 ≤ (10001251680056489/10000000000000000 : ℝ)^4149 := by
      have hnat : (100050724731433697031 : ℕ)^1024*10000000000000000^4149 ≤ 10001251680056489^4149*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050724731433697031 100000000000000000000 10001251680056489 10000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001251680056489/10000000000000000 : ℝ)) (X := (100050724731433697031/100000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037151839844000359/50000000000000000000 : ℝ) ≤ (500091672656521/500000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (50037151839844000359/50000000000000000000 : ℝ)^1024 ≤ (500091672656521/500000000000000 : ℝ)^4149 := by
      have hnat : (50037151839844000359 : ℕ)^1024*500000000000000^4149 ≤ 500091672656521^4149*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037151839844000359 50000000000000000000 500091672656521 500000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500091672656521/500000000000000 : ℝ)) (X := (50037151839844000359/50000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(424152862178021/3125000000000000000 : ℝ) ≤ ((1957448602412771669/1958125000000000000 : ℝ)+2*(581773073931/313300000000000 : ℝ)*(2221/20000 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (1957448602412771669/1958125000000000000 : ℝ)+2*(581773073931/313300000000000 : ℝ)*(2221/20000 : ℝ)=(5000334953491279/5000000000000000 : ℝ) by norm_num, show 1+2*(424152862178021/3125000000000000000 : ℝ)=(1562924152862178021/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37151839844000359/100000000000000000000 : ℝ)+(424152862178021/3125000000000000000 : ℝ) ≤ ((1957448602412771669/1958125000000000000 : ℝ)+(581773073931/313300000000000 : ℝ)*((7119/50000 : ℝ)+(2221/20000 : ℝ)))^(4149/1024 : ℝ) := by
    rw [show (1957448602412771669/1958125000000000000 : ℝ)+(581773073931/313300000000000 : ℝ)*((7119/50000 : ℝ)+(2221/20000 : ℝ))=(10001251680056489/10000000000000000 : ℝ) by norm_num, show 1+(37151839844000359/100000000000000000000 : ℝ)+(424152862178021/3125000000000000000 : ℝ)=(100050724731433697031/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37151839844000359/100000000000000000000 : ℝ) ≤ ((1957448602412771669/1958125000000000000 : ℝ)+2*(581773073931/313300000000000 : ℝ)*(7119/50000 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (1957448602412771669/1958125000000000000 : ℝ)+2*(581773073931/313300000000000 : ℝ)*(7119/50000 : ℝ)=(500091672656521/500000000000000 : ℝ) by norm_num, show 1+2*(37151839844000359/100000000000000000000 : ℝ)=(50037151839844000359/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1957448602412771669/1958125000000000000 : ℝ)*(X 1 0+X 2 0)+(581773073931/313300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (2221/20000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (1957448602412771669/1958125000000000000 : ℝ)) (alpha := (581773073931/313300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1957448602412771669/1958125000000000000 : ℝ)*(X 0 1+X 2 1)+(581773073931/313300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (2221/20000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (1957448602412771669/1958125000000000000 : ℝ)) (alpha := (581773073931/313300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1957448602412771669/1958125000000000000 : ℝ)*(X 0 2+X 1 2)+(581773073931/313300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (2221/20000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (1957448602412771669/1958125000000000000 : ℝ)) (alpha := (581773073931/313300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-273003487/1250000000 : ℝ)*X 0 0+(5395879411/10000000000 : ℝ)*X 0 1+(263153291/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672715179/5000000000 : ℝ)*X 1 0+(-2251435171/10000000000 : ℝ)*X 1 1+(2631532753/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672715013/5000000000 : ℝ)*X 2 0+(5263065639/10000000000 : ℝ)*X 2 1+(-1125717719/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4369658763/10000000000 : ℝ)*X 0 0+(424045227/1000000000 : ℝ)*X 0 1+(1125704401/2500000000 : ℝ)*X 0 2+(4369658763/10000000000 : ℝ)*X 1 0+(424045227/1000000000 : ℝ)*X 1 1+(1125704401/2500000000 : ℝ)*X 1 2+(4369658763/10000000000 : ℝ)*X 2 0+(424045227/1000000000 : ℝ)*X 2 1+(1125704401/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2184033289/10000000000 : ℝ)*X 0 0+(2631705053/5000000000 : ℝ)*X 0 1+(5395533907/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311872787/10000000000 : ℝ)*X 1 0+(-529741787/2500000000 : ℝ)*X 1 1+(1079106759/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311872711/10000000000 : ℝ)*X 2 0+(2697766989/5000000000 : ℝ)*X 2 1+(-1059483501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1092417377/2500000000 : ℝ)*X 0 0+(4502137503/10000000000 : ℝ)*X 0 1+(848226999/2000000000 : ℝ)*X 0 2+(1092417377/2500000000 : ℝ)*X 1 0+(4502137503/10000000000 : ℝ)*X 1 1+(848226999/2000000000 : ℝ)*X 1 2+(1092417377/2500000000 : ℝ)*X 2 0+(4502137503/10000000000 : ℝ)*X 2 1+(848226999/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (142668316137967922445867/15665000000000000000000000000 : ℝ) := by norm_num
    linear_combination (280924237/20000000000000 : ℝ)*(base19) + (323812563/25000000000000 : ℝ)*(base23) + (31556413/25000000000000 : ℝ)*(upper3) + (203118877/100000000000000 : ℝ)*(lower4) + (177202062804369/3125000000000 : ℝ)*(major0) + (177202062804369/3125000000000 : ℝ)*(major1) + (177202062804369/3125000000000 : ℝ)*(major2) + (470586827485581/6250000000000 : ℝ)*(sp0) + (94117633584247/1250000000000 : ℝ)*(sp1) + (752940733757743/10000000000000 : ℝ)*(sp2) + (381150035864557/10000000000000 : ℝ)*(sp3) + (22851591649/100000000000000 : ℝ)*(sp4) + (3458533263/100000000000000 : ℝ)*(sp6) + (19265891187/100000000000000 : ℝ)*(sp7) + (952879906134189/25000000000000 : ℝ)*(f.failure) + (1505882418272189/20000000000000 : ℝ)*(f.sum) + (82389551990537/15665000000000000000000000000 : ℝ)*base66 + (339496840488684487/48953125000000000000000000000000 : ℝ)*base68 + (41460229614153097/12238281250000000000000000000000 : ℝ)*base69 + (247062307521490681/24476562500000000000000000000000 : ℝ)*base72 + (7682538385417/15665000000000000000000000000 : ℝ)*base74 + (415790033359721763/48953125000000000000000000000000 : ℝ)*base75 + (547374115611246987/48953125000000000000000000000000 : ℝ)*base78 + (165382754557846763/48953125000000000000000000000000 : ℝ)*base79 + (172154393673287/15665000000000000000000000000 : ℝ)*base82 + (16137501/2500000000000000000000 : ℝ)*base90 + (16137501/2500000000000000000000 : ℝ)*base92 + (16137501/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (298994287941451460082918303/48953125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (184101469/100000000000000 : ℝ)*(base19) + (387885271/100000000000000 : ℝ)*(base23) + (3416497/6250000000000 : ℝ)*(lower2) + (1623681/1000000000000 : ℝ)*(lower4) + (94904321/100000000000000 : ℝ)*(lower5) + (2850008780294443/50000000000000 : ℝ)*(major0) + (2850008780294443/50000000000000 : ℝ)*(major1) + (2850008780294443/50000000000000 : ℝ)*(major2) + (3460644199/20000000000000 : ℝ)*(sp2) + (437128413/50000000000000 : ℝ)*(sp3) + (3784325807077387/50000000000000 : ℝ)*(sp4) + (1513730286010661/20000000000000 : ℝ)*(sp5) + (7568633923048509/100000000000000 : ℝ)*(sp6) + (3831382429173921/100000000000000 : ℝ)*(sp7) + (1915691651715373/50000000000000 : ℝ)*(f.failure) + (3784325807077387/50000000000000 : ℝ)*(f.sum) + (80679016911717/7832500000000000000000000000 : ℝ)*base66 + (1896148235932852133/97906250000000000000000000000000 : ℝ)*base68 + (659959641703789633/97906250000000000000000000000000 : ℝ)*base70 + (488332513784789633/97906250000000000000000000000000 : ℝ)*base72 + (39422860240771/15665000000000000000000000000 : ℝ)*base73 + (1787450019571945883/97906250000000000000000000000000 : ℝ)*base76 + (222421364585477133/97906250000000000000000000000000 : ℝ)*base78 + (1929424961022820883/97906250000000000000000000000000 : ℝ)*base80 + (24568340932349/15665000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (36556957/5000000000000000000000 : ℝ)*base90 + (36556957/5000000000000000000000 : ℝ)*base92 + (36556957/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1106_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2221/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11261/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1106_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1106_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16613/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1113/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11261/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1106_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1106_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1106_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16613/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1113/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11261/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1106_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

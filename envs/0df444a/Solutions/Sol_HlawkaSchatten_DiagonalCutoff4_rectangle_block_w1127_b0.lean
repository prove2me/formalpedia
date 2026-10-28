-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1127_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:11:51.904525+00:00
-- url     : https://prove2.me/submissions/05afb52f-1c0c-4f6f-bb0f-e66b87eac5f9

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
theorem support_rectangle_w1127_s0_0 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-189656731/1000000000 : ℝ)*x 0 + (3028901807/5000000000 : ℝ)*x 1 + (4778572233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (189656731/1000000000 : ℝ)^65 ≤ (11020537956699/100000000000000 : ℝ)^49 := by
    have hnat : (189656731 : ℕ)^65*100000000000000^49 ≤ 11020537956699^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189656731 1000000000 11020537956699 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3028901807/5000000000 : ℝ)^65 ≤ (51432121141317/100000000000000 : ℝ)^49 := by
    have hnat : (3028901807 : ℕ)^65*100000000000000^49 ≤ 51432121141317^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3028901807 5000000000 51432121141317 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4778572233/10000000000 : ℝ)^65 ≤ (3754734087779/10000000000000 : ℝ)^49 := by
    have hnat : (4778572233 : ℕ)^65*10000000000000^49 ≤ 3754734087779^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4778572233 10000000000 3754734087779 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-189656731/1000000000 : ℝ), (3028901807/5000000000 : ℝ), (4778572233/10000000000 : ℝ)] ![(11020537956699/100000000000000 : ℝ), (51432121141317/100000000000000 : ℝ), (3754734087779/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-189656731/1000000000 : ℝ)|^65 ≤ (11020537956699/100000000000000 : ℝ)^49
        have hw : |(-189656731/1000000000 : ℝ)|=(189656731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3028901807/5000000000 : ℝ)|^65 ≤ (51432121141317/100000000000000 : ℝ)^49
        have hw : |(3028901807/5000000000 : ℝ)|=(3028901807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4778572233/10000000000 : ℝ)|^65 ≤ (3754734087779/10000000000000 : ℝ)^49
        have hw : |(4778572233/10000000000 : ℝ)|=(4778572233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s0_1 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5517638639/10000000000 : ℝ)*x 0 + (-41111357/156250000 : ℝ)*x 1 + (119464307/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5517638639/10000000000 : ℝ)^65 ≤ (45438897593423/100000000000000 : ℝ)^49 := by
    have hnat : (5517638639 : ℕ)^65*100000000000000^49 ≤ 45438897593423^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517638639 10000000000 45438897593423 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41111357/156250000 : ℝ)^65 ≤ (3402752206201/20000000000000 : ℝ)^49 := by
    have hnat : (41111357 : ℕ)^65*20000000000000^49 ≤ 3402752206201^49*156250000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41111357 156250000 3402752206201 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119464307/250000000 : ℝ)^65 ≤ (37547341367677/100000000000000 : ℝ)^49 := by
    have hnat : (119464307 : ℕ)^65*100000000000000^49 ≤ 37547341367677^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119464307 250000000 37547341367677 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5517638639/10000000000 : ℝ), (-41111357/156250000 : ℝ), (119464307/250000000 : ℝ)] ![(45438897593423/100000000000000 : ℝ), (3402752206201/20000000000000 : ℝ), (37547341367677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5517638639/10000000000 : ℝ)|^65 ≤ (45438897593423/100000000000000 : ℝ)^49
        have hw : |(5517638639/10000000000 : ℝ)|=(5517638639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41111357/156250000 : ℝ)|^65 ≤ (3402752206201/20000000000000 : ℝ)^49
        have hw : |(-41111357/156250000 : ℝ)|=(41111357/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(119464307/250000000 : ℝ)|^65 ≤ (37547341367677/100000000000000 : ℝ)^49
        have hw : |(119464307/250000000 : ℝ)|=(119464307/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s0_2 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5517638587/10000000000 : ℝ)*x 0 + (1194643077/2500000000 : ℝ)*x 1 + (-2631126879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5517638587/10000000000 : ℝ)^65 ≤ (22719448512681/50000000000000 : ℝ)^49 := by
    have hnat : (5517638587 : ℕ)^65*50000000000000^49 ≤ 22719448512681^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517638587 10000000000 22719448512681 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1194643077/2500000000 : ℝ)^65 ≤ (1501893666381/4000000000000 : ℝ)^49 := by
    have hnat : (1194643077 : ℕ)^65*4000000000000^49 ≤ 1501893666381^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194643077 2500000000 1501893666381 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631126879/10000000000 : ℝ)^65 ≤ (4253440324229/25000000000000 : ℝ)^49 := by
    have hnat : (2631126879 : ℕ)^65*25000000000000^49 ≤ 4253440324229^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631126879 10000000000 4253440324229 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5517638587/10000000000 : ℝ), (1194643077/2500000000 : ℝ), (-2631126879/10000000000 : ℝ)] ![(22719448512681/50000000000000 : ℝ), (1501893666381/4000000000000 : ℝ), (4253440324229/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5517638587/10000000000 : ℝ)|^65 ≤ (22719448512681/50000000000000 : ℝ)^49
        have hw : |(5517638587/10000000000 : ℝ)|=(5517638587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1194643077/2500000000 : ℝ)|^65 ≤ (1501893666381/4000000000000 : ℝ)^49
        have hw : |(1194643077/2500000000 : ℝ)|=(1194643077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2631126879/10000000000 : ℝ)|^65 ≤ (4253440324229/25000000000000 : ℝ)^49
        have hw : |(-2631126879/10000000000 : ℝ)|=(2631126879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s0_3 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2101103389/5000000000 : ℝ)*x 0 + (3121783567/10000000000 : ℝ)*x 1 + (2829647817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101103389/5000000000 : ℝ)^65 ≤ (1266459369499/4000000000000 : ℝ)^49 := by
    have hnat : (2101103389 : ℕ)^65*4000000000000^49 ≤ 1266459369499^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101103389 5000000000 1266459369499 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3121783567/10000000000 : ℝ)^65 ≤ (21345671605329/100000000000000 : ℝ)^49 := by
    have hnat : (3121783567 : ℕ)^65*100000000000000^49 ≤ 21345671605329^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3121783567 10000000000 21345671605329 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2829647817/5000000000 : ℝ)^65 ≤ (23496422069741/50000000000000 : ℝ)^49 := by
    have hnat : (2829647817 : ℕ)^65*50000000000000^49 ≤ 23496422069741^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829647817 5000000000 23496422069741 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2101103389/5000000000 : ℝ), (3121783567/10000000000 : ℝ), (2829647817/5000000000 : ℝ)] ![(1266459369499/4000000000000 : ℝ), (21345671605329/100000000000000 : ℝ), (23496422069741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2101103389/5000000000 : ℝ)|^65 ≤ (1266459369499/4000000000000 : ℝ)^49
        have hw : |(2101103389/5000000000 : ℝ)|=(2101103389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3121783567/10000000000 : ℝ)|^65 ≤ (21345671605329/100000000000000 : ℝ)^49
        have hw : |(3121783567/10000000000 : ℝ)|=(3121783567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2829647817/5000000000 : ℝ)|^65 ≤ (23496422069741/50000000000000 : ℝ)^49
        have hw : |(2829647817/5000000000 : ℝ)|=(2829647817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s0_4 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1901757131/10000000000 : ℝ)*x 0 + (4811580069/10000000000 : ℝ)*x 1 + (120472729/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1901757131/10000000000 : ℝ)^65 ≤ (2212111977827/20000000000000 : ℝ)^49 := by
    have hnat : (1901757131 : ℕ)^65*20000000000000^49 ≤ 2212111977827^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901757131 10000000000 2212111977827 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4811580069/10000000000 : ℝ)^65 ≤ (18945886680553/50000000000000 : ℝ)^49 := by
    have hnat : (4811580069 : ℕ)^65*50000000000000^49 ≤ 18945886680553^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4811580069 10000000000 18945886680553 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (120472729/200000000 : ℝ)^65 ≤ (51047666734503/100000000000000 : ℝ)^49 := by
    have hnat : (120472729 : ℕ)^65*100000000000000^49 ≤ 51047666734503^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120472729 200000000 51047666734503 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1901757131/10000000000 : ℝ), (4811580069/10000000000 : ℝ), (120472729/200000000 : ℝ)] ![(2212111977827/20000000000000 : ℝ), (18945886680553/50000000000000 : ℝ), (51047666734503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1901757131/10000000000 : ℝ)|^65 ≤ (2212111977827/20000000000000 : ℝ)^49
        have hw : |(-1901757131/10000000000 : ℝ)|=(1901757131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4811580069/10000000000 : ℝ)|^65 ≤ (18945886680553/50000000000000 : ℝ)^49
        have hw : |(4811580069/10000000000 : ℝ)|=(4811580069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(120472729/200000000 : ℝ)|^65 ≤ (51047666734503/100000000000000 : ℝ)^49
        have hw : |(120472729/200000000 : ℝ)|=(120472729/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s0_5 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (64626469/125000000 : ℝ)*x 0 + (-1386062771/10000000000 : ℝ)*x 1 + (3011818189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64626469/125000000 : ℝ)^65 ≤ (8336418827357/20000000000000 : ℝ)^49 := by
    have hnat : (64626469 : ℕ)^65*20000000000000^49 ≤ 8336418827357^49*125000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64626469 125000000 8336418827357 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1386062771/10000000000 : ℝ)^65 ≤ (7270239924677/100000000000000 : ℝ)^49 := by
    have hnat : (1386062771 : ℕ)^65*100000000000000^49 ≤ 7270239924677^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1386062771 10000000000 7270239924677 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3011818189/5000000000 : ℝ)^65 ≤ (51047665925097/100000000000000 : ℝ)^49 := by
    have hnat : (3011818189 : ℕ)^65*100000000000000^49 ≤ 51047665925097^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3011818189 5000000000 51047665925097 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(64626469/125000000 : ℝ), (-1386062771/10000000000 : ℝ), (3011818189/5000000000 : ℝ)] ![(8336418827357/20000000000000 : ℝ), (7270239924677/100000000000000 : ℝ), (51047665925097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(64626469/125000000 : ℝ)|^65 ≤ (8336418827357/20000000000000 : ℝ)^49
        have hw : |(64626469/125000000 : ℝ)|=(64626469/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1386062771/10000000000 : ℝ)|^65 ≤ (7270239924677/100000000000000 : ℝ)^49
        have hw : |(-1386062771/10000000000 : ℝ)|=(1386062771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3011818189/5000000000 : ℝ)|^65 ≤ (51047665925097/100000000000000 : ℝ)^49
        have hw : |(3011818189/5000000000 : ℝ)|=(3011818189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s0_6 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1292529387/2500000000 : ℝ)*x 0 + (376477273/625000000 : ℝ)*x 1 + (-173257843/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292529387/2500000000 : ℝ)^65 ≤ (8336418887247/20000000000000 : ℝ)^49 := by
    have hnat : (1292529387 : ℕ)^65*20000000000000^49 ≤ 8336418887247^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292529387 2500000000 8336418887247 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (376477273/625000000 : ℝ)^65 ≤ (51047665812679/100000000000000 : ℝ)^49 := by
    have hnat : (376477273 : ℕ)^65*100000000000000^49 ≤ 51047665812679^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376477273 625000000 51047665812679 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (173257843/1250000000 : ℝ)^65 ≤ (7270239736811/100000000000000 : ℝ)^49 := by
    have hnat : (173257843 : ℕ)^65*100000000000000^49 ≤ 7270239736811^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173257843 1250000000 7270239736811 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292529387/2500000000 : ℝ), (376477273/625000000 : ℝ), (-173257843/1250000000 : ℝ)] ![(8336418887247/20000000000000 : ℝ), (51047665812679/100000000000000 : ℝ), (7270239736811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292529387/2500000000 : ℝ)|^65 ≤ (8336418887247/20000000000000 : ℝ)^49
        have hw : |(1292529387/2500000000 : ℝ)|=(1292529387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(376477273/625000000 : ℝ)|^65 ≤ (51047665812679/100000000000000 : ℝ)^49
        have hw : |(376477273/625000000 : ℝ)|=(376477273/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-173257843/1250000000 : ℝ)|^65 ≤ (7270239736811/100000000000000 : ℝ)^49
        have hw : |(-173257843/1250000000 : ℝ)|=(173257843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s0_7 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1053125399/2500000000 : ℝ)*x 0 + (5593820509/10000000000 : ℝ)*x 1 + (3189558491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053125399/2500000000 : ℝ)^65 ≤ (31764419310899/100000000000000 : ℝ)^49 := by
    have hnat : (1053125399 : ℕ)^65*100000000000000^49 ≤ 31764419310899^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053125399 2500000000 31764419310899 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5593820509/10000000000 : ℝ)^65 ≤ (9254599591889/20000000000000 : ℝ)^49 := by
    have hnat : (5593820509 : ℕ)^65*20000000000000^49 ≤ 9254599591889^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5593820509 10000000000 9254599591889 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3189558491/10000000000 : ℝ)^65 ≤ (21962582718523/100000000000000 : ℝ)^49 := by
    have hnat : (3189558491 : ℕ)^65*100000000000000^49 ≤ 21962582718523^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3189558491 10000000000 21962582718523 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053125399/2500000000 : ℝ), (5593820509/10000000000 : ℝ), (3189558491/10000000000 : ℝ)] ![(31764419310899/100000000000000 : ℝ), (9254599591889/20000000000000 : ℝ), (21962582718523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053125399/2500000000 : ℝ)|^65 ≤ (31764419310899/100000000000000 : ℝ)^49
        have hw : |(1053125399/2500000000 : ℝ)|=(1053125399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5593820509/10000000000 : ℝ)|^65 ≤ (9254599591889/20000000000000 : ℝ)^49
        have hw : |(5593820509/10000000000 : ℝ)|=(5593820509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3189558491/10000000000 : ℝ)|^65 ≤ (21962582718523/100000000000000 : ℝ)^49
        have hw : |(3189558491/10000000000 : ℝ)|=(3189558491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1127_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37295281/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (11/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27873/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8319/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8319 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8319*1^2048 ≤ 0^2048*1^8319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8319 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8319/2048 : ℝ) ≤ (604648569982807427/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8319 ≤ (604648569982807427/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8319*25000000000000000000^2048 ≤ 604648569982807427^2048*5^8319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 604648569982807427 25000000000000000000 8319 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (604648569982807427/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8319/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8319 := by
      have hnat : (1 : ℕ)^2048*1^8319 ≤ 1^8319*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25604648569982807427/25000000000000000000 : ℝ) ≤ (2011801311585179/2000000000000000 : ℝ) ^ (8319/2048 : ℝ) := by
    have hpowers : (25604648569982807427/25000000000000000000 : ℝ)^2048 ≤ (2011801311585179/2000000000000000 : ℝ)^8319 := by
      have hnat : (25604648569982807427 : ℕ)^2048*2000000000000000^8319 ≤ 2011801311585179^8319*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25604648569982807427 25000000000000000000 2011801311585179 2000000000000000 2048 8319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2011801311585179/2000000000000000 : ℝ)) (X := (25604648569982807427/25000000000000000000 : ℝ)) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (13104648569982807427/12500000000000000000 : ℝ) ≤ (1011801311585179/1000000000000000 : ℝ) ^ (8319/2048 : ℝ) := by
    have hpowers : (13104648569982807427/12500000000000000000 : ℝ)^2048 ≤ (1011801311585179/1000000000000000 : ℝ)^8319 := by
      have hnat : (13104648569982807427 : ℕ)^2048*1000000000000000^8319 ≤ 1011801311585179^8319*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13104648569982807427 12500000000000000000 1011801311585179 1000000000000000 2048 8319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1011801311585179/1000000000000000 : ℝ)) (X := (13104648569982807427/12500000000000000000 : ℝ)) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11801311585179/800000000000000 : ℝ)*(0 : ℝ))^(8319/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(11801311585179/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(604648569982807427/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11801311585179/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8319/2048 : ℝ) := by
    rw [show (1 : ℝ)+(11801311585179/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2011801311585179/2000000000000000 : ℝ) by norm_num, show 1+(604648569982807427/25000000000000000000 : ℝ)+(0 : ℝ)=(25604648569982807427/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(604648569982807427/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11801311585179/800000000000000 : ℝ)*(2/5 : ℝ))^(8319/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(11801311585179/800000000000000 : ℝ)*(2/5 : ℝ)=(1011801311585179/1000000000000000 : ℝ) by norm_num, show 1+2*(604648569982807427/25000000000000000000 : ℝ)=(13104648569982807427/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11801311585179/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8319/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11801311585179/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11801311585179/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8319/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11801311585179/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11801311585179/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8319/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11801311585179/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-189656731/1000000000 : ℝ)*X 0 0+(3028901807/5000000000 : ℝ)*X 0 1+(4778572233/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5517638639/10000000000 : ℝ)*X 1 0+(-41111357/156250000 : ℝ)*X 1 1+(119464307/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5517638587/10000000000 : ℝ)*X 2 0+(1194643077/2500000000 : ℝ)*X 2 1+(-2631126879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2101103389/5000000000 : ℝ)*X 0 0+(3121783567/10000000000 : ℝ)*X 0 1+(2829647817/5000000000 : ℝ)*X 0 2+(2101103389/5000000000 : ℝ)*X 1 0+(3121783567/10000000000 : ℝ)*X 1 1+(2829647817/5000000000 : ℝ)*X 1 2+(2101103389/5000000000 : ℝ)*X 2 0+(3121783567/10000000000 : ℝ)*X 2 1+(2829647817/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1901757131/10000000000 : ℝ)*X 0 0+(4811580069/10000000000 : ℝ)*X 0 1+(120472729/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((64626469/125000000 : ℝ)*X 1 0+(-1386062771/10000000000 : ℝ)*X 1 1+(3011818189/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1292529387/2500000000 : ℝ)*X 2 0+(376477273/625000000 : ℝ)*X 2 1+(-173257843/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1053125399/2500000000 : ℝ)*X 0 0+(5593820509/10000000000 : ℝ)*X 0 1+(3189558491/10000000000 : ℝ)*X 0 2+(1053125399/2500000000 : ℝ)*X 1 0+(5593820509/10000000000 : ℝ)*X 1 1+(3189558491/10000000000 : ℝ)*X 1 2+(1053125399/2500000000 : ℝ)*X 2 0+(5593820509/10000000000 : ℝ)*X 2 1+(3189558491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7491294668247441613209/4000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19641967/100000000000000 : ℝ)*(base1) + (240356169/50000000000000 : ℝ)*(base19) + (88527309/20000000000000 : ℝ)*(base23) + (30708597/100000000000000 : ℝ)*(base24) + (7024671/6250000000000 : ℝ)*(upper3) + (293952582142857/50000000000000 : ℝ)*(major0) + (293952582142857/50000000000000 : ℝ)*(major1) + (293952582142857/50000000000000 : ℝ)*(major2) + (156344209318401/20000000000000 : ℝ)*(sp0) + (781721613602521/100000000000000 : ℝ)*(sp1) + (390860810484859/50000000000000 : ℝ)*(sp2) + (98521824819687/25000000000000 : ℝ)*(sp3) + (533682411/50000000000000 : ℝ)*(sp4) + (852908393/100000000000000 : ℝ)*(sp7) + (98522042957277/25000000000000 : ℝ)*(f.failure) + (39086104715743/5000000000000 : ℝ)*(f.sum) + (38125636883597/20000000000000000000000000000 : ℝ)*base66 + (127240895723597/40000000000000000000000000000 : ℝ)*base68 + (158587108483597/40000000000000000000000000000 : ℝ)*base70 + (21204978276403/40000000000000000000000000000 : ℝ)*base71 + (70384344983597/20000000000000000000000000000 : ℝ)*base74 + (5345461083597/40000000000000000000000000000 : ℝ)*base76 + (240311003603597/40000000000000000000000000000 : ℝ)*base78 + (222518109963597/40000000000000000000000000000 : ℝ)*base80 + (55425719543597/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4209837/625000000000000000000 : ℝ)*base89 + (4209837/625000000000000000000 : ℝ)*base91 + (4209837/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (299212242334595207313027/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (88963569/100000000000000 : ℝ)*(base1) + (921571941/50000000000000 : ℝ)*(base19) + (1847048473/100000000000000 : ℝ)*(base23) + (12762551/6250000000000 : ℝ)*(upper3) + (213507723/100000000000000 : ℝ)*(upper5) + (620486230682771/100000000000000 : ℝ)*(major0) + (620486230682771/100000000000000 : ℝ)*(major1) + (620486230682771/100000000000000 : ℝ)*(major2) + (3768251571/100000000000000 : ℝ)*(sp1) + (3759867379/100000000000000 : ℝ)*(sp2) + (825044190212809/100000000000000 : ℝ)*(sp4) + (825038489853787/100000000000000 : ℝ)*(sp5) + (825038494333387/100000000000000 : ℝ)*(sp6) + (51991002726149/12500000000000 : ℝ)*(sp7) + (207964055386381/50000000000000 : ℝ)*(f.failure) + (20626102531231/2500000000000 : ℝ)*(f.sum) + (67530316131009/40000000000000000000000000000 : ℝ)*base65 + (176880309668991/80000000000000000000000000000 : ℝ)*base68 + (91081491508991/80000000000000000000000000000 : ℝ)*base70 + (176028149028991/80000000000000000000000000000 : ℝ)*base72 + (89938424531009/40000000000000000000000000000 : ℝ)*base73 + (648843676788991/80000000000000000000000000000 : ℝ)*base76 + (98814424228991/80000000000000000000000000000 : ℝ)*base78 + (284011264171009/80000000000000000000000000000 : ℝ)*base79 + (18191913868991/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5468061/1250000000000000000000 : ℝ)*base89 + (5468061/1250000000000000000000 : ℝ)*base91 + (5468061/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1127_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37295281/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27873/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1127_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1127_s1_0 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2102311177/10000000000 : ℝ)*x 0 + (2852770477/5000000000 : ℝ)*x 1 + (62488899/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102311177/10000000000 : ℝ)^65 ≤ (6316941283061/50000000000000 : ℝ)^49 := by
    have hnat : (2102311177 : ℕ)^65*50000000000000^49 ≤ 6316941283061^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102311177 10000000000 6316941283061 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2852770477/5000000000 : ℝ)^65 ≤ (11875729297227/25000000000000 : ℝ)^49 := by
    have hnat : (2852770477 : ℕ)^65*25000000000000^49 ≤ 11875729297227^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2852770477 5000000000 11875729297227 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62488899/125000000 : ℝ)^65 ≤ (996580005631/2500000000000 : ℝ)^49 := by
    have hnat : (62488899 : ℕ)^65*2500000000000^49 ≤ 996580005631^49*125000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62488899 125000000 996580005631 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2102311177/10000000000 : ℝ), (2852770477/5000000000 : ℝ), (62488899/125000000 : ℝ)] ![(6316941283061/50000000000000 : ℝ), (11875729297227/25000000000000 : ℝ), (996580005631/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2102311177/10000000000 : ℝ)|^65 ≤ (6316941283061/50000000000000 : ℝ)^49
        have hw : |(-2102311177/10000000000 : ℝ)|=(2102311177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2852770477/5000000000 : ℝ)|^65 ≤ (11875729297227/25000000000000 : ℝ)^49
        have hw : |(2852770477/5000000000 : ℝ)|=(2852770477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(62488899/125000000 : ℝ)|^65 ≤ (996580005631/2500000000000 : ℝ)^49
        have hw : |(62488899/125000000 : ℝ)|=(62488899/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s1_1 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2709974589/5000000000 : ℝ)*x 0 + (-310479019/1250000000 : ℝ)*x 1 + (4999111557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2709974589/5000000000 : ℝ)^65 ≤ (22187405109873/50000000000000 : ℝ)^49 := by
    have hnat : (2709974589 : ℕ)^65*50000000000000^49 ≤ 22187405109873^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709974589 5000000000 22187405109873 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (310479019/1250000000 : ℝ)^65 ≤ (15761993376933/100000000000000 : ℝ)^49 := by
    have hnat : (310479019 : ℕ)^65*100000000000000^49 ≤ 15761993376933^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310479019 1250000000 15761993376933 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4999111557/10000000000 : ℝ)^65 ≤ (2491449774093/6250000000000 : ℝ)^49 := by
    have hnat : (4999111557 : ℕ)^65*6250000000000^49 ≤ 2491449774093^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999111557 10000000000 2491449774093 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2709974589/5000000000 : ℝ), (-310479019/1250000000 : ℝ), (4999111557/10000000000 : ℝ)] ![(22187405109873/50000000000000 : ℝ), (15761993376933/100000000000000 : ℝ), (2491449774093/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2709974589/5000000000 : ℝ)|^65 ≤ (22187405109873/50000000000000 : ℝ)^49
        have hw : |(2709974589/5000000000 : ℝ)|=(2709974589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-310479019/1250000000 : ℝ)|^65 ≤ (15761993376933/100000000000000 : ℝ)^49
        have hw : |(-310479019/1250000000 : ℝ)|=(310479019/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4999111557/10000000000 : ℝ)|^65 ≤ (2491449774093/6250000000000 : ℝ)^49
        have hw : |(4999111557/10000000000 : ℝ)|=(4999111557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s1_2 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5419950833/10000000000 : ℝ)*x 0 + (249955503/500000000 : ℝ)*x 1 + (-2483831899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5419950833/10000000000 : ℝ)^65 ≤ (44374828194237/100000000000000 : ℝ)^49 := by
    have hnat : (5419950833 : ℕ)^65*100000000000000^49 ≤ 44374828194237^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419950833 10000000000 44374828194237 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (249955503/500000000 : ℝ)^65 ≤ (19931590275239/50000000000000 : ℝ)^49 := by
    have hnat : (249955503 : ℕ)^65*50000000000000^49 ≤ 19931590275239^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249955503 500000000 19931590275239 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2483831899/10000000000 : ℝ)^65 ≤ (1970248905899/12500000000000 : ℝ)^49 := by
    have hnat : (2483831899 : ℕ)^65*12500000000000^49 ≤ 1970248905899^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2483831899 10000000000 1970248905899 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5419950833/10000000000 : ℝ), (249955503/500000000 : ℝ), (-2483831899/10000000000 : ℝ)] ![(44374828194237/100000000000000 : ℝ), (19931590275239/50000000000000 : ℝ), (1970248905899/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5419950833/10000000000 : ℝ)|^65 ≤ (44374828194237/100000000000000 : ℝ)^49
        have hw : |(5419950833/10000000000 : ℝ)|=(5419950833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(249955503/500000000 : ℝ)|^65 ≤ (19931590275239/50000000000000 : ℝ)^49
        have hw : |(249955503/500000000 : ℝ)|=(249955503/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2483831899/10000000000 : ℝ)|^65 ≤ (1970248905899/12500000000000 : ℝ)^49
        have hw : |(-2483831899/10000000000 : ℝ)|=(2483831899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s1_3 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1079676287/2500000000 : ℝ)*x 0 + (734841367/2000000000 : ℝ)*x 1 + (5075493371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079676287/2500000000 : ℝ)^65 ≤ (32831091933257/100000000000000 : ℝ)^49 := by
    have hnat : (1079676287 : ℕ)^65*100000000000000^49 ≤ 32831091933257^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079676287 2500000000 32831091933257 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (734841367/2000000000 : ℝ)^65 ≤ (26495749250211/100000000000000 : ℝ)^49 := by
    have hnat : (734841367 : ℕ)^65*100000000000000^49 ≤ 26495749250211^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      734841367 2000000000 26495749250211 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5075493371/10000000000 : ℝ)^65 ≤ (4067315880667/10000000000000 : ℝ)^49 := by
    have hnat : (5075493371 : ℕ)^65*10000000000000^49 ≤ 4067315880667^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075493371 10000000000 4067315880667 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079676287/2500000000 : ℝ), (734841367/2000000000 : ℝ), (5075493371/10000000000 : ℝ)] ![(32831091933257/100000000000000 : ℝ), (26495749250211/100000000000000 : ℝ), (4067315880667/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079676287/2500000000 : ℝ)|^65 ≤ (32831091933257/100000000000000 : ℝ)^49
        have hw : |(1079676287/2500000000 : ℝ)|=(1079676287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(734841367/2000000000 : ℝ)|^65 ≤ (26495749250211/100000000000000 : ℝ)^49
        have hw : |(734841367/2000000000 : ℝ)|=(734841367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5075493371/10000000000 : ℝ)|^65 ≤ (4067315880667/10000000000000 : ℝ)^49
        have hw : |(5075493371/10000000000 : ℝ)|=(5075493371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s1_4 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2103138643/10000000000 : ℝ)*x 0 + (2504406527/5000000000 : ℝ)*x 1 + (2847823283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103138643/10000000000 : ℝ)^65 ≤ (252809587887/2000000000000 : ℝ)^49 := by
    have hnat : (2103138643 : ℕ)^65*2000000000000^49 ≤ 252809587887^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103138643 10000000000 252809587887 2000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2504406527/5000000000 : ℝ)^65 ≤ (19982924834013/50000000000000 : ℝ)^49 := by
    have hnat : (2504406527 : ℕ)^65*50000000000000^49 ≤ 19982924834013^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2504406527 5000000000 19982924834013 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2847823283/5000000000 : ℝ)^65 ≤ (9478734182661/20000000000000 : ℝ)^49 := by
    have hnat : (2847823283 : ℕ)^65*20000000000000^49 ≤ 9478734182661^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2847823283 5000000000 9478734182661 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2103138643/10000000000 : ℝ), (2504406527/5000000000 : ℝ), (2847823283/5000000000 : ℝ)] ![(252809587887/2000000000000 : ℝ), (19982924834013/50000000000000 : ℝ), (9478734182661/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2103138643/10000000000 : ℝ)|^65 ≤ (252809587887/2000000000000 : ℝ)^49
        have hw : |(-2103138643/10000000000 : ℝ)|=(2103138643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2504406527/5000000000 : ℝ)|^65 ≤ (19982924834013/50000000000000 : ℝ)^49
        have hw : |(2504406527/5000000000 : ℝ)|=(2504406527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2847823283/5000000000 : ℝ)|^65 ≤ (9478734182661/20000000000000 : ℝ)^49
        have hw : |(2847823283/5000000000 : ℝ)|=(2847823283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s1_5 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (130974249/250000000 : ℝ)*x 0 + (-223412097/1250000000 : ℝ)*x 1 + (1423911579/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130974249/250000000 : ℝ)^65 ≤ (5302505354773/12500000000000 : ℝ)^49 := by
    have hnat : (130974249 : ℕ)^65*12500000000000^49 ≤ 5302505354773^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130974249 250000000 5302505354773 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223412097/1250000000 : ℝ)^65 ≤ (2037257799239/20000000000000 : ℝ)^49 := by
    have hnat : (223412097 : ℕ)^65*20000000000000^49 ≤ 2037257799239^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223412097 1250000000 2037257799239 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1423911579/2500000000 : ℝ)^65 ≤ (23696834076889/50000000000000 : ℝ)^49 := by
    have hnat : (1423911579 : ℕ)^65*50000000000000^49 ≤ 23696834076889^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1423911579 2500000000 23696834076889 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(130974249/250000000 : ℝ), (-223412097/1250000000 : ℝ), (1423911579/2500000000 : ℝ)] ![(5302505354773/12500000000000 : ℝ), (2037257799239/20000000000000 : ℝ), (23696834076889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(130974249/250000000 : ℝ)|^65 ≤ (5302505354773/12500000000000 : ℝ)^49
        have hw : |(130974249/250000000 : ℝ)|=(130974249/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-223412097/1250000000 : ℝ)|^65 ≤ (2037257799239/20000000000000 : ℝ)^49
        have hw : |(-223412097/1250000000 : ℝ)|=(223412097/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1423911579/2500000000 : ℝ)|^65 ≤ (23696834076889/50000000000000 : ℝ)^49
        have hw : |(1423911579/2500000000 : ℝ)|=(1423911579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s1_6 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5238970001/10000000000 : ℝ)*x 0 + (5695646483/10000000000 : ℝ)*x 1 + (-893648237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5238970001/10000000000 : ℝ)^65 ≤ (42420043278563/100000000000000 : ℝ)^49 := by
    have hnat : (5238970001 : ℕ)^65*100000000000000^49 ≤ 42420043278563^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238970001 10000000000 42420043278563 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5695646483/10000000000 : ℝ)^65 ≤ (23696834998571/50000000000000 : ℝ)^49 := by
    have hnat : (5695646483 : ℕ)^65*50000000000000^49 ≤ 23696834998571^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5695646483 10000000000 23696834998571 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (893648237/5000000000 : ℝ)^65 ≤ (10186286712997/100000000000000 : ℝ)^49 := by
    have hnat : (893648237 : ℕ)^65*100000000000000^49 ≤ 10186286712997^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893648237 5000000000 10186286712997 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5238970001/10000000000 : ℝ), (5695646483/10000000000 : ℝ), (-893648237/5000000000 : ℝ)] ![(42420043278563/100000000000000 : ℝ), (23696834998571/50000000000000 : ℝ), (10186286712997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5238970001/10000000000 : ℝ)|^65 ≤ (42420043278563/100000000000000 : ℝ)^49
        have hw : |(5238970001/10000000000 : ℝ)|=(5238970001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5695646483/10000000000 : ℝ)|^65 ≤ (23696834998571/50000000000000 : ℝ)^49
        have hw : |(5695646483/10000000000 : ℝ)|=(5695646483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-893648237/5000000000 : ℝ)|^65 ≤ (10186286712997/100000000000000 : ℝ)^49
        have hw : |(-893648237/5000000000 : ℝ)|=(893648237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s1_7 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (540042973/1250000000 : ℝ)*x 0 + (5056250809/10000000000 : ℝ)*x 1 + (3693832507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540042973/1250000000 : ℝ)^65 ≤ (32847617579113/100000000000000 : ℝ)^49 := by
    have hnat : (540042973 : ℕ)^65*100000000000000^49 ≤ 32847617579113^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540042973 1250000000 32847617579113 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5056250809/10000000000 : ℝ)^65 ≤ (20234365333771/50000000000000 : ℝ)^49 := by
    have hnat : (5056250809 : ℕ)^65*50000000000000^49 ≤ 20234365333771^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5056250809 10000000000 20234365333771 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3693832507/10000000000 : ℝ)^65 ≤ (1067346069651/4000000000000 : ℝ)^49 := by
    have hnat : (3693832507 : ℕ)^65*4000000000000^49 ≤ 1067346069651^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3693832507 10000000000 1067346069651 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540042973/1250000000 : ℝ), (5056250809/10000000000 : ℝ), (3693832507/10000000000 : ℝ)] ![(32847617579113/100000000000000 : ℝ), (20234365333771/50000000000000 : ℝ), (1067346069651/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540042973/1250000000 : ℝ)|^65 ≤ (32847617579113/100000000000000 : ℝ)^49
        have hw : |(540042973/1250000000 : ℝ)|=(540042973/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5056250809/10000000000 : ℝ)|^65 ≤ (20234365333771/50000000000000 : ℝ)^49
        have hw : |(5056250809/10000000000 : ℝ)|=(5056250809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3693832507/10000000000 : ℝ)|^65 ≤ (1067346069651/4000000000000 : ℝ)^49
        have hw : |(3693832507/10000000000 : ℝ)|=(3693832507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1127_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37295281/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27873/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (1113/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10253/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27873/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27873/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27873/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27873/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27873/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27873/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11/3125 : ℝ) ^ (8319/2048 : ℝ) ≤ (1351878187/12500000000000000000 : ℝ) := by
    have hpowers : (11/3125 : ℝ)^8319 ≤ (1351878187/12500000000000000000 : ℝ)^2048 := by
      have hnat : (11 : ℕ)^8319*12500000000000000000^2048 ≤ 1351878187^2048*3125^8319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11 3125 1351878187 12500000000000000000 8319 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11/3125 : ℝ)) (X := (1351878187/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27873/100000 : ℝ) ^ (8319/2048 : ℝ) ≤ (139402241314274151/25000000000000000000 : ℝ) := by
    have hpowers : (27873/100000 : ℝ)^8319 ≤ (139402241314274151/25000000000000000000 : ℝ)^2048 := by
      have hnat : (27873 : ℕ)^8319*25000000000000000000^2048 ≤ 139402241314274151^2048*100000^8319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27873 100000 139402241314274151 25000000000000000000 8319 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27873/100000 : ℝ)) (X := (139402241314274151/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250000001351878187/6250000000000000000 : ℝ) ≤ (10000000000532497/10000000000000000 : ℝ) ^ (8319/2048 : ℝ) := by
    have hpowers : (6250000001351878187/6250000000000000000 : ℝ)^2048 ≤ (10000000000532497/10000000000000000 : ℝ)^8319 := by
      have hnat : (6250000001351878187 : ℕ)^2048*10000000000000000^8319 ≤ 10000000000532497^8319*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250000001351878187 6250000000000000000 10000000000532497 10000000000000000 2048 8319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000532497/10000000000000000 : ℝ)) (X := (6250000001351878187/6250000000000000000 : ℝ)) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (1005576089760721221/1000000000000000000 : ℝ) ≤ (1251712331560361/1250000000000000 : ℝ) ^ (8319/2048 : ℝ) := by
    have hpowers : (1005576089760721221/1000000000000000000 : ℝ)^2048 ≤ (1251712331560361/1250000000000000 : ℝ)^8319 := by
      have hnat : (1005576089760721221 : ℕ)^2048*1250000000000000^8319 ≤ 1251712331560361^8319*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1005576089760721221 1000000000000000000 1251712331560361 1250000000000000 2048 8319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251712331560361/1250000000000000 : ℝ)) (X := (1005576089760721221/1000000000000000000 : ℝ)) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12639402241314274151/12500000000000000000 : ℝ) ≤ (10027397304433279/10000000000000000 : ℝ) ^ (8319/2048 : ℝ) := by
    have hpowers : (12639402241314274151/12500000000000000000 : ℝ)^2048 ≤ (10027397304433279/10000000000000000 : ℝ)^8319 := by
      have hnat : (12639402241314274151 : ℕ)^2048*10000000000000000^8319 ≤ 10027397304433279^8319*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12639402241314274151 12500000000000000000 10027397304433279 10000000000000000 2048 8319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10027397304433279/10000000000000000 : ℝ)) (X := (12639402241314274151/12500000000000000000 : ℝ)) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1351878187/12500000000000000000 : ℝ) ≤ ((275200356163681774673/275210000000000000000 : ℝ)+2*(13698651950391/2752100000000000 : ℝ)*(11/3125 : ℝ))^(8319/2048 : ℝ) := by
    rw [show (275200356163681774673/275210000000000000000 : ℝ)+2*(13698651950391/2752100000000000 : ℝ)*(11/3125 : ℝ)=(10000000000532497/10000000000000000 : ℝ) by norm_num, show 1+2*(1351878187/12500000000000000000 : ℝ)=(6250000001351878187/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(139402241314274151/25000000000000000000 : ℝ)+(1351878187/12500000000000000000 : ℝ) ≤ ((275200356163681774673/275210000000000000000 : ℝ)+(13698651950391/2752100000000000 : ℝ)*((27873/100000 : ℝ)+(11/3125 : ℝ)))^(8319/2048 : ℝ) := by
    rw [show (275200356163681774673/275210000000000000000 : ℝ)+(13698651950391/2752100000000000 : ℝ)*((27873/100000 : ℝ)+(11/3125 : ℝ))=(1251712331560361/1250000000000000 : ℝ) by norm_num, show 1+(139402241314274151/25000000000000000000 : ℝ)+(1351878187/12500000000000000000 : ℝ)=(1005576089760721221/1000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(139402241314274151/25000000000000000000 : ℝ) ≤ ((275200356163681774673/275210000000000000000 : ℝ)+2*(13698651950391/2752100000000000 : ℝ)*(27873/100000 : ℝ))^(8319/2048 : ℝ) := by
    rw [show (275200356163681774673/275210000000000000000 : ℝ)+2*(13698651950391/2752100000000000 : ℝ)*(27873/100000 : ℝ)=(10027397304433279/10000000000000000 : ℝ) by norm_num, show 1+2*(139402241314274151/25000000000000000000 : ℝ)=(12639402241314274151/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (275200356163681774673/275210000000000000000 : ℝ)*(X 1 0+X 2 0)+(13698651950391/2752100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8319/2048 : ℝ)) (lo := (11/3125 : ℝ)) (hi := (27873/100000 : ℝ)) (c := (275200356163681774673/275210000000000000000 : ℝ)) (alpha := (13698651950391/2752100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (275200356163681774673/275210000000000000000 : ℝ)*(X 0 1+X 2 1)+(13698651950391/2752100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8319/2048 : ℝ)) (lo := (11/3125 : ℝ)) (hi := (27873/100000 : ℝ)) (c := (275200356163681774673/275210000000000000000 : ℝ)) (alpha := (13698651950391/2752100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (275200356163681774673/275210000000000000000 : ℝ)*(X 0 2+X 1 2)+(13698651950391/2752100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8319/2048 : ℝ)) (lo := (11/3125 : ℝ)) (hi := (27873/100000 : ℝ)) (c := (275200356163681774673/275210000000000000000 : ℝ)) (alpha := (13698651950391/2752100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2102311177/10000000000 : ℝ)*X 0 0+(2852770477/5000000000 : ℝ)*X 0 1+(62488899/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2709974589/5000000000 : ℝ)*X 1 0+(-310479019/1250000000 : ℝ)*X 1 1+(4999111557/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5419950833/10000000000 : ℝ)*X 2 0+(249955503/500000000 : ℝ)*X 2 1+(-2483831899/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1079676287/2500000000 : ℝ)*X 0 0+(734841367/2000000000 : ℝ)*X 0 1+(5075493371/10000000000 : ℝ)*X 0 2+(1079676287/2500000000 : ℝ)*X 1 0+(734841367/2000000000 : ℝ)*X 1 1+(5075493371/10000000000 : ℝ)*X 1 2+(1079676287/2500000000 : ℝ)*X 2 0+(734841367/2000000000 : ℝ)*X 2 1+(5075493371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2103138643/10000000000 : ℝ)*X 0 0+(2504406527/5000000000 : ℝ)*X 0 1+(2847823283/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((130974249/250000000 : ℝ)*X 1 0+(-223412097/1250000000 : ℝ)*X 1 1+(1423911579/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5238970001/10000000000 : ℝ)*X 2 0+(5695646483/10000000000 : ℝ)*X 2 1+(-893648237/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((540042973/1250000000 : ℝ)*X 0 0+(5056250809/10000000000 : ℝ)*X 0 1+(3693832507/10000000000 : ℝ)*X 0 2+(540042973/1250000000 : ℝ)*X 1 0+(5056250809/10000000000 : ℝ)*X 1 1+(3693832507/10000000000 : ℝ)*X 1 2+(540042973/1250000000 : ℝ)*X 2 0+(5056250809/10000000000 : ℝ)*X 2 1+(3693832507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4329328528244841912803843751/688025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (191069243/50000000000000 : ℝ)*(base1) + (208113941/20000000000000 : ℝ)*(base19) + (146022779/10000000000000 : ℝ)*(base23) + (12592229/100000000000000 : ℝ)*(base24) + (84743187/50000000000000 : ℝ)*(upper5) + (53230176607057/5000000000000 : ℝ)*(major0) + (53230176607057/5000000000000 : ℝ)*(major1) + (53230176607057/5000000000000 : ℝ)*(major2) + (88473232488613/6250000000000 : ℝ)*(sp0) + (1415574287673647/100000000000000 : ℝ)*(sp1) + (707786927711667/50000000000000 : ℝ)*(sp2) + (713630664737763/100000000000000 : ℝ)*(sp3) + (3990564031/100000000000000 : ℝ)*(sp4) + (119854001/25000000000000 : ℝ)*(sp7) + (356815763146127/50000000000000 : ℝ)*(f.failure) + (1415575328243353/100000000000000 : ℝ)*(f.sum) + (2070789189317/27521000000000000000000000000 : ℝ)*base65 + (378400690091379909/47450000000000000000000000000000 : ℝ)*base67 + (169510456149379909/47450000000000000000000000000000 : ℝ)*base69 + (286745872507829909/47450000000000000000000000000000 : ℝ)*base71 + (61999806380711/27521000000000000000000000000 : ℝ)*base73 + (283736866155529909/47450000000000000000000000000000 : ℝ)*base75 + (187526733600629909/47450000000000000000000000000000 : ℝ)*base77 + (79467088253079909/47450000000000000000000000000000 : ℝ)*base79 + (70120679998113/27521000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (526687/1250000000000000000000 : ℝ)*base89 + (526687/1250000000000000000000 : ℝ)*base91 + (526687/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2361367851143896736092203963/264625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26627409/25000000000000 : ℝ)*(base1) + (1974634953/100000000000000 : ℝ)*(base19) + (250832179/12500000000000 : ℝ)*(base23) + (195246403/100000000000000 : ℝ)*(upper3) + (20164363/10000000000000 : ℝ)*(upper5) + (547486583147501/50000000000000 : ℝ)*(major0) + (547486583147501/50000000000000 : ℝ)*(major1) + (547486583147501/50000000000000 : ℝ)*(major2) + (8005964743/100000000000000 : ℝ)*(sp1) + (344121281/4000000000000 : ℝ)*(sp2) + (36398926428773/2500000000000 : ℝ)*(sp4) + (363986742510397/25000000000000 : ℝ)*(sp5) + (727973170475913/50000000000000 : ℝ)*(sp6) + (733988977990761/100000000000000 : ℝ)*(sp7) + (733989084500397/100000000000000 : ℝ)*(f.failure) + (363989237660321/25000000000000 : ℝ)*(f.sum) + (429354874531/68802500000000000000000000000 : ℝ)*base65 + (223149479986564063/474500000000000000000000000000000 : ℝ)*base68 + (1317926896927564063/474500000000000000000000000000000 : ℝ)*base70 + (1615959782747064063/474500000000000000000000000000000 : ℝ)*base72 + (622852524773657/137605000000000000000000000000 : ℝ)*base73 + (2021650225983064063/474500000000000000000000000000000 : ℝ)*base76 + (202932432863564063/474500000000000000000000000000000 : ℝ)*base78 + (1122110320352435937/474500000000000000000000000000000 : ℝ)*base79 + (36687031945579/68802500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (726557/2500000000000000000000 : ℝ)*base89 + (726557/2500000000000000000000 : ℝ)*base91 + (726557/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1127_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37295281/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27873/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1113/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10253/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1127_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1127_s2_0 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2156355267/10000000000 : ℝ)*x 0 + (2756848271/5000000000 : ℝ)*x 1 + (5156605727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156355267/10000000000 : ℝ)^65 ≤ (13066509847871/100000000000000 : ℝ)^49 := by
    have hnat : (2156355267 : ℕ)^65*100000000000000^49 ≤ 13066509847871^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156355267 10000000000 13066509847871 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2756848271/5000000000 : ℝ)^65 ≤ (11348959536669/25000000000000 : ℝ)^49 := by
    have hnat : (2756848271 : ℕ)^65*25000000000000^49 ≤ 11348959536669^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756848271 5000000000 11348959536669 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5156605727/10000000000 : ℝ)^65 ≤ (41537651994847/100000000000000 : ℝ)^49 := by
    have hnat : (5156605727 : ℕ)^65*100000000000000^49 ≤ 41537651994847^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5156605727 10000000000 41537651994847 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2156355267/10000000000 : ℝ), (2756848271/5000000000 : ℝ), (5156605727/10000000000 : ℝ)] ![(13066509847871/100000000000000 : ℝ), (11348959536669/25000000000000 : ℝ), (41537651994847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2156355267/10000000000 : ℝ)|^65 ≤ (13066509847871/100000000000000 : ℝ)^49
        have hw : |(-2156355267/10000000000 : ℝ)|=(2156355267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2756848271/5000000000 : ℝ)|^65 ≤ (11348959536669/25000000000000 : ℝ)^49
        have hw : |(2756848271/5000000000 : ℝ)|=(2756848271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5156605727/10000000000 : ℝ)|^65 ≤ (41537651994847/100000000000000 : ℝ)^49
        have hw : |(5156605727/10000000000 : ℝ)|=(5156605727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s2_1 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2687257039/5000000000 : ℝ)*x 0 + (-46842341/200000000 : ℝ)*x 1 + (2578303681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687257039/5000000000 : ℝ)^65 ≤ (43882029016083/100000000000000 : ℝ)^49 := by
    have hnat : (2687257039 : ℕ)^65*100000000000000^49 ≤ 43882029016083^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687257039 5000000000 43882029016083 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46842341/200000000 : ℝ)^65 ≤ (2916060298379/20000000000000 : ℝ)^49 := by
    have hnat : (46842341 : ℕ)^65*20000000000000^49 ≤ 2916060298379^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46842341 200000000 2916060298379 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2578303681/5000000000 : ℝ)^65 ≤ (20768834732829/50000000000000 : ℝ)^49 := by
    have hnat : (2578303681 : ℕ)^65*50000000000000^49 ≤ 20768834732829^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2578303681 5000000000 20768834732829 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687257039/5000000000 : ℝ), (-46842341/200000000 : ℝ), (2578303681/5000000000 : ℝ)] ![(43882029016083/100000000000000 : ℝ), (2916060298379/20000000000000 : ℝ), (20768834732829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687257039/5000000000 : ℝ)|^65 ≤ (43882029016083/100000000000000 : ℝ)^49
        have hw : |(2687257039/5000000000 : ℝ)|=(2687257039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-46842341/200000000 : ℝ)|^65 ≤ (2916060298379/20000000000000 : ℝ)^49
        have hw : |(-46842341/200000000 : ℝ)|=(46842341/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2578303681/5000000000 : ℝ)|^65 ≤ (20768834732829/50000000000000 : ℝ)^49
        have hw : |(2578303681/5000000000 : ℝ)|=(2578303681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s2_2 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5374514001/10000000000 : ℝ)*x 0 + (161143981/312500000 : ℝ)*x 1 + (-1171058557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374514001/10000000000 : ℝ)^65 ≤ (5485253522763/12500000000000 : ℝ)^49 := by
    have hnat : (5374514001 : ℕ)^65*12500000000000^49 ≤ 5485253522763^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374514001 10000000000 5485253522763 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161143981/312500000 : ℝ)^65 ≤ (2596104361639/6250000000000 : ℝ)^49 := by
    have hnat : (161143981 : ℕ)^65*6250000000000^49 ≤ 2596104361639^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161143981 312500000 2596104361639 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1171058557/5000000000 : ℝ)^65 ≤ (14580302020407/100000000000000 : ℝ)^49 := by
    have hnat : (1171058557 : ℕ)^65*100000000000000^49 ≤ 14580302020407^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171058557 5000000000 14580302020407 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374514001/10000000000 : ℝ), (161143981/312500000 : ℝ), (-1171058557/5000000000 : ℝ)] ![(5485253522763/12500000000000 : ℝ), (2596104361639/6250000000000 : ℝ), (14580302020407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374514001/10000000000 : ℝ)|^65 ≤ (5485253522763/12500000000000 : ℝ)^49
        have hw : |(5374514001/10000000000 : ℝ)|=(5374514001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161143981/312500000 : ℝ)|^65 ≤ (2596104361639/6250000000000 : ℝ)^49
        have hw : |(161143981/312500000 : ℝ)|=(161143981/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1171058557/5000000000 : ℝ)|^65 ≤ (14580302020407/100000000000000 : ℝ)^49
        have hw : |(-1171058557/5000000000 : ℝ)|=(1171058557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s2_3 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1088935451/2500000000 : ℝ)*x 0 + (2007947751/5000000000 : ℝ)*x 1 + (236211243/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088935451/2500000000 : ℝ)^65 ≤ (8301276363221/25000000000000 : ℝ)^49 := by
    have hnat : (1088935451 : ℕ)^65*25000000000000^49 ≤ 8301276363221^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088935451 2500000000 8301276363221 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2007947751/5000000000 : ℝ)^65 ≤ (7453242260047/25000000000000 : ℝ)^49 := by
    have hnat : (2007947751 : ℕ)^65*25000000000000^49 ≤ 7453242260047^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007947751 5000000000 7453242260047 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (236211243/500000000 : ℝ)^65 ≤ (36981925486987/100000000000000 : ℝ)^49 := by
    have hnat : (236211243 : ℕ)^65*100000000000000^49 ≤ 36981925486987^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236211243 500000000 36981925486987 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088935451/2500000000 : ℝ), (2007947751/5000000000 : ℝ), (236211243/500000000 : ℝ)] ![(8301276363221/25000000000000 : ℝ), (7453242260047/25000000000000 : ℝ), (36981925486987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088935451/2500000000 : ℝ)|^65 ≤ (8301276363221/25000000000000 : ℝ)^49
        have hw : |(1088935451/2500000000 : ℝ)|=(1088935451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2007947751/5000000000 : ℝ)|^65 ≤ (7453242260047/25000000000000 : ℝ)^49
        have hw : |(2007947751/5000000000 : ℝ)|=(2007947751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(236211243/500000000 : ℝ)|^65 ≤ (36981925486987/100000000000000 : ℝ)^49
        have hw : |(236211243/500000000 : ℝ)|=(236211243/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s2_4 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-33694721/156250000 : ℝ)*x 0 + (1289773589/2500000000 : ℝ)*x 1 + (5511182693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33694721/156250000 : ℝ)^65 ≤ (3266842237271/25000000000000 : ℝ)^49 := by
    have hnat : (33694721 : ℕ)^65*25000000000000^49 ≤ 3266842237271^49*156250000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33694721 156250000 3266842237271 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1289773589/2500000000 : ℝ)^65 ≤ (41564246362333/100000000000000 : ℝ)^49 := by
    have hnat : (1289773589 : ℕ)^65*100000000000000^49 ≤ 41564246362333^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1289773589 2500000000 41564246362333 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5511182693/10000000000 : ℝ)^65 ≤ (45368384672549/100000000000000 : ℝ)^49 := by
    have hnat : (5511182693 : ℕ)^65*100000000000000^49 ≤ 45368384672549^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511182693 10000000000 45368384672549 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-33694721/156250000 : ℝ), (1289773589/2500000000 : ℝ), (5511182693/10000000000 : ℝ)] ![(3266842237271/25000000000000 : ℝ), (41564246362333/100000000000000 : ℝ), (45368384672549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-33694721/156250000 : ℝ)|^65 ≤ (3266842237271/25000000000000 : ℝ)^49
        have hw : |(-33694721/156250000 : ℝ)|=(33694721/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1289773589/2500000000 : ℝ)|^65 ≤ (41564246362333/100000000000000 : ℝ)^49
        have hw : |(1289773589/2500000000 : ℝ)|=(1289773589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5511182693/10000000000 : ℝ)|^65 ≤ (45368384672549/100000000000000 : ℝ)^49
        have hw : |(5511182693/10000000000 : ℝ)|=(5511182693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s2_5 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5284001709/10000000000 : ℝ)*x 0 + (-397508001/2000000000 : ℝ)*x 1 + (5511183247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284001709/10000000000 : ℝ)^65 ≤ (4290440382683/10000000000000 : ℝ)^49 := by
    have hnat : (5284001709 : ℕ)^65*10000000000000^49 ≤ 4290440382683^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284001709 10000000000 4290440382683 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397508001/2000000000 : ℝ)^65 ≤ (2345441087331/20000000000000 : ℝ)^49 := by
    have hnat : (397508001 : ℕ)^65*20000000000000^49 ≤ 2345441087331^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397508001 2000000000 2345441087331 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5511183247/10000000000 : ℝ)^65 ≤ (45368390722273/100000000000000 : ℝ)^49 := by
    have hnat : (5511183247 : ℕ)^65*100000000000000^49 ≤ 45368390722273^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511183247 10000000000 45368390722273 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284001709/10000000000 : ℝ), (-397508001/2000000000 : ℝ), (5511183247/10000000000 : ℝ)] ![(4290440382683/10000000000000 : ℝ), (2345441087331/20000000000000 : ℝ), (45368390722273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284001709/10000000000 : ℝ)|^65 ≤ (4290440382683/10000000000000 : ℝ)^49
        have hw : |(5284001709/10000000000 : ℝ)|=(5284001709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-397508001/2000000000 : ℝ)|^65 ≤ (2345441087331/20000000000000 : ℝ)^49
        have hw : |(-397508001/2000000000 : ℝ)|=(397508001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5511183247/10000000000 : ℝ)|^65 ≤ (45368390722273/100000000000000 : ℝ)^49
        have hw : |(5511183247/10000000000 : ℝ)|=(5511183247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s2_6 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1321000117/2500000000 : ℝ)*x 0 + (5511183119/10000000000 : ℝ)*x 1 + (-1987541891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321000117/2500000000 : ℝ)^65 ≤ (21452195230007/50000000000000 : ℝ)^49 := by
    have hnat : (1321000117 : ℕ)^65*50000000000000^49 ≤ 21452195230007^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321000117 2500000000 21452195230007 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5511183119/10000000000 : ℝ)^65 ≤ (22684194662251/50000000000000 : ℝ)^49 := by
    have hnat : (5511183119 : ℕ)^65*50000000000000^49 ≤ 22684194662251^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511183119 10000000000 22684194662251 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1987541891/10000000000 : ℝ)^65 ≤ (458094539/3906250000 : ℝ)^49 := by
    have hnat : (1987541891 : ℕ)^65*3906250000^49 ≤ 458094539^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987541891 10000000000 458094539 3906250000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321000117/2500000000 : ℝ), (5511183119/10000000000 : ℝ), (-1987541891/10000000000 : ℝ)] ![(21452195230007/50000000000000 : ℝ), (22684194662251/50000000000000 : ℝ), (458094539/3906250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321000117/2500000000 : ℝ)|^65 ≤ (21452195230007/50000000000000 : ℝ)^49
        have hw : |(1321000117/2500000000 : ℝ)|=(1321000117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5511183119/10000000000 : ℝ)|^65 ≤ (22684194662251/50000000000000 : ℝ)^49
        have hw : |(5511183119/10000000000 : ℝ)|=(5511183119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1987541891/10000000000 : ℝ)|^65 ≤ (458094539/3906250000 : ℝ)^49
        have hw : |(-1987541891/10000000000 : ℝ)|=(1987541891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s2_7 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1088988331/2500000000 : ℝ)*x 0 + (2359644829/5000000000 : ℝ)*x 1 + (2010440221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088988331/2500000000 : ℝ)^65 ≤ (33207244473121/100000000000000 : ℝ)^49 := by
    have hnat : (1088988331 : ℕ)^65*100000000000000^49 ≤ 33207244473121^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088988331 2500000000 33207244473121 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2359644829/5000000000 : ℝ)^65 ≤ (3693068572863/10000000000000 : ℝ)^49 := by
    have hnat : (2359644829 : ℕ)^65*10000000000000^49 ≤ 3693068572863^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2359644829 5000000000 3693068572863 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2010440221/5000000000 : ℝ)^65 ≤ (3732758722263/12500000000000 : ℝ)^49 := by
    have hnat : (2010440221 : ℕ)^65*12500000000000^49 ≤ 3732758722263^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010440221 5000000000 3732758722263 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088988331/2500000000 : ℝ), (2359644829/5000000000 : ℝ), (2010440221/5000000000 : ℝ)] ![(33207244473121/100000000000000 : ℝ), (3693068572863/10000000000000 : ℝ), (3732758722263/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088988331/2500000000 : ℝ)|^65 ≤ (33207244473121/100000000000000 : ℝ)^49
        have hw : |(1088988331/2500000000 : ℝ)|=(1088988331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2359644829/5000000000 : ℝ)|^65 ≤ (3693068572863/10000000000000 : ℝ)^49
        have hw : |(2359644829/5000000000 : ℝ)|=(2359644829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2010440221/5000000000 : ℝ)|^65 ≤ (3732758722263/12500000000000 : ℝ)^49
        have hw : |(2010440221/5000000000 : ℝ)|=(2010440221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1127_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37295281/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10253/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1113/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (4501/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4137/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10253/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1113/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10253/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1113/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10253/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1113/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10253/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1113/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10253/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1113/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10253/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1113/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1113/20000 : ℝ) ^ (8319/2048 : ℝ) ≤ (400898856869113/50000000000000000000 : ℝ) := by
    have hpowers : (1113/20000 : ℝ)^8319 ≤ (400898856869113/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1113 : ℕ)^8319*50000000000000000000^2048 ≤ 400898856869113^2048*20000^8319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1113 20000 400898856869113 50000000000000000000 8319 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1113/20000 : ℝ)) (X := (400898856869113/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (10253/50000 : ℝ) ^ (8319/2048 : ℝ) ≤ (160270048128363597/100000000000000000000 : ℝ) := by
    have hpowers : (10253/50000 : ℝ)^8319 ≤ (160270048128363597/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10253 : ℕ)^8319*100000000000000000000^2048 ≤ 160270048128363597^2048*50000^8319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10253 50000 160270048128363597 100000000000000000000 8319 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10253/50000 : ℝ)) (X := (160270048128363597/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000400898856869113/25000000000000000000 : ℝ) ≤ (2000007895524909/2000000000000000 : ℝ) ^ (8319/2048 : ℝ) := by
    have hpowers : (25000400898856869113/25000000000000000000 : ℝ)^2048 ≤ (2000007895524909/2000000000000000 : ℝ)^8319 := by
      have hnat : (25000400898856869113 : ℕ)^2048*2000000000000000^8319 ≤ 2000007895524909^8319*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000400898856869113 25000000000000000000 2000007895524909 2000000000000000 2048 8319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000007895524909/2000000000000000 : ℝ)) (X := (25000400898856869113/25000000000000000000 : ℝ)) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100161071845842101823/100000000000000000000 : ℝ) ≤ (10003962916981869/10000000000000000 : ℝ) ^ (8319/2048 : ℝ) := by
    have hpowers : (100161071845842101823/100000000000000000000 : ℝ)^2048 ≤ (10003962916981869/10000000000000000 : ℝ)^8319 := by
      have hnat : (100161071845842101823 : ℕ)^2048*10000000000000000^8319 ≤ 10003962916981869^8319*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100161071845842101823 100000000000000000000 10003962916981869 10000000000000000 2048 8319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003962916981869/10000000000000000 : ℝ)) (X := (100161071845842101823/100000000000000000000 : ℝ)) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50160270048128363597/50000000000000000000 : ℝ) ≤ (10007886356339193/10000000000000000 : ℝ) ^ (8319/2048 : ℝ) := by
    have hpowers : (50160270048128363597/50000000000000000000 : ℝ)^2048 ≤ (10007886356339193/10000000000000000 : ℝ)^8319 := by
      have hnat : (50160270048128363597 : ℕ)^2048*10000000000000000^8319 ≤ 10007886356339193^8319*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50160270048128363597 50000000000000000000 10007886356339193 10000000000000000 2048 8319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007886356339193/10000000000000000 : ℝ)) (X := (50160270048128363597/50000000000000000000 : ℝ)) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(400898856869113/50000000000000000000 : ℝ) ≤ ((5974676878205652429/5976400000000000000 : ℝ)+2*(980859839331/373525000000000 : ℝ)*(1113/20000 : ℝ))^(8319/2048 : ℝ) := by
    rw [show (5974676878205652429/5976400000000000000 : ℝ)+2*(980859839331/373525000000000 : ℝ)*(1113/20000 : ℝ)=(2000007895524909/2000000000000000 : ℝ) by norm_num, show 1+2*(400898856869113/50000000000000000000 : ℝ)=(25000400898856869113/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(160270048128363597/100000000000000000000 : ℝ)+(400898856869113/50000000000000000000 : ℝ) ≤ ((5974676878205652429/5976400000000000000 : ℝ)+(980859839331/373525000000000 : ℝ)*((10253/50000 : ℝ)+(1113/20000 : ℝ)))^(8319/2048 : ℝ) := by
    rw [show (5974676878205652429/5976400000000000000 : ℝ)+(980859839331/373525000000000 : ℝ)*((10253/50000 : ℝ)+(1113/20000 : ℝ))=(10003962916981869/10000000000000000 : ℝ) by norm_num, show 1+(160270048128363597/100000000000000000000 : ℝ)+(400898856869113/50000000000000000000 : ℝ)=(100161071845842101823/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(160270048128363597/100000000000000000000 : ℝ) ≤ ((5974676878205652429/5976400000000000000 : ℝ)+2*(980859839331/373525000000000 : ℝ)*(10253/50000 : ℝ))^(8319/2048 : ℝ) := by
    rw [show (5974676878205652429/5976400000000000000 : ℝ)+2*(980859839331/373525000000000 : ℝ)*(10253/50000 : ℝ)=(10007886356339193/10000000000000000 : ℝ) by norm_num, show 1+2*(160270048128363597/100000000000000000000 : ℝ)=(50160270048128363597/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5974676878205652429/5976400000000000000 : ℝ)*(X 1 0+X 2 0)+(980859839331/373525000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8319/2048 : ℝ)) (lo := (1113/20000 : ℝ)) (hi := (10253/50000 : ℝ)) (c := (5974676878205652429/5976400000000000000 : ℝ)) (alpha := (980859839331/373525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5974676878205652429/5976400000000000000 : ℝ)*(X 0 1+X 2 1)+(980859839331/373525000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8319/2048 : ℝ)) (lo := (1113/20000 : ℝ)) (hi := (10253/50000 : ℝ)) (c := (5974676878205652429/5976400000000000000 : ℝ)) (alpha := (980859839331/373525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5974676878205652429/5976400000000000000 : ℝ)*(X 0 2+X 1 2)+(980859839331/373525000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8319/2048 : ℝ)) (lo := (1113/20000 : ℝ)) (hi := (10253/50000 : ℝ)) (c := (5974676878205652429/5976400000000000000 : ℝ)) (alpha := (980859839331/373525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2156355267/10000000000 : ℝ)*X 0 0+(2756848271/5000000000 : ℝ)*X 0 1+(5156605727/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2687257039/5000000000 : ℝ)*X 1 0+(-46842341/200000000 : ℝ)*X 1 1+(2578303681/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5374514001/10000000000 : ℝ)*X 2 0+(161143981/312500000 : ℝ)*X 2 1+(-1171058557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088935451/2500000000 : ℝ)*X 0 0+(2007947751/5000000000 : ℝ)*X 0 1+(236211243/500000000 : ℝ)*X 0 2+(1088935451/2500000000 : ℝ)*X 1 0+(2007947751/5000000000 : ℝ)*X 1 1+(236211243/500000000 : ℝ)*X 1 2+(1088935451/2500000000 : ℝ)*X 2 0+(2007947751/5000000000 : ℝ)*X 2 1+(236211243/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-33694721/156250000 : ℝ)*X 0 0+(1289773589/2500000000 : ℝ)*X 0 1+(5511182693/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5284001709/10000000000 : ℝ)*X 1 0+(-397508001/2000000000 : ℝ)*X 1 1+(5511183247/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1321000117/2500000000 : ℝ)*X 2 0+(5511183119/10000000000 : ℝ)*X 2 1+(-1987541891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1088988331/2500000000 : ℝ)*X 0 0+(2359644829/5000000000 : ℝ)*X 0 1+(2010440221/5000000000 : ℝ)*X 0 2+(1088988331/2500000000 : ℝ)*X 1 0+(2359644829/5000000000 : ℝ)*X 1 1+(2010440221/5000000000 : ℝ)*X 1 2+(1088988331/2500000000 : ℝ)*X 2 0+(2359644829/5000000000 : ℝ)*X 2 1+(2010440221/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (137442367737243623373133953/37352500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20340939/25000000000000 : ℝ)*(base29) + (21571779/20000000000000 : ℝ)*(upper2) + (2083461/5000000000000 : ℝ)*(upper3) + (43147793/50000000000000 : ℝ)*(upper4) + (24129237/100000000000000 : ℝ)*(upper5) + (1053051341960023/50000000000000 : ℝ)*(major0) + (1053051382641901/50000000000000 : ℝ)*(major1) + (1053051382641901/50000000000000 : ℝ)*(major2) + (2800419209094249/100000000000000 : ℝ)*(sp0) + (350053711055627/12500000000000 : ℝ)*(sp1) + (350053711055627/12500000000000 : ℝ)*(sp2) + (705887062852649/50000000000000 : ℝ)*(sp3) + (2640178631/25000000000000 : ℝ)*(sp4) + (756200049/50000000000000 : ℝ)*(sp7) + (352943909526349/25000000000000 : ℝ)*(f.failure) + (700107442452193/25000000000000 : ℝ)*(f.sum) + (167827355609677/74705000000000000000000000000 : ℝ)*base66 + (1323893349416283529/298820000000000000000000000000000 : ℝ)*base67 + (2376071736664296471/298820000000000000000000000000000 : ℝ)*base70 + (2524732808821101867/298820000000000000000000000000000 : ℝ)*base71 + (4160971669311/4669062500000000000000000000 : ℝ)*base73 + (1749578209289475529/298820000000000000000000000000000 : ℝ)*base75 + (1332520564267341867/298820000000000000000000000000000 : ℝ)*base77 + (1220333635746995529/298820000000000000000000000000000 : ℝ)*base79 + (137370826653971/18676250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (359069/625000000000000000000 : ℝ)*base89 + (359069/625000000000000000000 : ℝ)*base91 + (359069/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (650649360293159203979509371/74705000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1563125647/100000000000000 : ℝ)*(base19) + (214864547/20000000000000 : ℝ)*(base23) + (14393293/6250000000000 : ℝ)*(upper2) + (92899529/100000000000000 : ℝ)*(upper3) + (128590949/50000000000000 : ℝ)*(upper5) + (1068003735516267/50000000000000 : ℝ)*(major0) + (1068003735516267/50000000000000 : ℝ)*(major1) + (1068003735516267/50000000000000 : ℝ)*(major2) + (10803126507/50000000000000 : ℝ)*(sp1) + (1642155447/25000000000000 : ℝ)*(sp2) + (1420096554536721/50000000000000 : ℝ)*(sp4) + (2840169939694781/100000000000000 : ℝ)*(sp5) + (2840185466128919/100000000000000 : ℝ)*(sp6) + (357955385668051/25000000000000 : ℝ)*(sp7) + (357955385668051/25000000000000 : ℝ)*(f.failure) + (1420096554536721/50000000000000 : ℝ)*(f.sum) + (21588054702353/9338125000000000000000000000 : ℝ)*base66 + (244750111344714543/298820000000000000000000000000000 : ℝ)*base67 + (2215344332734914543/298820000000000000000000000000000 : ℝ)*base69 + (1344778746277654543/298820000000000000000000000000000 : ℝ)*base71 + (47449341576019/74705000000000000000000000000 : ℝ)*base74 + (2289665746764334543/298820000000000000000000000000000 : ℝ)*base75 + (659907833672725457/298820000000000000000000000000000 : ℝ)*base78 + (1765181560492614543/298820000000000000000000000000000 : ℝ)*base79 + (124167102163581/74705000000000000000000000000 : ℝ)*base81 + (2732669/625000000000000000000 : ℝ)*base90 + (2732669/625000000000000000000 : ℝ)*base92 + (2732669/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1127_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37295281/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10253/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1113/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4501/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4137/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1127_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1127_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37295281/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4501/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4137/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1127_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1127_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1127_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37295281/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4501/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4137/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1127_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

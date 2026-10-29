-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1512_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:55:38.261337+00:00
-- url     : https://prove2.me/submissions/93e912d0-3a7b-4ee9-a987-55d7da4e377f

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
theorem support_rectangle_w1512_s0_0 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-67433361/400000000 : ℝ)*x 0 + (5912828431/10000000000 : ℝ)*x 1 + (971063433/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67433361/400000000 : ℝ)^4521 ≤ (31279433587/312500000000 : ℝ)^3497 := by
    have hnat : (67433361 : ℕ)^4521*312500000000^3497 ≤ 31279433587^3497*400000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67433361 400000000 31279433587 312500000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5912828431/10000000000 : ℝ)^4521 ≤ (50695781068539/100000000000000 : ℝ)^3497 := by
    have hnat : (5912828431 : ℕ)^4521*100000000000000^3497 ≤ 50695781068539^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5912828431 10000000000 50695781068539 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (971063433/2000000000 : ℝ)^4521 ≤ (19647400086589/50000000000000 : ℝ)^3497 := by
    have hnat : (971063433 : ℕ)^4521*50000000000000^3497 ≤ 19647400086589^3497*2000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971063433 2000000000 19647400086589 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67433361/400000000 : ℝ), (5912828431/10000000000 : ℝ), (971063433/2000000000 : ℝ)] ![(31279433587/312500000000 : ℝ), (50695781068539/100000000000000 : ℝ), (19647400086589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67433361/400000000 : ℝ)|^4521 ≤ (31279433587/312500000000 : ℝ)^3497
        have hw : |(-67433361/400000000 : ℝ)|=(67433361/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5912828431/10000000000 : ℝ)|^4521 ≤ (50695781068539/100000000000000 : ℝ)^3497
        have hw : |(5912828431/10000000000 : ℝ)|=(5912828431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(971063433/2000000000 : ℝ)|^4521 ≤ (19647400086589/50000000000000 : ℝ)^3497
        have hw : |(971063433/2000000000 : ℝ)|=(971063433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s0_1 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1369495029/2500000000 : ℝ)*x 0 + (-455717831/2000000000 : ℝ)*x 1 + (4855317087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1369495029/2500000000 : ℝ)^4521 ≤ (11482135521749/25000000000000 : ℝ)^3497 := by
    have hnat : (1369495029 : ℕ)^4521*25000000000000^3497 ≤ 11482135521749^3497*2500000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369495029 2500000000 11482135521749 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (455717831/2000000000 : ℝ)^4521 ≤ (14776658542501/100000000000000 : ℝ)^3497 := by
    have hnat : (455717831 : ℕ)^4521*100000000000000^3497 ≤ 14776658542501^3497*2000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455717831 2000000000 14776658542501 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4855317087/10000000000 : ℝ)^4521 ≤ (4911849919633/12500000000000 : ℝ)^3497 := by
    have hnat : (4855317087 : ℕ)^4521*12500000000000^3497 ≤ 4911849919633^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4855317087 10000000000 4911849919633 12500000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1369495029/2500000000 : ℝ), (-455717831/2000000000 : ℝ), (4855317087/10000000000 : ℝ)] ![(11482135521749/25000000000000 : ℝ), (14776658542501/100000000000000 : ℝ), (4911849919633/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1369495029/2500000000 : ℝ)|^4521 ≤ (11482135521749/25000000000000 : ℝ)^3497
        have hw : |(1369495029/2500000000 : ℝ)|=(1369495029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-455717831/2000000000 : ℝ)|^4521 ≤ (14776658542501/100000000000000 : ℝ)^3497
        have hw : |(-455717831/2000000000 : ℝ)|=(455717831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4855317087/10000000000 : ℝ)|^4521 ≤ (4911849919633/12500000000000 : ℝ)^3497
        have hw : |(4855317087/10000000000 : ℝ)|=(4855317087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s0_2 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5477980179/10000000000 : ℝ)*x 0 + (4855317111/10000000000 : ℝ)*x 1 + (-569647261/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5477980179/10000000000 : ℝ)^4521 ≤ (45928542769871/100000000000000 : ℝ)^3497 := by
    have hnat : (5477980179 : ℕ)^4521*100000000000000^3497 ≤ 45928542769871^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477980179 10000000000 45928542769871 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4855317111/10000000000 : ℝ)^4521 ≤ (2455924975511/6250000000000 : ℝ)^3497 := by
    have hnat : (4855317111 : ℕ)^4521*6250000000000^3497 ≤ 2455924975511^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4855317111 10000000000 2455924975511 6250000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (569647261/2500000000 : ℝ)^4521 ≤ (7388328805941/50000000000000 : ℝ)^3497 := by
    have hnat : (569647261 : ℕ)^4521*50000000000000^3497 ≤ 7388328805941^3497*2500000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569647261 2500000000 7388328805941 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5477980179/10000000000 : ℝ), (4855317111/10000000000 : ℝ), (-569647261/2500000000 : ℝ)] ![(45928542769871/100000000000000 : ℝ), (2455924975511/6250000000000 : ℝ), (7388328805941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5477980179/10000000000 : ℝ)|^4521 ≤ (45928542769871/100000000000000 : ℝ)^3497
        have hw : |(5477980179/10000000000 : ℝ)|=(5477980179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4855317111/10000000000 : ℝ)|^4521 ≤ (2455924975511/6250000000000 : ℝ)^3497
        have hw : |(4855317111/10000000000 : ℝ)|=(4855317111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-569647261/2500000000 : ℝ)|^4521 ≤ (7388328805941/50000000000000 : ℝ)^3497
        have hw : |(-569647261/2500000000 : ℝ)|=(569647261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s0_3 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2072571869/5000000000 : ℝ)*x 0 + (3091269367/10000000000 : ℝ)*x 1 + (2744633273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2072571869/5000000000 : ℝ)^4521 ≤ (32029238528497/100000000000000 : ℝ)^3497 := by
    have hnat : (2072571869 : ℕ)^4521*100000000000000^3497 ≤ 32029238528497^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072571869 5000000000 32029238528497 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091269367/10000000000 : ℝ)^4521 ≤ (5479961381887/25000000000000 : ℝ)^3497 := by
    have hnat : (3091269367 : ℕ)^4521*25000000000000^3497 ≤ 5479961381887^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091269367 10000000000 5479961381887 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2744633273/5000000000 : ℝ)^4521 ≤ (46050915930113/100000000000000 : ℝ)^3497 := by
    have hnat : (2744633273 : ℕ)^4521*100000000000000^3497 ≤ 46050915930113^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744633273 5000000000 46050915930113 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2072571869/5000000000 : ℝ), (3091269367/10000000000 : ℝ), (2744633273/5000000000 : ℝ)] ![(32029238528497/100000000000000 : ℝ), (5479961381887/25000000000000 : ℝ), (46050915930113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2072571869/5000000000 : ℝ)|^4521 ≤ (32029238528497/100000000000000 : ℝ)^3497
        have hw : |(2072571869/5000000000 : ℝ)|=(2072571869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091269367/10000000000 : ℝ)|^4521 ≤ (5479961381887/25000000000000 : ℝ)^3497
        have hw : |(3091269367/10000000000 : ℝ)|=(3091269367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2744633273/5000000000 : ℝ)|^4521 ≤ (46050915930113/100000000000000 : ℝ)^3497
        have hw : |(2744633273/5000000000 : ℝ)|=(2744633273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s0_4 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1689354103/10000000000 : ℝ)*x 0 + (1220572867/2500000000 : ℝ)*x 1 + (5884888087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1689354103/10000000000 : ℝ)^4521 ≤ (5018223497713/50000000000000 : ℝ)^3497 := by
    have hnat : (1689354103 : ℕ)^4521*50000000000000^3497 ≤ 5018223497713^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1689354103 10000000000 5018223497713 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1220572867/2500000000 : ℝ)^4521 ≤ (39577261658721/100000000000000 : ℝ)^3497 := by
    have hnat : (1220572867 : ℕ)^4521*100000000000000^3497 ≤ 39577261658721^3497*2500000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1220572867 2500000000 39577261658721 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5884888087/10000000000 : ℝ)^4521 ≤ (25193145663181/50000000000000 : ℝ)^3497 := by
    have hnat : (5884888087 : ℕ)^4521*50000000000000^3497 ≤ 25193145663181^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5884888087 10000000000 25193145663181 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1689354103/10000000000 : ℝ), (1220572867/2500000000 : ℝ), (5884888087/10000000000 : ℝ)] ![(5018223497713/50000000000000 : ℝ), (39577261658721/100000000000000 : ℝ), (25193145663181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1689354103/10000000000 : ℝ)|^4521 ≤ (5018223497713/50000000000000 : ℝ)^3497
        have hw : |(-1689354103/10000000000 : ℝ)|=(1689354103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1220572867/2500000000 : ℝ)|^4521 ≤ (39577261658721/100000000000000 : ℝ)^3497
        have hw : |(1220572867/2500000000 : ℝ)|=(1220572867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5884888087/10000000000 : ℝ)|^4521 ≤ (25193145663181/50000000000000 : ℝ)^3497
        have hw : |(5884888087/10000000000 : ℝ)|=(5884888087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s0_5 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (648632011/1250000000 : ℝ)*x 0 + (-312254591/2500000000 : ℝ)*x 1 + (58848879/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (648632011/1250000000 : ℝ)^4521 ≤ (42821300290771/100000000000000 : ℝ)^3497 := by
    have hnat : (648632011 : ℕ)^4521*100000000000000^3497 ≤ 42821300290771^3497*1250000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648632011 1250000000 42821300290771 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (312254591/2500000000 : ℝ)^4521 ≤ (3396205222289/50000000000000 : ℝ)^3497 := by
    have hnat : (312254591 : ℕ)^4521*50000000000000^3497 ≤ 3396205222289^3497*2500000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312254591 2500000000 3396205222289 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58848879/100000000 : ℝ)^4521 ≤ (12596572314109/25000000000000 : ℝ)^3497 := by
    have hnat : (58848879 : ℕ)^4521*25000000000000^3497 ≤ 12596572314109^3497*100000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58848879 100000000 12596572314109 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(648632011/1250000000 : ℝ), (-312254591/2500000000 : ℝ), (58848879/100000000 : ℝ)] ![(42821300290771/100000000000000 : ℝ), (3396205222289/50000000000000 : ℝ), (12596572314109/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(648632011/1250000000 : ℝ)|^4521 ≤ (42821300290771/100000000000000 : ℝ)^3497
        have hw : |(648632011/1250000000 : ℝ)|=(648632011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-312254591/2500000000 : ℝ)|^4521 ≤ (3396205222289/50000000000000 : ℝ)^3497
        have hw : |(-312254591/2500000000 : ℝ)|=(312254591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(58848879/100000000 : ℝ)|^4521 ≤ (12596572314109/25000000000000 : ℝ)^3497
        have hw : |(58848879/100000000 : ℝ)|=(58848879/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s0_6 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (32431601/62500000 : ℝ)*x 0 + (5884887827/10000000000 : ℝ)*x 1 + (-1249018369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32431601/62500000 : ℝ)^4521 ≤ (8564260211783/20000000000000 : ℝ)^3497 := by
    have hnat : (32431601 : ℕ)^4521*20000000000000^3497 ≤ 8564260211783^3497*62500000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32431601 62500000 8564260211783 20000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5884887827/10000000000 : ℝ)^4521 ≤ (50386288448391/100000000000000 : ℝ)^3497 := by
    have hnat : (5884887827 : ℕ)^4521*100000000000000^3497 ≤ 50386288448391^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5884887827 10000000000 50386288448391 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1249018369/10000000000 : ℝ)^4521 ≤ (6792410479731/100000000000000 : ℝ)^3497 := by
    have hnat : (1249018369 : ℕ)^4521*100000000000000^3497 ≤ 6792410479731^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249018369 10000000000 6792410479731 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32431601/62500000 : ℝ), (5884887827/10000000000 : ℝ), (-1249018369/10000000000 : ℝ)] ![(8564260211783/20000000000000 : ℝ), (50386288448391/100000000000000 : ℝ), (6792410479731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32431601/62500000 : ℝ)|^4521 ≤ (8564260211783/20000000000000 : ℝ)^3497
        have hw : |(32431601/62500000 : ℝ)|=(32431601/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5884887827/10000000000 : ℝ)|^4521 ≤ (50386288448391/100000000000000 : ℝ)^3497
        have hw : |(5884887827/10000000000 : ℝ)|=(5884887827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1249018369/10000000000 : ℝ)|^4521 ≤ (6792410479731/100000000000000 : ℝ)^3497
        have hw : |(-1249018369/10000000000 : ℝ)|=(1249018369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s0_7 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4153126207/10000000000 : ℝ)*x 0 + (5428100073/10000000000 : ℝ)*x 1 + (3154627207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4153126207/10000000000 : ℝ)^4521 ≤ (8027250567197/25000000000000 : ℝ)^3497 := by
    have hnat : (4153126207 : ℕ)^4521*25000000000000^3497 ≤ 8027250567197^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153126207 10000000000 8027250567197 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428100073/10000000000 : ℝ)^4521 ≤ (22694299935417/50000000000000 : ℝ)^3497 := by
    have hnat : (5428100073 : ℕ)^4521*50000000000000^3497 ≤ 22694299935417^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428100073 10000000000 22694299935417 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154627207/10000000000 : ℝ)^4521 ≤ (22502397846067/100000000000000 : ℝ)^3497 := by
    have hnat : (3154627207 : ℕ)^4521*100000000000000^3497 ≤ 22502397846067^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154627207 10000000000 22502397846067 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4153126207/10000000000 : ℝ), (5428100073/10000000000 : ℝ), (3154627207/10000000000 : ℝ)] ![(8027250567197/25000000000000 : ℝ), (22694299935417/50000000000000 : ℝ), (22502397846067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4153126207/10000000000 : ℝ)|^4521 ≤ (8027250567197/25000000000000 : ℝ)^3497
        have hw : |(4153126207/10000000000 : ℝ)|=(4153126207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428100073/10000000000 : ℝ)|^4521 ≤ (22694299935417/50000000000000 : ℝ)^3497
        have hw : |(5428100073/10000000000 : ℝ)|=(5428100073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154627207/10000000000 : ℝ)|^4521 ≤ (22502397846067/100000000000000 : ℝ)^3497
        have hw : |(3154627207/10000000000 : ℝ)|=(3154627207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1512_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81689629/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2827/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6371/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4519/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4519 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4519*1^1024 ≤ 0^1024*1^4519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4519/1024 : ℝ) ≤ (438325313840255253/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4519 ≤ (438325313840255253/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4519*25000000000000000000^1024 ≤ 438325313840255253^1024*5^4519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 438325313840255253 25000000000000000000 4519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (438325313840255253/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4519/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4519 := by
      have hnat : (1 : ℕ)^1024*1^4519 ≤ 1^4519*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25438325313840255253/25000000000000000000 : ℝ) ≤ (2509865746886099/2500000000000000 : ℝ) ^ (4519/1024 : ℝ) := by
    have hpowers : (25438325313840255253/25000000000000000000 : ℝ)^1024 ≤ (2509865746886099/2500000000000000 : ℝ)^4519 := by
      have hnat : (25438325313840255253 : ℕ)^1024*2500000000000000^4519 ≤ 2509865746886099^4519*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25438325313840255253 25000000000000000000 2509865746886099 2500000000000000 1024 4519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2509865746886099/2500000000000000 : ℝ)) (X := (25438325313840255253/25000000000000000000 : ℝ)) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12938325313840255253/12500000000000000000 : ℝ) ≤ (1259865746886099/1250000000000000 : ℝ) ^ (4519/1024 : ℝ) := by
    have hpowers : (12938325313840255253/12500000000000000000 : ℝ)^1024 ≤ (1259865746886099/1250000000000000 : ℝ)^4519 := by
      have hnat : (12938325313840255253 : ℕ)^1024*1250000000000000^4519 ≤ 1259865746886099^4519*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12938325313840255253 12500000000000000000 1259865746886099 1250000000000000 1024 4519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1259865746886099/1250000000000000 : ℝ)) (X := (12938325313840255253/12500000000000000000 : ℝ)) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(9865746886099/1000000000000000 : ℝ)*(0 : ℝ))^(4519/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9865746886099/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(438325313840255253/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(9865746886099/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4519/1024 : ℝ) := by
    rw [show (1 : ℝ)+(9865746886099/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2509865746886099/2500000000000000 : ℝ) by norm_num, show 1+(438325313840255253/25000000000000000000 : ℝ)+(0 : ℝ)=(25438325313840255253/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(438325313840255253/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(9865746886099/1000000000000000 : ℝ)*(2/5 : ℝ))^(4519/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9865746886099/1000000000000000 : ℝ)*(2/5 : ℝ)=(1259865746886099/1250000000000000 : ℝ) by norm_num, show 1+2*(438325313840255253/25000000000000000000 : ℝ)=(12938325313840255253/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(9865746886099/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4519/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9865746886099/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(9865746886099/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4519/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9865746886099/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(9865746886099/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4519/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9865746886099/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-67433361/400000000 : ℝ)*X 0 0+(5912828431/10000000000 : ℝ)*X 0 1+(971063433/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1369495029/2500000000 : ℝ)*X 1 0+(-455717831/2000000000 : ℝ)*X 1 1+(4855317087/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5477980179/10000000000 : ℝ)*X 2 0+(4855317111/10000000000 : ℝ)*X 2 1+(-569647261/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2072571869/5000000000 : ℝ)*X 0 0+(3091269367/10000000000 : ℝ)*X 0 1+(2744633273/5000000000 : ℝ)*X 0 2+(2072571869/5000000000 : ℝ)*X 1 0+(3091269367/10000000000 : ℝ)*X 1 1+(2744633273/5000000000 : ℝ)*X 1 2+(2072571869/5000000000 : ℝ)*X 2 0+(3091269367/10000000000 : ℝ)*X 2 1+(2744633273/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1689354103/10000000000 : ℝ)*X 0 0+(1220572867/2500000000 : ℝ)*X 0 1+(5884888087/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((648632011/1250000000 : ℝ)*X 1 0+(-312254591/2500000000 : ℝ)*X 1 1+(58848879/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((32431601/62500000 : ℝ)*X 2 0+(5884887827/10000000000 : ℝ)*X 2 1+(-1249018369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4153126207/10000000000 : ℝ)*X 0 0+(5428100073/10000000000 : ℝ)*X 0 1+(3154627207/10000000000 : ℝ)*X 0 2+(4153126207/10000000000 : ℝ)*X 1 0+(5428100073/10000000000 : ℝ)*X 1 1+(3154627207/10000000000 : ℝ)*X 1 2+(4153126207/10000000000 : ℝ)*X 2 0+(5428100073/10000000000 : ℝ)*X 2 1+(3154627207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3125288253947508608847/390625000000000000000000000 : ℝ) := by norm_num
    linear_combination (65541047/100000000000000 : ℝ)*(base1) + (1824406381/100000000000000 : ℝ)*(base19) + (36705633/2000000000000 : ℝ)*(base23) + (54361791/25000000000000 : ℝ)*(upper3) + (252178789/100000000000000 : ℝ)*(upper5) + (42582801458993/6250000000000 : ℝ)*(major0) + (42582801458993/6250000000000 : ℝ)*(major1) + (42582801458993/6250000000000 : ℝ)*(major2) + (945622429140879/100000000000000 : ℝ)*(sp0) + (189125432572891/20000000000000 : ℝ)*(sp1) + (472813575994593/50000000000000 : ℝ)*(sp2) + (83403493856549/20000000000000 : ℝ)*(sp3) + (1655917751/25000000000000 : ℝ)*(sp4) + (71447547/2500000000000 : ℝ)*(sp7) + (52127549090709/12500000000000 : ℝ)*(f.failure) + (236407246817709/25000000000000 : ℝ)*(f.sum) + (292699161473/195312500000000000000000000 : ℝ)*base66 + (20723299611693/6250000000000000000000000000 : ℝ)*base68 + (30273805467943/6250000000000000000000000000 : ℝ)*base70 + (10005876949193/6250000000000000000000000000 : ℝ)*base72 + (7346910167943/3125000000000000000000000000 : ℝ)*base74 + (33821462980443/6250000000000000000000000000 : ℝ)*base76 + (30238173911693/6250000000000000000000000000 : ℝ)*base78 + (24154780392943/6250000000000000000000000000 : ℝ)*base80 + (49708967943/3125000000000000000000000000 : ℝ)*base82 + (5556961/625000000000000000000 : ℝ)*base89 + (5556961/625000000000000000000 : ℝ)*base91 + (5556961/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (63641856630405178478607/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (503469469/50000000000000 : ℝ)*(base19) + (1030694903/100000000000000 : ℝ)*(base23) + (9359123/10000000000000 : ℝ)*(base32) + (146652017/100000000000000 : ℝ)*(upper3) + (46900823/50000000000000 : ℝ)*(upper5) + (359316362907077/50000000000000 : ℝ)*(major0) + (359316362907077/50000000000000 : ℝ)*(major1) + (359316362907077/50000000000000 : ℝ)*(major2) + (96763847/4000000000000 : ℝ)*(sp1) + (2597197089/100000000000000 : ℝ)*(sp2) + (997409736842439/100000000000000 : ℝ)*(sp4) + (498703155403663/50000000000000 : ℝ)*(sp5) + (997406108950447/100000000000000 : ℝ)*(sp6) + (219927725741507/50000000000000 : ℝ)*(sp7) + (439855545074243/100000000000000 : ℝ)*(f.failure) + (997409736842439/100000000000000 : ℝ)*(f.sum) + (33599227002377/25000000000000000000000000000 : ℝ)*base66 + (758943483677377/50000000000000000000000000000 : ℝ)*base68 + (323354264527377/50000000000000000000000000000 : ℝ)*base70 + (235645204277377/50000000000000000000000000000 : ℝ)*base72 + (215733540802377/25000000000000000000000000000 : ℝ)*base74 + (389127936127377/50000000000000000000000000000 : ℝ)*base76 + (341727477427377/50000000000000000000000000000 : ℝ)*base78 + (407322888477377/50000000000000000000000000000 : ℝ)*base80 + (55482660952377/25000000000000000000000000000 : ℝ)*base82 + (11874153/5000000000000000000000 : ℝ)*base90 + (11874153/5000000000000000000000 : ℝ)*base92 + (11874153/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1512_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81689629/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2827/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6371/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1512_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1512_s1_0 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-459886819/2500000000 : ℝ)*x 0 + (2785255837/5000000000 : ℝ)*x 1 + (5098839469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (459886819/2500000000 : ℝ)^4521 ≤ (2240948272361/20000000000000 : ℝ)^3497 := by
    have hnat : (459886819 : ℕ)^4521*20000000000000^3497 ≤ 2240948272361^3497*2500000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459886819 2500000000 2240948272361 20000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2785255837/5000000000 : ℝ)^4521 ≤ (23466994858647/50000000000000 : ℝ)^3497 := by
    have hnat : (2785255837 : ℕ)^4521*50000000000000^3497 ≤ 23466994858647^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2785255837 5000000000 23466994858647 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5098839469/10000000000 : ℝ)^4521 ≤ (20930634457443/50000000000000 : ℝ)^3497 := by
    have hnat : (5098839469 : ℕ)^4521*50000000000000^3497 ≤ 20930634457443^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5098839469 10000000000 20930634457443 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-459886819/2500000000 : ℝ), (2785255837/5000000000 : ℝ), (5098839469/10000000000 : ℝ)] ![(2240948272361/20000000000000 : ℝ), (23466994858647/50000000000000 : ℝ), (20930634457443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-459886819/2500000000 : ℝ)|^4521 ≤ (2240948272361/20000000000000 : ℝ)^3497
        have hw : |(-459886819/2500000000 : ℝ)|=(459886819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2785255837/5000000000 : ℝ)|^4521 ≤ (23466994858647/50000000000000 : ℝ)^3497
        have hw : |(2785255837/5000000000 : ℝ)|=(2785255837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5098839469/10000000000 : ℝ)|^4521 ≤ (20930634457443/50000000000000 : ℝ)^3497
        have hw : |(5098839469/10000000000 : ℝ)|=(5098839469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s1_1 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2693311113/5000000000 : ℝ)*x 0 + (-1043956383/5000000000 : ℝ)*x 1 + (5098838893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2693311113/5000000000 : ℝ)^4521 ≤ (5617589297797/12500000000000 : ℝ)^3497 := by
    have hnat : (2693311113 : ℕ)^4521*12500000000000^3497 ≤ 5617589297797^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693311113 5000000000 5617589297797 12500000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043956383/5000000000 : ℝ)^4521 ≤ (6599011397903/50000000000000 : ℝ)^3497 := by
    have hnat : (1043956383 : ℕ)^4521*50000000000000^3497 ≤ 6599011397903^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043956383 5000000000 6599011397903 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5098838893/10000000000 : ℝ)^4521 ≤ (4186126280121/10000000000000 : ℝ)^3497 := by
    have hnat : (5098838893 : ℕ)^4521*10000000000000^3497 ≤ 4186126280121^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5098838893 10000000000 4186126280121 10000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2693311113/5000000000 : ℝ), (-1043956383/5000000000 : ℝ), (5098838893/10000000000 : ℝ)] ![(5617589297797/12500000000000 : ℝ), (6599011397903/50000000000000 : ℝ), (4186126280121/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2693311113/5000000000 : ℝ)|^4521 ≤ (5617589297797/12500000000000 : ℝ)^3497
        have hw : |(2693311113/5000000000 : ℝ)|=(2693311113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1043956383/5000000000 : ℝ)|^4521 ≤ (6599011397903/50000000000000 : ℝ)^3497
        have hw : |(-1043956383/5000000000 : ℝ)|=(1043956383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5098838893/10000000000 : ℝ)|^4521 ≤ (4186126280121/10000000000000 : ℝ)^3497
        have hw : |(5098838893/10000000000 : ℝ)|=(5098838893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s1_2 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53866217/100000000 : ℝ)*x 0 + (5098839493/10000000000 : ℝ)*x 1 + (-2087912681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53866217/100000000 : ℝ)^4521 ≤ (8988141741783/20000000000000 : ℝ)^3497 := by
    have hnat : (53866217 : ℕ)^4521*20000000000000^3497 ≤ 8988141741783^3497*100000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53866217 100000000 8988141741783 20000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5098839493/10000000000 : ℝ)^4521 ≤ (20930634584811/50000000000000 : ℝ)^3497 := by
    have hnat : (5098839493 : ℕ)^4521*50000000000000^3497 ≤ 20930634584811^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5098839493 10000000000 20930634584811 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2087912681/10000000000 : ℝ)^4521 ≤ (527920884047/4000000000000 : ℝ)^3497 := by
    have hnat : (2087912681 : ℕ)^4521*4000000000000^3497 ≤ 527920884047^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087912681 10000000000 527920884047 4000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53866217/100000000 : ℝ), (5098839493/10000000000 : ℝ), (-2087912681/10000000000 : ℝ)] ![(8988141741783/20000000000000 : ℝ), (20930634584811/50000000000000 : ℝ), (527920884047/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53866217/100000000 : ℝ)|^4521 ≤ (8988141741783/20000000000000 : ℝ)^3497
        have hw : |(53866217/100000000 : ℝ)|=(53866217/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5098839493/10000000000 : ℝ)|^4521 ≤ (20930634584811/50000000000000 : ℝ)^3497
        have hw : |(5098839493/10000000000 : ℝ)|=(5098839493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2087912681/10000000000 : ℝ)|^4521 ≤ (527920884047/4000000000000 : ℝ)^3497
        have hw : |(-2087912681/10000000000 : ℝ)|=(2087912681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s1_3 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4249611293/10000000000 : ℝ)*x 0 + (467905683/1250000000 : ℝ)*x 1 + (1203200667/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4249611293/10000000000 : ℝ)^4521 ≤ (33076650417073/100000000000000 : ℝ)^3497 := by
    have hnat : (4249611293 : ℕ)^4521*100000000000000^3497 ≤ 33076650417073^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249611293 10000000000 33076650417073 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (467905683/1250000000 : ℝ)^4521 ≤ (7018201813407/25000000000000 : ℝ)^3497 := by
    have hnat : (467905683 : ℕ)^4521*25000000000000^3497 ≤ 7018201813407^3497*1250000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467905683 1250000000 7018201813407 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1203200667/2500000000 : ℝ)^4521 ≤ (4856317789859/12500000000000 : ℝ)^3497 := by
    have hnat : (1203200667 : ℕ)^4521*12500000000000^3497 ≤ 4856317789859^3497*2500000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203200667 2500000000 4856317789859 12500000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4249611293/10000000000 : ℝ), (467905683/1250000000 : ℝ), (1203200667/2500000000 : ℝ)] ![(33076650417073/100000000000000 : ℝ), (7018201813407/25000000000000 : ℝ), (4856317789859/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4249611293/10000000000 : ℝ)|^4521 ≤ (33076650417073/100000000000000 : ℝ)^3497
        have hw : |(4249611293/10000000000 : ℝ)|=(4249611293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(467905683/1250000000 : ℝ)|^4521 ≤ (7018201813407/25000000000000 : ℝ)^3497
        have hw : |(467905683/1250000000 : ℝ)|=(467905683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1203200667/2500000000 : ℝ)|^4521 ≤ (4856317789859/12500000000000 : ℝ)^3497
        have hw : |(1203200667/2500000000 : ℝ)|=(1203200667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s1_4 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1839849113/10000000000 : ℝ)*x 0 + (5104114441/10000000000 : ℝ)*x 1 + (5565151859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1839849113/10000000000 : ℝ)^4521 ≤ (11207118271411/100000000000000 : ℝ)^3497 := by
    have hnat : (1839849113 : ℕ)^4521*100000000000000^3497 ≤ 11207118271411^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1839849113 10000000000 11207118271411 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5104114441/10000000000 : ℝ)^4521 ≤ (2619829128413/6250000000000 : ℝ)^3497 := by
    have hnat : (5104114441 : ℕ)^4521*6250000000000^3497 ≤ 2619829128413^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5104114441 10000000000 2619829128413 6250000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5565151859/10000000000 : ℝ)^4521 ≤ (4687561566257/10000000000000 : ℝ)^3497 := by
    have hnat : (5565151859 : ℕ)^4521*10000000000000^3497 ≤ 4687561566257^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5565151859 10000000000 4687561566257 10000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1839849113/10000000000 : ℝ), (5104114441/10000000000 : ℝ), (5565151859/10000000000 : ℝ)] ![(11207118271411/100000000000000 : ℝ), (2619829128413/6250000000000 : ℝ), (4687561566257/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1839849113/10000000000 : ℝ)|^4521 ≤ (11207118271411/100000000000000 : ℝ)^3497
        have hw : |(-1839849113/10000000000 : ℝ)|=(1839849113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5104114441/10000000000 : ℝ)|^4521 ≤ (2619829128413/6250000000000 : ℝ)^3497
        have hw : |(5104114441/10000000000 : ℝ)|=(5104114441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5565151859/10000000000 : ℝ)|^4521 ≤ (4687561566257/10000000000000 : ℝ)^3497
        have hw : |(5565151859/10000000000 : ℝ)|=(5565151859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s1_5 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328899123/625000000 : ℝ)*x 0 + (-810799997/5000000000 : ℝ)*x 1 + (2782576019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328899123/625000000 : ℝ)^4521 ≤ (43605246033257/100000000000000 : ℝ)^3497 := by
    have hnat : (328899123 : ℕ)^4521*100000000000000^3497 ≤ 43605246033257^3497*625000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328899123 625000000 43605246033257 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (810799997/5000000000 : ℝ)^4521 ≤ (1903827267243/20000000000000 : ℝ)^3497 := by
    have hnat : (810799997 : ℕ)^4521*20000000000000^3497 ≤ 1903827267243^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      810799997 5000000000 1903827267243 20000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2782576019/5000000000 : ℝ)^4521 ≤ (9375123522359/20000000000000 : ℝ)^3497 := by
    have hnat : (2782576019 : ℕ)^4521*20000000000000^3497 ≤ 9375123522359^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2782576019 5000000000 9375123522359 20000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328899123/625000000 : ℝ), (-810799997/5000000000 : ℝ), (2782576019/5000000000 : ℝ)] ![(43605246033257/100000000000000 : ℝ), (1903827267243/20000000000000 : ℝ), (9375123522359/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328899123/625000000 : ℝ)|^4521 ≤ (43605246033257/100000000000000 : ℝ)^3497
        have hw : |(328899123/625000000 : ℝ)|=(328899123/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-810799997/5000000000 : ℝ)|^4521 ≤ (1903827267243/20000000000000 : ℝ)^3497
        have hw : |(-810799997/5000000000 : ℝ)|=(810799997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2782576019/5000000000 : ℝ)|^4521 ≤ (9375123522359/20000000000000 : ℝ)^3497
        have hw : |(2782576019/5000000000 : ℝ)|=(2782576019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s1_6 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5262385747/10000000000 : ℝ)*x 0 + (5565152131/10000000000 : ℝ)*x 1 + (-810800087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5262385747/10000000000 : ℝ)^4521 ≤ (10901310916443/25000000000000 : ℝ)^3497 := by
    have hnat : (5262385747 : ℕ)^4521*25000000000000^3497 ≤ 10901310916443^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262385747 10000000000 10901310916443 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5565152131/10000000000 : ℝ)^4521 ≤ (1171890465613/2500000000000 : ℝ)^3497 := by
    have hnat : (5565152131 : ℕ)^4521*2500000000000^3497 ≤ 1171890465613^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5565152131 10000000000 1171890465613 2500000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (810800087/5000000000 : ℝ)^4521 ≤ (9519137702261/100000000000000 : ℝ)^3497 := by
    have hnat : (810800087 : ℕ)^4521*100000000000000^3497 ≤ 9519137702261^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      810800087 5000000000 9519137702261 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5262385747/10000000000 : ℝ), (5565152131/10000000000 : ℝ), (-810800087/5000000000 : ℝ)] ![(10901310916443/25000000000000 : ℝ), (1171890465613/2500000000000 : ℝ), (9519137702261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5262385747/10000000000 : ℝ)|^4521 ≤ (10901310916443/25000000000000 : ℝ)^3497
        have hw : |(5262385747/10000000000 : ℝ)|=(5262385747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5565152131/10000000000 : ℝ)|^4521 ≤ (1171890465613/2500000000000 : ℝ)^3497
        have hw : |(5565152131/10000000000 : ℝ)|=(5565152131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-810800087/5000000000 : ℝ)|^4521 ≤ (9519137702261/100000000000000 : ℝ)^3497
        have hw : |(-810800087/5000000000 : ℝ)|=(810800087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s1_7 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (850059299/2000000000 : ℝ)*x 0 + (4800841473/10000000000 : ℝ)*x 1 + (1877699259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (850059299/2000000000 : ℝ)^4521 ≤ (33083545509059/100000000000000 : ℝ)^3497 := by
    have hnat : (850059299 : ℕ)^4521*100000000000000^3497 ≤ 33083545509059^3497*2000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850059299 2000000000 33083545509059 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4800841473/10000000000 : ℝ)^4521 ≤ (7745151926809/20000000000000 : ℝ)^3497 := by
    have hnat : (4800841473 : ℕ)^4521*20000000000000^3497 ≤ 7745151926809^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4800841473 10000000000 7745151926809 20000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1877699259/5000000000 : ℝ)^4521 ≤ (28190694839267/100000000000000 : ℝ)^3497 := by
    have hnat : (1877699259 : ℕ)^4521*100000000000000^3497 ≤ 28190694839267^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877699259 5000000000 28190694839267 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(850059299/2000000000 : ℝ), (4800841473/10000000000 : ℝ), (1877699259/5000000000 : ℝ)] ![(33083545509059/100000000000000 : ℝ), (7745151926809/20000000000000 : ℝ), (28190694839267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(850059299/2000000000 : ℝ)|^4521 ≤ (33083545509059/100000000000000 : ℝ)^3497
        have hw : |(850059299/2000000000 : ℝ)|=(850059299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4800841473/10000000000 : ℝ)|^4521 ≤ (7745151926809/20000000000000 : ℝ)^3497
        have hw : |(4800841473/10000000000 : ℝ)|=(4800841473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1877699259/5000000000 : ℝ)|^4521 ≤ (28190694839267/100000000000000 : ℝ)^3497
        have hw : |(1877699259/5000000000 : ℝ)|=(1877699259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1512_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81689629/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6371/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2827/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2089/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18333/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6371/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2827/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6371/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2827/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6371/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2827/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6371/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2827/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6371/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2827/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6371/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2827/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2827/100000 : ℝ) ^ (4519/1024 : ℝ) ≤ (7320448809007/50000000000000000000 : ℝ) := by
    have hpowers : (2827/100000 : ℝ)^4519 ≤ (7320448809007/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2827 : ℕ)^4519*50000000000000000000^1024 ≤ 7320448809007^1024*100000^4519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2827 100000 7320448809007 50000000000000000000 4519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2827/100000 : ℝ)) (X := (7320448809007/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6371/25000 : ℝ) ^ (4519/1024 : ℝ) ≤ (239777197054691783/100000000000000000000 : ℝ) := by
    have hpowers : (6371/25000 : ℝ)^4519 ≤ (239777197054691783/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6371 : ℕ)^4519*100000000000000000000^1024 ≤ 239777197054691783^1024*25000^4519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6371 25000 239777197054691783 100000000000000000000 4519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6371/25000 : ℝ)) (X := (239777197054691783/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000007320448809007/25000000000000000000 : ℝ) ≤ (5000000331760953/5000000000000000 : ℝ) ^ (4519/1024 : ℝ) := by
    have hpowers : (25000007320448809007/25000000000000000000 : ℝ)^1024 ≤ (5000000331760953/5000000000000000 : ℝ)^4519 := by
      have hnat : (25000007320448809007 : ℕ)^1024*5000000000000000^4519 ≤ 5000000331760953^4519*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000007320448809007 25000000000000000000 5000000331760953 5000000000000000 1024 4519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000331760953/5000000000000000 : ℝ)) (X := (25000007320448809007/25000000000000000000 : ℝ)) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100239791837952309797/100000000000000000000 : ℝ) ≤ (1000542862302427/1000000000000000 : ℝ) ^ (4519/1024 : ℝ) := by
    have hpowers : (100239791837952309797/100000000000000000000 : ℝ)^1024 ≤ (1000542862302427/1000000000000000 : ℝ)^4519 := by
      have hnat : (100239791837952309797 : ℕ)^1024*1000000000000000^4519 ≤ 1000542862302427^4519*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100239791837952309797 100000000000000000000 1000542862302427 1000000000000000 1024 4519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000542862302427/1000000000000000 : ℝ)) (X := (100239791837952309797/100000000000000000000 : ℝ)) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50239777197054691783/50000000000000000000 : ℝ) ≤ (5005428291263317/5000000000000000 : ℝ) ^ (4519/1024 : ℝ) := by
    have hpowers : (50239777197054691783/50000000000000000000 : ℝ)^1024 ≤ (5005428291263317/5000000000000000 : ℝ)^4519 := by
      have hnat : (50239777197054691783 : ℕ)^1024*5000000000000000^4519 ≤ 5005428291263317^4519*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50239777197054691783 50000000000000000000 5005428291263317 5000000000000000 1024 4519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005428291263317/5000000000000000 : ℝ)) (X := (50239777197054691783/50000000000000000000 : ℝ)) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7320448809007/50000000000000000000 : ℝ) ≤ ((113269662675194729093/113285000000000000000 : ℝ)+2*(1356989875591/566425000000000 : ℝ)*(2827/100000 : ℝ))^(4519/1024 : ℝ) := by
    rw [show (113269662675194729093/113285000000000000000 : ℝ)+2*(1356989875591/566425000000000 : ℝ)*(2827/100000 : ℝ)=(5000000331760953/5000000000000000 : ℝ) by norm_num, show 1+2*(7320448809007/50000000000000000000 : ℝ)=(25000007320448809007/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(239777197054691783/100000000000000000000 : ℝ)+(7320448809007/50000000000000000000 : ℝ) ≤ ((113269662675194729093/113285000000000000000 : ℝ)+(1356989875591/566425000000000 : ℝ)*((6371/25000 : ℝ)+(2827/100000 : ℝ)))^(4519/1024 : ℝ) := by
    rw [show (113269662675194729093/113285000000000000000 : ℝ)+(1356989875591/566425000000000 : ℝ)*((6371/25000 : ℝ)+(2827/100000 : ℝ))=(1000542862302427/1000000000000000 : ℝ) by norm_num, show 1+(239777197054691783/100000000000000000000 : ℝ)+(7320448809007/50000000000000000000 : ℝ)=(100239791837952309797/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(239777197054691783/100000000000000000000 : ℝ) ≤ ((113269662675194729093/113285000000000000000 : ℝ)+2*(1356989875591/566425000000000 : ℝ)*(6371/25000 : ℝ))^(4519/1024 : ℝ) := by
    rw [show (113269662675194729093/113285000000000000000 : ℝ)+2*(1356989875591/566425000000000 : ℝ)*(6371/25000 : ℝ)=(5005428291263317/5000000000000000 : ℝ) by norm_num, show 1+2*(239777197054691783/100000000000000000000 : ℝ)=(50239777197054691783/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (113269662675194729093/113285000000000000000 : ℝ)*(X 1 0+X 2 0)+(1356989875591/566425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4519/1024 : ℝ)) (lo := (2827/100000 : ℝ)) (hi := (6371/25000 : ℝ)) (c := (113269662675194729093/113285000000000000000 : ℝ)) (alpha := (1356989875591/566425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (113269662675194729093/113285000000000000000 : ℝ)*(X 0 1+X 2 1)+(1356989875591/566425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4519/1024 : ℝ)) (lo := (2827/100000 : ℝ)) (hi := (6371/25000 : ℝ)) (c := (113269662675194729093/113285000000000000000 : ℝ)) (alpha := (1356989875591/566425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (113269662675194729093/113285000000000000000 : ℝ)*(X 0 2+X 1 2)+(1356989875591/566425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4519/1024 : ℝ)) (lo := (2827/100000 : ℝ)) (hi := (6371/25000 : ℝ)) (c := (113269662675194729093/113285000000000000000 : ℝ)) (alpha := (1356989875591/566425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-459886819/2500000000 : ℝ)*X 0 0+(2785255837/5000000000 : ℝ)*X 0 1+(5098839469/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2693311113/5000000000 : ℝ)*X 1 0+(-1043956383/5000000000 : ℝ)*X 1 1+(5098838893/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53866217/100000000 : ℝ)*X 2 0+(5098839493/10000000000 : ℝ)*X 2 1+(-2087912681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4249611293/10000000000 : ℝ)*X 0 0+(467905683/1250000000 : ℝ)*X 0 1+(1203200667/2500000000 : ℝ)*X 0 2+(4249611293/10000000000 : ℝ)*X 1 0+(467905683/1250000000 : ℝ)*X 1 1+(1203200667/2500000000 : ℝ)*X 1 2+(4249611293/10000000000 : ℝ)*X 2 0+(467905683/1250000000 : ℝ)*X 2 1+(1203200667/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1839849113/10000000000 : ℝ)*X 0 0+(5104114441/10000000000 : ℝ)*X 0 1+(5565151859/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((328899123/625000000 : ℝ)*X 1 0+(-810799997/5000000000 : ℝ)*X 1 1+(2782576019/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5262385747/10000000000 : ℝ)*X 2 0+(5565152131/10000000000 : ℝ)*X 2 1+(-810800087/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((850059299/2000000000 : ℝ)*X 0 0+(4800841473/10000000000 : ℝ)*X 0 1+(1877699259/5000000000 : ℝ)*X 0 2+(850059299/2000000000 : ℝ)*X 1 0+(4800841473/10000000000 : ℝ)*X 1 1+(1877699259/5000000000 : ℝ)*X 1 2+(850059299/2000000000 : ℝ)*X 2 0+(4800841473/10000000000 : ℝ)*X 2 1+(1877699259/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9728471948036610356958871371/1416062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (381536939/25000000000000 : ℝ)*(base19) + (640855177/50000000000000 : ℝ)*(base23) + (125695693/100000000000000 : ℝ)*(upper3) + (10074991/50000000000000 : ℝ)*(upper4) + (49109393/50000000000000 : ℝ)*(upper5) + (381889379382283/25000000000000 : ℝ)*(major0) + (381889379382283/25000000000000 : ℝ)*(major1) + (381889379382283/25000000000000 : ℝ)*(major2) + (2120127672105369/100000000000000 : ℝ)*(sp0) + (212013687211347/10000000000000 : ℝ)*(sp1) + (265017139568859/12500000000000 : ℝ)*(sp2) + (934971350043689/100000000000000 : ℝ)*(sp3) + (10726155857/100000000000000 : ℝ)*(sp4) + (5057750459/100000000000000 : ℝ)*(sp7) + (233744101948537/25000000000000 : ℝ)*(f.failure) + (1060069199130613/50000000000000 : ℝ)*(f.sum) + (99407967458903/113285000000000000000000000000 : ℝ)*base65 + (14166306163283290681/2832125000000000000000000000000000 : ℝ)*base68 + (9729521206201290681/2832125000000000000000000000000000 : ℝ)*base70 + (12527168097707290681/2832125000000000000000000000000000 : ℝ)*base72 + (141833956474107/113285000000000000000000000000 : ℝ)*base74 + (22909923630989040681/2832125000000000000000000000000000 : ℝ)*base76 + (10185392065739790681/2832125000000000000000000000000000 : ℝ)*base78 + (19247646080185915681/2832125000000000000000000000000000 : ℝ)*base80 + (102538752669911/56642500000000000000000000000 : ℝ)*base82 + (14622773/1250000000000000000000 : ℝ)*base89 + (14622773/1250000000000000000000 : ℝ)*base91 + (14622773/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (552813854182830253619631/56642500000000000000000000000 : ℝ) := by norm_num
    linear_combination (924796679/50000000000000 : ℝ)*(base19) + (957814811/50000000000000 : ℝ)*(base23) + (53090549/20000000000000 : ℝ)*(upper3) + (34450849/50000000000000 : ℝ)*(lower4) + (30463543/20000000000000 : ℝ)*(upper5) + (390693990603511/25000000000000 : ℝ)*(major0) + (390693990603511/25000000000000 : ℝ)*(major1) + (390693990603511/25000000000000 : ℝ)*(major2) + (3182621127/25000000000000 : ℝ)*(sp1) + (13840050367/100000000000000 : ℝ)*(sp2) + (1084509469758977/50000000000000 : ℝ)*(sp4) + (2169004359440089/100000000000000 : ℝ)*(sp5) + (433800636767593/20000000000000 : ℝ)*(sp6) + (59783291249173/6250000000000 : ℝ)*(sp7) + (59783291249173/6250000000000 : ℝ)*(f.failure) + (1084509469758977/50000000000000 : ℝ)*(f.sum) + (368931835555507/56642500000000000000000000000 : ℝ)*base66 + (2467439498151595523/2832125000000000000000000000000000 : ℝ)*base67 + (4861765179011095523/2832125000000000000000000000000000 : ℝ)*base69 + (12629829116135154477/2832125000000000000000000000000000 : ℝ)*base72 + (129571029249533/56642500000000000000000000000 : ℝ)*base73 + (28258929988836404477/2832125000000000000000000000000000 : ℝ)*base76 + (8563237555575470523/2832125000000000000000000000000000 : ℝ)*base77 + (18651783555626404477/2832125000000000000000000000000000 : ℝ)*base80 + (53466421272721/113285000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1426817/312500000000000000000 : ℝ)*base89 + (1426817/312500000000000000000 : ℝ)*base91 + (1426817/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1512_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81689629/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6371/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2827/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2089/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18333/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1512_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1512_s2_0 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-932031527/5000000000 : ℝ)*x 0 + (5457923381/10000000000 : ℝ)*x 1 + (2597773987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (932031527/5000000000 : ℝ)^4521 ≤ (11398169378687/100000000000000 : ℝ)^3497 := by
    have hnat : (932031527 : ℕ)^4521*100000000000000^3497 ≤ 11398169378687^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932031527 5000000000 11398169378687 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457923381/10000000000 : ℝ)^4521 ≤ (1828450313479/4000000000000 : ℝ)^3497 := by
    have hnat : (5457923381 : ℕ)^4521*4000000000000^3497 ≤ 1828450313479^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457923381 10000000000 1828450313479 4000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2597773987/5000000000 : ℝ)^4521 ≤ (10722643193843/25000000000000 : ℝ)^3497 := by
    have hnat : (2597773987 : ℕ)^4521*25000000000000^3497 ≤ 10722643193843^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597773987 5000000000 10722643193843 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-932031527/5000000000 : ℝ), (5457923381/10000000000 : ℝ), (2597773987/5000000000 : ℝ)] ![(11398169378687/100000000000000 : ℝ), (1828450313479/4000000000000 : ℝ), (10722643193843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-932031527/5000000000 : ℝ)|^4521 ≤ (11398169378687/100000000000000 : ℝ)^3497
        have hw : |(-932031527/5000000000 : ℝ)|=(932031527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457923381/10000000000 : ℝ)|^4521 ≤ (1828450313479/4000000000000 : ℝ)^3497
        have hw : |(5457923381/10000000000 : ℝ)|=(5457923381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2597773987/5000000000 : ℝ)|^4521 ≤ (10722643193843/25000000000000 : ℝ)^3497
        have hw : |(2597773987/5000000000 : ℝ)|=(2597773987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s2_1 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071602977/2000000000 : ℝ)*x 0 + (-199912891/1000000000 : ℝ)*x 1 + (324721749/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071602977/2000000000 : ℝ)^4521 ≤ (11158098617473/25000000000000 : ℝ)^3497 := by
    have hnat : (1071602977 : ℕ)^4521*25000000000000^3497 ≤ 11158098617473^3497*2000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071602977 2000000000 11158098617473 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (199912891/1000000000 : ℝ)^4521 ≤ (12477032640217/100000000000000 : ℝ)^3497 := by
    have hnat : (199912891 : ℕ)^4521*100000000000000^3497 ≤ 12477032640217^3497*1000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199912891 1000000000 12477032640217 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (324721749/625000000 : ℝ)^4521 ≤ (21445286441049/50000000000000 : ℝ)^3497 := by
    have hnat : (324721749 : ℕ)^4521*50000000000000^3497 ≤ 21445286441049^3497*625000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324721749 625000000 21445286441049 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071602977/2000000000 : ℝ), (-199912891/1000000000 : ℝ), (324721749/625000000 : ℝ)] ![(11158098617473/25000000000000 : ℝ), (12477032640217/100000000000000 : ℝ), (21445286441049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071602977/2000000000 : ℝ)|^4521 ≤ (11158098617473/25000000000000 : ℝ)^3497
        have hw : |(1071602977/2000000000 : ℝ)|=(1071602977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-199912891/1000000000 : ℝ)|^4521 ≤ (12477032640217/100000000000000 : ℝ)^3497
        have hw : |(-199912891/1000000000 : ℝ)|=(199912891/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(324721749/625000000 : ℝ)|^4521 ≤ (21445286441049/50000000000000 : ℝ)^3497
        have hw : |(324721749/625000000 : ℝ)|=(324721749/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s2_2 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679007279/5000000000 : ℝ)*x 0 + (5195548153/10000000000 : ℝ)*x 1 + (-999564561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679007279/5000000000 : ℝ)^4521 ≤ (892647818967/2000000000000 : ℝ)^3497 := by
    have hnat : (2679007279 : ℕ)^4521*2000000000000^3497 ≤ 892647818967^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679007279 5000000000 892647818967 2000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5195548153/10000000000 : ℝ)^4521 ≤ (10722643671441/25000000000000 : ℝ)^3497 := by
    have hnat : (5195548153 : ℕ)^4521*25000000000000^3497 ≤ 10722643671441^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195548153 10000000000 10722643671441 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (999564561/5000000000 : ℝ)^4521 ≤ (3119258587701/25000000000000 : ℝ)^3497 := by
    have hnat : (999564561 : ℕ)^4521*25000000000000^3497 ≤ 3119258587701^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999564561 5000000000 3119258587701 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679007279/5000000000 : ℝ), (5195548153/10000000000 : ℝ), (-999564561/5000000000 : ℝ)] ![(892647818967/2000000000000 : ℝ), (10722643671441/25000000000000 : ℝ), (3119258587701/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679007279/5000000000 : ℝ)|^4521 ≤ (892647818967/2000000000000 : ℝ)^3497
        have hw : |(2679007279/5000000000 : ℝ)|=(2679007279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5195548153/10000000000 : ℝ)|^4521 ≤ (10722643671441/25000000000000 : ℝ)^3497
        have hw : |(5195548153/10000000000 : ℝ)|=(5195548153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-999564561/5000000000 : ℝ)|^4521 ≤ (3119258587701/25000000000000 : ℝ)^3497
        have hw : |(-999564561/5000000000 : ℝ)|=(999564561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s2_3 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (853442487/2000000000 : ℝ)*x 0 + (3978529031/10000000000 : ℝ)*x 1 + (4573485451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (853442487/2000000000 : ℝ)^4521 ≤ (33253871367441/100000000000000 : ℝ)^3497 := by
    have hnat : (853442487 : ℕ)^4521*100000000000000^3497 ≤ 33253871367441^3497*2000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853442487 2000000000 33253871367441 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3978529031/10000000000 : ℝ)^4521 ≤ (15187361101473/50000000000000 : ℝ)^3497 := by
    have hnat : (3978529031 : ℕ)^4521*50000000000000^3497 ≤ 15187361101473^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3978529031 10000000000 15187361101473 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4573485451/10000000000 : ℝ)^4521 ≤ (9092851606143/25000000000000 : ℝ)^3497 := by
    have hnat : (4573485451 : ℕ)^4521*25000000000000^3497 ≤ 9092851606143^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4573485451 10000000000 9092851606143 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(853442487/2000000000 : ℝ), (3978529031/10000000000 : ℝ), (4573485451/10000000000 : ℝ)] ![(33253871367441/100000000000000 : ℝ), (15187361101473/50000000000000 : ℝ), (9092851606143/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(853442487/2000000000 : ℝ)|^4521 ≤ (33253871367441/100000000000000 : ℝ)^3497
        have hw : |(853442487/2000000000 : ℝ)|=(853442487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3978529031/10000000000 : ℝ)|^4521 ≤ (15187361101473/50000000000000 : ℝ)^3497
        have hw : |(3978529031/10000000000 : ℝ)|=(3978529031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4573485451/10000000000 : ℝ)|^4521 ≤ (9092851606143/25000000000000 : ℝ)^3497
        have hw : |(4573485451/10000000000 : ℝ)|=(4573485451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s2_4 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-58253577/312500000 : ℝ)*x 0 + (5197190163/10000000000 : ℝ)*x 1 + (5456267029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (58253577/312500000 : ℝ)^4521 ≤ (11398575787147/100000000000000 : ℝ)^3497 := by
    have hnat : (58253577 : ℕ)^4521*100000000000000^3497 ≤ 11398575787147^3497*312500000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58253577 312500000 11398575787147 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5197190163/10000000000 : ℝ)^4521 ≤ (2145404998877/5000000000000 : ℝ)^3497 := by
    have hnat : (5197190163 : ℕ)^4521*5000000000000^3497 ≤ 2145404998877^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197190163 10000000000 2145404998877 5000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456267029/10000000000 : ℝ)^4521 ≤ (11423331054381/25000000000000 : ℝ)^3497 := by
    have hnat : (5456267029 : ℕ)^4521*25000000000000^3497 ≤ 11423331054381^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456267029 10000000000 11423331054381 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-58253577/312500000 : ℝ), (5197190163/10000000000 : ℝ), (5456267029/10000000000 : ℝ)] ![(11398575787147/100000000000000 : ℝ), (2145404998877/5000000000000 : ℝ), (11423331054381/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-58253577/312500000 : ℝ)|^4521 ≤ (11398575787147/100000000000000 : ℝ)^3497
        have hw : |(-58253577/312500000 : ℝ)|=(58253577/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5197190163/10000000000 : ℝ)|^4521 ≤ (2145404998877/5000000000000 : ℝ)^3497
        have hw : |(5197190163/10000000000 : ℝ)|=(5197190163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5456267029/10000000000 : ℝ)|^4521 ≤ (11423331054381/25000000000000 : ℝ)^3497
        have hw : |(5456267029/10000000000 : ℝ)|=(5456267029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s2_5 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289119359/10000000000 : ℝ)*x 0 + (-869205091/5000000000 : ℝ)*x 1 + (5456268139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289119359/10000000000 : ℝ)^4521 ≤ (1371620091549/3125000000000 : ℝ)^3497 := by
    have hnat : (5289119359 : ℕ)^4521*3125000000000^3497 ≤ 1371620091549^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289119359 10000000000 1371620091549 3125000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (869205091/5000000000 : ℝ)^4521 ≤ (5207410410907/50000000000000 : ℝ)^3497 := by
    have hnat : (869205091 : ℕ)^4521*50000000000000^3497 ≤ 5207410410907^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869205091 5000000000 5207410410907 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456268139/10000000000 : ℝ)^4521 ≤ (45693336235159/100000000000000 : ℝ)^3497 := by
    have hnat : (5456268139 : ℕ)^4521*100000000000000^3497 ≤ 45693336235159^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456268139 10000000000 45693336235159 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289119359/10000000000 : ℝ), (-869205091/5000000000 : ℝ), (5456268139/10000000000 : ℝ)] ![(1371620091549/3125000000000 : ℝ), (5207410410907/50000000000000 : ℝ), (45693336235159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289119359/10000000000 : ℝ)|^4521 ≤ (1371620091549/3125000000000 : ℝ)^3497
        have hw : |(5289119359/10000000000 : ℝ)|=(5289119359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-869205091/5000000000 : ℝ)|^4521 ≤ (5207410410907/50000000000000 : ℝ)^3497
        have hw : |(-869205091/5000000000 : ℝ)|=(869205091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5456268139/10000000000 : ℝ)|^4521 ≤ (45693336235159/100000000000000 : ℝ)^3497
        have hw : |(5456268139/10000000000 : ℝ)|=(5456268139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s2_6 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289120091/10000000000 : ℝ)*x 0 + (5456267349/10000000000 : ℝ)*x 1 + (-1738410271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289120091/10000000000 : ℝ)^4521 ≤ (10972962695709/25000000000000 : ℝ)^3497 := by
    have hnat : (5289120091 : ℕ)^4521*25000000000000^3497 ≤ 10972962695709^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289120091 10000000000 10972962695709 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5456267349/10000000000 : ℝ)^4521 ≤ (45693327682067/100000000000000 : ℝ)^3497 := by
    have hnat : (5456267349 : ℕ)^4521*100000000000000^3497 ≤ 45693327682067^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456267349 10000000000 45693327682067 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1738410271/10000000000 : ℝ)^4521 ≤ (5207410755573/50000000000000 : ℝ)^3497 := by
    have hnat : (1738410271 : ℕ)^4521*50000000000000^3497 ≤ 5207410755573^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1738410271 10000000000 5207410755573 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289120091/10000000000 : ℝ), (5456267349/10000000000 : ℝ), (-1738410271/10000000000 : ℝ)] ![(10972962695709/25000000000000 : ℝ), (45693327682067/100000000000000 : ℝ), (5207410755573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289120091/10000000000 : ℝ)|^4521 ≤ (10972962695709/25000000000000 : ℝ)^3497
        have hw : |(5289120091/10000000000 : ℝ)|=(5289120091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5456267349/10000000000 : ℝ)|^4521 ≤ (45693327682067/100000000000000 : ℝ)^3497
        have hw : |(5456267349/10000000000 : ℝ)|=(5456267349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1738410271/10000000000 : ℝ)|^4521 ≤ (5207410755573/50000000000000 : ℝ)^3497
        have hw : |(-1738410271/10000000000 : ℝ)|=(1738410271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s2_7 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4267331271/10000000000 : ℝ)*x 0 + (2284882607/5000000000 : ℝ)*x 1 + (1991140973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4267331271/10000000000 : ℝ)^4521 ≤ (3325506862233/10000000000000 : ℝ)^3497 := by
    have hnat : (4267331271 : ℕ)^4521*10000000000000^3497 ≤ 3325506862233^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4267331271 10000000000 3325506862233 10000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2284882607/5000000000 : ℝ)^4521 ≤ (18166580893939/50000000000000 : ℝ)^3497 := by
    have hnat : (2284882607 : ℕ)^4521*50000000000000^3497 ≤ 18166580893939^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284882607 5000000000 18166580893939 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1991140973/5000000000 : ℝ)^4521 ≤ (15205884785011/50000000000000 : ℝ)^3497 := by
    have hnat : (1991140973 : ℕ)^4521*50000000000000^3497 ≤ 15205884785011^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991140973 5000000000 15205884785011 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4267331271/10000000000 : ℝ), (2284882607/5000000000 : ℝ), (1991140973/5000000000 : ℝ)] ![(3325506862233/10000000000000 : ℝ), (18166580893939/50000000000000 : ℝ), (15205884785011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4267331271/10000000000 : ℝ)|^4521 ≤ (3325506862233/10000000000000 : ℝ)^3497
        have hw : |(4267331271/10000000000 : ℝ)|=(4267331271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2284882607/5000000000 : ℝ)|^4521 ≤ (18166580893939/50000000000000 : ℝ)^3497
        have hw : |(2284882607/5000000000 : ℝ)|=(2284882607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1991140973/5000000000 : ℝ)|^4521 ≤ (15205884785011/50000000000000 : ℝ)^3497
        have hw : |(1991140973/5000000000 : ℝ)|=(1991140973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1512_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81689629/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18333/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2089/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10443/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3999/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18333/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2089/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18333/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2089/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18333/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2089/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18333/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2089/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18333/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2089/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18333/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2089/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (2089/25000 : ℝ) ^ (4519/1024 : ℝ) ≤ (1748583744094341/100000000000000000000 : ℝ) := by
    have hpowers : (2089/25000 : ℝ)^4519 ≤ (1748583744094341/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2089 : ℕ)^4519*100000000000000000000^1024 ≤ 1748583744094341^1024*25000^4519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2089 25000 1748583744094341 100000000000000000000 4519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2089/25000 : ℝ)) (X := (1748583744094341/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18333/100000 : ℝ) ^ (4519/1024 : ℝ) ≤ (28025688693655833/50000000000000000000 : ℝ) := by
    have hpowers : (18333/100000 : ℝ)^4519 ≤ (28025688693655833/50000000000000000000 : ℝ)^1024 := by
      have hnat : (18333 : ℕ)^4519*50000000000000000000^1024 ≤ 28025688693655833^1024*100000^4519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18333 100000 28025688693655833 50000000000000000000 4519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18333/100000 : ℝ)) (X := (28025688693655833/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001748583744094341/50000000000000000000 : ℝ) ≤ (10000079244325729/10000000000000000 : ℝ) ^ (4519/1024 : ℝ) := by
    have hpowers : (50001748583744094341/50000000000000000000 : ℝ)^1024 ≤ (10000079244325729/10000000000000000 : ℝ)^4519 := by
      have hnat : (50001748583744094341 : ℕ)^1024*10000000000000000^4519 ≤ 10000079244325729^4519*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001748583744094341 50000000000000000000 10000079244325729 10000000000000000 1024 4519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000079244325729/10000000000000000 : ℝ)) (X := (50001748583744094341/50000000000000000000 : ℝ)) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100057799961131406007/100000000000000000000 : ℝ) ≤ (10001309447568693/10000000000000000 : ℝ) ^ (4519/1024 : ℝ) := by
    have hpowers : (100057799961131406007/100000000000000000000 : ℝ)^1024 ≤ (10001309447568693/10000000000000000 : ℝ)^4519 := by
      have hnat : (100057799961131406007 : ℕ)^1024*10000000000000000^4519 ≤ 10001309447568693^4519*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100057799961131406007 100000000000000000000 10001309447568693 10000000000000000 1024 4519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001309447568693/10000000000000000 : ℝ)) (X := (100057799961131406007/100000000000000000000 : ℝ)) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25028025688693655833/25000000000000000000 : ℝ) ≤ (10002539650811657/10000000000000000 : ℝ) ^ (4519/1024 : ℝ) := by
    have hpowers : (25028025688693655833/25000000000000000000 : ℝ)^1024 ≤ (10002539650811657/10000000000000000 : ℝ)^4519 := by
      have hnat : (25028025688693655833 : ℕ)^1024*10000000000000000^4519 ≤ 10002539650811657^4519*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25028025688693655833 25000000000000000000 10002539650811657 10000000000000000 1024 4519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002539650811657/10000000000000000 : ℝ)) (X := (25028025688693655833/25000000000000000000 : ℝ)) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1748583744094341/100000000000000000000 : ℝ) ≤ ((19950046292808276773/19954000000000000000 : ℝ)+2*(307550810741/249425000000000 : ℝ)*(2089/25000 : ℝ))^(4519/1024 : ℝ) := by
    rw [show (19950046292808276773/19954000000000000000 : ℝ)+2*(307550810741/249425000000000 : ℝ)*(2089/25000 : ℝ)=(10000079244325729/10000000000000000 : ℝ) by norm_num, show 1+2*(1748583744094341/100000000000000000000 : ℝ)=(50001748583744094341/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28025688693655833/50000000000000000000 : ℝ)+(1748583744094341/100000000000000000000 : ℝ) ≤ ((19950046292808276773/19954000000000000000 : ℝ)+(307550810741/249425000000000 : ℝ)*((18333/100000 : ℝ)+(2089/25000 : ℝ)))^(4519/1024 : ℝ) := by
    rw [show (19950046292808276773/19954000000000000000 : ℝ)+(307550810741/249425000000000 : ℝ)*((18333/100000 : ℝ)+(2089/25000 : ℝ))=(10001309447568693/10000000000000000 : ℝ) by norm_num, show 1+(28025688693655833/50000000000000000000 : ℝ)+(1748583744094341/100000000000000000000 : ℝ)=(100057799961131406007/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28025688693655833/50000000000000000000 : ℝ) ≤ ((19950046292808276773/19954000000000000000 : ℝ)+2*(307550810741/249425000000000 : ℝ)*(18333/100000 : ℝ))^(4519/1024 : ℝ) := by
    rw [show (19950046292808276773/19954000000000000000 : ℝ)+2*(307550810741/249425000000000 : ℝ)*(18333/100000 : ℝ)=(10002539650811657/10000000000000000 : ℝ) by norm_num, show 1+2*(28025688693655833/50000000000000000000 : ℝ)=(25028025688693655833/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19950046292808276773/19954000000000000000 : ℝ)*(X 1 0+X 2 0)+(307550810741/249425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4519/1024 : ℝ)) (lo := (2089/25000 : ℝ)) (hi := (18333/100000 : ℝ)) (c := (19950046292808276773/19954000000000000000 : ℝ)) (alpha := (307550810741/249425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19950046292808276773/19954000000000000000 : ℝ)*(X 0 1+X 2 1)+(307550810741/249425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4519/1024 : ℝ)) (lo := (2089/25000 : ℝ)) (hi := (18333/100000 : ℝ)) (c := (19950046292808276773/19954000000000000000 : ℝ)) (alpha := (307550810741/249425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19950046292808276773/19954000000000000000 : ℝ)*(X 0 2+X 1 2)+(307550810741/249425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4519/1024 : ℝ)) (lo := (2089/25000 : ℝ)) (hi := (18333/100000 : ℝ)) (c := (19950046292808276773/19954000000000000000 : ℝ)) (alpha := (307550810741/249425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-932031527/5000000000 : ℝ)*X 0 0+(5457923381/10000000000 : ℝ)*X 0 1+(2597773987/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071602977/2000000000 : ℝ)*X 1 0+(-199912891/1000000000 : ℝ)*X 1 1+(324721749/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2679007279/5000000000 : ℝ)*X 2 0+(5195548153/10000000000 : ℝ)*X 2 1+(-999564561/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((853442487/2000000000 : ℝ)*X 0 0+(3978529031/10000000000 : ℝ)*X 0 1+(4573485451/10000000000 : ℝ)*X 0 2+(853442487/2000000000 : ℝ)*X 1 0+(3978529031/10000000000 : ℝ)*X 1 1+(4573485451/10000000000 : ℝ)*X 1 2+(853442487/2000000000 : ℝ)*X 2 0+(3978529031/10000000000 : ℝ)*X 2 1+(4573485451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-58253577/312500000 : ℝ)*X 0 0+(5197190163/10000000000 : ℝ)*X 0 1+(5456267029/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289119359/10000000000 : ℝ)*X 1 0+(-869205091/5000000000 : ℝ)*X 1 1+(5456268139/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289120091/10000000000 : ℝ)*X 2 0+(5456267349/10000000000 : ℝ)*X 2 1+(-1738410271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4267331271/10000000000 : ℝ)*X 0 0+(2284882607/5000000000 : ℝ)*X 0 1+(1991140973/5000000000 : ℝ)*X 0 2+(4267331271/10000000000 : ℝ)*X 1 0+(2284882607/5000000000 : ℝ)*X 1 1+(1991140973/5000000000 : ℝ)*X 1 2+(4267331271/10000000000 : ℝ)*X 2 0+(2284882607/5000000000 : ℝ)*X 2 1+(1991140973/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1278480365294900106956994897/498850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (606509449/100000000000000 : ℝ)*(base19) + (51480041/12500000000000 : ℝ)*(base23) + (1760537/3125000000000 : ℝ)*(upper3) + (4286431/12500000000000 : ℝ)*(lower4) + (1373038214033579/50000000000000 : ℝ)*(major0) + (1373038214033579/50000000000000 : ℝ)*(major1) + (1373038214033579/50000000000000 : ℝ)*(major2) + (952836229716011/25000000000000 : ℝ)*(sp0) + (952838368568759/25000000000000 : ℝ)*(sp1) + (14888092351753/390625000000 : ℝ)*(sp2) + (26262454873077/1562500000000 : ℝ)*(sp3) + (4580960221/50000000000000 : ℝ)*(sp4) + (202689539/10000000000000 : ℝ)*(sp6) + (789022191/50000000000000 : ℝ)*(sp7) + (168079868992131/10000000000000 : ℝ)*(f.failure) + (1905677040392243/50000000000000 : ℝ)*(f.sum) + (115227687068091/24942500000000000000000000000 : ℝ)*base65 + (4448112349760680567/997700000000000000000000000000000 : ℝ)*base67 + (5959022996131080567/997700000000000000000000000000000 : ℝ)*base69 + (10866186014453480567/997700000000000000000000000000000 : ℝ)*base71 + (1079571889563/12471250000000000000000000000 : ℝ)*base73 + (5001257185756080567/997700000000000000000000000000000 : ℝ)*base75 + (4857703209053680567/997700000000000000000000000000000 : ℝ)*base77 + (3495187325909880567/997700000000000000000000000000000 : ℝ)*base79 + (110299952585211/24942500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (4690601/500000000000000000000 : ℝ)*base90 + (4690601/500000000000000000000 : ℝ)*base92 + (4690601/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101884213530723732219773367/62356250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1266943/1250000000000 : ℝ)*(base8) + (185216203/25000000000000 : ℝ)*(base15) + (63775729/50000000000000 : ℝ)*(lower2) + (101646909/50000000000000 : ℝ)*(lower4) + (347627500082607/12500000000000 : ℝ)*(major0) + (347627500082607/12500000000000 : ℝ)*(major1) + (347627500082607/12500000000000 : ℝ)*(major2) + (609927807/20000000000000 : ℝ)*(sp1) + (26624963/1562500000000 : ℝ)*(sp2) + (6331008357/100000000000000 : ℝ)*(sp3) + (3859853145241901/100000000000000 : ℝ)*(sp4) + (1929924728046747/50000000000000 : ℝ)*(sp5) + (964962885649927/25000000000000 : ℝ)*(sp6) + (170218036925249/10000000000000 : ℝ)*(sp7) + (1702186700260847/100000000000000 : ℝ)*(f.failure) + (192992662329867/5000000000000 : ℝ)*(f.sum) + (521748998639599/49885000000000000000000000000 : ℝ)*base65 + (3658542192366597211/249425000000000000000000000000000 : ℝ)*base67 + (4140574241326047211/249425000000000000000000000000000 : ℝ)*base69 + (2826234509095797211/249425000000000000000000000000000 : ℝ)*base71 + (69311385958381/49885000000000000000000000000 : ℝ)*base74 + (419852840362177789/249425000000000000000000000000000 : ℝ)*base76 + (4330099205759522211/249425000000000000000000000000000 : ℝ)*base77 + (3444363956673472211/249425000000000000000000000000000 : ℝ)*base79 + (218765968281691/49885000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (5344237/5000000000000000000000 : ℝ)*base90 + (5344237/5000000000000000000000 : ℝ)*base92 + (5344237/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1512_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81689629/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18333/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2089/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10443/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3999/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1512_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1512_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81689629/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10443/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3999/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1512_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1512_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1512_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81689629/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10443/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3999/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1512_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

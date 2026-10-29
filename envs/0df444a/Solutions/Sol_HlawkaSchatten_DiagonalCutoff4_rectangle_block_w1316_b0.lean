-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1316_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:41:42.548694+00:00
-- url     : https://prove2.me/submissions/05030af3-813e-48f7-b10d-1d6cf5864b99

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
theorem support_rectangle_w1316_s0_0 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1824616869/10000000000 : ℝ)*x 0 + (1201644433/2000000000 : ℝ)*x 1 + (4804667849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1824616869/10000000000 : ℝ)^1069 ≤ (10678914260717/100000000000000 : ℝ)^813 := by
    have hnat : (1824616869 : ℕ)^1069*100000000000000^813 ≤ 10678914260717^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824616869 10000000000 10678914260717 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1201644433/2000000000 : ℝ)^1069 ≤ (5117723540617/10000000000000 : ℝ)^813 := by
    have hnat : (1201644433 : ℕ)^1069*10000000000000^813 ≤ 5117723540617^813*2000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1201644433 2000000000 5117723540617 10000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4804667849/10000000000 : ℝ)^1069 ≤ (38143850309211/100000000000000 : ℝ)^813 := by
    have hnat : (4804667849 : ℕ)^1069*100000000000000^813 ≤ 38143850309211^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4804667849 10000000000 38143850309211 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1824616869/10000000000 : ℝ), (1201644433/2000000000 : ℝ), (4804667849/10000000000 : ℝ)] ![(10678914260717/100000000000000 : ℝ), (5117723540617/10000000000000 : ℝ), (38143850309211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1824616869/10000000000 : ℝ)|^1069 ≤ (10678914260717/100000000000000 : ℝ)^813
        have hw : |(-1824616869/10000000000 : ℝ)|=(1824616869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1201644433/2000000000 : ℝ)|^1069 ≤ (5117723540617/10000000000000 : ℝ)^813
        have hw : |(1201644433/2000000000 : ℝ)|=(1201644433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4804667849/10000000000 : ℝ)|^1069 ≤ (38143850309211/100000000000000 : ℝ)^813
        have hw : |(4804667849/10000000000 : ℝ)|=(4804667849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s0_1 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (86011353/156250000 : ℝ)*x 0 + (-156875929/625000000 : ℝ)*x 1 + (2402333941/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86011353/156250000 : ℝ)^1069 ≤ (5701745441429/12500000000000 : ℝ)^813 := by
    have hnat : (86011353 : ℕ)^1069*12500000000000^813 ≤ 5701745441429^813*156250000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86011353 156250000 5701745441429 12500000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156875929/625000000 : ℝ)^1069 ≤ (16242185800903/100000000000000 : ℝ)^813 := by
    have hnat : (156875929 : ℕ)^1069*100000000000000^813 ≤ 16242185800903^813*625000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156875929 625000000 16242185800903 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2402333941/5000000000 : ℝ)^1069 ≤ (38143850653689/100000000000000 : ℝ)^813 := by
    have hnat : (2402333941 : ℕ)^1069*100000000000000^813 ≤ 38143850653689^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2402333941 5000000000 38143850653689 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86011353/156250000 : ℝ), (-156875929/625000000 : ℝ), (2402333941/5000000000 : ℝ)] ![(5701745441429/12500000000000 : ℝ), (16242185800903/100000000000000 : ℝ), (38143850653689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86011353/156250000 : ℝ)|^1069 ≤ (5701745441429/12500000000000 : ℝ)^813
        have hw : |(86011353/156250000 : ℝ)|=(86011353/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-156875929/625000000 : ℝ)|^1069 ≤ (16242185800903/100000000000000 : ℝ)^813
        have hw : |(-156875929/625000000 : ℝ)|=(156875929/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2402333941/5000000000 : ℝ)|^1069 ≤ (38143850653689/100000000000000 : ℝ)^813
        have hw : |(2402333941/5000000000 : ℝ)|=(2402333941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s0_2 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5504725823/10000000000 : ℝ)*x 0 + (960933681/2000000000 : ℝ)*x 1 + (-2510015207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5504725823/10000000000 : ℝ)^1069 ≤ (45613955152753/100000000000000 : ℝ)^813 := by
    have hnat : (5504725823 : ℕ)^1069*100000000000000^813 ≤ 45613955152753^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504725823 10000000000 45613955152753 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (960933681/2000000000 : ℝ)^1069 ≤ (38143856113153/100000000000000 : ℝ)^813 := by
    have hnat : (960933681 : ℕ)^1069*100000000000000^813 ≤ 38143856113153^813*2000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960933681 2000000000 38143856113153 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2510015207/10000000000 : ℝ)^1069 ≤ (8121094359667/50000000000000 : ℝ)^813 := by
    have hnat : (2510015207 : ℕ)^1069*50000000000000^813 ≤ 8121094359667^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510015207 10000000000 8121094359667 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5504725823/10000000000 : ℝ), (960933681/2000000000 : ℝ), (-2510015207/10000000000 : ℝ)] ![(45613955152753/100000000000000 : ℝ), (38143856113153/100000000000000 : ℝ), (8121094359667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5504725823/10000000000 : ℝ)|^1069 ≤ (45613955152753/100000000000000 : ℝ)^813
        have hw : |(5504725823/10000000000 : ℝ)|=(5504725823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(960933681/2000000000 : ℝ)|^1069 ≤ (38143856113153/100000000000000 : ℝ)^813
        have hw : |(960933681/2000000000 : ℝ)|=(960933681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2510015207/10000000000 : ℝ)|^1069 ≤ (8121094359667/50000000000000 : ℝ)^813
        have hw : |(-2510015207/10000000000 : ℝ)|=(2510015207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s0_3 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4182665537/10000000000 : ℝ)*x 0 + (38849487/125000000 : ℝ)*x 1 + (5604250881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4182665537/10000000000 : ℝ)^1069 ≤ (15893703776343/50000000000000 : ℝ)^813 := by
    have hnat : (4182665537 : ℕ)^1069*50000000000000^813 ≤ 15893703776343^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4182665537 10000000000 15893703776343 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38849487/125000000 : ℝ)^1069 ≤ (4302236571069/20000000000000 : ℝ)^813 := by
    have hnat : (38849487 : ℕ)^1069*20000000000000^813 ≤ 4302236571069^813*125000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38849487 125000000 4302236571069 20000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5604250881/10000000000 : ℝ)^1069 ≤ (46701409573893/100000000000000 : ℝ)^813 := by
    have hnat : (5604250881 : ℕ)^1069*100000000000000^813 ≤ 46701409573893^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5604250881 10000000000 46701409573893 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4182665537/10000000000 : ℝ), (38849487/125000000 : ℝ), (5604250881/10000000000 : ℝ)] ![(15893703776343/50000000000000 : ℝ), (4302236571069/20000000000000 : ℝ), (46701409573893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4182665537/10000000000 : ℝ)|^1069 ≤ (15893703776343/50000000000000 : ℝ)^813
        have hw : |(4182665537/10000000000 : ℝ)|=(4182665537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(38849487/125000000 : ℝ)|^1069 ≤ (4302236571069/20000000000000 : ℝ)^813
        have hw : |(38849487/125000000 : ℝ)|=(38849487/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5604250881/10000000000 : ℝ)|^1069 ≤ (46701409573893/100000000000000 : ℝ)^813
        have hw : |(5604250881/10000000000 : ℝ)|=(5604250881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s0_4 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-228651439/1250000000 : ℝ)*x 0 + (2417845077/5000000000 : ℝ)*x 1 + (5976093723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (228651439/1250000000 : ℝ)^1069 ≤ (5357143406359/50000000000000 : ℝ)^813 := by
    have hnat : (228651439 : ℕ)^1069*50000000000000^813 ≤ 5357143406359^813*1250000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228651439 1250000000 5357143406359 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2417845077/5000000000 : ℝ)^1069 ≤ (7693602594697/20000000000000 : ℝ)^813 := by
    have hnat : (2417845077 : ℕ)^1069*20000000000000^813 ≤ 7693602594697^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417845077 5000000000 7693602594697 20000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5976093723/10000000000 : ℝ)^1069 ≤ (10163540039361/20000000000000 : ℝ)^813 := by
    have hnat : (5976093723 : ℕ)^1069*20000000000000^813 ≤ 10163540039361^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5976093723 10000000000 10163540039361 20000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-228651439/1250000000 : ℝ), (2417845077/5000000000 : ℝ), (5976093723/10000000000 : ℝ)] ![(5357143406359/50000000000000 : ℝ), (7693602594697/20000000000000 : ℝ), (10163540039361/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-228651439/1250000000 : ℝ)|^1069 ≤ (5357143406359/50000000000000 : ℝ)^813
        have hw : |(-228651439/1250000000 : ℝ)|=(228651439/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2417845077/5000000000 : ℝ)|^1069 ≤ (7693602594697/20000000000000 : ℝ)^813
        have hw : |(2417845077/5000000000 : ℝ)|=(2417845077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5976093723/10000000000 : ℝ)|^1069 ≤ (10163540039361/20000000000000 : ℝ)^813
        have hw : |(5976093723/10000000000 : ℝ)|=(5976093723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s0_5 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2588446741/5000000000 : ℝ)*x 0 + (-66929493/500000000 : ℝ)*x 1 + (1494023417/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2588446741/5000000000 : ℝ)^1069 ≤ (42076000123623/100000000000000 : ℝ)^813 := by
    have hnat : (2588446741 : ℕ)^1069*100000000000000^813 ≤ 42076000123623^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588446741 5000000000 42076000123623 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66929493/500000000 : ℝ)^1069 ≤ (7106300287471/100000000000000 : ℝ)^813 := by
    have hnat : (66929493 : ℕ)^1069*100000000000000^813 ≤ 7106300287471^813*500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66929493 500000000 7106300287471 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1494023417/2500000000 : ℝ)^1069 ≤ (12704424895461/25000000000000 : ℝ)^813 := by
    have hnat : (1494023417 : ℕ)^1069*25000000000000^813 ≤ 12704424895461^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1494023417 2500000000 12704424895461 25000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2588446741/5000000000 : ℝ), (-66929493/500000000 : ℝ), (1494023417/2500000000 : ℝ)] ![(42076000123623/100000000000000 : ℝ), (7106300287471/100000000000000 : ℝ), (12704424895461/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2588446741/5000000000 : ℝ)|^1069 ≤ (42076000123623/100000000000000 : ℝ)^813
        have hw : |(2588446741/5000000000 : ℝ)|=(2588446741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-66929493/500000000 : ℝ)|^1069 ≤ (7106300287471/100000000000000 : ℝ)^813
        have hw : |(-66929493/500000000 : ℝ)|=(66929493/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1494023417/2500000000 : ℝ)|^1069 ≤ (12704424895461/25000000000000 : ℝ)^813
        have hw : |(1494023417/2500000000 : ℝ)|=(1494023417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s0_6 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2588446747/5000000000 : ℝ)*x 0 + (59760937/100000000 : ℝ)*x 1 + (-1338589789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2588446747/5000000000 : ℝ)^1069 ≤ (21038000125933/50000000000000 : ℝ)^813 := by
    have hnat : (2588446747 : ℕ)^1069*50000000000000^813 ≤ 21038000125933^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588446747 5000000000 21038000125933 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (59760937/100000000 : ℝ)^1069 ≤ (50817699939639/100000000000000 : ℝ)^813 := by
    have hnat : (59760937 : ℕ)^1069*100000000000000^813 ≤ 50817699939639^813*100000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59760937 100000000 50817699939639 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1338589789/10000000000 : ℝ)^1069 ≤ (7106299791859/100000000000000 : ℝ)^813 := by
    have hnat : (1338589789 : ℕ)^1069*100000000000000^813 ≤ 7106299791859^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338589789 10000000000 7106299791859 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2588446747/5000000000 : ℝ), (59760937/100000000 : ℝ), (-1338589789/10000000000 : ℝ)] ![(21038000125933/50000000000000 : ℝ), (50817699939639/100000000000000 : ℝ), (7106299791859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2588446747/5000000000 : ℝ)|^1069 ≤ (21038000125933/50000000000000 : ℝ)^813
        have hw : |(2588446747/5000000000 : ℝ)|=(2588446747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(59760937/100000000 : ℝ)|^1069 ≤ (50817699939639/100000000000000 : ℝ)^813
        have hw : |(59760937/100000000 : ℝ)|=(59760937/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1338589789/10000000000 : ℝ)|^1069 ≤ (7106299791859/100000000000000 : ℝ)^813
        have hw : |(-1338589789/10000000000 : ℝ)|=(1338589789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s0_7 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2096097347/5000000000 : ℝ)*x 0 + (1384977013/2500000000 : ℝ)*x 1 + (3174595903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096097347/5000000000 : ℝ)^1069 ≤ (6376533015073/20000000000000 : ℝ)^813 := by
    have hnat : (2096097347 : ℕ)^1069*20000000000000^813 ≤ 6376533015073^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096097347 5000000000 6376533015073 20000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1384977013/2500000000 : ℝ)^1069 ≤ (22998835044247/50000000000000 : ℝ)^813 := by
    have hnat : (1384977013 : ℕ)^1069*50000000000000^813 ≤ 22998835044247^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1384977013 2500000000 22998835044247 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3174595903/10000000000 : ℝ)^1069 ≤ (11059832413009/50000000000000 : ℝ)^813 := by
    have hnat : (3174595903 : ℕ)^1069*50000000000000^813 ≤ 11059832413009^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3174595903 10000000000 11059832413009 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2096097347/5000000000 : ℝ), (1384977013/2500000000 : ℝ), (3174595903/10000000000 : ℝ)] ![(6376533015073/20000000000000 : ℝ), (22998835044247/50000000000000 : ℝ), (11059832413009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2096097347/5000000000 : ℝ)|^1069 ≤ (6376533015073/20000000000000 : ℝ)^813
        have hw : |(2096097347/5000000000 : ℝ)|=(2096097347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1384977013/2500000000 : ℝ)|^1069 ≤ (22998835044247/50000000000000 : ℝ)^813
        have hw : |(1384977013/2500000000 : ℝ)|=(1384977013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3174595903/10000000000 : ℝ)|^1069 ≤ (11059832413009/50000000000000 : ℝ)^813
        have hw : |(3174595903/10000000000 : ℝ)|=(3174595903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1316_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76852523/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1217/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27059/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4275/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4275 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4275*1^1024 ≤ 0^1024*1^4275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4275 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4275/1024 : ℝ) ≤ (2181113101364812361/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4275 ≤ (2181113101364812361/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4275*100000000000000000000^1024 ≤ 2181113101364812361^1024*5^4275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2181113101364812361 100000000000000000000 4275 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2181113101364812361/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4275/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4275 := by
      have hnat : (1 : ℕ)^1024*1^4275 ≤ 1^4275*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102181113101364812361/100000000000000000000 : ℝ) ≤ (10051816855204179/10000000000000000 : ℝ) ^ (4275/1024 : ℝ) := by
    have hpowers : (102181113101364812361/100000000000000000000 : ℝ)^1024 ≤ (10051816855204179/10000000000000000 : ℝ)^4275 := by
      have hnat : (102181113101364812361 : ℕ)^1024*10000000000000000^4275 ≤ 10051816855204179^4275*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102181113101364812361 100000000000000000000 10051816855204179 10000000000000000 1024 4275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10051816855204179/10000000000000000 : ℝ)) (X := (102181113101364812361/100000000000000000000 : ℝ)) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52181113101364812361/50000000000000000000 : ℝ) ≤ (5051816855204179/5000000000000000 : ℝ) ^ (4275/1024 : ℝ) := by
    have hpowers : (52181113101364812361/50000000000000000000 : ℝ)^1024 ≤ (5051816855204179/5000000000000000 : ℝ)^4275 := by
      have hnat : (52181113101364812361 : ℕ)^1024*5000000000000000^4275 ≤ 5051816855204179^4275*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52181113101364812361 50000000000000000000 5051816855204179 5000000000000000 1024 4275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5051816855204179/5000000000000000 : ℝ)) (X := (52181113101364812361/50000000000000000000 : ℝ)) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(51816855204179/4000000000000000 : ℝ)*(0 : ℝ))^(4275/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(51816855204179/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2181113101364812361/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(51816855204179/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4275/1024 : ℝ) := by
    rw [show (1 : ℝ)+(51816855204179/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10051816855204179/10000000000000000 : ℝ) by norm_num, show 1+(2181113101364812361/100000000000000000000 : ℝ)+(0 : ℝ)=(102181113101364812361/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2181113101364812361/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(51816855204179/4000000000000000 : ℝ)*(2/5 : ℝ))^(4275/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(51816855204179/4000000000000000 : ℝ)*(2/5 : ℝ)=(5051816855204179/5000000000000000 : ℝ) by norm_num, show 1+2*(2181113101364812361/100000000000000000000 : ℝ)=(52181113101364812361/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(51816855204179/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4275/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (51816855204179/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(51816855204179/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4275/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (51816855204179/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(51816855204179/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4275/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (51816855204179/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1824616869/10000000000 : ℝ)*X 0 0+(1201644433/2000000000 : ℝ)*X 0 1+(4804667849/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((86011353/156250000 : ℝ)*X 1 0+(-156875929/625000000 : ℝ)*X 1 1+(2402333941/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5504725823/10000000000 : ℝ)*X 2 0+(960933681/2000000000 : ℝ)*X 2 1+(-2510015207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4182665537/10000000000 : ℝ)*X 0 0+(38849487/125000000 : ℝ)*X 0 1+(5604250881/10000000000 : ℝ)*X 0 2+(4182665537/10000000000 : ℝ)*X 1 0+(38849487/125000000 : ℝ)*X 1 1+(5604250881/10000000000 : ℝ)*X 1 2+(4182665537/10000000000 : ℝ)*X 2 0+(38849487/125000000 : ℝ)*X 2 1+(5604250881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-228651439/1250000000 : ℝ)*X 0 0+(2417845077/5000000000 : ℝ)*X 0 1+(5976093723/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2588446741/5000000000 : ℝ)*X 1 0+(-66929493/500000000 : ℝ)*X 1 1+(1494023417/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2588446747/5000000000 : ℝ)*X 2 0+(59760937/100000000 : ℝ)*X 2 1+(-1338589789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2096097347/5000000000 : ℝ)*X 0 0+(1384977013/2500000000 : ℝ)*X 0 1+(3174595903/10000000000 : ℝ)*X 0 2+(2096097347/5000000000 : ℝ)*X 1 0+(1384977013/2500000000 : ℝ)*X 1 1+(3174595903/10000000000 : ℝ)*X 1 2+(2096097347/5000000000 : ℝ)*X 2 0+(1384977013/2500000000 : ℝ)*X 2 1+(3174595903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6631664049003711009/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (94514863/100000000000000 : ℝ)*(base1) + (843219641/50000000000000 : ℝ)*(base19) + (785183349/50000000000000 : ℝ)*(base23) + (2991009/1250000000000 : ℝ)*(upper3) + (28785977/25000000000000 : ℝ)*(upper5) + (615741240388979/100000000000000 : ℝ)*(major0) + (615741240388979/100000000000000 : ℝ)*(major1) + (615741240388979/100000000000000 : ℝ)*(major2) + (166175609083689/20000000000000 : ℝ)*(sp0) + (41544066850513/5000000000000 : ℝ)*(sp1) + (207720363270711/25000000000000 : ℝ)*(sp2) + (200298227067213/50000000000000 : ℝ)*(sp3) + (126813649/2500000000000 : ℝ)*(sp4) + (335952957/12500000000000 : ℝ)*(sp7) + (80119847254589/20000000000000 : ℝ)*(f.failure) + (415441511724771/50000000000000 : ℝ)*(f.sum) + (71981133856759/200000000000000000000000000000 : ℝ)*base66 + (54656108456759/400000000000000000000000000000 : ℝ)*base68 + (210635397256759/400000000000000000000000000000 : ℝ)*base70 + (1479394352056759/400000000000000000000000000000 : ℝ)*base72 + (293016339943241/200000000000000000000000000000 : ℝ)*base73 + (390010428743241/400000000000000000000000000000 : ℝ)*base75 + (2409893028856759/400000000000000000000000000000 : ℝ)*base78 + (752930869543241/400000000000000000000000000000 : ℝ)*base79 + (364042033143241/200000000000000000000000000000 : ℝ)*base81 + (2021953/1000000000000000000000 : ℝ)*base90 + (2021953/1000000000000000000000 : ℝ)*base92 + (2021953/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3467273005959249267231/1562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (531586061/100000000000000 : ℝ)*(base19) + (539629753/100000000000000 : ℝ)*(base23) + (6478809/50000000000000 : ℝ)*(base32) + (17854443/25000000000000 : ℝ)*(upper3) + (7074237/12500000000000 : ℝ)*(upper5) + (40614366632599/6250000000000 : ℝ)*(major0) + (40614366632599/6250000000000 : ℝ)*(major1) + (40614366632599/6250000000000 : ℝ)*(major2) + (1175188621/100000000000000 : ℝ)*(sp1) + (6350571/500000000000 : ℝ)*(sp2) + (175376494727823/20000000000000 : ℝ)*(sp4) + (438440383432217/50000000000000 : ℝ)*(sp5) + (438440331947581/50000000000000 : ℝ)*(sp6) + (26423573229871/6250000000000 : ℝ)*(sp7) + (211388592317777/50000000000000 : ℝ)*(f.failure) + (175376494727823/20000000000000 : ℝ)*(f.sum) + (12863576131221/12500000000000000000000000000 : ℝ)*base65 + (97622962881221/25000000000000000000000000000 : ℝ)*base67 + (136924038606221/25000000000000000000000000000 : ℝ)*base69 + (2649187668779/25000000000000000000000000000 : ℝ)*base72 + (47215336331221/12500000000000000000000000000 : ℝ)*base73 + (181415948618779/25000000000000000000000000000 : ℝ)*base76 + (68147467131221/25000000000000000000000000000 : ℝ)*base77 + (107229045631221/25000000000000000000000000000 : ℝ)*base79 + (48736372556221/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (19798629/2500000000000000000000 : ℝ)*base90 + (19798629/2500000000000000000000 : ℝ)*base92 + (19798629/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1316_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76852523/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1217/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27059/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1316_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1316_s1_0 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2013192413/10000000000 : ℝ)*x 0 + (5653992907/10000000000 : ℝ)*x 1 + (629769291/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2013192413/10000000000 : ℝ)^1069 ≤ (303829892731/2500000000000 : ℝ)^813 := by
    have hnat : (2013192413 : ℕ)^1069*2500000000000^813 ≤ 303829892731^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013192413 10000000000 303829892731 2500000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5653992907/10000000000 : ℝ)^1069 ≤ (47247202989359/100000000000000 : ℝ)^813 := by
    have hnat : (5653992907 : ℕ)^1069*100000000000000^813 ≤ 47247202989359^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5653992907 10000000000 47247202989359 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (629769291/1250000000 : ℝ)^1069 ≤ (10149900320811/25000000000000 : ℝ)^813 := by
    have hnat : (629769291 : ℕ)^1069*25000000000000^813 ≤ 10149900320811^813*1250000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629769291 1250000000 10149900320811 25000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2013192413/10000000000 : ℝ), (5653992907/10000000000 : ℝ), (629769291/1250000000 : ℝ)] ![(303829892731/2500000000000 : ℝ), (47247202989359/100000000000000 : ℝ), (10149900320811/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2013192413/10000000000 : ℝ)|^1069 ≤ (303829892731/2500000000000 : ℝ)^813
        have hw : |(-2013192413/10000000000 : ℝ)|=(2013192413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5653992907/10000000000 : ℝ)|^1069 ≤ (47247202989359/100000000000000 : ℝ)^813
        have hw : |(5653992907/10000000000 : ℝ)|=(5653992907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(629769291/1250000000 : ℝ)|^1069 ≤ (10149900320811/25000000000000 : ℝ)^813
        have hw : |(629769291/1250000000 : ℝ)|=(629769291/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s1_1 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2704221293/5000000000 : ℝ)*x 0 + (-468512297/2000000000 : ℝ)*x 1 + (5038154411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2704221293/5000000000 : ℝ)^1069 ≤ (44567796770307/100000000000000 : ℝ)^813 := by
    have hnat : (2704221293 : ℕ)^1069*100000000000000^813 ≤ 44567796770307^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704221293 5000000000 44567796770307 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (468512297/2000000000 : ℝ)^1069 ≤ (2966520208383/20000000000000 : ℝ)^813 := by
    have hnat : (468512297 : ℕ)^1069*20000000000000^813 ≤ 2966520208383^813*2000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468512297 2000000000 2966520208383 20000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5038154411/10000000000 : ℝ)^1069 ≤ (40599602162703/100000000000000 : ℝ)^813 := by
    have hnat : (5038154411 : ℕ)^1069*100000000000000^813 ≤ 40599602162703^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5038154411 10000000000 40599602162703 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2704221293/5000000000 : ℝ), (-468512297/2000000000 : ℝ), (5038154411/10000000000 : ℝ)] ![(44567796770307/100000000000000 : ℝ), (2966520208383/20000000000000 : ℝ), (40599602162703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2704221293/5000000000 : ℝ)|^1069 ≤ (44567796770307/100000000000000 : ℝ)^813
        have hw : |(2704221293/5000000000 : ℝ)|=(2704221293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-468512297/2000000000 : ℝ)|^1069 ≤ (2966520208383/20000000000000 : ℝ)^813
        have hw : |(-468512297/2000000000 : ℝ)|=(468512297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5038154411/10000000000 : ℝ)|^1069 ≤ (40599602162703/100000000000000 : ℝ)^813
        have hw : |(5038154411/10000000000 : ℝ)|=(5038154411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s1_2 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1081688477/2000000000 : ℝ)*x 0 + (1259538551/2500000000 : ℝ)*x 1 + (-585640503/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081688477/2000000000 : ℝ)^1069 ≤ (11141948648109/25000000000000 : ℝ)^813 := by
    have hnat : (1081688477 : ℕ)^1069*25000000000000^813 ≤ 11141948648109^813*2000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081688477 2000000000 11141948648109 25000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1259538551/2500000000 : ℝ)^1069 ≤ (20299799984677/50000000000000 : ℝ)^813 := by
    have hnat : (1259538551 : ℕ)^1069*50000000000000^813 ≤ 20299799984677^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1259538551 2500000000 20299799984677 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (585640503/2500000000 : ℝ)^1069 ≤ (7416302714743/50000000000000 : ℝ)^813 := by
    have hnat : (585640503 : ℕ)^1069*50000000000000^813 ≤ 7416302714743^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585640503 2500000000 7416302714743 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081688477/2000000000 : ℝ), (1259538551/2500000000 : ℝ), (-585640503/2500000000 : ℝ)] ![(11141948648109/25000000000000 : ℝ), (20299799984677/50000000000000 : ℝ), (7416302714743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081688477/2000000000 : ℝ)|^1069 ≤ (11141948648109/25000000000000 : ℝ)^813
        have hw : |(1081688477/2000000000 : ℝ)|=(1081688477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1259538551/2500000000 : ℝ)|^1069 ≤ (20299799984677/50000000000000 : ℝ)^813
        have hw : |(1259538551/2500000000 : ℝ)|=(1259538551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-585640503/2500000000 : ℝ)|^1069 ≤ (7416302714743/50000000000000 : ℝ)^813
        have hw : |(-585640503/2500000000 : ℝ)|=(585640503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s1_3 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1074230279/2500000000 : ℝ)*x 0 + (1851377557/5000000000 : ℝ)*x 1 + (498006547/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074230279/2500000000 : ℝ)^1069 ≤ (16467012916761/50000000000000 : ℝ)^813 := by
    have hnat : (1074230279 : ℕ)^1069*50000000000000^813 ≤ 16467012916761^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074230279 2500000000 16467012916761 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1851377557/5000000000 : ℝ)^1069 ≤ (27080755788589/100000000000000 : ℝ)^813 := by
    have hnat : (1851377557 : ℕ)^1069*100000000000000^813 ≤ 27080755788589^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1851377557 5000000000 27080755788589 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (498006547/1000000000 : ℝ)^1069 ≤ (19992609182167/50000000000000 : ℝ)^813 := by
    have hnat : (498006547 : ℕ)^1069*50000000000000^813 ≤ 19992609182167^813*1000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498006547 1000000000 19992609182167 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074230279/2500000000 : ℝ), (1851377557/5000000000 : ℝ), (498006547/1000000000 : ℝ)] ![(16467012916761/50000000000000 : ℝ), (27080755788589/100000000000000 : ℝ), (19992609182167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074230279/2500000000 : ℝ)|^1069 ≤ (16467012916761/50000000000000 : ℝ)^813
        have hw : |(1074230279/2500000000 : ℝ)|=(1074230279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1851377557/5000000000 : ℝ)|^1069 ≤ (27080755788589/100000000000000 : ℝ)^813
        have hw : |(1851377557/5000000000 : ℝ)|=(1851377557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(498006547/1000000000 : ℝ)|^1069 ≤ (19992609182167/50000000000000 : ℝ)^813
        have hw : |(498006547/1000000000 : ℝ)|=(498006547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s1_4 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2013779229/10000000000 : ℝ)*x 0 + (201841483/400000000 : ℝ)*x 1 + (2822981831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2013779229/10000000000 : ℝ)^1069 ≤ (3039463466881/25000000000000 : ℝ)^813 := by
    have hnat : (2013779229 : ℕ)^1069*25000000000000^813 ≤ 3039463466881^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013779229 10000000000 3039463466881 25000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201841483/400000000 : ℝ)^1069 ≤ (317837082617/781250000000 : ℝ)^813 := by
    have hnat : (201841483 : ℕ)^1069*781250000000^813 ≤ 317837082617^813*400000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201841483 400000000 317837082617 781250000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2822981831/5000000000 : ℝ)^1069 ≤ (23579499769877/50000000000000 : ℝ)^813 := by
    have hnat : (2822981831 : ℕ)^1069*50000000000000^813 ≤ 23579499769877^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2822981831 5000000000 23579499769877 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2013779229/10000000000 : ℝ), (201841483/400000000 : ℝ), (2822981831/5000000000 : ℝ)] ![(3039463466881/25000000000000 : ℝ), (317837082617/781250000000 : ℝ), (23579499769877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2013779229/10000000000 : ℝ)|^1069 ≤ (3039463466881/25000000000000 : ℝ)^813
        have hw : |(-2013779229/10000000000 : ℝ)|=(2013779229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(201841483/400000000 : ℝ)|^1069 ≤ (317837082617/781250000000 : ℝ)^813
        have hw : |(201841483/400000000 : ℝ)|=(201841483/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2822981831/5000000000 : ℝ)|^1069 ≤ (23579499769877/50000000000000 : ℝ)^813
        have hw : |(2822981831/5000000000 : ℝ)|=(2822981831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s1_5 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5248994813/10000000000 : ℝ)*x 0 + (-173475261/1000000000 : ℝ)*x 1 + (1129192667/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5248994813/10000000000 : ℝ)^1069 ≤ (21424112618863/50000000000000 : ℝ)^813 := by
    have hnat : (5248994813 : ℕ)^1069*50000000000000^813 ≤ 21424112618863^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5248994813 10000000000 21424112618863 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (173475261/1000000000 : ℝ)^1069 ≤ (4996389396449/50000000000000 : ℝ)^813 := by
    have hnat : (173475261 : ℕ)^1069*50000000000000^813 ≤ 4996389396449^813*1000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173475261 1000000000 4996389396449 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129192667/2000000000 : ℝ)^1069 ≤ (23579497974187/50000000000000 : ℝ)^813 := by
    have hnat : (1129192667 : ℕ)^1069*50000000000000^813 ≤ 23579497974187^813*2000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129192667 2000000000 23579497974187 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5248994813/10000000000 : ℝ), (-173475261/1000000000 : ℝ), (1129192667/2000000000 : ℝ)] ![(21424112618863/50000000000000 : ℝ), (4996389396449/50000000000000 : ℝ), (23579497974187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5248994813/10000000000 : ℝ)|^1069 ≤ (21424112618863/50000000000000 : ℝ)^813
        have hw : |(5248994813/10000000000 : ℝ)|=(5248994813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-173475261/1000000000 : ℝ)|^1069 ≤ (4996389396449/50000000000000 : ℝ)^813
        have hw : |(-173475261/1000000000 : ℝ)|=(173475261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1129192667/2000000000 : ℝ)|^1069 ≤ (23579497974187/50000000000000 : ℝ)^813
        have hw : |(1129192667/2000000000 : ℝ)|=(1129192667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s1_6 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1049798939/2000000000 : ℝ)*x 0 + (282298159/500000000 : ℝ)*x 1 + (-867376501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049798939/2000000000 : ℝ)^1069 ≤ (8569644794233/20000000000000 : ℝ)^813 := by
    have hnat : (1049798939 : ℕ)^1069*20000000000000^813 ≤ 8569644794233^813*2000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049798939 2000000000 8569644794233 20000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282298159/500000000 : ℝ)^1069 ≤ (47158994246037/100000000000000 : ℝ)^813 := by
    have hnat : (282298159 : ℕ)^1069*100000000000000^813 ≤ 47158994246037^813*500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282298159 500000000 47158994246037 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (867376501/5000000000 : ℝ)^1069 ≤ (4996390880989/50000000000000 : ℝ)^813 := by
    have hnat : (867376501 : ℕ)^1069*50000000000000^813 ≤ 4996390880989^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867376501 5000000000 4996390880989 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049798939/2000000000 : ℝ), (282298159/500000000 : ℝ), (-867376501/5000000000 : ℝ)] ![(8569644794233/20000000000000 : ℝ), (47158994246037/100000000000000 : ℝ), (4996390880989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049798939/2000000000 : ℝ)|^1069 ≤ (8569644794233/20000000000000 : ℝ)^813
        have hw : |(1049798939/2000000000 : ℝ)|=(1049798939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(282298159/500000000 : ℝ)|^1069 ≤ (47158994246037/100000000000000 : ℝ)^813
        have hw : |(282298159/500000000 : ℝ)|=(282298159/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-867376501/5000000000 : ℝ)|^1069 ≤ (4996390880989/50000000000000 : ℝ)^813
        have hw : |(-867376501/5000000000 : ℝ)|=(867376501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s1_7 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4298137527/10000000000 : ℝ)*x 0 + (4963715471/10000000000 : ℝ)*x 1 + (1859704237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298137527/10000000000 : ℝ)^1069 ≤ (4118285672111/12500000000000 : ℝ)^813 := by
    have hnat : (4298137527 : ℕ)^1069*12500000000000^813 ≤ 4118285672111^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298137527 10000000000 4118285672111 12500000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4963715471/10000000000 : ℝ)^1069 ≤ (19906348159409/50000000000000 : ℝ)^813 := by
    have hnat : (4963715471 : ℕ)^1069*50000000000000^813 ≤ 19906348159409^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4963715471 10000000000 19906348159409 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1859704237/5000000000 : ℝ)^1069 ≤ (27241018291701/100000000000000 : ℝ)^813 := by
    have hnat : (1859704237 : ℕ)^1069*100000000000000^813 ≤ 27241018291701^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1859704237 5000000000 27241018291701 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298137527/10000000000 : ℝ), (4963715471/10000000000 : ℝ), (1859704237/5000000000 : ℝ)] ![(4118285672111/12500000000000 : ℝ), (19906348159409/50000000000000 : ℝ), (27241018291701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298137527/10000000000 : ℝ)|^1069 ≤ (4118285672111/12500000000000 : ℝ)^813
        have hw : |(4298137527/10000000000 : ℝ)|=(4298137527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4963715471/10000000000 : ℝ)|^1069 ≤ (19906348159409/50000000000000 : ℝ)^813
        have hw : |(4963715471/10000000000 : ℝ)|=(4963715471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1859704237/5000000000 : ℝ)|^1069 ≤ (27241018291701/100000000000000 : ℝ)^813
        have hw : |(1859704237/5000000000 : ℝ)|=(1859704237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1316_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76852523/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1217/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1661/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (983/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27059/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1217/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27059/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1217/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27059/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1217/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27059/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1217/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27059/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1217/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27059/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1217/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (1217/100000 : ℝ) ^ (4275/1024 : ℝ) ≤ (1014990858487/100000000000000000000 : ℝ) := by
    have hpowers : (1217/100000 : ℝ)^4275 ≤ (1014990858487/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1217 : ℕ)^4275*100000000000000000000^1024 ≤ 1014990858487^1024*100000^4275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1217 100000 1014990858487 100000000000000000000 4275 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1217/100000 : ℝ)) (X := (1014990858487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27059/100000 : ℝ) ^ (4275/1024 : ℝ) ≤ (213295850416396187/50000000000000000000 : ℝ) := by
    have hpowers : (27059/100000 : ℝ)^4275 ≤ (213295850416396187/50000000000000000000 : ℝ)^1024 := by
      have hnat : (27059 : ℕ)^4275*50000000000000000000^1024 ≤ 213295850416396187^1024*100000^4275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27059 100000 213295850416396187 50000000000000000000 4275 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27059/100000 : ℝ)) (X := (213295850416396187/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000001014990858487/50000000000000000000 : ℝ) ≤ (10000000048624591/10000000000000000 : ℝ) ^ (4275/1024 : ℝ) := by
    have hpowers : (50000001014990858487/50000000000000000000 : ℝ)^1024 ≤ (10000000048624591/10000000000000000 : ℝ)^4275 := by
      have hnat : (50000001014990858487 : ℕ)^1024*10000000000000000^4275 ≤ 10000000048624591^4275*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000001014990858487 50000000000000000000 10000000048624591 10000000000000000 1024 4275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000048624591/10000000000000000 : ℝ)) (X := (50000001014990858487/50000000000000000000 : ℝ)) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100426592715823650861/100000000000000000000 : ℝ) ≤ (2002040346890557/2000000000000000 : ℝ) ^ (4275/1024 : ℝ) := by
    have hpowers : (100426592715823650861/100000000000000000000 : ℝ)^1024 ≤ (2002040346890557/2000000000000000 : ℝ)^4275 := by
      have hnat : (100426592715823650861 : ℕ)^1024*2000000000000000^4275 ≤ 2002040346890557^4275*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100426592715823650861 100000000000000000000 2002040346890557 2000000000000000 1024 4275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002040346890557/2000000000000000 : ℝ)) (X := (100426592715823650861/100000000000000000000 : ℝ)) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25213295850416396187/25000000000000000000 : ℝ) ≤ (10020403420280979/10000000000000000 : ℝ) ^ (4275/1024 : ℝ) := by
    have hpowers : (25213295850416396187/25000000000000000000 : ℝ)^1024 ≤ (10020403420280979/10000000000000000 : ℝ)^4275 := by
      have hnat : (25213295850416396187 : ℕ)^1024*10000000000000000^4275 ≤ 10020403420280979^4275*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25213295850416396187 25000000000000000000 10020403420280979 10000000000000000 1024 4275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10020403420280979/10000000000000000 : ℝ)) (X := (25213295850416396187/25000000000000000000 : ℝ)) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1014990858487/100000000000000000000 : ℝ) ≤ ((129197585176625428213/129210000000000000000 : ℝ)+2*(5100842914097/1292100000000000 : ℝ)*(1217/100000 : ℝ))^(4275/1024 : ℝ) := by
    rw [show (129197585176625428213/129210000000000000000 : ℝ)+2*(5100842914097/1292100000000000 : ℝ)*(1217/100000 : ℝ)=(10000000048624591/10000000000000000 : ℝ) by norm_num, show 1+2*(1014990858487/100000000000000000000 : ℝ)=(50000001014990858487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(213295850416396187/50000000000000000000 : ℝ)+(1014990858487/100000000000000000000 : ℝ) ≤ ((129197585176625428213/129210000000000000000 : ℝ)+(5100842914097/1292100000000000 : ℝ)*((27059/100000 : ℝ)+(1217/100000 : ℝ)))^(4275/1024 : ℝ) := by
    rw [show (129197585176625428213/129210000000000000000 : ℝ)+(5100842914097/1292100000000000 : ℝ)*((27059/100000 : ℝ)+(1217/100000 : ℝ))=(2002040346890557/2000000000000000 : ℝ) by norm_num, show 1+(213295850416396187/50000000000000000000 : ℝ)+(1014990858487/100000000000000000000 : ℝ)=(100426592715823650861/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(213295850416396187/50000000000000000000 : ℝ) ≤ ((129197585176625428213/129210000000000000000 : ℝ)+2*(5100842914097/1292100000000000 : ℝ)*(27059/100000 : ℝ))^(4275/1024 : ℝ) := by
    rw [show (129197585176625428213/129210000000000000000 : ℝ)+2*(5100842914097/1292100000000000 : ℝ)*(27059/100000 : ℝ)=(10020403420280979/10000000000000000 : ℝ) by norm_num, show 1+2*(213295850416396187/50000000000000000000 : ℝ)=(25213295850416396187/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (129197585176625428213/129210000000000000000 : ℝ)*(X 1 0+X 2 0)+(5100842914097/1292100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4275/1024 : ℝ)) (lo := (1217/100000 : ℝ)) (hi := (27059/100000 : ℝ)) (c := (129197585176625428213/129210000000000000000 : ℝ)) (alpha := (5100842914097/1292100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (129197585176625428213/129210000000000000000 : ℝ)*(X 0 1+X 2 1)+(5100842914097/1292100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4275/1024 : ℝ)) (lo := (1217/100000 : ℝ)) (hi := (27059/100000 : ℝ)) (c := (129197585176625428213/129210000000000000000 : ℝ)) (alpha := (5100842914097/1292100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (129197585176625428213/129210000000000000000 : ℝ)*(X 0 2+X 1 2)+(5100842914097/1292100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4275/1024 : ℝ)) (lo := (1217/100000 : ℝ)) (hi := (27059/100000 : ℝ)) (c := (129197585176625428213/129210000000000000000 : ℝ)) (alpha := (5100842914097/1292100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2013192413/10000000000 : ℝ)*X 0 0+(5653992907/10000000000 : ℝ)*X 0 1+(629769291/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2704221293/5000000000 : ℝ)*X 1 0+(-468512297/2000000000 : ℝ)*X 1 1+(5038154411/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1081688477/2000000000 : ℝ)*X 2 0+(1259538551/2500000000 : ℝ)*X 2 1+(-585640503/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1074230279/2500000000 : ℝ)*X 0 0+(1851377557/5000000000 : ℝ)*X 0 1+(498006547/1000000000 : ℝ)*X 0 2+(1074230279/2500000000 : ℝ)*X 1 0+(1851377557/5000000000 : ℝ)*X 1 1+(498006547/1000000000 : ℝ)*X 1 2+(1074230279/2500000000 : ℝ)*X 2 0+(1851377557/5000000000 : ℝ)*X 2 1+(498006547/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2013779229/10000000000 : ℝ)*X 0 0+(201841483/400000000 : ℝ)*X 0 1+(2822981831/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5248994813/10000000000 : ℝ)*X 1 0+(-173475261/1000000000 : ℝ)*X 1 1+(1129192667/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1049798939/2000000000 : ℝ)*X 2 0+(282298159/500000000 : ℝ)*X 2 1+(-867376501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4298137527/10000000000 : ℝ)*X 0 0+(4963715471/10000000000 : ℝ)*X 0 1+(1859704237/5000000000 : ℝ)*X 0 2+(4298137527/10000000000 : ℝ)*X 1 0+(4963715471/10000000000 : ℝ)*X 1 1+(1859704237/5000000000 : ℝ)*X 1 2+(4298137527/10000000000 : ℝ)*X 2 0+(4963715471/10000000000 : ℝ)*X 2 1+(1859704237/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11082538960247609865528099663/2153500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70734913/100000000000000 : ℝ)*(base1) + (25340347/100000000000000 : ℝ)*(base16) + (345389491/50000000000000 : ℝ)*(base19) + (327885963/50000000000000 : ℝ)*(base23) + (30870713/20000000000000 : ℝ)*(upper3) + (1203353468241651/100000000000000 : ℝ)*(major0) + (1203353468241651/100000000000000 : ℝ)*(major1) + (1203353468241651/100000000000000 : ℝ)*(major2) + (1623806481615831/100000000000000 : ℝ)*(sp0) + (1623808219792159/100000000000000 : ℝ)*(sp1) + (811904140069781/50000000000000 : ℝ)*(sp2) + (391448043535889/50000000000000 : ℝ)*(sp3) + (2525030571/100000000000000 : ℝ)*(sp4) + (334244413/20000000000000 : ℝ)*(sp7) + (195724457257189/25000000000000 : ℝ)*(f.failure) + (25372014623617/1562500000000 : ℝ)*(f.sum) + (3211885636307/10767500000000000000000000000 : ℝ)*base65 + (21779176830159066779/4307000000000000000000000000000000 : ℝ)*base68 + (29582130789796066779/4307000000000000000000000000000000 : ℝ)*base70 + (10674911759355066779/4307000000000000000000000000000000 : ℝ)*base72 + (32047263143329/21535000000000000000000000000 : ℝ)*base73 + (1953784460050933221/4307000000000000000000000000000000 : ℝ)*base75 + (10811237767527066779/4307000000000000000000000000000000 : ℝ)*base78 + (9017216497298933221/4307000000000000000000000000000000 : ℝ)*base79 + (78068116091361/21535000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2962153/1250000000000000000000 : ℝ)*base90 + (2962153/1250000000000000000000 : ℝ)*base92 + (2962153/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6416407578601865730914300183/1076750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (213647291/20000000000000 : ℝ)*(base19) + (995051701/100000000000000 : ℝ)*(base23) + (3157363/50000000000000 : ℝ)*(upper2) + (48602869/50000000000000 : ℝ)*(upper3) + (170703989/100000000000000 : ℝ)*(upper5) + (617632787911897/50000000000000 : ℝ)*(major0) + (617632787911897/50000000000000 : ℝ)*(major1) + (617632787911897/50000000000000 : ℝ)*(major2) + (1289063183/25000000000000 : ℝ)*(sp1) + (1792280749/50000000000000 : ℝ)*(sp2) + (83343560560413/5000000000000 : ℝ)*(sp4) + (1666864986719073/100000000000000 : ℝ)*(sp5) + (1666866631595061/100000000000000 : ℝ)*(sp6) + (803659741804309/100000000000000 : ℝ)*(sp7) + (803659741804309/100000000000000 : ℝ)*(f.failure) + (83343560560413/5000000000000 : ℝ)*(f.sum) + (330367170011297/64605000000000000000000000000 : ℝ)*base66 + (1830794315005483313/2153500000000000000000000000000000 : ℝ)*base68 + (6519089895969983313/2153500000000000000000000000000000 : ℝ)*base70 + (8699626136622983313/2153500000000000000000000000000000 : ℝ)*base72 + (13135374099673/64605000000000000000000000000 : ℝ)*base73 + (8641452842174483313/2153500000000000000000000000000000 : ℝ)*base76 + (17328013291106983313/2153500000000000000000000000000000 : ℝ)*base78 + (10907478252057483313/2153500000000000000000000000000000 : ℝ)*base80 + (123565207617811/32302500000000000000000000000 : ℝ)*base82 + (18921607/5000000000000000000000 : ℝ)*base89 + (18921607/5000000000000000000000 : ℝ)*base91 + (18921607/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1316_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76852523/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1217/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1661/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (983/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1316_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1316_s2_0 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1027829011/5000000000 : ℝ)*x 0 + (5487077139/10000000000 : ℝ)*x 1 + (5177908939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1027829011/5000000000 : ℝ)^1069 ≤ (12491387272993/100000000000000 : ℝ)^813 := by
    have hnat : (1027829011 : ℕ)^1069*100000000000000^813 ≤ 12491387272993^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027829011 5000000000 12491387272993 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5487077139/10000000000 : ℝ)^1069 ≤ (22710880075531/50000000000000 : ℝ)^813 := by
    have hnat : (5487077139 : ℕ)^1069*50000000000000^813 ≤ 22710880075531^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487077139 10000000000 22710880075531 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177908939/10000000000 : ℝ)^1069 ≤ (42086852561967/100000000000000 : ℝ)^813 := by
    have hnat : (5177908939 : ℕ)^1069*100000000000000^813 ≤ 42086852561967^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177908939 10000000000 42086852561967 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1027829011/5000000000 : ℝ), (5487077139/10000000000 : ℝ), (5177908939/10000000000 : ℝ)] ![(12491387272993/100000000000000 : ℝ), (22710880075531/50000000000000 : ℝ), (42086852561967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1027829011/5000000000 : ℝ)|^1069 ≤ (12491387272993/100000000000000 : ℝ)^813
        have hw : |(-1027829011/5000000000 : ℝ)|=(1027829011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5487077139/10000000000 : ℝ)|^1069 ≤ (22710880075531/50000000000000 : ℝ)^813
        have hw : |(5487077139/10000000000 : ℝ)|=(5487077139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177908939/10000000000 : ℝ)|^1069 ≤ (42086852561967/100000000000000 : ℝ)^813
        have hw : |(5177908939/10000000000 : ℝ)|=(5177908939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s2_1 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (134195313/250000000 : ℝ)*x 0 + (-553910953/2500000000 : ℝ)*x 1 + (2588954251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134195313/250000000 : ℝ)^1069 ≤ (22064042153403/50000000000000 : ℝ)^813 := by
    have hnat : (134195313 : ℕ)^1069*50000000000000^813 ≤ 22064042153403^813*250000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134195313 250000000 22064042153403 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553910953/2500000000 : ℝ)^1069 ≤ (6892533889633/50000000000000 : ℝ)^813 := by
    have hnat : (553910953 : ℕ)^1069*50000000000000^813 ≤ 6892533889633^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553910953 2500000000 6892533889633 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588954251/5000000000 : ℝ)^1069 ≤ (5260855986437/12500000000000 : ℝ)^813 := by
    have hnat : (2588954251 : ℕ)^1069*12500000000000^813 ≤ 5260855986437^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588954251 5000000000 5260855986437 12500000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134195313/250000000 : ℝ), (-553910953/2500000000 : ℝ), (2588954251/5000000000 : ℝ)] ![(22064042153403/50000000000000 : ℝ), (6892533889633/50000000000000 : ℝ), (5260855986437/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134195313/250000000 : ℝ)|^1069 ≤ (22064042153403/50000000000000 : ℝ)^813
        have hw : |(134195313/250000000 : ℝ)|=(134195313/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-553910953/2500000000 : ℝ)|^1069 ≤ (6892533889633/50000000000000 : ℝ)^813
        have hw : |(-553910953/2500000000 : ℝ)|=(553910953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588954251/5000000000 : ℝ)|^1069 ≤ (5260855986437/12500000000000 : ℝ)^813
        have hw : |(2588954251/5000000000 : ℝ)|=(2588954251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s2_2 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5367811889/10000000000 : ℝ)*x 0 + (1035581823/2000000000 : ℝ)*x 1 + (-443128769/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367811889/10000000000 : ℝ)^1069 ≤ (44128077486023/100000000000000 : ℝ)^813 := by
    have hnat : (5367811889 : ℕ)^1069*100000000000000^813 ≤ 44128077486023^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367811889 10000000000 44128077486023 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035581823/2000000000 : ℝ)^1069 ≤ (2104342722149/5000000000000 : ℝ)^813 := by
    have hnat : (1035581823 : ℕ)^1069*5000000000000^813 ≤ 2104342722149^813*2000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035581823 2000000000 2104342722149 5000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (443128769/2000000000 : ℝ)^1069 ≤ (861566753077/6250000000000 : ℝ)^813 := by
    have hnat : (443128769 : ℕ)^1069*6250000000000^813 ≤ 861566753077^813*2000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443128769 2000000000 861566753077 6250000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367811889/10000000000 : ℝ), (1035581823/2000000000 : ℝ), (-443128769/2000000000 : ℝ)] ![(44128077486023/100000000000000 : ℝ), (2104342722149/5000000000000 : ℝ), (861566753077/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367811889/10000000000 : ℝ)|^1069 ≤ (44128077486023/100000000000000 : ℝ)^813
        have hw : |(5367811889/10000000000 : ℝ)|=(5367811889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035581823/2000000000 : ℝ)|^1069 ≤ (2104342722149/5000000000000 : ℝ)^813
        have hw : |(1035581823/2000000000 : ℝ)|=(1035581823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-443128769/2000000000 : ℝ)|^1069 ≤ (861566753077/6250000000000 : ℝ)^813
        have hw : |(-443128769/2000000000 : ℝ)|=(443128769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s2_3 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2163264649/5000000000 : ℝ)*x 0 + (4017101121/10000000000 : ℝ)*x 1 + (931671077/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163264649/5000000000 : ℝ)^1069 ≤ (4154092558273/12500000000000 : ℝ)^813 := by
    have hnat : (2163264649 : ℕ)^1069*12500000000000^813 ≤ 4154092558273^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163264649 5000000000 4154092558273 12500000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4017101121/10000000000 : ℝ)^1069 ≤ (30143353604693/100000000000000 : ℝ)^813 := by
    have hnat : (4017101121 : ℕ)^1069*100000000000000^813 ≤ 30143353604693^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4017101121 10000000000 30143353604693 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (931671077/2000000000 : ℝ)^1069 ≤ (3662390591779/10000000000000 : ℝ)^813 := by
    have hnat : (931671077 : ℕ)^1069*10000000000000^813 ≤ 3662390591779^813*2000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931671077 2000000000 3662390591779 10000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163264649/5000000000 : ℝ), (4017101121/10000000000 : ℝ), (931671077/2000000000 : ℝ)] ![(4154092558273/12500000000000 : ℝ), (30143353604693/100000000000000 : ℝ), (3662390591779/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163264649/5000000000 : ℝ)|^1069 ≤ (4154092558273/12500000000000 : ℝ)^813
        have hw : |(2163264649/5000000000 : ℝ)|=(2163264649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4017101121/10000000000 : ℝ)|^1069 ≤ (30143353604693/100000000000000 : ℝ)^813
        have hw : |(4017101121/10000000000 : ℝ)|=(4017101121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(931671077/2000000000 : ℝ)|^1069 ≤ (3662390591779/10000000000000 : ℝ)^813
        have hw : |(931671077/2000000000 : ℝ)|=(931671077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s2_4 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2055731827/10000000000 : ℝ)*x 0 + (517990489/1000000000 : ℝ)*x 1 + (1371265723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2055731827/10000000000 : ℝ)^1069 ≤ (12491976978529/100000000000000 : ℝ)^813 := by
    have hnat : (2055731827 : ℕ)^1069*100000000000000^813 ≤ 12491976978529^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055731827 10000000000 12491976978529 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517990489/1000000000 : ℝ)^1069 ≤ (42108185733679/100000000000000 : ℝ)^813 := by
    have hnat : (517990489 : ℕ)^1069*100000000000000^813 ≤ 42108185733679^813*1000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517990489 1000000000 42108185733679 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1371265723/2500000000 : ℝ)^1069 ≤ (45399837267553/100000000000000 : ℝ)^813 := by
    have hnat : (1371265723 : ℕ)^1069*100000000000000^813 ≤ 45399837267553^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371265723 2500000000 45399837267553 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2055731827/10000000000 : ℝ), (517990489/1000000000 : ℝ), (1371265723/2500000000 : ℝ)] ![(12491976978529/100000000000000 : ℝ), (42108185733679/100000000000000 : ℝ), (45399837267553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2055731827/10000000000 : ℝ)|^1069 ≤ (12491976978529/100000000000000 : ℝ)^813
        have hw : |(-2055731827/10000000000 : ℝ)|=(2055731827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517990489/1000000000 : ℝ)|^1069 ≤ (42108185733679/100000000000000 : ℝ)^813
        have hw : |(517990489/1000000000 : ℝ)|=(517990489/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1371265723/2500000000 : ℝ)|^1069 ≤ (45399837267553/100000000000000 : ℝ)^813
        have hw : |(1371265723/2500000000 : ℝ)|=(1371265723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s2_5 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1057670633/2000000000 : ℝ)*x 0 + (-477122239/2500000000 : ℝ)*x 1 + (685632871/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057670633/2000000000 : ℝ)^1069 ≤ (8654235681607/20000000000000 : ℝ)^813 := by
    have hnat : (1057670633 : ℕ)^1069*20000000000000^813 ≤ 8654235681607^813*2000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057670633 2000000000 8654235681607 20000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (477122239/2500000000 : ℝ)^1069 ≤ (2832245869877/25000000000000 : ℝ)^813 := by
    have hnat : (477122239 : ℕ)^1069*25000000000000^813 ≤ 2832245869877^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477122239 2500000000 2832245869877 25000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (685632871/1250000000 : ℝ)^1069 ≤ (45399838094683/100000000000000 : ℝ)^813 := by
    have hnat : (685632871 : ℕ)^1069*100000000000000^813 ≤ 45399838094683^813*1250000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685632871 1250000000 45399838094683 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057670633/2000000000 : ℝ), (-477122239/2500000000 : ℝ), (685632871/1250000000 : ℝ)] ![(8654235681607/20000000000000 : ℝ), (2832245869877/25000000000000 : ℝ), (45399838094683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057670633/2000000000 : ℝ)|^1069 ≤ (8654235681607/20000000000000 : ℝ)^813
        have hw : |(1057670633/2000000000 : ℝ)|=(1057670633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-477122239/2500000000 : ℝ)|^1069 ≤ (2832245869877/25000000000000 : ℝ)^813
        have hw : |(-477122239/2500000000 : ℝ)|=(477122239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(685632871/1250000000 : ℝ)|^1069 ≤ (45399838094683/100000000000000 : ℝ)^813
        have hw : |(685632871/1250000000 : ℝ)|=(685632871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s2_6 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1322088317/2500000000 : ℝ)*x 0 + (5485062899/10000000000 : ℝ)*x 1 + (-1908488911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322088317/2500000000 : ℝ)^1069 ≤ (10817794879049/25000000000000 : ℝ)^813 := by
    have hnat : (1322088317 : ℕ)^1069*25000000000000^813 ≤ 10817794879049^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322088317 2500000000 10817794879049 25000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5485062899/10000000000 : ℝ)^1069 ≤ (5674979667967/12500000000000 : ℝ)^813 := by
    have hnat : (5485062899 : ℕ)^1069*12500000000000^813 ≤ 5674979667967^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485062899 10000000000 5674979667967 12500000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1908488911/10000000000 : ℝ)^1069 ≤ (11328983128271/100000000000000 : ℝ)^813 := by
    have hnat : (1908488911 : ℕ)^1069*100000000000000^813 ≤ 11328983128271^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1908488911 10000000000 11328983128271 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322088317/2500000000 : ℝ), (5485062899/10000000000 : ℝ), (-1908488911/10000000000 : ℝ)] ![(10817794879049/25000000000000 : ℝ), (5674979667967/12500000000000 : ℝ), (11328983128271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322088317/2500000000 : ℝ)|^1069 ≤ (10817794879049/25000000000000 : ℝ)^813
        have hw : |(1322088317/2500000000 : ℝ)|=(1322088317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5485062899/10000000000 : ℝ)|^1069 ≤ (5674979667967/12500000000000 : ℝ)^813
        have hw : |(5485062899/10000000000 : ℝ)|=(5485062899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1908488911/10000000000 : ℝ)|^1069 ≤ (11328983128271/100000000000000 : ℝ)^813
        have hw : |(-1908488911/10000000000 : ℝ)|=(1908488911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s2_7 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2163340489/5000000000 : ℝ)*x 0 + (2327106737/5000000000 : ℝ)*x 1 + (4021284203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163340489/5000000000 : ℝ)^1069 ≤ (33234272415453/100000000000000 : ℝ)^813 := by
    have hnat : (2163340489 : ℕ)^1069*100000000000000^813 ≤ 33234272415453^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163340489 5000000000 33234272415453 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2327106737/5000000000 : ℝ)^1069 ≤ (36581094545201/100000000000000 : ℝ)^813 := by
    have hnat : (2327106737 : ℕ)^1069*100000000000000^813 ≤ 36581094545201^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2327106737 5000000000 36581094545201 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4021284203/10000000000 : ℝ)^1069 ≤ (15092316509187/50000000000000 : ℝ)^813 := by
    have hnat : (4021284203 : ℕ)^1069*50000000000000^813 ≤ 15092316509187^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021284203 10000000000 15092316509187 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163340489/5000000000 : ℝ), (2327106737/5000000000 : ℝ), (4021284203/10000000000 : ℝ)] ![(33234272415453/100000000000000 : ℝ), (36581094545201/100000000000000 : ℝ), (15092316509187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163340489/5000000000 : ℝ)|^1069 ≤ (33234272415453/100000000000000 : ℝ)^813
        have hw : |(2163340489/5000000000 : ℝ)|=(2163340489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2327106737/5000000000 : ℝ)|^1069 ≤ (36581094545201/100000000000000 : ℝ)^813
        have hw : |(2327106737/5000000000 : ℝ)|=(2327106737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4021284203/10000000000 : ℝ)|^1069 ≤ (15092316509187/50000000000000 : ℝ)^813
        have hw : |(4021284203/10000000000 : ℝ)|=(4021284203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1316_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76852523/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (983/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1661/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2419/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16211/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (983/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1661/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (983/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1661/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (983/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1661/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (983/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1661/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (983/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1661/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (983/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1661/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1661/25000 : ℝ) ^ (4275/1024 : ℝ) ≤ (18953686784969/1562500000000000000 : ℝ) := by
    have hpowers : (1661/25000 : ℝ)^4275 ≤ (18953686784969/1562500000000000000 : ℝ)^1024 := by
      have hnat : (1661 : ℕ)^4275*1562500000000000000^1024 ≤ 18953686784969^1024*25000^4275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1661 25000 18953686784969 1562500000000000000 4275 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1661/25000 : ℝ)) (X := (18953686784969/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (983/5000 : ℝ) ^ (4275/1024 : ℝ) ≤ (7026339950975011/6250000000000000000 : ℝ) := by
    have hpowers : (983/5000 : ℝ)^4275 ≤ (7026339950975011/6250000000000000000 : ℝ)^1024 := by
      have hnat : (983 : ℕ)^4275*6250000000000000000^1024 ≤ 7026339950975011^1024*5000^4275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        983 5000 7026339950975011 6250000000000000000 4275 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (983/5000 : ℝ)) (X := (7026339950975011/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (781268953686784969/781250000000000000 : ℝ) ≤ (10000058111689301/10000000000000000 : ℝ) ^ (4275/1024 : ℝ) := by
    have hpowers : (781268953686784969/781250000000000000 : ℝ)^1024 ≤ (10000058111689301/10000000000000000 : ℝ)^4275 := by
      have hnat : (781268953686784969 : ℕ)^1024*10000000000000000^4275 ≤ 10000058111689301^4275*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781268953686784969 781250000000000000 10000058111689301 10000000000000000 1024 4275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000058111689301/10000000000000000 : ℝ)) (X := (781268953686784969/781250000000000000 : ℝ)) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6257102154698114887/6250000000000000000 : ℝ) ≤ (2000544147176047/2000000000000000 : ℝ) ^ (4275/1024 : ℝ) := by
    have hpowers : (6257102154698114887/6250000000000000000 : ℝ)^1024 ≤ (2000544147176047/2000000000000000 : ℝ)^4275 := by
      have hnat : (6257102154698114887 : ℕ)^1024*2000000000000000^4275 ≤ 2000544147176047^4275*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6257102154698114887 6250000000000000000 2000544147176047 2000000000000000 1024 4275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000544147176047/2000000000000000 : ℝ)) (X := (6257102154698114887/6250000000000000000 : ℝ)) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3132026339950975011/3125000000000000000 : ℝ) ≤ (10005383360071169/10000000000000000 : ℝ) ^ (4275/1024 : ℝ) := by
    have hpowers : (3132026339950975011/3125000000000000000 : ℝ)^1024 ≤ (10005383360071169/10000000000000000 : ℝ)^4275 := by
      have hnat : (3132026339950975011 : ℕ)^1024*10000000000000000^4275 ≤ 10005383360071169^4275*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3132026339950975011 3125000000000000000 10005383360071169 10000000000000000 1024 4275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005383360071169/10000000000000000 : ℝ)) (X := (3132026339950975011/3125000000000000000 : ℝ)) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(18953686784969/1562500000000000000 : ℝ) ≤ ((16265671928937351353/16270000000000000000 : ℝ)+2*(1331312095467/650800000000000 : ℝ)*(1661/25000 : ℝ))^(4275/1024 : ℝ) := by
    rw [show (16265671928937351353/16270000000000000000 : ℝ)+2*(1331312095467/650800000000000 : ℝ)*(1661/25000 : ℝ)=(10000058111689301/10000000000000000 : ℝ) by norm_num, show 1+2*(18953686784969/1562500000000000000 : ℝ)=(781268953686784969/781250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7026339950975011/6250000000000000000 : ℝ)+(18953686784969/1562500000000000000 : ℝ) ≤ ((16265671928937351353/16270000000000000000 : ℝ)+(1331312095467/650800000000000 : ℝ)*((983/5000 : ℝ)+(1661/25000 : ℝ)))^(4275/1024 : ℝ) := by
    rw [show (16265671928937351353/16270000000000000000 : ℝ)+(1331312095467/650800000000000 : ℝ)*((983/5000 : ℝ)+(1661/25000 : ℝ))=(2000544147176047/2000000000000000 : ℝ) by norm_num, show 1+(7026339950975011/6250000000000000000 : ℝ)+(18953686784969/1562500000000000000 : ℝ)=(6257102154698114887/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7026339950975011/6250000000000000000 : ℝ) ≤ ((16265671928937351353/16270000000000000000 : ℝ)+2*(1331312095467/650800000000000 : ℝ)*(983/5000 : ℝ))^(4275/1024 : ℝ) := by
    rw [show (16265671928937351353/16270000000000000000 : ℝ)+2*(1331312095467/650800000000000 : ℝ)*(983/5000 : ℝ)=(10005383360071169/10000000000000000 : ℝ) by norm_num, show 1+2*(7026339950975011/6250000000000000000 : ℝ)=(3132026339950975011/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16265671928937351353/16270000000000000000 : ℝ)*(X 1 0+X 2 0)+(1331312095467/650800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4275/1024 : ℝ)) (lo := (1661/25000 : ℝ)) (hi := (983/5000 : ℝ)) (c := (16265671928937351353/16270000000000000000 : ℝ)) (alpha := (1331312095467/650800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16265671928937351353/16270000000000000000 : ℝ)*(X 0 1+X 2 1)+(1331312095467/650800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4275/1024 : ℝ)) (lo := (1661/25000 : ℝ)) (hi := (983/5000 : ℝ)) (c := (16265671928937351353/16270000000000000000 : ℝ)) (alpha := (1331312095467/650800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16265671928937351353/16270000000000000000 : ℝ)*(X 0 2+X 1 2)+(1331312095467/650800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4275/1024 : ℝ)) (lo := (1661/25000 : ℝ)) (hi := (983/5000 : ℝ)) (c := (16265671928937351353/16270000000000000000 : ℝ)) (alpha := (1331312095467/650800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1027829011/5000000000 : ℝ)*X 0 0+(5487077139/10000000000 : ℝ)*X 0 1+(5177908939/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((134195313/250000000 : ℝ)*X 1 0+(-553910953/2500000000 : ℝ)*X 1 1+(2588954251/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5367811889/10000000000 : ℝ)*X 2 0+(1035581823/2000000000 : ℝ)*X 2 1+(-443128769/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2163264649/5000000000 : ℝ)*X 0 0+(4017101121/10000000000 : ℝ)*X 0 1+(931671077/2000000000 : ℝ)*X 0 2+(2163264649/5000000000 : ℝ)*X 1 0+(4017101121/10000000000 : ℝ)*X 1 1+(931671077/2000000000 : ℝ)*X 1 2+(2163264649/5000000000 : ℝ)*X 2 0+(4017101121/10000000000 : ℝ)*X 2 1+(931671077/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2055731827/10000000000 : ℝ)*X 0 0+(517990489/1000000000 : ℝ)*X 0 1+(1371265723/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057670633/2000000000 : ℝ)*X 1 0+(-477122239/2500000000 : ℝ)*X 1 1+(685632871/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1322088317/2500000000 : ℝ)*X 2 0+(5485062899/10000000000 : ℝ)*X 2 1+(-1908488911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2163340489/5000000000 : ℝ)*X 0 0+(2327106737/5000000000 : ℝ)*X 0 1+(4021284203/10000000000 : ℝ)*X 0 2+(2163340489/5000000000 : ℝ)*X 1 0+(2327106737/5000000000 : ℝ)*X 1 1+(4021284203/10000000000 : ℝ)*X 1 2+(2163340489/5000000000 : ℝ)*X 2 0+(2327106737/5000000000 : ℝ)*X 2 1+(4021284203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (234388512277115410417659/32540000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1221161199/50000000000000 : ℝ)*(base19) + (93825719/6250000000000 : ℝ)*(base23) + (301072901/100000000000000 : ℝ)*(lower2) + (737129357/100000000000000 : ℝ)*(upper3) + (85564997/50000000000000 : ℝ)*(upper5) + (2396996519066493/100000000000000 : ℝ)*(major0) + (2396996519066493/100000000000000 : ℝ)*(major1) + (2396996519066493/100000000000000 : ℝ)*(major2) + (3234504963667667/100000000000000 : ℝ)*(sp0) + (1617256131724349/50000000000000 : ℝ)*(sp1) + (3234513204559591/100000000000000 : ℝ)*(sp2) + (12475664984861/800000000000 : ℝ)*(sp3) + (2435525857/25000000000000 : ℝ)*(sp4) + (9984575647/50000000000000 : ℝ)*(sp7) + (779739046129459/50000000000000 : ℝ)*(f.failure) + (404314338221387/12500000000000 : ℝ)*(f.sum) + (149786534758849/32540000000000000000000000000 : ℝ)*base66 + (8511197075286709971/1627000000000000000000000000000000 : ℝ)*base68 + (4412262773399290029/1627000000000000000000000000000000 : ℝ)*base69 + (9846429000542709971/1627000000000000000000000000000000 : ℝ)*base72 + (82094257823469/32540000000000000000000000000 : ℝ)*base74 + (2652399826910290029/1627000000000000000000000000000000 : ℝ)*base75 + (3044815179204290029/1627000000000000000000000000000000 : ℝ)*base77 + (6928849003450709971/1627000000000000000000000000000000 : ℝ)*base80 + (24509056329249/32540000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (16224943/2500000000000000000000 : ℝ)*base90 + (16224943/2500000000000000000000 : ℝ)*base92 + (16224943/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1277449895800097998345298517/203375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1249732367/100000000000000 : ℝ)*(base19) + (759084919/50000000000000 : ℝ)*(base23) + (91031621/50000000000000 : ℝ)*(upper3) + (3071617/4000000000000 : ℝ)*(lower4) + (2444441/3125000000000 : ℝ)*(upper5) + (607118075413579/25000000000000 : ℝ)*(major0) + (607118075413579/25000000000000 : ℝ)*(major1) + (607118075413579/25000000000000 : ℝ)*(major2) + (6626766141/50000000000000 : ℝ)*(sp1) + (8603694493/50000000000000 : ℝ)*(sp2) + (1638494130256339/50000000000000 : ℝ)*(sp4) + (3276973757248029/100000000000000 : ℝ)*(sp5) + (1638484767476927/50000000000000 : ℝ)*(sp6) + (315991226684167/20000000000000 : ℝ)*(sp7) + (315991226684167/20000000000000 : ℝ)*(f.failure) + (1638494130256339/50000000000000 : ℝ)*(f.sum) + (13403125274653/8135000000000000000000000000 : ℝ)*base65 + (1776981854052547387/406750000000000000000000000000000 : ℝ)*base67 + (3228514756173297387/406750000000000000000000000000000 : ℝ)*base69 + (6909034931848797387/406750000000000000000000000000000 : ℝ)*base71 + (56173497260677/8135000000000000000000000000 : ℝ)*base74 + (2836079565868297387/406750000000000000000000000000000 : ℝ)*base75 + (3519742966692047387/406750000000000000000000000000000 : ℝ)*base77 + (6034322363319547387/406750000000000000000000000000000 : ℝ)*base79 + (10249301951321/4067500000000000000000000000 : ℝ)*base82 + (1896659/1000000000000000000000 : ℝ)*base90 + (1896659/1000000000000000000000 : ℝ)*base92 + (1896659/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1316_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76852523/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (983/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1661/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2419/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16211/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1316_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1316_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76852523/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2419/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16211/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1316_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1316_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1316_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76852523/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2419/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16211/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1316_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1270_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:09.713901+00:00
-- url     : https://prove2.me/submissions/4dd2c5a0-aee7-4d11-86ca-d4110ea1b4e3

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
theorem support_rectangle_w1270_s0_0 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-925822353/5000000000 : ℝ)*x 0 + (3012496539/5000000000 : ℝ)*x 1 + (4796567377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (925822353/5000000000 : ℝ)^529 ≤ (5404189947671/50000000000000 : ℝ)^401 := by
    have hnat : (925822353 : ℕ)^529*50000000000000^401 ≤ 5404189947671^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925822353 5000000000 5404189947671 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3012496539/5000000000 : ℝ)^529 ≤ (25626438260711/50000000000000 : ℝ)^401 := by
    have hnat : (3012496539 : ℕ)^529*50000000000000^401 ≤ 25626438260711^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3012496539 5000000000 25626438260711 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4796567377/10000000000 : ℝ)^529 ≤ (7587748714657/20000000000000 : ℝ)^401 := by
    have hnat : (4796567377 : ℕ)^529*20000000000000^401 ≤ 7587748714657^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4796567377 10000000000 7587748714657 20000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-925822353/5000000000 : ℝ), (3012496539/5000000000 : ℝ), (4796567377/10000000000 : ℝ)] ![(5404189947671/50000000000000 : ℝ), (25626438260711/50000000000000 : ℝ), (7587748714657/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-925822353/5000000000 : ℝ)|^529 ≤ (5404189947671/50000000000000 : ℝ)^401
        have hw : |(-925822353/5000000000 : ℝ)|=(925822353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3012496539/5000000000 : ℝ)|^529 ≤ (25626438260711/50000000000000 : ℝ)^401
        have hw : |(3012496539/5000000000 : ℝ)|=(3012496539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4796567377/10000000000 : ℝ)|^529 ≤ (7587748714657/20000000000000 : ℝ)^401
        have hw : |(4796567377/10000000000 : ℝ)|=(4796567377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s0_1 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1377381447/2500000000 : ℝ)*x 0 + (-1276567451/5000000000 : ℝ)*x 1 + (4796567351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1377381447/2500000000 : ℝ)^529 ≤ (45548844360233/100000000000000 : ℝ)^401 := by
    have hnat : (1377381447 : ℕ)^529*100000000000000^401 ≤ 45548844360233^401*2500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377381447 2500000000 45548844360233 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1276567451/5000000000 : ℝ)^529 ≤ (8256206162631/50000000000000 : ℝ)^401 := by
    have hnat : (1276567451 : ℕ)^529*50000000000000^401 ≤ 8256206162631^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1276567451 5000000000 8256206162631 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4796567351/10000000000 : ℝ)^529 ≤ (37938743301993/100000000000000 : ℝ)^401 := by
    have hnat : (4796567351 : ℕ)^529*100000000000000^401 ≤ 37938743301993^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4796567351 10000000000 37938743301993 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1377381447/2500000000 : ℝ), (-1276567451/5000000000 : ℝ), (4796567351/10000000000 : ℝ)] ![(45548844360233/100000000000000 : ℝ), (8256206162631/50000000000000 : ℝ), (37938743301993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1377381447/2500000000 : ℝ)|^529 ≤ (45548844360233/100000000000000 : ℝ)^401
        have hw : |(1377381447/2500000000 : ℝ)|=(1377381447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1276567451/5000000000 : ℝ)|^529 ≤ (8256206162631/50000000000000 : ℝ)^401
        have hw : |(-1276567451/5000000000 : ℝ)|=(1276567451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4796567351/10000000000 : ℝ)|^529 ≤ (37938743301993/100000000000000 : ℝ)^401
        have hw : |(4796567351/10000000000 : ℝ)|=(4796567351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s0_2 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2754762903/5000000000 : ℝ)*x 0 + (4796567351/10000000000 : ℝ)*x 1 + (-1276567439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2754762903/5000000000 : ℝ)^529 ≤ (9109768911309/20000000000000 : ℝ)^401 := by
    have hnat : (2754762903 : ℕ)^529*20000000000000^401 ≤ 9109768911309^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754762903 5000000000 9109768911309 20000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4796567351/10000000000 : ℝ)^529 ≤ (37938743301993/100000000000000 : ℝ)^401 := by
    have hnat : (4796567351 : ℕ)^529*100000000000000^401 ≤ 37938743301993^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4796567351 10000000000 37938743301993 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1276567439/5000000000 : ℝ)^529 ≤ (1032025757531/6250000000000 : ℝ)^401 := by
    have hnat : (1276567439 : ℕ)^529*6250000000000^401 ≤ 1032025757531^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1276567439 5000000000 1032025757531 6250000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2754762903/5000000000 : ℝ), (4796567351/10000000000 : ℝ), (-1276567439/5000000000 : ℝ)] ![(9109768911309/20000000000000 : ℝ), (37938743301993/100000000000000 : ℝ), (1032025757531/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2754762903/5000000000 : ℝ)|^529 ≤ (9109768911309/20000000000000 : ℝ)^401
        have hw : |(2754762903/5000000000 : ℝ)|=(2754762903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4796567351/10000000000 : ℝ)|^529 ≤ (37938743301993/100000000000000 : ℝ)^401
        have hw : |(4796567351/10000000000 : ℝ)|=(4796567351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1276567439/5000000000 : ℝ)|^529 ≤ (1032025757531/6250000000000 : ℝ)^401
        have hw : |(-1276567439/5000000000 : ℝ)|=(1276567439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s0_3 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4190753249/10000000000 : ℝ)*x 0 + (194739913/625000000 : ℝ)*x 1 + (5621747911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4190753249/10000000000 : ℝ)^529 ≤ (7937193732501/25000000000000 : ℝ)^401 := by
    have hnat : (4190753249 : ℕ)^529*25000000000000^401 ≤ 7937193732501^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4190753249 10000000000 7937193732501 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (194739913/625000000 : ℝ)^529 ≤ (21474500427177/100000000000000 : ℝ)^401 := by
    have hnat : (194739913 : ℕ)^529*100000000000000^401 ≤ 21474500427177^401*625000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194739913 625000000 21474500427177 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5621747911/10000000000 : ℝ)^529 ≤ (5847090577859/12500000000000 : ℝ)^401 := by
    have hnat : (5621747911 : ℕ)^529*12500000000000^401 ≤ 5847090577859^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5621747911 10000000000 5847090577859 12500000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4190753249/10000000000 : ℝ), (194739913/625000000 : ℝ), (5621747911/10000000000 : ℝ)] ![(7937193732501/25000000000000 : ℝ), (21474500427177/100000000000000 : ℝ), (5847090577859/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4190753249/10000000000 : ℝ)|^529 ≤ (7937193732501/25000000000000 : ℝ)^401
        have hw : |(4190753249/10000000000 : ℝ)|=(4190753249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(194739913/625000000 : ℝ)|^529 ≤ (21474500427177/100000000000000 : ℝ)^401
        have hw : |(194739913/625000000 : ℝ)|=(194739913/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5621747911/10000000000 : ℝ)|^529 ≤ (5847090577859/12500000000000 : ℝ)^401
        have hw : |(5621747911/10000000000 : ℝ)|=(5621747911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s0_4 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-29006567/156250000 : ℝ)*x 0 + (96563649/200000000 : ℝ)*x 1 + (374516233/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (29006567/156250000 : ℝ)^529 ≤ (2647746337/24414062500 : ℝ)^401 := by
    have hnat : (29006567 : ℕ)^529*24414062500^401 ≤ 2647746337^401*156250000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29006567 156250000 2647746337 24414062500 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96563649/200000000 : ℝ)^529 ≤ (38268971518879/100000000000000 : ℝ)^401 := by
    have hnat : (96563649 : ℕ)^529*100000000000000^401 ≤ 38268971518879^401*200000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96563649 200000000 38268971518879 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (374516233/625000000 : ℝ)^529 ≤ (795091554243/1562500000000 : ℝ)^401 := by
    have hnat : (374516233 : ℕ)^529*1562500000000^401 ≤ 795091554243^401*625000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374516233 625000000 795091554243 1562500000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-29006567/156250000 : ℝ), (96563649/200000000 : ℝ), (374516233/625000000 : ℝ)] ![(2647746337/24414062500 : ℝ), (38268971518879/100000000000000 : ℝ), (795091554243/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-29006567/156250000 : ℝ)|^529 ≤ (2647746337/24414062500 : ℝ)^401
        have hw : |(-29006567/156250000 : ℝ)|=(29006567/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(96563649/200000000 : ℝ)|^529 ≤ (38268971518879/100000000000000 : ℝ)^401
        have hw : |(96563649/200000000 : ℝ)|=(96563649/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(374516233/625000000 : ℝ)|^529 ≤ (795091554243/1562500000000 : ℝ)^401
        have hw : |(374516233/625000000 : ℝ)|=(374516233/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s0_5 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5175169399/10000000000 : ℝ)*x 0 + (-678720031/5000000000 : ℝ)*x 1 + (5992262209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5175169399/10000000000 : ℝ)^529 ≤ (41938097226653/100000000000000 : ℝ)^401 := by
    have hnat : (5175169399 : ℕ)^529*100000000000000^401 ≤ 41938097226653^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175169399 10000000000 41938097226653 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678720031/5000000000 : ℝ)^529 ≤ (3588007745207/50000000000000 : ℝ)^401 := by
    have hnat : (678720031 : ℕ)^529*50000000000000^401 ≤ 3588007745207^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678720031 5000000000 3588007745207 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5992262209/10000000000 : ℝ)^529 ≤ (50885887265137/100000000000000 : ℝ)^401 := by
    have hnat : (5992262209 : ℕ)^529*100000000000000^401 ≤ 50885887265137^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5992262209 10000000000 50885887265137 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5175169399/10000000000 : ℝ), (-678720031/5000000000 : ℝ), (5992262209/10000000000 : ℝ)] ![(41938097226653/100000000000000 : ℝ), (3588007745207/50000000000000 : ℝ), (50885887265137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5175169399/10000000000 : ℝ)|^529 ≤ (41938097226653/100000000000000 : ℝ)^401
        have hw : |(5175169399/10000000000 : ℝ)|=(5175169399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-678720031/5000000000 : ℝ)|^529 ≤ (3588007745207/50000000000000 : ℝ)^401
        have hw : |(-678720031/5000000000 : ℝ)|=(678720031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5992262209/10000000000 : ℝ)|^529 ≤ (50885887265137/100000000000000 : ℝ)^401
        have hw : |(5992262209/10000000000 : ℝ)|=(5992262209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s0_6 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5175170521/10000000000 : ℝ)*x 0 + (299613007/500000000 : ℝ)*x 1 + (-678720833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5175170521/10000000000 : ℝ)^529 ≤ (41938109221323/100000000000000 : ℝ)^401 := by
    have hnat : (5175170521 : ℕ)^529*100000000000000^401 ≤ 41938109221323^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175170521 10000000000 41938109221323 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (299613007/500000000 : ℝ)^529 ≤ (12721466021753/25000000000000 : ℝ)^401 := by
    have hnat : (299613007 : ℕ)^529*25000000000000^401 ≤ 12721466021753^401*500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299613007 500000000 12721466021753 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678720833/5000000000 : ℝ)^529 ≤ (7176026676507/100000000000000 : ℝ)^401 := by
    have hnat : (678720833 : ℕ)^529*100000000000000^401 ≤ 7176026676507^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678720833 5000000000 7176026676507 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5175170521/10000000000 : ℝ), (299613007/500000000 : ℝ), (-678720833/5000000000 : ℝ)] ![(41938109221323/100000000000000 : ℝ), (12721466021753/25000000000000 : ℝ), (7176026676507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5175170521/10000000000 : ℝ)|^529 ≤ (41938109221323/100000000000000 : ℝ)^401
        have hw : |(5175170521/10000000000 : ℝ)|=(5175170521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(299613007/500000000 : ℝ)|^529 ≤ (12721466021753/25000000000000 : ℝ)^401
        have hw : |(299613007/500000000 : ℝ)|=(299613007/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-678720833/5000000000 : ℝ)|^529 ≤ (7176026676507/100000000000000 : ℝ)^401
        have hw : |(-678720833/5000000000 : ℝ)|=(678720833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s0_7 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2100249119/5000000000 : ℝ)*x 0 + (5557261377/10000000000 : ℝ)*x 1 + (3182606263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100249119/5000000000 : ℝ)^529 ≤ (31846204009367/100000000000000 : ℝ)^401 := by
    have hnat : (2100249119 : ℕ)^529*100000000000000^401 ≤ 31846204009367^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100249119 5000000000 31846204009367 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5557261377/10000000000 : ℝ)^529 ≤ (46070177924331/100000000000000 : ℝ)^401 := by
    have hnat : (5557261377 : ℕ)^529*100000000000000^401 ≤ 46070177924331^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5557261377 10000000000 46070177924331 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3182606263/10000000000 : ℝ)^529 ≤ (22083618042289/100000000000000 : ℝ)^401 := by
    have hnat : (3182606263 : ℕ)^529*100000000000000^401 ≤ 22083618042289^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3182606263 10000000000 22083618042289 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2100249119/5000000000 : ℝ), (5557261377/10000000000 : ℝ), (3182606263/10000000000 : ℝ)] ![(31846204009367/100000000000000 : ℝ), (46070177924331/100000000000000 : ℝ), (22083618042289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2100249119/5000000000 : ℝ)|^529 ≤ (31846204009367/100000000000000 : ℝ)^401
        have hw : |(2100249119/5000000000 : ℝ)|=(2100249119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5557261377/10000000000 : ℝ)|^529 ≤ (46070177924331/100000000000000 : ℝ)^401
        have hw : |(5557261377/10000000000 : ℝ)|=(5557261377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3182606263/10000000000 : ℝ)|^529 ≤ (22083618042289/100000000000000 : ℝ)^401
        have hw : |(3182606263/10000000000 : ℝ)|=(3182606263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1270_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (933/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (854/3125 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8463/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8463 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8463*1^2048 ≤ 0^2048*1^8463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8463 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8463/2048 : ℝ) ≤ (2267685716401933501/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8463 ≤ (2267685716401933501/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8463*100000000000000000000^2048 ≤ 2267685716401933501^2048*5^8463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2267685716401933501 100000000000000000000 8463 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2267685716401933501/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8463 := by
      have hnat : (1 : ℕ)^2048*1^8463 ≤ 1^8463*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102267685716401933501/100000000000000000000 : ℝ) ≤ (1005441128961863/1000000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (102267685716401933501/100000000000000000000 : ℝ)^2048 ≤ (1005441128961863/1000000000000000 : ℝ)^8463 := by
      have hnat : (102267685716401933501 : ℕ)^2048*1000000000000000^8463 ≤ 1005441128961863^8463*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102267685716401933501 100000000000000000000 1005441128961863 1000000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1005441128961863/1000000000000000 : ℝ)) (X := (102267685716401933501/100000000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52267685716401933501/50000000000000000000 : ℝ) ≤ (505441128961863/500000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (52267685716401933501/50000000000000000000 : ℝ)^2048 ≤ (505441128961863/500000000000000 : ℝ)^8463 := by
      have hnat : (52267685716401933501 : ℕ)^2048*500000000000000^8463 ≤ 505441128961863^8463*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52267685716401933501 50000000000000000000 505441128961863 500000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (505441128961863/500000000000000 : ℝ)) (X := (52267685716401933501/50000000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(5441128961863/400000000000000 : ℝ)*(0 : ℝ))^(8463/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(5441128961863/400000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2267685716401933501/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(5441128961863/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8463/2048 : ℝ) := by
    rw [show (1 : ℝ)+(5441128961863/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1005441128961863/1000000000000000 : ℝ) by norm_num, show 1+(2267685716401933501/100000000000000000000 : ℝ)+(0 : ℝ)=(102267685716401933501/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2267685716401933501/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(5441128961863/400000000000000 : ℝ)*(2/5 : ℝ))^(8463/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(5441128961863/400000000000000 : ℝ)*(2/5 : ℝ)=(505441128961863/500000000000000 : ℝ) by norm_num, show 1+2*(2267685716401933501/100000000000000000000 : ℝ)=(52267685716401933501/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(5441128961863/400000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5441128961863/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(5441128961863/400000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5441128961863/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(5441128961863/400000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5441128961863/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-925822353/5000000000 : ℝ)*X 0 0+(3012496539/5000000000 : ℝ)*X 0 1+(4796567377/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1377381447/2500000000 : ℝ)*X 1 0+(-1276567451/5000000000 : ℝ)*X 1 1+(4796567351/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2754762903/5000000000 : ℝ)*X 2 0+(4796567351/10000000000 : ℝ)*X 2 1+(-1276567439/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4190753249/10000000000 : ℝ)*X 0 0+(194739913/625000000 : ℝ)*X 0 1+(5621747911/10000000000 : ℝ)*X 0 2+(4190753249/10000000000 : ℝ)*X 1 0+(194739913/625000000 : ℝ)*X 1 1+(5621747911/10000000000 : ℝ)*X 1 2+(4190753249/10000000000 : ℝ)*X 2 0+(194739913/625000000 : ℝ)*X 2 1+(5621747911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-29006567/156250000 : ℝ)*X 0 0+(96563649/200000000 : ℝ)*X 0 1+(374516233/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5175169399/10000000000 : ℝ)*X 1 0+(-678720031/5000000000 : ℝ)*X 1 1+(5992262209/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5175170521/10000000000 : ℝ)*X 2 0+(299613007/500000000 : ℝ)*X 2 1+(-678720833/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2100249119/5000000000 : ℝ)*X 0 0+(5557261377/10000000000 : ℝ)*X 0 1+(3182606263/10000000000 : ℝ)*X 0 2+(2100249119/5000000000 : ℝ)*X 1 0+(5557261377/10000000000 : ℝ)*X 1 1+(3182606263/10000000000 : ℝ)*X 1 2+(2100249119/5000000000 : ℝ)*X 2 0+(5557261377/10000000000 : ℝ)*X 2 1+(3182606263/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18509547189078339039921/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1760963/4000000000000 : ℝ)*(base1) + (901972017/100000000000000 : ℝ)*(base19) + (90463159/10000000000000 : ℝ)*(base23) + (101866427/100000000000000 : ℝ)*(upper3) + (54280419/50000000000000 : ℝ)*(upper5) + (303278794952589/50000000000000 : ℝ)*(major0) + (303278794952589/50000000000000 : ℝ)*(major1) + (303278794952589/50000000000000 : ℝ)*(major2) + (814052732223481/100000000000000 : ℝ)*(sp0) + (407027332596219/50000000000000 : ℝ)*(sp1) + (162810932506573/20000000000000 : ℝ)*(sp2) + (39905806513397/10000000000000 : ℝ)*(sp3) + (2878965049/100000000000000 : ℝ)*(sp4) + (172511359/12500000000000 : ℝ)*(sp7) + (99764872312229/25000000000000 : ℝ)*(f.failure) + (162811113432891/20000000000000 : ℝ)*(f.sum) + (6816089566693/10000000000000000000000000000 : ℝ)*base66 + (126838507326693/20000000000000000000000000000 : ℝ)*base68 + (69754006186693/20000000000000000000000000000 : ℝ)*base70 + (110914990086693/20000000000000000000000000000 : ℝ)*base72 + (930939833307/10000000000000000000000000000 : ℝ)*base73 + (13007320766693/20000000000000000000000000000 : ℝ)*base76 + (68855451006693/20000000000000000000000000000 : ℝ)*base78 + (104923228266693/20000000000000000000000000000 : ℝ)*base80 + (11567848753307/10000000000000000000000000000 : ℝ)*base81 + (116971/156250000000000000000 : ℝ)*base89 + (116971/156250000000000000000 : ℝ)*base91 + (116971/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2791804045756929219/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (279473039/100000000000000 : ℝ)*(base1) + (1161379847/100000000000000 : ℝ)*(base19) + (663315603/50000000000000 : ℝ)*(base23) + (62150857/25000000000000 : ℝ)*(upper3) + (64008153871727/10000000000000 : ℝ)*(major0) + (64008153871727/10000000000000 : ℝ)*(major1) + (64008153871727/10000000000000 : ℝ)*(major2) + (274431843/12500000000000 : ℝ)*(sp1) + (23381493/1250000000000 : ℝ)*(sp2) + (193406049/100000000000000 : ℝ)*(sp3) + (171809597080929/20000000000000 : ℝ)*(sp4) + (171808869819403/20000000000000 : ℝ)*(sp5) + (5369028179881/625000000000 : ℝ)*(sp6) + (84222942500713/20000000000000 : ℝ)*(sp7) + (105278796345663/25000000000000 : ℝ)*(f.failure) + (859047705931607/100000000000000 : ℝ)*(f.sum) + (317990874599/2000000000000000000000000000 : ℝ)*base66 + (11568660759401/4000000000000000000000000000 : ℝ)*base67 + (3747665771401/4000000000000000000000000000 : ℝ)*base69 + (23737961235401/4000000000000000000000000000 : ℝ)*base71 + (4685940610599/2000000000000000000000000000 : ℝ)*base74 + (20107534895401/4000000000000000000000000000 : ℝ)*base75 + (18227695063401/4000000000000000000000000000 : ℝ)*base77 + (16463630399401/4000000000000000000000000000 : ℝ)*base79 + (7118090160599/2000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1353263/156250000000000000000 : ℝ)*base90 + (1353263/156250000000000000000 : ℝ)*base92 + (1353263/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1270_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (933/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (854/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1270_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1270_s1_0 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1023472109/5000000000 : ℝ)*x 0 + (1133679169/2000000000 : ℝ)*x 1 + (5028148987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1023472109/5000000000 : ℝ)^529 ≤ (2467400603857/20000000000000 : ℝ)^401 := by
    have hnat : (1023472109 : ℕ)^529*20000000000000^401 ≤ 2467400603857^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023472109 5000000000 2467400603857 20000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133679169/2000000000 : ℝ)^529 ≤ (47289439413721/100000000000000 : ℝ)^401 := by
    have hnat : (1133679169 : ℕ)^529*100000000000000^401 ≤ 47289439413721^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133679169 2000000000 47289439413721 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5028148987/10000000000 : ℝ)^529 ≤ (1009338939013/2500000000000 : ℝ)^401 := by
    have hnat : (5028148987 : ℕ)^529*2500000000000^401 ≤ 1009338939013^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5028148987 10000000000 1009338939013 2500000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1023472109/5000000000 : ℝ), (1133679169/2000000000 : ℝ), (5028148987/10000000000 : ℝ)] ![(2467400603857/20000000000000 : ℝ), (47289439413721/100000000000000 : ℝ), (1009338939013/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1023472109/5000000000 : ℝ)|^529 ≤ (2467400603857/20000000000000 : ℝ)^401
        have hw : |(-1023472109/5000000000 : ℝ)|=(1023472109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1133679169/2000000000 : ℝ)|^529 ≤ (47289439413721/100000000000000 : ℝ)^401
        have hw : |(1133679169/2000000000 : ℝ)|=(1133679169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5028148987/10000000000 : ℝ)|^529 ≤ (1009338939013/2500000000000 : ℝ)^401
        have hw : |(5028148987/10000000000 : ℝ)|=(5028148987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s1_1 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5412087063/10000000000 : ℝ)*x 0 + (-478055383/2000000000 : ℝ)*x 1 + (5028149161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5412087063/10000000000 : ℝ)^529 ≤ (1390286482117/3125000000000 : ℝ)^401 := by
    have hnat : (5412087063 : ℕ)^529*3125000000000^401 ≤ 1390286482117^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412087063 10000000000 1390286482117 3125000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (478055383/2000000000 : ℝ)^529 ≤ (15137273159099/100000000000000 : ℝ)^401 := by
    have hnat : (478055383 : ℕ)^529*100000000000000^401 ≤ 15137273159099^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478055383 2000000000 15137273159099 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5028149161/10000000000 : ℝ)^529 ≤ (40373559403623/100000000000000 : ℝ)^401 := by
    have hnat : (5028149161 : ℕ)^529*100000000000000^401 ≤ 40373559403623^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5028149161 10000000000 40373559403623 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5412087063/10000000000 : ℝ), (-478055383/2000000000 : ℝ), (5028149161/10000000000 : ℝ)] ![(1390286482117/3125000000000 : ℝ), (15137273159099/100000000000000 : ℝ), (40373559403623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5412087063/10000000000 : ℝ)|^529 ≤ (1390286482117/3125000000000 : ℝ)^401
        have hw : |(5412087063/10000000000 : ℝ)|=(5412087063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-478055383/2000000000 : ℝ)|^529 ≤ (15137273159099/100000000000000 : ℝ)^401
        have hw : |(-478055383/2000000000 : ℝ)|=(478055383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5028149161/10000000000 : ℝ)|^529 ≤ (40373559403623/100000000000000 : ℝ)^401
        have hw : |(5028149161/10000000000 : ℝ)|=(5028149161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s1_2 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5412087217/10000000000 : ℝ)*x 0 + (5028149069/10000000000 : ℝ)*x 1 + (-74696151/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5412087217/10000000000 : ℝ)^529 ≤ (44489169097763/100000000000000 : ℝ)^401 := by
    have hnat : (5412087217 : ℕ)^529*100000000000000^401 ≤ 44489169097763^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412087217 10000000000 44489169097763 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5028149069/10000000000 : ℝ)^529 ≤ (40373558429109/100000000000000 : ℝ)^401 := by
    have hnat : (5028149069 : ℕ)^529*100000000000000^401 ≤ 40373558429109^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5028149069 10000000000 40373558429109 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74696151/312500000 : ℝ)^529 ≤ (15137272465691/100000000000000 : ℝ)^401 := by
    have hnat : (74696151 : ℕ)^529*100000000000000^401 ≤ 15137272465691^401*312500000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74696151 312500000 15137272465691 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5412087217/10000000000 : ℝ), (5028149069/10000000000 : ℝ), (-74696151/312500000 : ℝ)] ![(44489169097763/100000000000000 : ℝ), (40373558429109/100000000000000 : ℝ), (15137272465691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5412087217/10000000000 : ℝ)|^529 ≤ (44489169097763/100000000000000 : ℝ)^401
        have hw : |(5412087217/10000000000 : ℝ)|=(5412087217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5028149069/10000000000 : ℝ)|^529 ≤ (40373558429109/100000000000000 : ℝ)^401
        have hw : |(5028149069/10000000000 : ℝ)|=(5028149069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-74696151/312500000 : ℝ)|^529 ≤ (15137272465691/100000000000000 : ℝ)^401
        have hw : |(-74696151/312500000 : ℝ)|=(74696151/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s1_3 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (53829111/125000000 : ℝ)*x 0 + (740128593/2000000000 : ℝ)*x 1 + (250335289/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53829111/125000000 : ℝ)^529 ≤ (16454454353501/50000000000000 : ℝ)^401 := by
    have hnat : (53829111 : ℕ)^529*50000000000000^401 ≤ 16454454353501^401*125000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53829111 125000000 16454454353501 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (740128593/2000000000 : ℝ)^529 ≤ (1347225851543/5000000000000 : ℝ)^401 := by
    have hnat : (740128593 : ℕ)^529*5000000000000^401 ≤ 1347225851543^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740128593 2000000000 1347225851543 5000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250335289/500000000 : ℝ)^529 ≤ (10036643561457/25000000000000 : ℝ)^401 := by
    have hnat : (250335289 : ℕ)^529*25000000000000^401 ≤ 10036643561457^401*500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250335289 500000000 10036643561457 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53829111/125000000 : ℝ), (740128593/2000000000 : ℝ), (250335289/500000000 : ℝ)] ![(16454454353501/50000000000000 : ℝ), (1347225851543/5000000000000 : ℝ), (10036643561457/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53829111/125000000 : ℝ)|^529 ≤ (16454454353501/50000000000000 : ℝ)^401
        have hw : |(53829111/125000000 : ℝ)|=(53829111/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(740128593/2000000000 : ℝ)|^529 ≤ (1347225851543/5000000000000 : ℝ)^401
        have hw : |(740128593/2000000000 : ℝ)|=(740128593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(250335289/500000000 : ℝ)|^529 ≤ (10036643561457/25000000000000 : ℝ)^401
        have hw : |(250335289/500000000 : ℝ)|=(250335289/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s1_4 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2047586993/10000000000 : ℝ)*x 0 + (5036464017/10000000000 : ℝ)*x 1 + (14149811/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2047586993/10000000000 : ℝ)^529 ≤ (1542764237439/12500000000000 : ℝ)^401 := by
    have hnat : (2047586993 : ℕ)^529*12500000000000^401 ≤ 1542764237439^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047586993 10000000000 1542764237439 12500000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5036464017/10000000000 : ℝ)^529 ≤ (20230829049981/50000000000000 : ℝ)^401 := by
    have hnat : (5036464017 : ℕ)^529*50000000000000^401 ≤ 20230829049981^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5036464017 10000000000 20230829049981 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14149811/25000000 : ℝ)^529 ≤ (11799056996917/25000000000000 : ℝ)^401 := by
    have hnat : (14149811 : ℕ)^529*25000000000000^401 ≤ 11799056996917^401*25000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14149811 25000000 11799056996917 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2047586993/10000000000 : ℝ), (5036464017/10000000000 : ℝ), (14149811/25000000 : ℝ)] ![(1542764237439/12500000000000 : ℝ), (20230829049981/50000000000000 : ℝ), (11799056996917/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2047586993/10000000000 : ℝ)|^529 ≤ (1542764237439/12500000000000 : ℝ)^401
        have hw : |(-2047586993/10000000000 : ℝ)|=(2047586993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5036464017/10000000000 : ℝ)|^529 ≤ (20230829049981/50000000000000 : ℝ)^401
        have hw : |(5036464017/10000000000 : ℝ)|=(5036464017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(14149811/25000000 : ℝ)|^529 ≤ (11799056996917/25000000000000 : ℝ)^401
        have hw : |(14149811/25000000 : ℝ)|=(14149811/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s1_5 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (262345857/500000000 : ℝ)*x 0 + (-1758501263/10000000000 : ℝ)*x 1 + (5659924963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262345857/500000000 : ℝ)^529 ≤ (10676700942811/25000000000000 : ℝ)^401 := by
    have hnat : (262345857 : ℕ)^529*25000000000000^401 ≤ 10676700942811^401*500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262345857 500000000 10676700942811 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1758501263/10000000000 : ℝ)^529 ≤ (5048481020329/50000000000000 : ℝ)^401 := by
    have hnat : (1758501263 : ℕ)^529*50000000000000^401 ≤ 5048481020329^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1758501263 10000000000 5048481020329 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5659924963/10000000000 : ℝ)^529 ≤ (23598117090443/50000000000000 : ℝ)^401 := by
    have hnat : (5659924963 : ℕ)^529*50000000000000^401 ≤ 23598117090443^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5659924963 10000000000 23598117090443 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262345857/500000000 : ℝ), (-1758501263/10000000000 : ℝ), (5659924963/10000000000 : ℝ)] ![(10676700942811/25000000000000 : ℝ), (5048481020329/50000000000000 : ℝ), (23598117090443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262345857/500000000 : ℝ)|^529 ≤ (10676700942811/25000000000000 : ℝ)^401
        have hw : |(262345857/500000000 : ℝ)|=(262345857/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1758501263/10000000000 : ℝ)|^529 ≤ (5048481020329/50000000000000 : ℝ)^401
        have hw : |(-1758501263/10000000000 : ℝ)|=(1758501263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5659924963/10000000000 : ℝ)|^529 ≤ (23598117090443/50000000000000 : ℝ)^401
        have hw : |(5659924963/10000000000 : ℝ)|=(5659924963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s1_6 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1049383411/2000000000 : ℝ)*x 0 + (5659924627/10000000000 : ℝ)*x 1 + (-175850187/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049383411/2000000000 : ℝ)^529 ≤ (8541360571711/20000000000000 : ℝ)^401 := by
    have hnat : (1049383411 : ℕ)^529*20000000000000^401 ≤ 8541360571711^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049383411 2000000000 8541360571711 20000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5659924627/10000000000 : ℝ)^529 ≤ (11799057621189/25000000000000 : ℝ)^401 := by
    have hnat : (5659924627 : ℕ)^529*25000000000000^401 ≤ 11799057621189^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5659924627 10000000000 11799057621189 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (175850187/1000000000 : ℝ)^529 ≤ (10096966638437/100000000000000 : ℝ)^401 := by
    have hnat : (175850187 : ℕ)^529*100000000000000^401 ≤ 10096966638437^401*1000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175850187 1000000000 10096966638437 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049383411/2000000000 : ℝ), (5659924627/10000000000 : ℝ), (-175850187/1000000000 : ℝ)] ![(8541360571711/20000000000000 : ℝ), (11799057621189/25000000000000 : ℝ), (10096966638437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049383411/2000000000 : ℝ)|^529 ≤ (8541360571711/20000000000000 : ℝ)^401
        have hw : |(1049383411/2000000000 : ℝ)|=(1049383411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5659924627/10000000000 : ℝ)|^529 ≤ (11799057621189/25000000000000 : ℝ)^401
        have hw : |(5659924627/10000000000 : ℝ)|=(5659924627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-175850187/1000000000 : ℝ)|^529 ≤ (10096966638437/100000000000000 : ℝ)^401
        have hw : |(-175850187/1000000000 : ℝ)|=(175850187/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s1_7 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2153819811/5000000000 : ℝ)*x 0 + (997948783/2000000000 : ℝ)*x 1 + (3717924201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153819811/5000000000 : ℝ)^529 ≤ (6584424672813/20000000000000 : ℝ)^401 := by
    have hnat : (2153819811 : ℕ)^529*20000000000000^401 ≤ 6584424672813^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153819811 5000000000 6584424672813 20000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (997948783/2000000000 : ℝ)^529 ≤ (7993449401899/20000000000000 : ℝ)^401 := by
    have hnat : (997948783 : ℕ)^529*20000000000000^401 ≤ 7993449401899^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997948783 2000000000 7993449401899 20000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3717924201/10000000000 : ℝ)^529 ≤ (27110629615559/100000000000000 : ℝ)^401 := by
    have hnat : (3717924201 : ℕ)^529*100000000000000^401 ≤ 27110629615559^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3717924201 10000000000 27110629615559 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2153819811/5000000000 : ℝ), (997948783/2000000000 : ℝ), (3717924201/10000000000 : ℝ)] ![(6584424672813/20000000000000 : ℝ), (7993449401899/20000000000000 : ℝ), (27110629615559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2153819811/5000000000 : ℝ)|^529 ≤ (6584424672813/20000000000000 : ℝ)^401
        have hw : |(2153819811/5000000000 : ℝ)|=(2153819811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(997948783/2000000000 : ℝ)|^529 ≤ (7993449401899/20000000000000 : ℝ)^401
        have hw : |(997948783/2000000000 : ℝ)|=(997948783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3717924201/10000000000 : ℝ)|^529 ≤ (27110629615559/100000000000000 : ℝ)^401
        have hw : |(3717924201/10000000000 : ℝ)|=(3717924201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1270_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (854/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (933/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (6341/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19877/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (854/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (933/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (854/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (933/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (854/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (933/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (854/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (933/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (854/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (933/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (854/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (933/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (933/100000 : ℝ) ^ (8463/2048 : ℝ) ≤ (81643712589/20000000000000000000 : ℝ) := by
    have hpowers : (933/100000 : ℝ)^8463 ≤ (81643712589/20000000000000000000 : ℝ)^2048 := by
      have hnat : (933 : ℕ)^8463*20000000000000000000^2048 ≤ 81643712589^2048*100000^8463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        933 100000 81643712589 20000000000000000000 8463 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (933/100000 : ℝ)) (X := (81643712589/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (854/3125 : ℝ) ^ (8463/2048 : ℝ) ≤ (117441334753509791/25000000000000000000 : ℝ) := by
    have hpowers : (854/3125 : ℝ)^8463 ≤ (117441334753509791/25000000000000000000 : ℝ)^2048 := by
      have hnat : (854 : ℕ)^8463*25000000000000000000^2048 ≤ 117441334753509791^2048*3125^8463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        854 3125 117441334753509791 25000000000000000000 8463 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (854/3125 : ℝ)) (X := (117441334753509791/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000081643712589/10000000000000000000 : ℝ) ≤ (2000000003951467/2000000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (10000000081643712589/10000000000000000000 : ℝ)^2048 ≤ (2000000003951467/2000000000000000 : ℝ)^8463 := by
      have hnat : (10000000081643712589 : ℕ)^2048*2000000000000000^8463 ≤ 2000000003951467^8463*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000081643712589 10000000000000000000 2000000003951467 2000000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000003951467/2000000000000000 : ℝ)) (X := (10000000081643712589/10000000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100469765747232602109/100000000000000000000 : ℝ) ≤ (10011347891277289/10000000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (100469765747232602109/100000000000000000000 : ℝ)^2048 ≤ (10011347891277289/10000000000000000 : ℝ)^8463 := by
      have hnat : (100469765747232602109 : ℕ)^2048*10000000000000000^8463 ≤ 10011347891277289^8463*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100469765747232602109 100000000000000000000 10011347891277289 10000000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011347891277289/10000000000000000 : ℝ)) (X := (100469765747232602109/100000000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12617441334753509791/12500000000000000000 : ℝ) ≤ (10022695762797243/10000000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (12617441334753509791/12500000000000000000 : ℝ)^2048 ≤ (10022695762797243/10000000000000000 : ℝ)^8463 := by
      have hnat : (12617441334753509791 : ℕ)^2048*10000000000000000^8463 ≤ 10022695762797243^8463*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12617441334753509791 12500000000000000000 10022695762797243 10000000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10022695762797243/10000000000000000 : ℝ)) (X := (12617441334753509791/12500000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(81643712589/20000000000000000000 : ℝ) ≤ ((263928825393238623161/263950000000000000000 : ℝ)+2*(5673935759977/1319750000000000 : ℝ)*(933/100000 : ℝ))^(8463/2048 : ℝ) := by
    rw [show (263928825393238623161/263950000000000000000 : ℝ)+2*(5673935759977/1319750000000000 : ℝ)*(933/100000 : ℝ)=(2000000003951467/2000000000000000 : ℝ) by norm_num, show 1+2*(81643712589/20000000000000000000 : ℝ)=(10000000081643712589/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(117441334753509791/25000000000000000000 : ℝ)+(81643712589/20000000000000000000 : ℝ) ≤ ((263928825393238623161/263950000000000000000 : ℝ)+(5673935759977/1319750000000000 : ℝ)*((854/3125 : ℝ)+(933/100000 : ℝ)))^(8463/2048 : ℝ) := by
    rw [show (263928825393238623161/263950000000000000000 : ℝ)+(5673935759977/1319750000000000 : ℝ)*((854/3125 : ℝ)+(933/100000 : ℝ))=(10011347891277289/10000000000000000 : ℝ) by norm_num, show 1+(117441334753509791/25000000000000000000 : ℝ)+(81643712589/20000000000000000000 : ℝ)=(100469765747232602109/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(117441334753509791/25000000000000000000 : ℝ) ≤ ((263928825393238623161/263950000000000000000 : ℝ)+2*(5673935759977/1319750000000000 : ℝ)*(854/3125 : ℝ))^(8463/2048 : ℝ) := by
    rw [show (263928825393238623161/263950000000000000000 : ℝ)+2*(5673935759977/1319750000000000 : ℝ)*(854/3125 : ℝ)=(10022695762797243/10000000000000000 : ℝ) by norm_num, show 1+2*(117441334753509791/25000000000000000000 : ℝ)=(12617441334753509791/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (263928825393238623161/263950000000000000000 : ℝ)*(X 1 0+X 2 0)+(5673935759977/1319750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (933/100000 : ℝ)) (hi := (854/3125 : ℝ)) (c := (263928825393238623161/263950000000000000000 : ℝ)) (alpha := (5673935759977/1319750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (263928825393238623161/263950000000000000000 : ℝ)*(X 0 1+X 2 1)+(5673935759977/1319750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (933/100000 : ℝ)) (hi := (854/3125 : ℝ)) (c := (263928825393238623161/263950000000000000000 : ℝ)) (alpha := (5673935759977/1319750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (263928825393238623161/263950000000000000000 : ℝ)*(X 0 2+X 1 2)+(5673935759977/1319750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (933/100000 : ℝ)) (hi := (854/3125 : ℝ)) (c := (263928825393238623161/263950000000000000000 : ℝ)) (alpha := (5673935759977/1319750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1023472109/5000000000 : ℝ)*X 0 0+(1133679169/2000000000 : ℝ)*X 0 1+(5028148987/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5412087063/10000000000 : ℝ)*X 1 0+(-478055383/2000000000 : ℝ)*X 1 1+(5028149161/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5412087217/10000000000 : ℝ)*X 2 0+(5028149069/10000000000 : ℝ)*X 2 1+(-74696151/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((53829111/125000000 : ℝ)*X 0 0+(740128593/2000000000 : ℝ)*X 0 1+(250335289/500000000 : ℝ)*X 0 2+(53829111/125000000 : ℝ)*X 1 0+(740128593/2000000000 : ℝ)*X 1 1+(250335289/500000000 : ℝ)*X 1 2+(53829111/125000000 : ℝ)*X 2 0+(740128593/2000000000 : ℝ)*X 2 1+(250335289/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2047586993/10000000000 : ℝ)*X 0 0+(5036464017/10000000000 : ℝ)*X 0 1+(14149811/25000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((262345857/500000000 : ℝ)*X 1 0+(-1758501263/10000000000 : ℝ)*X 1 1+(5659924963/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1049383411/2000000000 : ℝ)*X 2 0+(5659924627/10000000000 : ℝ)*X 2 1+(-175850187/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2153819811/5000000000 : ℝ)*X 0 0+(997948783/2000000000 : ℝ)*X 0 1+(3717924201/10000000000 : ℝ)*X 0 2+(2153819811/5000000000 : ℝ)*X 1 0+(997948783/2000000000 : ℝ)*X 1 1+(3717924201/10000000000 : ℝ)*X 1 2+(2153819811/5000000000 : ℝ)*X 2 0+(997948783/2000000000 : ℝ)*X 2 1+(3717924201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57531736018999670701093820109/6598750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (199943/250000000000 : ℝ)*(base1) + (1893690177/100000000000000 : ℝ)*(base19) + (1938134277/100000000000000 : ℝ)*(base23) + (199779339/100000000000000 : ℝ)*(upper3) + (48573929/20000000000000 : ℝ)*(upper5) + (581897791015977/50000000000000 : ℝ)*(major0) + (581897791015977/50000000000000 : ℝ)*(major1) + (581897791015977/50000000000000 : ℝ)*(major2) + (1561908231108627/100000000000000 : ℝ)*(sp0) + (1561917791585039/100000000000000 : ℝ)*(sp1) + (78095887357047/5000000000000 : ℝ)*(sp2) + (95708191833067/12500000000000 : ℝ)*(sp3) + (1153414379/10000000000000 : ℝ)*(sp4) + (5573527583/100000000000000 : ℝ)*(sp7) + (765671188169319/100000000000000 : ℝ)*(f.failure) + (97619980329701/6250000000000 : ℝ)*(f.sum) + (166944112580567/65987500000000000000000000000 : ℝ)*base66 + (53980807055164043297/13197500000000000000000000000000000 : ℝ)*base67 + (48258710134280956703/13197500000000000000000000000000000 : ℝ)*base70 + (9465800129146543297/13197500000000000000000000000000000 : ℝ)*base71 + (63518124209971/32993750000000000000000000000 : ℝ)*base74 + (59412889978294043297/13197500000000000000000000000000000 : ℝ)*base75 + (11641889409354043297/13197500000000000000000000000000000 : ℝ)*base77 + (59561582748798456703/13197500000000000000000000000000000 : ℝ)*base80 + (814574305241309/131975000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (4033119/625000000000000000000 : ℝ)*base90 + (4033119/625000000000000000000 : ℝ)*base92 + (4033119/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34930837105936021738599781413/6598750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (477880691/50000000000000 : ℝ)*(base19) + (456395361/50000000000000 : ℝ)*(base23) + (10325729/100000000000000 : ℝ)*(upper2) + (31505731/20000000000000 : ℝ)*(upper3) + (55987829/50000000000000 : ℝ)*(upper5) + (597556414436289/50000000000000 : ℝ)*(major0) + (597556414436289/50000000000000 : ℝ)*(major1) + (597556414436289/50000000000000 : ℝ)*(major2) + (5501656811/100000000000000 : ℝ)*(sp1) + (108421997/2500000000000 : ℝ)*(sp2) + (1603950405320321/100000000000000 : ℝ)*(sp4) + (1603943947902129/100000000000000 : ℝ)*(sp5) + (1603945155649719/100000000000000 : ℝ)*(sp6) + (9828438449663/1250000000000 : ℝ)*(sp7) + (9828438449663/1250000000000 : ℝ)*(f.failure) + (1603950405320321/100000000000000 : ℝ)*(f.sum) + (553747781810587/131975000000000000000000000000 : ℝ)*base65 + (66005956361627389529/13197500000000000000000000000000000 : ℝ)*base67 + (326850486984889529/13197500000000000000000000000000000 : ℝ)*base69 + (17865172029132610471/13197500000000000000000000000000000 : ℝ)*base72 + (158835711445153/32993750000000000000000000000 : ℝ)*base73 + (67030542068120110471/13197500000000000000000000000000000 : ℝ)*base76 + (102654076585347389529/13197500000000000000000000000000000 : ℝ)*base77 + (44029847888617389529/13197500000000000000000000000000000 : ℝ)*base79 + (168708037309919/65987500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (38513/7812500000000000000 : ℝ)*base90 + (38513/7812500000000000000 : ℝ)*base92 + (38513/7812500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1270_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (854/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (933/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6341/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19877/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1270_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1270_s2_0 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-418711123/2000000000 : ℝ)*x 0 + (2743965101/5000000000 : ℝ)*x 1 + (5178863197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418711123/2000000000 : ℝ)^529 ≤ (3177236106847/25000000000000 : ℝ)^401 := by
    have hnat : (418711123 : ℕ)^529*25000000000000^401 ≤ 3177236106847^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418711123 2000000000 3177236106847 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2743965101/5000000000 : ℝ)^529 ≤ (11328366379839/25000000000000 : ℝ)^401 := by
    have hnat : (2743965101 : ℕ)^529*25000000000000^401 ≤ 11328366379839^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743965101 5000000000 11328366379839 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178863197/10000000000 : ℝ)^529 ≤ (1049439750961/2500000000000 : ℝ)^401 := by
    have hnat : (5178863197 : ℕ)^529*2500000000000^401 ≤ 1049439750961^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178863197 10000000000 1049439750961 2500000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-418711123/2000000000 : ℝ), (2743965101/5000000000 : ℝ), (5178863197/10000000000 : ℝ)] ![(3177236106847/25000000000000 : ℝ), (11328366379839/25000000000000 : ℝ), (1049439750961/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-418711123/2000000000 : ℝ)|^529 ≤ (3177236106847/25000000000000 : ℝ)^401
        have hw : |(-418711123/2000000000 : ℝ)|=(418711123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2743965101/5000000000 : ℝ)|^529 ≤ (11328366379839/25000000000000 : ℝ)^401
        have hw : |(2743965101/5000000000 : ℝ)|=(2743965101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178863197/10000000000 : ℝ)|^529 ≤ (1049439750961/2500000000000 : ℝ)^401
        have hw : |(5178863197/10000000000 : ℝ)|=(5178863197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s2_1 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5368518649/10000000000 : ℝ)*x 0 + (-2253491333/10000000000 : ℝ)*x 1 + (323678967/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368518649/10000000000 : ℝ)^529 ≤ (44017307408863/100000000000000 : ℝ)^401 := by
    have hnat : (5368518649 : ℕ)^529*100000000000000^401 ≤ 44017307408863^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368518649 10000000000 44017307408863 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253491333/10000000000 : ℝ)^529 ≤ (1750637450229/12500000000000 : ℝ)^401 := by
    have hnat : (2253491333 : ℕ)^529*12500000000000^401 ≤ 1750637450229^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253491333 10000000000 1750637450229 12500000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323678967/625000000 : ℝ)^529 ≤ (41977592978979/100000000000000 : ℝ)^401 := by
    have hnat : (323678967 : ℕ)^529*100000000000000^401 ≤ 41977592978979^401*625000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323678967 625000000 41977592978979 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368518649/10000000000 : ℝ), (-2253491333/10000000000 : ℝ), (323678967/625000000 : ℝ)] ![(44017307408863/100000000000000 : ℝ), (1750637450229/12500000000000 : ℝ), (41977592978979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368518649/10000000000 : ℝ)|^529 ≤ (44017307408863/100000000000000 : ℝ)^401
        have hw : |(5368518649/10000000000 : ℝ)|=(5368518649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2253491333/10000000000 : ℝ)|^529 ≤ (1750637450229/12500000000000 : ℝ)^401
        have hw : |(-2253491333/10000000000 : ℝ)|=(2253491333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323678967/625000000 : ℝ)|^529 ≤ (41977592978979/100000000000000 : ℝ)^401
        have hw : |(323678967/625000000 : ℝ)|=(323678967/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s2_2 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5368518611/10000000000 : ℝ)*x 0 + (103577269/200000000 : ℝ)*x 1 + (-2253491411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368518611/10000000000 : ℝ)^529 ≤ (22008653498921/50000000000000 : ℝ)^401 := by
    have hnat : (5368518611 : ℕ)^529*50000000000000^401 ≤ 22008653498921^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368518611 10000000000 22008653498921 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103577269/200000000 : ℝ)^529 ≤ (5247199092967/12500000000000 : ℝ)^401 := by
    have hnat : (103577269 : ℕ)^529*12500000000000^401 ≤ 5247199092967^401*200000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103577269 200000000 5247199092967 12500000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253491411/10000000000 : ℝ)^529 ≤ (560204009653/4000000000000 : ℝ)^401 := by
    have hnat : (2253491411 : ℕ)^529*4000000000000^401 ≤ 560204009653^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253491411 10000000000 560204009653 4000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368518611/10000000000 : ℝ), (103577269/200000000 : ℝ), (-2253491411/10000000000 : ℝ)] ![(22008653498921/50000000000000 : ℝ), (5247199092967/12500000000000 : ℝ), (560204009653/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368518611/10000000000 : ℝ)|^529 ≤ (22008653498921/50000000000000 : ℝ)^401
        have hw : |(5368518611/10000000000 : ℝ)|=(5368518611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103577269/200000000 : ℝ)|^529 ≤ (5247199092967/12500000000000 : ℝ)^401
        have hw : |(103577269/200000000 : ℝ)|=(103577269/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2253491411/10000000000 : ℝ)|^529 ≤ (560204009653/4000000000000 : ℝ)^401
        have hw : |(-2253491411/10000000000 : ℝ)|=(2253491411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s2_3 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4338582857/10000000000 : ℝ)*x 0 + (403436563/1000000000 : ℝ)*x 1 + (4664841659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4338582857/10000000000 : ℝ)^529 ≤ (8308614887249/25000000000000 : ℝ)^401 := by
    have hnat : (4338582857 : ℕ)^529*25000000000000^401 ≤ 8308614887249^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338582857 10000000000 8308614887249 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (403436563/1000000000 : ℝ)^529 ≤ (30195201372949/100000000000000 : ℝ)^401 := by
    have hnat : (403436563 : ℕ)^529*100000000000000^401 ≤ 30195201372949^401*1000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403436563 1000000000 30195201372949 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4664841659/10000000000 : ℝ)^529 ≤ (36570339056931/100000000000000 : ℝ)^401 := by
    have hnat : (4664841659 : ℕ)^529*100000000000000^401 ≤ 36570339056931^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4664841659 10000000000 36570339056931 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4338582857/10000000000 : ℝ), (403436563/1000000000 : ℝ), (4664841659/10000000000 : ℝ)] ![(8308614887249/25000000000000 : ℝ), (30195201372949/100000000000000 : ℝ), (36570339056931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4338582857/10000000000 : ℝ)|^529 ≤ (8308614887249/25000000000000 : ℝ)^401
        have hw : |(4338582857/10000000000 : ℝ)|=(4338582857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(403436563/1000000000 : ℝ)|^529 ≤ (30195201372949/100000000000000 : ℝ)^401
        have hw : |(403436563/1000000000 : ℝ)|=(403436563/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4664841659/10000000000 : ℝ)|^529 ≤ (36570339056931/100000000000000 : ℝ)^401
        have hw : |(4664841659/10000000000 : ℝ)|=(4664841659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s2_4 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1046814103/5000000000 : ℝ)*x 0 + (1036162153/2000000000 : ℝ)*x 1 + (5485964741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046814103/5000000000 : ℝ)^529 ≤ (12709525755681/100000000000000 : ℝ)^401 := by
    have hnat : (1046814103 : ℕ)^529*100000000000000^401 ≤ 12709525755681^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046814103 5000000000 12709525755681 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036162153/2000000000 : ℝ)^529 ≤ (41998416383303/100000000000000 : ℝ)^401 := by
    have hnat : (1036162153 : ℕ)^529*100000000000000^401 ≤ 41998416383303^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036162153 2000000000 41998416383303 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5485964741/10000000000 : ℝ)^529 ≤ (9058411567897/20000000000000 : ℝ)^401 := by
    have hnat : (5485964741 : ℕ)^529*20000000000000^401 ≤ 9058411567897^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485964741 10000000000 9058411567897 20000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1046814103/5000000000 : ℝ), (1036162153/2000000000 : ℝ), (5485964741/10000000000 : ℝ)] ![(12709525755681/100000000000000 : ℝ), (41998416383303/100000000000000 : ℝ), (9058411567897/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1046814103/5000000000 : ℝ)|^529 ≤ (12709525755681/100000000000000 : ℝ)^401
        have hw : |(-1046814103/5000000000 : ℝ)|=(1046814103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036162153/2000000000 : ℝ)|^529 ≤ (41998416383303/100000000000000 : ℝ)^401
        have hw : |(1036162153/2000000000 : ℝ)|=(1036162153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5485964741/10000000000 : ℝ)|^529 ≤ (9058411567897/20000000000000 : ℝ)^401
        have hw : |(5485964741/10000000000 : ℝ)|=(5485964741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s2_5 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (105789007/200000000 : ℝ)*x 0 + (-973194887/5000000000 : ℝ)*x 1 + (2742982391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105789007/200000000 : ℝ)^529 ≤ (43164094937427/100000000000000 : ℝ)^401 := by
    have hnat : (105789007 : ℕ)^529*100000000000000^401 ≤ 43164094937427^401*200000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105789007 200000000 43164094937427 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (973194887/5000000000 : ℝ)^529 ≤ (5771923378497/50000000000000 : ℝ)^401 := by
    have hnat : (973194887 : ℕ)^529*50000000000000^401 ≤ 5771923378497^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973194887 5000000000 5771923378497 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2742982391/5000000000 : ℝ)^529 ≤ (45292058286029/100000000000000 : ℝ)^401 := by
    have hnat : (2742982391 : ℕ)^529*100000000000000^401 ≤ 45292058286029^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742982391 5000000000 45292058286029 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105789007/200000000 : ℝ), (-973194887/5000000000 : ℝ), (2742982391/5000000000 : ℝ)] ![(43164094937427/100000000000000 : ℝ), (5771923378497/50000000000000 : ℝ), (45292058286029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105789007/200000000 : ℝ)|^529 ≤ (43164094937427/100000000000000 : ℝ)^401
        have hw : |(105789007/200000000 : ℝ)|=(105789007/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-973194887/5000000000 : ℝ)|^529 ≤ (5771923378497/50000000000000 : ℝ)^401
        have hw : |(-973194887/5000000000 : ℝ)|=(973194887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2742982391/5000000000 : ℝ)|^529 ≤ (45292058286029/100000000000000 : ℝ)^401
        have hw : |(2742982391/5000000000 : ℝ)|=(2742982391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s2_6 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5289450451/10000000000 : ℝ)*x 0 + (1097192981/2000000000 : ℝ)*x 1 + (-243298683/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289450451/10000000000 : ℝ)^529 ≤ (10791024006179/25000000000000 : ℝ)^401 := by
    have hnat : (5289450451 : ℕ)^529*25000000000000^401 ≤ 10791024006179^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289450451 10000000000 10791024006179 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097192981/2000000000 : ℝ)^529 ≤ (2264602981283/5000000000000 : ℝ)^401 := by
    have hnat : (1097192981 : ℕ)^529*5000000000000^401 ≤ 2264602981283^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097192981 2000000000 2264602981283 5000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (243298683/1250000000 : ℝ)^529 ≤ (721490270721/6250000000000 : ℝ)^401 := by
    have hnat : (243298683 : ℕ)^529*6250000000000^401 ≤ 721490270721^401*1250000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243298683 1250000000 721490270721 6250000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289450451/10000000000 : ℝ), (1097192981/2000000000 : ℝ), (-243298683/1250000000 : ℝ)] ![(10791024006179/25000000000000 : ℝ), (2264602981283/5000000000000 : ℝ), (721490270721/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289450451/10000000000 : ℝ)|^529 ≤ (10791024006179/25000000000000 : ℝ)^401
        have hw : |(5289450451/10000000000 : ℝ)|=(5289450451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097192981/2000000000 : ℝ)|^529 ≤ (2264602981283/5000000000000 : ℝ)^401
        have hw : |(1097192981/2000000000 : ℝ)|=(1097192981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-243298683/1250000000 : ℝ)|^529 ≤ (721490270721/6250000000000 : ℝ)^401
        have hw : |(-243298683/1250000000 : ℝ)|=(243298683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s2_7 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2169365281/5000000000 : ℝ)*x 0 + (291304333/625000000 : ℝ)*x 1 + (1009593509/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169365281/5000000000 : ℝ)^529 ≤ (259655876329/781250000000 : ℝ)^401 := by
    have hnat : (2169365281 : ℕ)^529*781250000000^401 ≤ 259655876329^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169365281 5000000000 259655876329 781250000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (291304333/625000000 : ℝ)^529 ≤ (18264631451649/50000000000000 : ℝ)^401 := by
    have hnat : (291304333 : ℕ)^529*50000000000000^401 ≤ 18264631451649^401*625000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291304333 625000000 18264631451649 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1009593509/2500000000 : ℝ)^529 ≤ (6046956980653/20000000000000 : ℝ)^401 := by
    have hnat : (1009593509 : ℕ)^529*20000000000000^401 ≤ 6046956980653^401*2500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009593509 2500000000 6046956980653 20000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169365281/5000000000 : ℝ), (291304333/625000000 : ℝ), (1009593509/2500000000 : ℝ)] ![(259655876329/781250000000 : ℝ), (18264631451649/50000000000000 : ℝ), (6046956980653/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169365281/5000000000 : ℝ)|^529 ≤ (259655876329/781250000000 : ℝ)^401
        have hw : |(2169365281/5000000000 : ℝ)|=(2169365281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(291304333/625000000 : ℝ)|^529 ≤ (18264631451649/50000000000000 : ℝ)^401
        have hw : |(291304333/625000000 : ℝ)|=(291304333/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1009593509/2500000000 : ℝ)|^529 ≤ (6046956980653/20000000000000 : ℝ)^401
        have hw : |(1009593509/2500000000 : ℝ)|=(1009593509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1270_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19877/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6341/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1923/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16149/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19877/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6341/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19877/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6341/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19877/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6341/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19877/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6341/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19877/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6341/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19877/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6341/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6341/100000 : ℝ) ^ (8463/2048 : ℝ) ≤ (561173917632181/50000000000000000000 : ℝ) := by
    have hpowers : (6341/100000 : ℝ)^8463 ≤ (561173917632181/50000000000000000000 : ℝ)^2048 := by
      have hnat : (6341 : ℕ)^8463*50000000000000000000^2048 ≤ 561173917632181^2048*100000^8463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6341 100000 561173917632181 50000000000000000000 8463 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6341/100000 : ℝ)) (X := (561173917632181/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (19877/100000 : ℝ) ^ (8463/2048 : ℝ) ≤ (15756805952689397/12500000000000000000 : ℝ) := by
    have hpowers : (19877/100000 : ℝ)^8463 ≤ (15756805952689397/12500000000000000000 : ℝ)^2048 := by
      have hnat : (19877 : ℕ)^8463*12500000000000000000^2048 ≤ 15756805952689397^2048*100000^8463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19877 100000 15756805952689397 12500000000000000000 8463 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19877/100000 : ℝ)) (X := (15756805952689397/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000561173917632181/25000000000000000000 : ℝ) ≤ (10000054319953017/10000000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (25000561173917632181/25000000000000000000 : ℝ)^2048 ≤ (10000054319953017/10000000000000000 : ℝ)^8463 := by
      have hnat : (25000561173917632181 : ℕ)^2048*10000000000000000^8463 ≤ 10000054319953017^8463*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000561173917632181 25000000000000000000 10000054319953017 10000000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000054319953017/10000000000000000 : ℝ)) (X := (25000561173917632181/25000000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50063588397728389769/50000000000000000000 : ℝ) ≤ (80024609016081/80000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (50063588397728389769/50000000000000000000 : ℝ)^2048 ≤ (80024609016081/80000000000000 : ℝ)^8463 := by
      have hnat : (50063588397728389769 : ℕ)^2048*80000000000000^8463 ≤ 80024609016081^8463*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50063588397728389769 50000000000000000000 80024609016081 80000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80024609016081/80000000000000 : ℝ)) (X := (50063588397728389769/50000000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6265756805952689397/6250000000000000000 : ℝ) ≤ (10006097934067233/10000000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (6265756805952689397/6250000000000000000 : ℝ)^2048 ≤ (10006097934067233/10000000000000000 : ℝ)^8463 := by
      have hnat : (6265756805952689397 : ℕ)^2048*10000000000000000^8463 ≤ 10006097934067233^8463*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6265756805952689397 6250000000000000000 10006097934067233 10000000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006097934067233/10000000000000000 : ℝ)) (X := (6265756805952689397/6250000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(561173917632181/50000000000000000000 : ℝ) ≤ ((5638433863241074769/5640000000000000000 : ℝ)+2*(251817254759/112800000000000 : ℝ)*(6341/100000 : ℝ))^(8463/2048 : ℝ) := by
    rw [show (5638433863241074769/5640000000000000000 : ℝ)+2*(251817254759/112800000000000 : ℝ)*(6341/100000 : ℝ)=(10000054319953017/10000000000000000 : ℝ) by norm_num, show 1+2*(561173917632181/50000000000000000000 : ℝ)=(25000561173917632181/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15756805952689397/12500000000000000000 : ℝ)+(561173917632181/50000000000000000000 : ℝ) ≤ ((5638433863241074769/5640000000000000000 : ℝ)+(251817254759/112800000000000 : ℝ)*((19877/100000 : ℝ)+(6341/100000 : ℝ)))^(8463/2048 : ℝ) := by
    rw [show (5638433863241074769/5640000000000000000 : ℝ)+(251817254759/112800000000000 : ℝ)*((19877/100000 : ℝ)+(6341/100000 : ℝ))=(80024609016081/80000000000000 : ℝ) by norm_num, show 1+(15756805952689397/12500000000000000000 : ℝ)+(561173917632181/50000000000000000000 : ℝ)=(50063588397728389769/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15756805952689397/12500000000000000000 : ℝ) ≤ ((5638433863241074769/5640000000000000000 : ℝ)+2*(251817254759/112800000000000 : ℝ)*(19877/100000 : ℝ))^(8463/2048 : ℝ) := by
    rw [show (5638433863241074769/5640000000000000000 : ℝ)+2*(251817254759/112800000000000 : ℝ)*(19877/100000 : ℝ)=(10006097934067233/10000000000000000 : ℝ) by norm_num, show 1+2*(15756805952689397/12500000000000000000 : ℝ)=(6265756805952689397/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5638433863241074769/5640000000000000000 : ℝ)*(X 1 0+X 2 0)+(251817254759/112800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (6341/100000 : ℝ)) (hi := (19877/100000 : ℝ)) (c := (5638433863241074769/5640000000000000000 : ℝ)) (alpha := (251817254759/112800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5638433863241074769/5640000000000000000 : ℝ)*(X 0 1+X 2 1)+(251817254759/112800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (6341/100000 : ℝ)) (hi := (19877/100000 : ℝ)) (c := (5638433863241074769/5640000000000000000 : ℝ)) (alpha := (251817254759/112800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5638433863241074769/5640000000000000000 : ℝ)*(X 0 2+X 1 2)+(251817254759/112800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (6341/100000 : ℝ)) (hi := (19877/100000 : ℝ)) (c := (5638433863241074769/5640000000000000000 : ℝ)) (alpha := (251817254759/112800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-418711123/2000000000 : ℝ)*X 0 0+(2743965101/5000000000 : ℝ)*X 0 1+(5178863197/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5368518649/10000000000 : ℝ)*X 1 0+(-2253491333/10000000000 : ℝ)*X 1 1+(323678967/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5368518611/10000000000 : ℝ)*X 2 0+(103577269/200000000 : ℝ)*X 2 1+(-2253491411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4338582857/10000000000 : ℝ)*X 0 0+(403436563/1000000000 : ℝ)*X 0 1+(4664841659/10000000000 : ℝ)*X 0 2+(4338582857/10000000000 : ℝ)*X 1 0+(403436563/1000000000 : ℝ)*X 1 1+(4664841659/10000000000 : ℝ)*X 1 2+(4338582857/10000000000 : ℝ)*X 2 0+(403436563/1000000000 : ℝ)*X 2 1+(4664841659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1046814103/5000000000 : ℝ)*X 0 0+(1036162153/2000000000 : ℝ)*X 0 1+(5485964741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((105789007/200000000 : ℝ)*X 1 0+(-973194887/5000000000 : ℝ)*X 1 1+(2742982391/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289450451/10000000000 : ℝ)*X 2 0+(1097192981/2000000000 : ℝ)*X 2 1+(-243298683/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2169365281/5000000000 : ℝ)*X 0 0+(291304333/625000000 : ℝ)*X 0 1+(1009593509/2500000000 : ℝ)*X 0 2+(2169365281/5000000000 : ℝ)*X 1 0+(291304333/625000000 : ℝ)*X 1 1+(1009593509/2500000000 : ℝ)*X 1 2+(2169365281/5000000000 : ℝ)*X 2 0+(291304333/625000000 : ℝ)*X 2 1+(1009593509/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (403871472048979485520259069/47000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (777534533/50000000000000 : ℝ)*(base19) + (731995911/50000000000000 : ℝ)*(base23) + (36599769/100000000000000 : ℝ)*(lower2) + (58647821/25000000000000 : ℝ)*(upper3) + (2333731/2000000000000 : ℝ)*(upper5) + (1205426852765299/50000000000000 : ℝ)*(major0) + (1205426852765299/50000000000000 : ℝ)*(major1) + (1205426852765299/50000000000000 : ℝ)*(major2) + (3235565930213191/100000000000000 : ℝ)*(sp0) + (3235584046401363/100000000000000 : ℝ)*(sp1) + (202224008592413/6250000000000 : ℝ)*(sp2) + (198263961230279/12500000000000 : ℝ)*(sp3) + (9835628619/50000000000000 : ℝ)*(sp4) + (4916657431/50000000000000 : ℝ)*(sp7) + (793060761578547/50000000000000 : ℝ)*(f.failure) + (323558560147043/10000000000000 : ℝ)*(f.sum) + (1313549702441/2820000000000000000000000000 : ℝ)*base65 + (69201521442896977/94000000000000000000000000000000 : ℝ)*base67 + (152979739884896977/94000000000000000000000000000000 : ℝ)*base69 + (262978074584896977/94000000000000000000000000000000 : ℝ)*base71 + (2102302879999/2820000000000000000000000000 : ℝ)*base74 + (584810783109103023/94000000000000000000000000000000 : ℝ)*base76 + (163539713890896977/94000000000000000000000000000000 : ℝ)*base77 + (234025177669103023/94000000000000000000000000000000 : ℝ)*base80 + (1408941117701/2820000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (462053/312500000000000000000 : ℝ)*base89 + (462053/312500000000000000000 : ℝ)*base91 + (462053/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3431769202758465318863/470000000000000000000000000 : ℝ) := by norm_num
    linear_combination (928753071/50000000000000 : ℝ)*(base19) + (414066809/20000000000000 : ℝ)*(base23) + (33109573/100000000000000 : ℝ)*(upper2) + (24955203/10000000000000 : ℝ)*(upper3) + (70253189/50000000000000 : ℝ)*(upper5) + (610433907459157/25000000000000 : ℝ)*(major0) + (610433907459157/25000000000000 : ℝ)*(major1) + (610433907459157/25000000000000 : ℝ)*(major2) + (19614654693/100000000000000 : ℝ)*(sp1) + (6369707651/25000000000000 : ℝ)*(sp2) + (1638516003894279/50000000000000 : ℝ)*(sp4) + (1638505267813861/50000000000000 : ℝ)*(sp5) + (327700445862391/10000000000000 : ℝ)*(sp6) + (401609752124201/25000000000000 : ℝ)*(sp7) + (401609752124201/25000000000000 : ℝ)*(f.failure) + (1638516003894279/50000000000000 : ℝ)*(f.sum) + (10449915850837/1410000000000000000000000000 : ℝ)*base66 + (117215200834380089/47000000000000000000000000000000 : ℝ)*base68 + (179521186685619911/47000000000000000000000000000000 : ℝ)*base69 + (171090238184619911/47000000000000000000000000000000 : ℝ)*base71 + (9650981953987/1410000000000000000000000000 : ℝ)*base74 + (270949007251619911/47000000000000000000000000000000 : ℝ)*base75 + (346416515674380089/47000000000000000000000000000000 : ℝ)*base78 + (282686948394380089/47000000000000000000000000000000 : ℝ)*base80 + (1703018589563/1410000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (1285599/156250000000000000000 : ℝ)*base89 + (1285599/156250000000000000000 : ℝ)*base91 + (1285599/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1270_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19877/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6341/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1923/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16149/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1270_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1270_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1923/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16149/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1270_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1270_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1270_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1923/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16149/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1270_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

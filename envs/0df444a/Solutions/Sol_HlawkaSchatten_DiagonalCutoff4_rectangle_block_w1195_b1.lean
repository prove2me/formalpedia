-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1195_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:01:06.854846+00:00
-- url     : https://prove2.me/submissions/5dea6556-97eb-4b27-96bf-369d27094018

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
theorem support_rectangle_w1195_s3_0 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2138534251/10000000000 : ℝ)*x 0 + (5423945541/10000000000 : ℝ)*x 1 + (2618407407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138534251/10000000000 : ℝ)^2097 ≤ (12993457418617/100000000000000 : ℝ)^1585 := by
    have hnat : (2138534251 : ℕ)^2097*100000000000000^1585 ≤ 12993457418617^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138534251 10000000000 12993457418617 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423945541/10000000000 : ℝ)^2097 ≤ (22256743977111/50000000000000 : ℝ)^1585 := by
    have hnat : (5423945541 : ℕ)^2097*50000000000000^1585 ≤ 22256743977111^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423945541 10000000000 22256743977111 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2618407407/5000000000 : ℝ)^2097 ≤ (42493054609061/100000000000000 : ℝ)^1585 := by
    have hnat : (2618407407 : ℕ)^2097*100000000000000^1585 ≤ 42493054609061^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618407407 5000000000 42493054609061 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2138534251/10000000000 : ℝ), (5423945541/10000000000 : ℝ), (2618407407/5000000000 : ℝ)] ![(12993457418617/100000000000000 : ℝ), (22256743977111/50000000000000 : ℝ), (42493054609061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2138534251/10000000000 : ℝ)|^2097 ≤ (12993457418617/100000000000000 : ℝ)^1585
        have hw : |(-2138534251/10000000000 : ℝ)|=(2138534251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423945541/10000000000 : ℝ)|^2097 ≤ (22256743977111/50000000000000 : ℝ)^1585
        have hw : |(5423945541/10000000000 : ℝ)|=(5423945541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2618407407/5000000000 : ℝ)|^2097 ≤ (42493054609061/100000000000000 : ℝ)^1585
        have hw : |(2618407407/5000000000 : ℝ)|=(2618407407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s3_1 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (41816789/78125000 : ℝ)*x 0 + (-2234082837/10000000000 : ℝ)*x 1 + (2618407547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41816789/78125000 : ℝ)^2097 ≤ (43739925089483/100000000000000 : ℝ)^1585 := by
    have hnat : (41816789 : ℕ)^2097*100000000000000^1585 ≤ 43739925089483^1585*78125000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41816789 78125000 43739925089483 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2234082837/10000000000 : ℝ)^2097 ≤ (13767017271321/100000000000000 : ℝ)^1585 := by
    have hnat : (2234082837 : ℕ)^2097*100000000000000^1585 ≤ 13767017271321^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234082837 10000000000 13767017271321 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2618407547/5000000000 : ℝ)^2097 ≤ (5311632201873/12500000000000 : ℝ)^1585 := by
    have hnat : (2618407547 : ℕ)^2097*12500000000000^1585 ≤ 5311632201873^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618407547 5000000000 5311632201873 12500000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41816789/78125000 : ℝ), (-2234082837/10000000000 : ℝ), (2618407547/5000000000 : ℝ)] ![(43739925089483/100000000000000 : ℝ), (13767017271321/100000000000000 : ℝ), (5311632201873/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41816789/78125000 : ℝ)|^2097 ≤ (43739925089483/100000000000000 : ℝ)^1585
        have hw : |(41816789/78125000 : ℝ)|=(41816789/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2234082837/10000000000 : ℝ)|^2097 ≤ (13767017271321/100000000000000 : ℝ)^1585
        have hw : |(-2234082837/10000000000 : ℝ)|=(2234082837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2618407547/5000000000 : ℝ)|^2097 ≤ (5311632201873/12500000000000 : ℝ)^1585
        have hw : |(2618407547/5000000000 : ℝ)|=(2618407547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s3_2 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2676274419/5000000000 : ℝ)*x 0 + (654601923/1250000000 : ℝ)*x 1 + (-2234082661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676274419/5000000000 : ℝ)^2097 ≤ (43739923424509/100000000000000 : ℝ)^1585 := by
    have hnat : (2676274419 : ℕ)^2097*100000000000000^1585 ≤ 43739923424509^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676274419 5000000000 43739923424509 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654601923/1250000000 : ℝ)^2097 ≤ (21246530364131/50000000000000 : ℝ)^1585 := by
    have hnat : (654601923 : ℕ)^2097*50000000000000^1585 ≤ 21246530364131^1585*1250000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654601923 1250000000 21246530364131 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2234082661/10000000000 : ℝ)^2097 ≤ (13767015836419/100000000000000 : ℝ)^1585 := by
    have hnat : (2234082661 : ℕ)^2097*100000000000000^1585 ≤ 13767015836419^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234082661 10000000000 13767015836419 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676274419/5000000000 : ℝ), (654601923/1250000000 : ℝ), (-2234082661/10000000000 : ℝ)] ![(43739923424509/100000000000000 : ℝ), (21246530364131/50000000000000 : ℝ), (13767015836419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676274419/5000000000 : ℝ)|^2097 ≤ (43739923424509/100000000000000 : ℝ)^1585
        have hw : |(2676274419/5000000000 : ℝ)|=(2676274419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654601923/1250000000 : ℝ)|^2097 ≤ (21246530364131/50000000000000 : ℝ)^1585
        have hw : |(654601923/1250000000 : ℝ)|=(654601923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2234082661/10000000000 : ℝ)|^2097 ≤ (13767015836419/100000000000000 : ℝ)^1585
        have hw : |(-2234082661/10000000000 : ℝ)|=(2234082661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s3_3 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4355317313/10000000000 : ℝ)*x 0 + (834244359/2000000000 : ℝ)*x 1 + (4547386911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355317313/10000000000 : ℝ)^2097 ≤ (33297601308381/100000000000000 : ℝ)^1585 := by
    have hnat : (4355317313 : ℕ)^2097*100000000000000^1585 ≤ 33297601308381^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355317313 10000000000 33297601308381 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (834244359/2000000000 : ℝ)^2097 ≤ (31448326687333/100000000000000 : ℝ)^1585 := by
    have hnat : (834244359 : ℕ)^2097*100000000000000^1585 ≤ 31448326687333^1585*2000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834244359 2000000000 31448326687333 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4547386911/10000000000 : ℝ)^2097 ≤ (2151737792/6103515625 : ℝ)^1585 := by
    have hnat : (4547386911 : ℕ)^2097*6103515625^1585 ≤ 2151737792^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4547386911 10000000000 2151737792 6103515625 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355317313/10000000000 : ℝ), (834244359/2000000000 : ℝ), (4547386911/10000000000 : ℝ)] ![(33297601308381/100000000000000 : ℝ), (31448326687333/100000000000000 : ℝ), (2151737792/6103515625 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355317313/10000000000 : ℝ)|^2097 ≤ (33297601308381/100000000000000 : ℝ)^1585
        have hw : |(4355317313/10000000000 : ℝ)|=(4355317313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(834244359/2000000000 : ℝ)|^2097 ≤ (31448326687333/100000000000000 : ℝ)^1585
        have hw : |(834244359/2000000000 : ℝ)|=(834244359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4547386911/10000000000 : ℝ)|^2097 ≤ (2151737792/6103515625 : ℝ)^1585
        have hw : |(4547386911/10000000000 : ℝ)|=(4547386911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s3_4 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-427710033/2000000000 : ℝ)*x 0 + (1309378929/2500000000 : ℝ)*x 1 + (1355810183/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427710033/2000000000 : ℝ)^2097 ≤ (2598717068849/20000000000000 : ℝ)^1585 := by
    have hnat : (427710033 : ℕ)^2097*20000000000000^1585 ≤ 2598717068849^1585*2000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427710033 2000000000 2598717068849 20000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309378929/2500000000 : ℝ)^2097 ≤ (8500115852789/20000000000000 : ℝ)^1585 := by
    have hnat : (1309378929 : ℕ)^2097*20000000000000^1585 ≤ 8500115852789^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309378929 2500000000 8500115852789 20000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355810183/2500000000 : ℝ)^2097 ≤ (44505835375689/100000000000000 : ℝ)^1585 := by
    have hnat : (1355810183 : ℕ)^2097*100000000000000^1585 ≤ 44505835375689^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355810183 2500000000 44505835375689 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-427710033/2000000000 : ℝ), (1309378929/2500000000 : ℝ), (1355810183/2500000000 : ℝ)] ![(2598717068849/20000000000000 : ℝ), (8500115852789/20000000000000 : ℝ), (44505835375689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-427710033/2000000000 : ℝ)|^2097 ≤ (2598717068849/20000000000000 : ℝ)^1585
        have hw : |(-427710033/2000000000 : ℝ)|=(427710033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309378929/2500000000 : ℝ)|^2097 ≤ (8500115852789/20000000000000 : ℝ)^1585
        have hw : |(1309378929/2500000000 : ℝ)|=(1309378929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355810183/2500000000 : ℝ)|^2097 ≤ (44505835375689/100000000000000 : ℝ)^1585
        have hw : |(1355810183/2500000000 : ℝ)|=(1355810183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s3_5 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5304961087/10000000000 : ℝ)*x 0 + (-1023828391/5000000000 : ℝ)*x 1 + (5423240659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304961087/10000000000 : ℝ)^2097 ≤ (10806542010569/25000000000000 : ℝ)^1585 := by
    have hnat : (5304961087 : ℕ)^2097*25000000000000^1585 ≤ 10806542010569^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304961087 10000000000 10806542010569 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1023828391/5000000000 : ℝ)^2097 ≤ (6133998681149/50000000000000 : ℝ)^1585 := by
    have hnat : (1023828391 : ℕ)^2097*50000000000000^1585 ≤ 6133998681149^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023828391 5000000000 6133998681149 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423240659/10000000000 : ℝ)^2097 ≤ (5563229322887/12500000000000 : ℝ)^1585 := by
    have hnat : (5423240659 : ℕ)^2097*12500000000000^1585 ≤ 5563229322887^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423240659 10000000000 5563229322887 12500000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304961087/10000000000 : ℝ), (-1023828391/5000000000 : ℝ), (5423240659/10000000000 : ℝ)] ![(10806542010569/25000000000000 : ℝ), (6133998681149/50000000000000 : ℝ), (5563229322887/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304961087/10000000000 : ℝ)|^2097 ≤ (10806542010569/25000000000000 : ℝ)^1585
        have hw : |(5304961087/10000000000 : ℝ)|=(5304961087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1023828391/5000000000 : ℝ)|^2097 ≤ (6133998681149/50000000000000 : ℝ)^1585
        have hw : |(-1023828391/5000000000 : ℝ)|=(1023828391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423240659/10000000000 : ℝ)|^2097 ≤ (5563229322887/12500000000000 : ℝ)^1585
        have hw : |(5423240659/10000000000 : ℝ)|=(5423240659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s3_6 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5304960703/10000000000 : ℝ)*x 0 + (338952567/625000000 : ℝ)*x 1 + (-1023828369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304960703/10000000000 : ℝ)^2097 ≤ (21613081951307/50000000000000 : ℝ)^1585 := by
    have hnat : (5304960703 : ℕ)^2097*50000000000000^1585 ≤ 21613081951307^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304960703 10000000000 21613081951307 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338952567/625000000 : ℝ)^2097 ≤ (44505839067217/100000000000000 : ℝ)^1585 := by
    have hnat : (338952567 : ℕ)^2097*100000000000000^1585 ≤ 44505839067217^1585*625000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338952567 625000000 44505839067217 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1023828369/5000000000 : ℝ)^2097 ≤ (12267997013529/100000000000000 : ℝ)^1585 := by
    have hnat : (1023828369 : ℕ)^2097*100000000000000^1585 ≤ 12267997013529^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023828369 5000000000 12267997013529 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304960703/10000000000 : ℝ), (338952567/625000000 : ℝ), (-1023828369/5000000000 : ℝ)] ![(21613081951307/50000000000000 : ℝ), (44505839067217/100000000000000 : ℝ), (12267997013529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304960703/10000000000 : ℝ)|^2097 ≤ (21613081951307/50000000000000 : ℝ)^1585
        have hw : |(5304960703/10000000000 : ℝ)|=(5304960703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338952567/625000000 : ℝ)|^2097 ≤ (44505839067217/100000000000000 : ℝ)^1585
        have hw : |(338952567/625000000 : ℝ)|=(338952567/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1023828369/5000000000 : ℝ)|^2097 ≤ (12267997013529/100000000000000 : ℝ)^1585
        have hw : |(-1023828369/5000000000 : ℝ)|=(1023828369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s3_7 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4355349477/10000000000 : ℝ)*x 0 + (142061803/312500000 : ℝ)*x 1 + (4172638103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355349477/10000000000 : ℝ)^2097 ≤ (665958532899/2000000000000 : ℝ)^1585 := by
    have hnat : (4355349477 : ℕ)^2097*2000000000000^1585 ≤ 665958532899^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355349477 10000000000 665958532899 2000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142061803/312500000 : ℝ)^2097 ≤ (17619809258133/50000000000000 : ℝ)^1585 := by
    have hnat : (142061803 : ℕ)^2097*50000000000000^1585 ≤ 17619809258133^1585*312500000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142061803 312500000 17619809258133 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172638103/10000000000 : ℝ)^2097 ≤ (31462454825911/100000000000000 : ℝ)^1585 := by
    have hnat : (4172638103 : ℕ)^2097*100000000000000^1585 ≤ 31462454825911^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172638103 10000000000 31462454825911 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355349477/10000000000 : ℝ), (142061803/312500000 : ℝ), (4172638103/10000000000 : ℝ)] ![(665958532899/2000000000000 : ℝ), (17619809258133/50000000000000 : ℝ), (31462454825911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355349477/10000000000 : ℝ)|^2097 ≤ (665958532899/2000000000000 : ℝ)^1585
        have hw : |(4355349477/10000000000 : ℝ)|=(4355349477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142061803/312500000 : ℝ)|^2097 ≤ (17619809258133/50000000000000 : ℝ)^1585
        have hw : |(142061803/312500000 : ℝ)|=(142061803/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172638103/10000000000 : ℝ)|^2097 ≤ (31462454825911/100000000000000 : ℝ)^1585
        have hw : |(4172638103/10000000000 : ℝ)|=(4172638103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1195_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (327/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9303/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5393/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14747/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (327/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9303/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (327/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9303/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (327/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9303/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (327/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9303/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (327/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9303/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (327/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9303/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9303/100000 : ℝ) ^ (8387/2048 : ℝ) ≤ (1493584144447041/25000000000000000000 : ℝ) := by
    have hpowers : (9303/100000 : ℝ)^8387 ≤ (1493584144447041/25000000000000000000 : ℝ)^2048 := by
      have hnat : (9303 : ℕ)^8387*25000000000000000000^2048 ≤ 1493584144447041^2048*100000^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9303 100000 1493584144447041 25000000000000000000 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9303/100000 : ℝ)) (X := (1493584144447041/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (327/2000 : ℝ) ^ (8387/2048 : ℝ) ≤ (30071580093025973/50000000000000000000 : ℝ) := by
    have hpowers : (327/2000 : ℝ)^8387 ≤ (30071580093025973/50000000000000000000 : ℝ)^2048 := by
      have hnat : (327 : ℕ)^8387*50000000000000000000^2048 ≤ 30071580093025973^2048*2000^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        327 2000 30071580093025973 50000000000000000000 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (327/2000 : ℝ)) (X := (30071580093025973/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501493584144447041/12500000000000000000 : ℝ) ≤ (5000145879204259/5000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (12501493584144447041/12500000000000000000 : ℝ)^2048 ≤ (5000145879204259/5000000000000000 : ℝ)^8387 := by
      have hnat : (12501493584144447041 : ℕ)^2048*5000000000000000^8387 ≤ 5000145879204259^8387*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501493584144447041 12500000000000000000 5000145879204259 5000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000145879204259/5000000000000000 : ℝ)) (X := (12501493584144447041/12500000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10006611749676384011/10000000000000000000 : ℝ) ≤ (156275220358323/156250000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (10006611749676384011/10000000000000000000 : ℝ)^2048 ≤ (156275220358323/156250000000000 : ℝ)^8387 := by
      have hnat : (10006611749676384011 : ℕ)^2048*156250000000000^8387 ≤ 156275220358323^8387*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006611749676384011 10000000000000000000 156275220358323 156250000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156275220358323/156250000000000 : ℝ)) (X := (10006611749676384011/10000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25030071580093025973/25000000000000000000 : ℝ) ≤ (5001468223728413/5000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (25030071580093025973/25000000000000000000 : ℝ)^2048 ≤ (5001468223728413/5000000000000000 : ℝ)^8387 := by
      have hnat : (25030071580093025973 : ℕ)^2048*5000000000000000^8387 ≤ 5001468223728413^8387*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25030071580093025973 25000000000000000000 5001468223728413 5000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001468223728413/5000000000000000 : ℝ)) (X := (25030071580093025973/25000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1493584144447041/25000000000000000000 : ℝ) ≤ ((11741242079881402837/11745000000000000000 : ℝ)+2*(661172262077/352350000000000 : ℝ)*(9303/100000 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (11741242079881402837/11745000000000000000 : ℝ)+2*(661172262077/352350000000000 : ℝ)*(9303/100000 : ℝ)=(5000145879204259/5000000000000000 : ℝ) by norm_num, show 1+2*(1493584144447041/25000000000000000000 : ℝ)=(12501493584144447041/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30071580093025973/50000000000000000000 : ℝ)+(1493584144447041/25000000000000000000 : ℝ) ≤ ((11741242079881402837/11745000000000000000 : ℝ)+(661172262077/352350000000000 : ℝ)*((327/2000 : ℝ)+(9303/100000 : ℝ)))^(8387/2048 : ℝ) := by
    rw [show (11741242079881402837/11745000000000000000 : ℝ)+(661172262077/352350000000000 : ℝ)*((327/2000 : ℝ)+(9303/100000 : ℝ))=(156275220358323/156250000000000 : ℝ) by norm_num, show 1+(30071580093025973/50000000000000000000 : ℝ)+(1493584144447041/25000000000000000000 : ℝ)=(10006611749676384011/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30071580093025973/50000000000000000000 : ℝ) ≤ ((11741242079881402837/11745000000000000000 : ℝ)+2*(661172262077/352350000000000 : ℝ)*(327/2000 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (11741242079881402837/11745000000000000000 : ℝ)+2*(661172262077/352350000000000 : ℝ)*(327/2000 : ℝ)=(5001468223728413/5000000000000000 : ℝ) by norm_num, show 1+2*(30071580093025973/50000000000000000000 : ℝ)=(25030071580093025973/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11741242079881402837/11745000000000000000 : ℝ)*(X 1 0+X 2 0)+(661172262077/352350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (9303/100000 : ℝ)) (hi := (327/2000 : ℝ)) (c := (11741242079881402837/11745000000000000000 : ℝ)) (alpha := (661172262077/352350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11741242079881402837/11745000000000000000 : ℝ)*(X 0 1+X 2 1)+(661172262077/352350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (9303/100000 : ℝ)) (hi := (327/2000 : ℝ)) (c := (11741242079881402837/11745000000000000000 : ℝ)) (alpha := (661172262077/352350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11741242079881402837/11745000000000000000 : ℝ)*(X 0 2+X 1 2)+(661172262077/352350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (9303/100000 : ℝ)) (hi := (327/2000 : ℝ)) (c := (11741242079881402837/11745000000000000000 : ℝ)) (alpha := (661172262077/352350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2138534251/10000000000 : ℝ)*X 0 0+(5423945541/10000000000 : ℝ)*X 0 1+(2618407407/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((41816789/78125000 : ℝ)*X 1 0+(-2234082837/10000000000 : ℝ)*X 1 1+(2618407547/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676274419/5000000000 : ℝ)*X 2 0+(654601923/1250000000 : ℝ)*X 2 1+(-2234082661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4355317313/10000000000 : ℝ)*X 0 0+(834244359/2000000000 : ℝ)*X 0 1+(4547386911/10000000000 : ℝ)*X 0 2+(4355317313/10000000000 : ℝ)*X 1 0+(834244359/2000000000 : ℝ)*X 1 1+(4547386911/10000000000 : ℝ)*X 1 2+(4355317313/10000000000 : ℝ)*X 2 0+(834244359/2000000000 : ℝ)*X 2 1+(4547386911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-427710033/2000000000 : ℝ)*X 0 0+(1309378929/2500000000 : ℝ)*X 0 1+(1355810183/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304961087/10000000000 : ℝ)*X 1 0+(-1023828391/5000000000 : ℝ)*X 1 1+(5423240659/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304960703/10000000000 : ℝ)*X 2 0+(338952567/625000000 : ℝ)*X 2 1+(-1023828369/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4355349477/10000000000 : ℝ)*X 0 0+(142061803/312500000 : ℝ)*X 0 1+(4172638103/10000000000 : ℝ)*X 0 2+(4355349477/10000000000 : ℝ)*X 1 0+(142061803/312500000 : ℝ)*X 1 1+(4172638103/10000000000 : ℝ)*X 1 2+(4355349477/10000000000 : ℝ)*X 2 0+(142061803/312500000 : ℝ)*X 2 1+(4172638103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2991774577843731540871181831/293625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (376968853/25000000000000 : ℝ)*(base19) + (576488391/50000000000000 : ℝ)*(base23) + (107664667/100000000000000 : ℝ)*(lower2) + (143271897/100000000000000 : ℝ)*(upper3) + (156076719/100000000000000 : ℝ)*(upper5) + (4001186920657121/100000000000000 : ℝ)*(major0) + (4001186920657121/100000000000000 : ℝ)*(major1) + (4001186920657121/100000000000000 : ℝ)*(major2) + (2671947482665933/50000000000000 : ℝ)*(sp0) + (667991540594437/12500000000000 : ℝ)*(sp1) + (5343932679654127/100000000000000 : ℝ)*(sp2) + (531684655351763/20000000000000 : ℝ)*(sp3) + (38867299043/100000000000000 : ℝ)*(sp4) + (2049035979/12500000000000 : ℝ)*(sp7) + (332304958630831/12500000000000 : ℝ)*(f.failure) + (1335983458157727/25000000000000 : ℝ)*(f.sum) + (9871578075349/8808750000000000000000000000 : ℝ)*base66 + (5980666253254156831/3523500000000000000000000000000000 : ℝ)*base67 + (40838820481090843169/3523500000000000000000000000000000 : ℝ)*base70 + (11442867538195843169/3523500000000000000000000000000000 : ℝ)*base72 + (170487778752059/35235000000000000000000000000 : ℝ)*base73 + (27431812159354843169/3523500000000000000000000000000000 : ℝ)*base76 + (35947028535454843169/3523500000000000000000000000000000 : ℝ)*base78 + (14147399636884843169/3523500000000000000000000000000000 : ℝ)*base80 + (1542187872667/1101093750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (1162043/78125000000000000000 : ℝ)*base89 + (1162043/78125000000000000000 : ℝ)*base91 + (1162043/78125000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1240072480052619793199287073/146812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2356044043/100000000000000 : ℝ)*(base19) + (224554157/10000000000000 : ℝ)*(base23) + (20594899/12500000000000 : ℝ)*(upper3) + (142135963/100000000000000 : ℝ)*(lower4) + (149705543/50000000000000 : ℝ)*(upper5) + (2015706536220143/50000000000000 : ℝ)*(major0) + (2015706536220143/50000000000000 : ℝ)*(major1) + (2015706536220143/50000000000000 : ℝ)*(major2) + (4689485859/10000000000000 : ℝ)*(sp1) + (12038866541/25000000000000 : ℝ)*(sp2) + (1076860710633773/20000000000000 : ℝ)*(sp4) + (5384254302266233/100000000000000 : ℝ)*(sp5) + (5384253152161131/100000000000000 : ℝ)*(sp6) + (2678522310156999/100000000000000 : ℝ)*(sp7) + (2678522310156999/100000000000000 : ℝ)*(f.failure) + (1076860710633773/20000000000000 : ℝ)*(f.sum) + (2770894470257/17617500000000000000000000000 : ℝ)*base65 + (11263406562975662927/1761750000000000000000000000000000 : ℝ)*base68 + (29266668914563412927/1761750000000000000000000000000000 : ℝ)*base70 + (11998020073778162927/1761750000000000000000000000000000 : ℝ)*base72 + (12076687588133/4404375000000000000000000000 : ℝ)*base73 + (28233782772780662927/1761750000000000000000000000000000 : ℝ)*base76 + (3717783599027337073/1761750000000000000000000000000000 : ℝ)*base77 + (29741445802524662927/1761750000000000000000000000000000 : ℝ)*base80 + (155030202313481/35235000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1164197/625000000000000000000 : ℝ)*base89 + (1164197/625000000000000000000 : ℝ)*base91 + (1164197/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1195_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (327/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9303/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5393/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1195_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1195_s4_0 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2141136919/10000000000 : ℝ)*x 0 + (1349868197/2500000000 : ℝ)*x 1 + (1314895863/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141136919/10000000000 : ℝ)^2097 ≤ (3253595801281/25000000000000 : ℝ)^1585 := by
    have hnat : (2141136919 : ℕ)^2097*25000000000000^1585 ≤ 3253595801281^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141136919 10000000000 3253595801281 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349868197/2500000000 : ℝ)^2097 ≤ (44247959317367/100000000000000 : ℝ)^1585 := by
    have hnat : (1349868197 : ℕ)^2097*100000000000000^1585 ≤ 44247959317367^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349868197 2500000000 44247959317367 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314895863/2500000000 : ℝ)^2097 ≤ (4273765746363/10000000000000 : ℝ)^1585 := by
    have hnat : (1314895863 : ℕ)^2097*10000000000000^1585 ≤ 4273765746363^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314895863 2500000000 4273765746363 10000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2141136919/10000000000 : ℝ), (1349868197/2500000000 : ℝ), (1314895863/2500000000 : ℝ)] ![(3253595801281/25000000000000 : ℝ), (44247959317367/100000000000000 : ℝ), (4273765746363/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2141136919/10000000000 : ℝ)|^2097 ≤ (3253595801281/25000000000000 : ℝ)^1585
        have hw : |(-2141136919/10000000000 : ℝ)|=(2141136919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349868197/2500000000 : ℝ)|^2097 ≤ (44247959317367/100000000000000 : ℝ)^1585
        have hw : |(1349868197/2500000000 : ℝ)|=(1349868197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1314895863/2500000000 : ℝ)|^2097 ≤ (4273765746363/10000000000000 : ℝ)^1585
        have hw : |(1314895863/2500000000 : ℝ)|=(1314895863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s4_1 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673203407/5000000000 : ℝ)*x 0 + (-1106094921/5000000000 : ℝ)*x 1 + (5259583581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673203407/5000000000 : ℝ)^2097 ≤ (2183676557603/5000000000000 : ℝ)^1585 := by
    have hnat : (2673203407 : ℕ)^2097*5000000000000^1585 ≤ 2183676557603^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673203407 5000000000 2183676557603 5000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1106094921/5000000000 : ℝ)^2097 ≤ (6794404990401/50000000000000 : ℝ)^1585 := by
    have hnat : (1106094921 : ℕ)^2097*50000000000000^1585 ≤ 6794404990401^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106094921 5000000000 6794404990401 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5259583581/10000000000 : ℝ)^2097 ≤ (10684414712611/25000000000000 : ℝ)^1585 := by
    have hnat : (5259583581 : ℕ)^2097*25000000000000^1585 ≤ 10684414712611^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259583581 10000000000 10684414712611 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673203407/5000000000 : ℝ), (-1106094921/5000000000 : ℝ), (5259583581/10000000000 : ℝ)] ![(2183676557603/5000000000000 : ℝ), (6794404990401/50000000000000 : ℝ), (10684414712611/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673203407/5000000000 : ℝ)|^2097 ≤ (2183676557603/5000000000000 : ℝ)^1585
        have hw : |(2673203407/5000000000 : ℝ)|=(2673203407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1106094921/5000000000 : ℝ)|^2097 ≤ (6794404990401/50000000000000 : ℝ)^1585
        have hw : |(-1106094921/5000000000 : ℝ)|=(1106094921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5259583581/10000000000 : ℝ)|^2097 ≤ (10684414712611/25000000000000 : ℝ)^1585
        have hw : |(5259583581/10000000000 : ℝ)|=(5259583581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s4_2 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5346406531/10000000000 : ℝ)*x 0 + (5259583421/10000000000 : ℝ)*x 1 + (-221219043/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346406531/10000000000 : ℝ)^2097 ≤ (1364797752923/3125000000000 : ℝ)^1585 := by
    have hnat : (5346406531 : ℕ)^2097*3125000000000^1585 ≤ 1364797752923^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346406531 10000000000 1364797752923 3125000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5259583421/10000000000 : ℝ)^2097 ≤ (10684414282591/25000000000000 : ℝ)^1585 := by
    have hnat : (5259583421 : ℕ)^2097*25000000000000^1585 ≤ 10684414282591^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259583421 10000000000 10684414282591 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221219043/1000000000 : ℝ)^2097 ≤ (2717762951891/20000000000000 : ℝ)^1585 := by
    have hnat : (221219043 : ℕ)^2097*20000000000000^1585 ≤ 2717762951891^1585*1000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221219043 1000000000 2717762951891 20000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346406531/10000000000 : ℝ), (5259583421/10000000000 : ℝ), (-221219043/1000000000 : ℝ)] ![(1364797752923/3125000000000 : ℝ), (10684414282591/25000000000000 : ℝ), (2717762951891/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346406531/10000000000 : ℝ)|^2097 ≤ (1364797752923/3125000000000 : ℝ)^1585
        have hw : |(5346406531/10000000000 : ℝ)|=(5346406531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5259583421/10000000000 : ℝ)|^2097 ≤ (10684414282591/25000000000000 : ℝ)^1585
        have hw : |(5259583421/10000000000 : ℝ)|=(5259583421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-221219043/1000000000 : ℝ)|^2097 ≤ (2717762951891/20000000000000 : ℝ)^1585
        have hw : |(-221219043/1000000000 : ℝ)|=(221219043/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s4_3 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (272304679/625000000 : ℝ)*x 0 + (4218502527/10000000000 : ℝ)*x 1 + (899941141/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272304679/625000000 : ℝ)^2097 ≤ (2082084794809/6250000000000 : ℝ)^1585 := by
    have hnat : (272304679 : ℕ)^2097*6250000000000^1585 ≤ 2082084794809^1585*625000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272304679 625000000 2082084794809 6250000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4218502527/10000000000 : ℝ)^2097 ≤ (15960401454611/50000000000000 : ℝ)^1585 := by
    have hnat : (4218502527 : ℕ)^2097*50000000000000^1585 ≤ 15960401454611^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4218502527 10000000000 15960401454611 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899941141/2000000000 : ℝ)^2097 ≤ (34765840362229/100000000000000 : ℝ)^1585 := by
    have hnat : (899941141 : ℕ)^2097*100000000000000^1585 ≤ 34765840362229^1585*2000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899941141 2000000000 34765840362229 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272304679/625000000 : ℝ), (4218502527/10000000000 : ℝ), (899941141/2000000000 : ℝ)] ![(2082084794809/6250000000000 : ℝ), (15960401454611/50000000000000 : ℝ), (34765840362229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272304679/625000000 : ℝ)|^2097 ≤ (2082084794809/6250000000000 : ℝ)^1585
        have hw : |(272304679/625000000 : ℝ)|=(272304679/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4218502527/10000000000 : ℝ)|^2097 ≤ (15960401454611/50000000000000 : ℝ)^1585
        have hw : |(4218502527/10000000000 : ℝ)|=(4218502527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899941141/2000000000 : ℝ)|^2097 ≤ (34765840362229/100000000000000 : ℝ)^1585
        have hw : |(899941141/2000000000 : ℝ)|=(899941141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s4_4 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2141143553/10000000000 : ℝ)*x 0 + (5259975929/10000000000 : ℝ)*x 1 + (1079815739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141143553/10000000000 : ℝ)^2097 ≤ (13014436553843/100000000000000 : ℝ)^1585 := by
    have hnat : (2141143553 : ℕ)^2097*100000000000000^1585 ≤ 13014436553843^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141143553 10000000000 13014436553843 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5259975929/10000000000 : ℝ)^2097 ≤ (42741876837149/100000000000000 : ℝ)^1585 := by
    have hnat : (5259975929 : ℕ)^2097*100000000000000^1585 ≤ 42741876837149^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259975929 10000000000 42741876837149 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079815739/2000000000 : ℝ)^2097 ≤ (22121843297597/50000000000000 : ℝ)^1585 := by
    have hnat : (1079815739 : ℕ)^2097*50000000000000^1585 ≤ 22121843297597^1585*2000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079815739 2000000000 22121843297597 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2141143553/10000000000 : ℝ), (5259975929/10000000000 : ℝ), (1079815739/2000000000 : ℝ)] ![(13014436553843/100000000000000 : ℝ), (42741876837149/100000000000000 : ℝ), (22121843297597/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2141143553/10000000000 : ℝ)|^2097 ≤ (13014436553843/100000000000000 : ℝ)^1585
        have hw : |(-2141143553/10000000000 : ℝ)|=(2141143553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5259975929/10000000000 : ℝ)|^2097 ≤ (42741876837149/100000000000000 : ℝ)^1585
        have hw : |(5259975929/10000000000 : ℝ)|=(5259975929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079815739/2000000000 : ℝ)|^2097 ≤ (22121843297597/50000000000000 : ℝ)^1585
        have hw : |(1079815739/2000000000 : ℝ)|=(1079815739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s4_5 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1327707737/2500000000 : ℝ)*x 0 + (-103634759/500000000 : ℝ)*x 1 + (1079815697/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327707737/2500000000 : ℝ)^2097 ≤ (10822364656593/25000000000000 : ℝ)^1585 := by
    have hnat : (1327707737 : ℕ)^2097*25000000000000^1585 ≤ 10822364656593^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327707737 2500000000 10822364656593 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103634759/500000000 : ℝ)^2097 ≤ (6233428520657/50000000000000 : ℝ)^1585 := by
    have hnat : (103634759 : ℕ)^2097*50000000000000^1585 ≤ 6233428520657^1585*500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103634759 500000000 6233428520657 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079815697/2000000000 : ℝ)^2097 ≤ (44243684318419/100000000000000 : ℝ)^1585 := by
    have hnat : (1079815697 : ℕ)^2097*100000000000000^1585 ≤ 44243684318419^1585*2000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079815697 2000000000 44243684318419 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327707737/2500000000 : ℝ), (-103634759/500000000 : ℝ), (1079815697/2000000000 : ℝ)] ![(10822364656593/25000000000000 : ℝ), (6233428520657/50000000000000 : ℝ), (44243684318419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327707737/2500000000 : ℝ)|^2097 ≤ (10822364656593/25000000000000 : ℝ)^1585
        have hw : |(1327707737/2500000000 : ℝ)|=(1327707737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103634759/500000000 : ℝ)|^2097 ≤ (6233428520657/50000000000000 : ℝ)^1585
        have hw : |(-103634759/500000000 : ℝ)|=(103634759/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079815697/2000000000 : ℝ)|^2097 ≤ (44243684318419/100000000000000 : ℝ)^1585
        have hw : |(1079815697/2000000000 : ℝ)|=(1079815697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s4_6 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1327707459/2500000000 : ℝ)*x 0 + (5399079893/10000000000 : ℝ)*x 1 + (-2072694769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327707459/2500000000 : ℝ)^2097 ≤ (43289446634317/100000000000000 : ℝ)^1585 := by
    have hnat : (1327707459 : ℕ)^2097*100000000000000^1585 ≤ 43289446634317^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327707459 2500000000 43289446634317 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399079893/10000000000 : ℝ)^2097 ≤ (22121849791827/50000000000000 : ℝ)^1585 := by
    have hnat : (5399079893 : ℕ)^2097*50000000000000^1585 ≤ 22121849791827^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399079893 10000000000 22121849791827 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072694769/10000000000 : ℝ)^2097 ≤ (498674150827/4000000000000 : ℝ)^1585 := by
    have hnat : (2072694769 : ℕ)^2097*4000000000000^1585 ≤ 498674150827^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072694769 10000000000 498674150827 4000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327707459/2500000000 : ℝ), (5399079893/10000000000 : ℝ), (-2072694769/10000000000 : ℝ)] ![(43289446634317/100000000000000 : ℝ), (22121849791827/50000000000000 : ℝ), (498674150827/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327707459/2500000000 : ℝ)|^2097 ≤ (43289446634317/100000000000000 : ℝ)^1585
        have hw : |(1327707459/2500000000 : ℝ)|=(1327707459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399079893/10000000000 : ℝ)|^2097 ≤ (22121849791827/50000000000000 : ℝ)^1585
        have hw : |(5399079893/10000000000 : ℝ)|=(5399079893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2072694769/10000000000 : ℝ)|^2097 ≤ (498674150827/4000000000000 : ℝ)^1585
        have hw : |(-2072694769/10000000000 : ℝ)|=(2072694769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s4_7 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (3403819/7812500 : ℝ)*x 0 + (4498917309/10000000000 : ℝ)*x 1 + (2109646943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3403819/7812500 : ℝ)^2097 ≤ (33313492839053/100000000000000 : ℝ)^1585 := by
    have hnat : (3403819 : ℕ)^2097*100000000000000^1585 ≤ 33313492839053^1585*7812500^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3403819 7812500 33313492839053 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498917309/10000000000 : ℝ)^2097 ≤ (34757781570973/100000000000000 : ℝ)^1585 := by
    have hnat : (4498917309 : ℕ)^2097*100000000000000^1585 ≤ 34757781570973^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498917309 10000000000 34757781570973 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2109646943/5000000000 : ℝ)^2097 ≤ (31928725575463/100000000000000 : ℝ)^1585 := by
    have hnat : (2109646943 : ℕ)^2097*100000000000000^1585 ≤ 31928725575463^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109646943 5000000000 31928725575463 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3403819/7812500 : ℝ), (4498917309/10000000000 : ℝ), (2109646943/5000000000 : ℝ)] ![(33313492839053/100000000000000 : ℝ), (34757781570973/100000000000000 : ℝ), (31928725575463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3403819/7812500 : ℝ)|^2097 ≤ (33313492839053/100000000000000 : ℝ)^1585
        have hw : |(3403819/7812500 : ℝ)|=(3403819/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498917309/10000000000 : ℝ)|^2097 ≤ (34757781570973/100000000000000 : ℝ)^1585
        have hw : |(4498917309/10000000000 : ℝ)|=(4498917309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2109646943/5000000000 : ℝ)|^2097 ≤ (31928725575463/100000000000000 : ℝ)^1585
        have hw : |(2109646943/5000000000 : ℝ)|=(2109646943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1195_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5393/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1409/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14747/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5393/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14747/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5393/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14747/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5393/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14747/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5393/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14747/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5393/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14747/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5393/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5393/50000 : ℝ) ^ (8387/2048 : ℝ) ≤ (10948525127265397/100000000000000000000 : ℝ) := by
    have hpowers : (5393/50000 : ℝ)^8387 ≤ (10948525127265397/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5393 : ℕ)^8387*100000000000000000000^2048 ≤ 10948525127265397^2048*50000^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5393 50000 10948525127265397 100000000000000000000 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5393/50000 : ℝ)) (X := (10948525127265397/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14747/100000 : ℝ) ^ (8387/2048 : ℝ) ≤ (9853782692829111/25000000000000000000 : ℝ) := by
    have hpowers : (14747/100000 : ℝ)^8387 ≤ (9853782692829111/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14747 : ℕ)^8387*25000000000000000000^2048 ≤ 9853782692829111^2048*100000^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14747 100000 9853782692829111 25000000000000000000 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14747/100000 : ℝ)) (X := (9853782692829111/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010948525127265397/50000000000000000000 : ℝ) ≤ (10000534654208241/10000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (50010948525127265397/50000000000000000000 : ℝ)^2048 ≤ (10000534654208241/10000000000000000 : ℝ)^8387 := by
      have hnat : (50010948525127265397 : ℕ)^2048*10000000000000000^8387 ≤ 10000534654208241^8387*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010948525127265397 50000000000000000000 10000534654208241 10000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000534654208241/10000000000000000 : ℝ)) (X := (50010948525127265397/50000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050363655898581841/100000000000000000000 : ℝ) ≤ (10001229583185733/10000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (100050363655898581841/100000000000000000000 : ℝ)^2048 ≤ (10001229583185733/10000000000000000 : ℝ)^8387 := by
      have hnat : (100050363655898581841 : ℕ)^2048*10000000000000000^8387 ≤ 10001229583185733^8387*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050363655898581841 100000000000000000000 10001229583185733 10000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001229583185733/10000000000000000 : ℝ)) (X := (100050363655898581841/100000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509853782692829111/12500000000000000000 : ℝ) ≤ (400076980486529/400000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (12509853782692829111/12500000000000000000 : ℝ)^2048 ≤ (400076980486529/400000000000000 : ℝ)^8387 := by
      have hnat : (12509853782692829111 : ℕ)^2048*400000000000000^8387 ≤ 400076980486529^8387*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509853782692829111 12500000000000000000 400076980486529 400000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400076980486529/400000000000000 : ℝ)) (X := (12509853782692829111/12500000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10948525127265397/100000000000000000000 : ℝ) ≤ ((39597126757416385177/39610000000000000000 : ℝ)+2*(173732244373/99025000000000 : ℝ)*(5393/50000 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (39597126757416385177/39610000000000000000 : ℝ)+2*(173732244373/99025000000000 : ℝ)*(5393/50000 : ℝ)=(10000534654208241/10000000000000000 : ℝ) by norm_num, show 1+2*(10948525127265397/100000000000000000000 : ℝ)=(50010948525127265397/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9853782692829111/25000000000000000000 : ℝ)+(10948525127265397/100000000000000000000 : ℝ) ≤ ((39597126757416385177/39610000000000000000 : ℝ)+(173732244373/99025000000000 : ℝ)*((14747/100000 : ℝ)+(5393/50000 : ℝ)))^(8387/2048 : ℝ) := by
    rw [show (39597126757416385177/39610000000000000000 : ℝ)+(173732244373/99025000000000 : ℝ)*((14747/100000 : ℝ)+(5393/50000 : ℝ))=(10001229583185733/10000000000000000 : ℝ) by norm_num, show 1+(9853782692829111/25000000000000000000 : ℝ)+(10948525127265397/100000000000000000000 : ℝ)=(100050363655898581841/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9853782692829111/25000000000000000000 : ℝ) ≤ ((39597126757416385177/39610000000000000000 : ℝ)+2*(173732244373/99025000000000 : ℝ)*(14747/100000 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (39597126757416385177/39610000000000000000 : ℝ)+2*(173732244373/99025000000000 : ℝ)*(14747/100000 : ℝ)=(400076980486529/400000000000000 : ℝ) by norm_num, show 1+2*(9853782692829111/25000000000000000000 : ℝ)=(12509853782692829111/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (39597126757416385177/39610000000000000000 : ℝ)*(X 1 0+X 2 0)+(173732244373/99025000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (5393/50000 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (39597126757416385177/39610000000000000000 : ℝ)) (alpha := (173732244373/99025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (39597126757416385177/39610000000000000000 : ℝ)*(X 0 1+X 2 1)+(173732244373/99025000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (5393/50000 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (39597126757416385177/39610000000000000000 : ℝ)) (alpha := (173732244373/99025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (39597126757416385177/39610000000000000000 : ℝ)*(X 0 2+X 1 2)+(173732244373/99025000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (5393/50000 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (39597126757416385177/39610000000000000000 : ℝ)) (alpha := (173732244373/99025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2141136919/10000000000 : ℝ)*X 0 0+(1349868197/2500000000 : ℝ)*X 0 1+(1314895863/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673203407/5000000000 : ℝ)*X 1 0+(-1106094921/5000000000 : ℝ)*X 1 1+(5259583581/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346406531/10000000000 : ℝ)*X 2 0+(5259583421/10000000000 : ℝ)*X 2 1+(-221219043/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((272304679/625000000 : ℝ)*X 0 0+(4218502527/10000000000 : ℝ)*X 0 1+(899941141/2000000000 : ℝ)*X 0 2+(272304679/625000000 : ℝ)*X 1 0+(4218502527/10000000000 : ℝ)*X 1 1+(899941141/2000000000 : ℝ)*X 1 2+(272304679/625000000 : ℝ)*X 2 0+(4218502527/10000000000 : ℝ)*X 2 1+(899941141/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2141143553/10000000000 : ℝ)*X 0 0+(5259975929/10000000000 : ℝ)*X 0 1+(1079815739/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327707737/2500000000 : ℝ)*X 1 0+(-103634759/500000000 : ℝ)*X 1 1+(1079815697/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327707459/2500000000 : ℝ)*X 2 0+(5399079893/10000000000 : ℝ)*X 2 1+(-2072694769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3403819/7812500 : ℝ)*X 0 0+(4498917309/10000000000 : ℝ)*X 0 1+(2109646943/5000000000 : ℝ)*X 0 2+(3403819/7812500 : ℝ)*X 1 0+(4498917309/10000000000 : ℝ)*X 1 1+(2109646943/5000000000 : ℝ)*X 1 2+(3403819/7812500 : ℝ)*X 2 0+(4498917309/10000000000 : ℝ)*X 2 1+(2109646943/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8539822894681436889807602817/1980500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (952307939/50000000000000 : ℝ)*(base19) + (908894183/50000000000000 : ℝ)*(base23) + (96581723/50000000000000 : ℝ)*(upper2) + (388524179/100000000000000 : ℝ)*(upper3) + (5352418410410369/100000000000000 : ℝ)*(major0) + (5352418410410369/100000000000000 : ℝ)*(major1) + (5352418410410369/100000000000000 : ℝ)*(major2) + (7148578073987099/100000000000000 : ℝ)*(sp0) + (1429723930375481/20000000000000 : ℝ)*(sp1) + (1429721852041749/20000000000000 : ℝ)*(sp2) + (142247182277727/4000000000000 : ℝ)*(sp3) + (5435313273/12500000000000 : ℝ)*(sp4) + (10478496173/100000000000000 : ℝ)*(sp6) + (7112730501/20000000000000 : ℝ)*(sp7) + (22226344503723/625000000000 : ℝ)*(f.failure) + (7148621556493283/100000000000000 : ℝ)*(f.sum) + (39982762812613/19805000000000000000000000000 : ℝ)*base65 + (25845973867904499687/3961000000000000000000000000000000 : ℝ)*base68 + (42431133273519499687/3961000000000000000000000000000000 : ℝ)*base70 + (8787583759076499687/3961000000000000000000000000000000 : ℝ)*base72 + (153245996793/309453125000000000000000000 : ℝ)*base74 + (59704466766116499687/3961000000000000000000000000000000 : ℝ)*base76 + (82806369122509499687/3961000000000000000000000000000000 : ℝ)*base78 + (4360556003650499687/3961000000000000000000000000000000 : ℝ)*base80 + (32129733698029/9902500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (22987/7812500000000000000 : ℝ)*base90 + (22987/7812500000000000000 : ℝ)*base92 + (22987/7812500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (100914125418203064626679/9902500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1111755597/50000000000000 : ℝ)*(base19) + (1213971913/100000000000000 : ℝ)*(base23) + (106833/97656250000 : ℝ)*(upper2) + (178795323/25000000000000 : ℝ)*(upper3) + (3074041/12500000000000 : ℝ)*(upper5) + (2691282217537677/50000000000000 : ℝ)*(major0) + (2691282217537677/50000000000000 : ℝ)*(major1) + (2691282217537677/50000000000000 : ℝ)*(major2) + (5622864639/50000000000000 : ℝ)*(sp1) + (54492185583/100000000000000 : ℝ)*(sp2) + (1797221001558117/25000000000000 : ℝ)*(sp4) + (1797217634247999/25000000000000 : ℝ)*(sp5) + (7188828300074971/100000000000000 : ℝ)*(sp6) + (1788122262112907/50000000000000 : ℝ)*(sp7) + (1788122262112907/50000000000000 : ℝ)*(f.failure) + (1797221001558117/25000000000000 : ℝ)*(f.sum) + (16623082769747/4951250000000000000000000000 : ℝ)*base65 + (6746648024938786171/1980500000000000000000000000000000 : ℝ)*base68 + (3410228736201786171/1980500000000000000000000000000000 : ℝ)*base70 + (31140301760860213829/1980500000000000000000000000000000 : ℝ)*base71 + (7834097780159/9902500000000000000000000000 : ℝ)*base73 + (11261963206500786171/1980500000000000000000000000000000 : ℝ)*base76 + (1521360157025713829/1980500000000000000000000000000000 : ℝ)*base77 + (3032239515154213829/1980500000000000000000000000000000 : ℝ)*base79 + (80041681416093/19805000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1343679/312500000000000000000 : ℝ)*base90 + (1343679/312500000000000000000 : ℝ)*base92 + (1343679/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1195_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5393/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1195_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1195_s5_0 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1070832803/5000000000 : ℝ)*x 0 + (2696781431/5000000000 : ℝ)*x 1 + (164535819/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070832803/5000000000 : ℝ)^2097 ≤ (13018634921291/100000000000000 : ℝ)^1585 := by
    have hnat : (1070832803 : ℕ)^2097*100000000000000^1585 ≤ 13018634921291^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070832803 5000000000 13018634921291 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696781431/5000000000 : ℝ)^2097 ≤ (44183894986493/100000000000000 : ℝ)^1585 := by
    have hnat : (2696781431 : ℕ)^2097*100000000000000^1585 ≤ 44183894986493^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696781431 5000000000 44183894986493 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164535819/312500000 : ℝ)^2097 ≤ (2139873503327/5000000000000 : ℝ)^1585 := by
    have hnat : (164535819 : ℕ)^2097*5000000000000^1585 ≤ 2139873503327^1585*312500000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164535819 312500000 2139873503327 5000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1070832803/5000000000 : ℝ), (2696781431/5000000000 : ℝ), (164535819/312500000 : ℝ)] ![(13018634921291/100000000000000 : ℝ), (44183894986493/100000000000000 : ℝ), (2139873503327/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1070832803/5000000000 : ℝ)|^2097 ≤ (13018634921291/100000000000000 : ℝ)^1585
        have hw : |(-1070832803/5000000000 : ℝ)|=(1070832803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696781431/5000000000 : ℝ)|^2097 ≤ (44183894986493/100000000000000 : ℝ)^1585
        have hw : |(2696781431/5000000000 : ℝ)|=(2696781431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164535819/312500000 : ℝ)|^2097 ≤ (2139873503327/5000000000000 : ℝ)^1585
        have hw : |(164535819/312500000 : ℝ)|=(164535819/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s5_1 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344917513/10000000000 : ℝ)*x 0 + (-441361729/2000000000 : ℝ)*x 1 + (5265146141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344917513/10000000000 : ℝ)^2097 ≤ (8731487249471/20000000000000 : ℝ)^1585 := by
    have hnat : (5344917513 : ℕ)^2097*20000000000000^1585 ≤ 8731487249471^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344917513 10000000000 8731487249471 20000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441361729/2000000000 : ℝ)^2097 ≤ (13545094392079/100000000000000 : ℝ)^1585 := by
    have hnat : (441361729 : ℕ)^2097*100000000000000^1585 ≤ 13545094392079^1585*2000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441361729 2000000000 13545094392079 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265146141/10000000000 : ℝ)^2097 ≤ (42797469346011/100000000000000 : ℝ)^1585 := by
    have hnat : (5265146141 : ℕ)^2097*100000000000000^1585 ≤ 42797469346011^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265146141 10000000000 42797469346011 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344917513/10000000000 : ℝ), (-441361729/2000000000 : ℝ), (5265146141/10000000000 : ℝ)] ![(8731487249471/20000000000000 : ℝ), (13545094392079/100000000000000 : ℝ), (42797469346011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344917513/10000000000 : ℝ)|^2097 ≤ (8731487249471/20000000000000 : ℝ)^1585
        have hw : |(5344917513/10000000000 : ℝ)|=(5344917513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-441361729/2000000000 : ℝ)|^2097 ≤ (13545094392079/100000000000000 : ℝ)^1585
        have hw : |(-441361729/2000000000 : ℝ)|=(441361729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265146141/10000000000 : ℝ)|^2097 ≤ (42797469346011/100000000000000 : ℝ)^1585
        have hw : |(5265146141/10000000000 : ℝ)|=(5265146141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s5_2 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344917467/10000000000 : ℝ)*x 0 + (5265146203/10000000000 : ℝ)*x 1 + (-137925539/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344917467/10000000000 : ℝ)^2097 ≤ (21828717875127/50000000000000 : ℝ)^1585 := by
    have hnat : (5344917467 : ℕ)^2097*50000000000000^1585 ≤ 21828717875127^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344917467 10000000000 21828717875127 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265146203/10000000000 : ℝ)^2097 ≤ (42797470012769/100000000000000 : ℝ)^1585 := by
    have hnat : (5265146203 : ℕ)^2097*100000000000000^1585 ≤ 42797470012769^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265146203 10000000000 42797470012769 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137925539/625000000 : ℝ)^2097 ≤ (13545094221547/100000000000000 : ℝ)^1585 := by
    have hnat : (137925539 : ℕ)^2097*100000000000000^1585 ≤ 13545094221547^1585*625000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137925539 625000000 13545094221547 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344917467/10000000000 : ℝ), (5265146203/10000000000 : ℝ), (-137925539/625000000 : ℝ)] ![(21828717875127/50000000000000 : ℝ), (42797470012769/100000000000000 : ℝ), (13545094221547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344917467/10000000000 : ℝ)|^2097 ≤ (21828717875127/50000000000000 : ℝ)^1585
        have hw : |(5344917467/10000000000 : ℝ)|=(5344917467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265146203/10000000000 : ℝ)|^2097 ≤ (42797470012769/100000000000000 : ℝ)^1585
        have hw : |(5265146203/10000000000 : ℝ)|=(5265146203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137925539/625000000 : ℝ)|^2097 ≤ (13545094221547/100000000000000 : ℝ)^1585
        have hw : |(-137925539/625000000 : ℝ)|=(137925539/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s5_3 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4357185299/10000000000 : ℝ)*x 0 + (528749247/1250000000 : ℝ)*x 1 + (561016793/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357185299/10000000000 : ℝ)^2097 ≤ (33316497139951/100000000000000 : ℝ)^1585 := by
    have hnat : (4357185299 : ℕ)^2097*100000000000000^1585 ≤ 33316497139951^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357185299 10000000000 33316497139951 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528749247/1250000000 : ℝ)^2097 ≤ (16017948148011/50000000000000 : ℝ)^1585 := by
    have hnat : (528749247 : ℕ)^2097*50000000000000^1585 ≤ 16017948148011^1585*1250000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528749247 1250000000 16017948148011 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561016793/1250000000 : ℝ)^2097 ≤ (8661901636829/25000000000000 : ℝ)^1585 := by
    have hnat : (561016793 : ℕ)^2097*25000000000000^1585 ≤ 8661901636829^1585*1250000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561016793 1250000000 8661901636829 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357185299/10000000000 : ℝ), (528749247/1250000000 : ℝ), (561016793/1250000000 : ℝ)] ![(33316497139951/100000000000000 : ℝ), (16017948148011/50000000000000 : ℝ), (8661901636829/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357185299/10000000000 : ℝ)|^2097 ≤ (33316497139951/100000000000000 : ℝ)^1585
        have hw : |(4357185299/10000000000 : ℝ)|=(4357185299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528749247/1250000000 : ℝ)|^2097 ≤ (16017948148011/50000000000000 : ℝ)^1585
        have hw : |(528749247/1250000000 : ℝ)|=(528749247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561016793/1250000000 : ℝ)|^2097 ≤ (8661901636829/25000000000000 : ℝ)^1585
        have hw : |(561016793/1250000000 : ℝ)|=(561016793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s5_4 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-214167079/1000000000 : ℝ)*x 0 + (2632738329/5000000000 : ℝ)*x 1 + (2696615561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214167079/1000000000 : ℝ)^2097 ≤ (813667288303/6250000000000 : ℝ)^1585 := by
    have hnat : (214167079 : ℕ)^2097*6250000000000^1585 ≤ 813667288303^1585*1000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214167079 1000000000 813667288303 6250000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632738329/5000000000 : ℝ)^2097 ≤ (5350127977181/12500000000000 : ℝ)^1585 := by
    have hnat : (2632738329 : ℕ)^2097*12500000000000^1585 ≤ 5350127977181^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632738329 5000000000 5350127977181 12500000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696615561/5000000000 : ℝ)^2097 ≤ (22090149777811/50000000000000 : ℝ)^1585 := by
    have hnat : (2696615561 : ℕ)^2097*50000000000000^1585 ≤ 22090149777811^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696615561 5000000000 22090149777811 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-214167079/1000000000 : ℝ), (2632738329/5000000000 : ℝ), (2696615561/5000000000 : ℝ)] ![(813667288303/6250000000000 : ℝ), (5350127977181/12500000000000 : ℝ), (22090149777811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-214167079/1000000000 : ℝ)|^2097 ≤ (813667288303/6250000000000 : ℝ)^1585
        have hw : |(-214167079/1000000000 : ℝ)|=(214167079/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632738329/5000000000 : ℝ)|^2097 ≤ (5350127977181/12500000000000 : ℝ)^1585
        have hw : |(2632738329/5000000000 : ℝ)|=(2632738329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696615561/5000000000 : ℝ)|^2097 ≤ (22090149777811/50000000000000 : ℝ)^1585
        have hw : |(2696615561/5000000000 : ℝ)|=(2696615561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s5_5 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1328064553/2500000000 : ℝ)*x 0 + (-103936191/500000000 : ℝ)*x 1 + (5393230677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328064553/2500000000 : ℝ)^2097 ≤ (43304851227033/100000000000000 : ℝ)^1585 := by
    have hnat : (1328064553 : ℕ)^2097*100000000000000^1585 ≤ 43304851227033^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328064553 2500000000 43304851227033 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103936191/500000000 : ℝ)^2097 ≤ (12514854019741/100000000000000 : ℝ)^1585 := by
    have hnat : (103936191 : ℕ)^2097*100000000000000^1585 ≤ 12514854019741^1585*500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103936191 500000000 12514854019741 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393230677/10000000000 : ℝ)^2097 ≤ (11045073683179/25000000000000 : ℝ)^1585 := by
    have hnat : (5393230677 : ℕ)^2097*25000000000000^1585 ≤ 11045073683179^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393230677 10000000000 11045073683179 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328064553/2500000000 : ℝ), (-103936191/500000000 : ℝ), (5393230677/10000000000 : ℝ)] ![(43304851227033/100000000000000 : ℝ), (12514854019741/100000000000000 : ℝ), (11045073683179/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328064553/2500000000 : ℝ)|^2097 ≤ (43304851227033/100000000000000 : ℝ)^1585
        have hw : |(1328064553/2500000000 : ℝ)|=(1328064553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103936191/500000000 : ℝ)|^2097 ≤ (12514854019741/100000000000000 : ℝ)^1585
        have hw : |(-103936191/500000000 : ℝ)|=(103936191/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393230677/10000000000 : ℝ)|^2097 ≤ (11045073683179/25000000000000 : ℝ)^1585
        have hw : |(5393230677/10000000000 : ℝ)|=(5393230677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s5_6 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312257797/10000000000 : ℝ)*x 0 + (5393231233/10000000000 : ℝ)*x 1 + (-2078723627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312257797/10000000000 : ℝ)^2097 ≤ (43304846751193/100000000000000 : ℝ)^1585 := by
    have hnat : (5312257797 : ℕ)^2097*100000000000000^1585 ≤ 43304846751193^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312257797 10000000000 43304846751193 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393231233/10000000000 : ℝ)^2097 ≤ (44180300758639/100000000000000 : ℝ)^1585 := by
    have hnat : (5393231233 : ℕ)^2097*100000000000000^1585 ≤ 44180300758639^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393231233 10000000000 44180300758639 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078723627/10000000000 : ℝ)^2097 ≤ (12514852482453/100000000000000 : ℝ)^1585 := by
    have hnat : (2078723627 : ℕ)^2097*100000000000000^1585 ≤ 12514852482453^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078723627 10000000000 12514852482453 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312257797/10000000000 : ℝ), (5393231233/10000000000 : ℝ), (-2078723627/10000000000 : ℝ)] ![(43304846751193/100000000000000 : ℝ), (44180300758639/100000000000000 : ℝ), (12514852482453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312257797/10000000000 : ℝ)|^2097 ≤ (43304846751193/100000000000000 : ℝ)^1585
        have hw : |(5312257797/10000000000 : ℝ)|=(5312257797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393231233/10000000000 : ℝ)|^2097 ≤ (44180300758639/100000000000000 : ℝ)^1585
        have hw : |(5393231233/10000000000 : ℝ)|=(5393231233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2078723627/10000000000 : ℝ)|^2097 ≤ (12514852482453/100000000000000 : ℝ)^1585
        have hw : |(-2078723627/10000000000 : ℝ)|=(2078723627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s5_7 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4357195227/10000000000 : ℝ)*x 0 + (2243734721/5000000000 : ℝ)*x 1 + (4230661667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357195227/10000000000 : ℝ)^2097 ≤ (4164574696849/12500000000000 : ℝ)^1585 := by
    have hnat : (4357195227 : ℕ)^2097*12500000000000^1585 ≤ 4164574696849^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357195227 10000000000 4164574696849 12500000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243734721/5000000000 : ℝ)^2097 ≤ (34640815702569/100000000000000 : ℝ)^1585 := by
    have hnat : (2243734721 : ℕ)^2097*100000000000000^1585 ≤ 34640815702569^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243734721 5000000000 34640815702569 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230661667/10000000000 : ℝ)^2097 ≤ (8010646677103/25000000000000 : ℝ)^1585 := by
    have hnat : (4230661667 : ℕ)^2097*25000000000000^1585 ≤ 8010646677103^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230661667 10000000000 8010646677103 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357195227/10000000000 : ℝ), (2243734721/5000000000 : ℝ), (4230661667/10000000000 : ℝ)] ![(4164574696849/12500000000000 : ℝ), (34640815702569/100000000000000 : ℝ), (8010646677103/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357195227/10000000000 : ℝ)|^2097 ≤ (4164574696849/12500000000000 : ℝ)^1585
        have hw : |(4357195227/10000000000 : ℝ)|=(4357195227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243734721/5000000000 : ℝ)|^2097 ≤ (34640815702569/100000000000000 : ℝ)^1585
        have hw : |(2243734721/5000000000 : ℝ)|=(2243734721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230661667/10000000000 : ℝ)|^2097 ≤ (8010646677103/25000000000000 : ℝ)^1585
        have hw : |(4230661667/10000000000 : ℝ)|=(4230661667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1195_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11391/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14111/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (1409/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1409/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1409/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1409/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1409/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1409/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1409/12500 : ℝ) ^ (8387/2048 : ℝ) ≤ (3278538972224563/25000000000000000000 : ℝ) := by
    have hpowers : (1409/12500 : ℝ)^8387 ≤ (3278538972224563/25000000000000000000 : ℝ)^2048 := by
      have hnat : (1409 : ℕ)^8387*25000000000000000000^2048 ≤ 3278538972224563^2048*12500^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1409 12500 3278538972224563 25000000000000000000 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1409/12500 : ℝ)) (X := (3278538972224563/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8387/2048 : ℝ) ≤ (34104913303350677/100000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8387 ≤ (34104913303350677/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8387*100000000000000000000^2048 ≤ 34104913303350677^2048*20000^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 34104913303350677 100000000000000000000 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (34104913303350677/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503278538972224563/12500000000000000000 : ℝ) ≤ (400025615957617/400000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (12503278538972224563/12500000000000000000 : ℝ)^2048 ≤ (400025615957617/400000000000000 : ℝ)^8387 := by
      have hnat : (12503278538972224563 : ℕ)^2048*400000000000000^8387 ≤ 400025615957617^8387*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503278538972224563 12500000000000000000 400025615957617 400000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400025615957617/400000000000000 : ℝ)) (X := (12503278538972224563/12500000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047219069192248929/100000000000000000000 : ℝ) ≤ (2000230564926969/2000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (100047219069192248929/100000000000000000000 : ℝ)^2048 ≤ (2000230564926969/2000000000000000 : ℝ)^8387 := by
      have hnat : (100047219069192248929 : ℕ)^2048*2000000000000000^8387 ≤ 2000230564926969^8387*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047219069192248929 100000000000000000000 2000230564926969 2000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000230564926969/2000000000000000 : ℝ)) (X := (100047219069192248929/100000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034104913303350677/50000000000000000000 : ℝ) ≤ (2000333050065853/2000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (50034104913303350677/50000000000000000000 : ℝ)^2048 ≤ (2000333050065853/2000000000000000 : ℝ)^8387 := by
      have hnat : (50034104913303350677 : ℕ)^2048*2000000000000000^8387 ≤ 2000333050065853^8387*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034104913303350677 50000000000000000000 2000333050065853 2000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000333050065853/2000000000000000 : ℝ)) (X := (50034104913303350677/50000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3278538972224563/25000000000000000000 : ℝ) ≤ ((5924069075441094959/5926000000000000000 : ℝ)+2*(25621284721/14815000000000 : ℝ)*(1409/12500 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (5924069075441094959/5926000000000000000 : ℝ)+2*(25621284721/14815000000000 : ℝ)*(1409/12500 : ℝ)=(400025615957617/400000000000000 : ℝ) by norm_num, show 1+2*(3278538972224563/25000000000000000000 : ℝ)=(12503278538972224563/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34104913303350677/100000000000000000000 : ℝ)+(3278538972224563/25000000000000000000 : ℝ) ≤ ((5924069075441094959/5926000000000000000 : ℝ)+(25621284721/14815000000000 : ℝ)*((2847/20000 : ℝ)+(1409/12500 : ℝ)))^(8387/2048 : ℝ) := by
    rw [show (5924069075441094959/5926000000000000000 : ℝ)+(25621284721/14815000000000 : ℝ)*((2847/20000 : ℝ)+(1409/12500 : ℝ))=(2000230564926969/2000000000000000 : ℝ) by norm_num, show 1+(34104913303350677/100000000000000000000 : ℝ)+(3278538972224563/25000000000000000000 : ℝ)=(100047219069192248929/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34104913303350677/100000000000000000000 : ℝ) ≤ ((5924069075441094959/5926000000000000000 : ℝ)+2*(25621284721/14815000000000 : ℝ)*(2847/20000 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (5924069075441094959/5926000000000000000 : ℝ)+2*(25621284721/14815000000000 : ℝ)*(2847/20000 : ℝ)=(2000333050065853/2000000000000000 : ℝ) by norm_num, show 1+2*(34104913303350677/100000000000000000000 : ℝ)=(50034104913303350677/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5924069075441094959/5926000000000000000 : ℝ)*(X 1 0+X 2 0)+(25621284721/14815000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (1409/12500 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (5924069075441094959/5926000000000000000 : ℝ)) (alpha := (25621284721/14815000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5924069075441094959/5926000000000000000 : ℝ)*(X 0 1+X 2 1)+(25621284721/14815000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (1409/12500 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (5924069075441094959/5926000000000000000 : ℝ)) (alpha := (25621284721/14815000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5924069075441094959/5926000000000000000 : ℝ)*(X 0 2+X 1 2)+(25621284721/14815000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (1409/12500 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (5924069075441094959/5926000000000000000 : ℝ)) (alpha := (25621284721/14815000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1070832803/5000000000 : ℝ)*X 0 0+(2696781431/5000000000 : ℝ)*X 0 1+(164535819/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344917513/10000000000 : ℝ)*X 1 0+(-441361729/2000000000 : ℝ)*X 1 1+(5265146141/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344917467/10000000000 : ℝ)*X 2 0+(5265146203/10000000000 : ℝ)*X 2 1+(-137925539/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4357185299/10000000000 : ℝ)*X 0 0+(528749247/1250000000 : ℝ)*X 0 1+(561016793/1250000000 : ℝ)*X 0 2+(4357185299/10000000000 : ℝ)*X 1 0+(528749247/1250000000 : ℝ)*X 1 1+(561016793/1250000000 : ℝ)*X 1 2+(4357185299/10000000000 : ℝ)*X 2 0+(528749247/1250000000 : ℝ)*X 2 1+(561016793/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-214167079/1000000000 : ℝ)*X 0 0+(2632738329/5000000000 : ℝ)*X 0 1+(2696615561/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328064553/2500000000 : ℝ)*X 1 0+(-103936191/500000000 : ℝ)*X 1 1+(5393230677/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312257797/10000000000 : ℝ)*X 2 0+(5393231233/10000000000 : ℝ)*X 2 1+(-2078723627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4357195227/10000000000 : ℝ)*X 0 0+(2243734721/5000000000 : ℝ)*X 0 1+(4230661667/10000000000 : ℝ)*X 0 2+(4357195227/10000000000 : ℝ)*X 1 0+(2243734721/5000000000 : ℝ)*X 1 1+(4230661667/10000000000 : ℝ)*X 1 2+(4357195227/10000000000 : ℝ)*X 2 0+(2243734721/5000000000 : ℝ)*X 2 1+(4230661667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (363813236762274767165847579/148150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (509137739/100000000000000 : ℝ)*(base19) + (52353187/12500000000000 : ℝ)*(base23) + (249003/2000000000000 : ℝ)*(lower2) + (23496701/50000000000000 : ℝ)*(upper3) + (636173/1250000000000 : ℝ)*(upper5) + (5830524639896727/100000000000000 : ℝ)*(major0) + (5830524639896727/100000000000000 : ℝ)*(major1) + (5830524639896727/100000000000000 : ℝ)*(major2) + (7787163116259367/100000000000000 : ℝ)*(sp0) + (7787173685850931/100000000000000 : ℝ)*(sp1) + (7787173776163173/100000000000000 : ℝ)*(sp2) + (387386831475713/10000000000000 : ℝ)*(sp3) + (5539364651/50000000000000 : ℝ)*(sp4) + (6688190689/100000000000000 : ℝ)*(sp7) + (1936937501473909/50000000000000 : ℝ)*(f.failure) + (778717419498867/10000000000000 : ℝ)*(f.sum) + (2048690246287/592600000000000000000000000 : ℝ)*base65 + (4827770305361700807/592600000000000000000000000000000 : ℝ)*base68 + (2486895400346700807/592600000000000000000000000000000 : ℝ)*base70 + (3578802034490500807/592600000000000000000000000000000 : ℝ)*base72 + (5664962827181/2963000000000000000000000000 : ℝ)*base74 + (9948701318273300807/592600000000000000000000000000000 : ℝ)*base76 + (2228329405300699193/592600000000000000000000000000000 : ℝ)*base77 + (11960849718999100807/592600000000000000000000000000000 : ℝ)*base80 + (6262248625817/592600000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (272073/312500000000000000000 : ℝ)*base90 + (272073/312500000000000000000 : ℝ)*base92 + (272073/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1209488352268125650490120273/148150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2014364689/100000000000000 : ℝ)*(base19) + (52898043/3125000000000 : ℝ)*(base23) + (138699563/100000000000000 : ℝ)*(upper2) + (135035447/50000000000000 : ℝ)*(upper5) + (5860744599686949/100000000000000 : ℝ)*(major0) + (5860744599686949/100000000000000 : ℝ)*(major1) + (5860744599686949/100000000000000 : ℝ)*(major2) + (8429520573/100000000000000 : ℝ)*(sp0) + (3355281421/6250000000000 : ℝ)*(sp1) + (58364394317/100000000000000 : ℝ)*(sp2) + (1956881741925707/25000000000000 : ℝ)*(sp4) + (313099187934239/4000000000000 : ℝ)*(sp5) + (3913737670045853/50000000000000 : ℝ)*(sp6) + (973488382504753/25000000000000 : ℝ)*(sp7) + (973488382504753/25000000000000 : ℝ)*(f.failure) + (39137676986117/500000000000 : ℝ)*(f.sum) + (36781326729/1481500000000000000000000000 : ℝ)*base65 + (17129498236326809909/592600000000000000000000000000000 : ℝ)*base68 + (8498684071016809909/592600000000000000000000000000000 : ℝ)*base70 + (2865976500385609909/592600000000000000000000000000000 : ℝ)*base72 + (624925453247/370375000000000000000000000 : ℝ)*base74 + (3630259750399409909/592600000000000000000000000000000 : ℝ)*base76 + (653524817233409909/592600000000000000000000000000000 : ℝ)*base78 + (2593158309205790091/592600000000000000000000000000000 : ℝ)*base79 + (1495587706163/1481500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (222159/156250000000000000000 : ℝ)*base89 + (222159/156250000000000000000 : ℝ)*base91 + (222159/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1195_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1195_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1195_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (327/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9303/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1195_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1195_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1195_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (327/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9303/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1195_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

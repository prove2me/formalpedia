-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1250_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:23:08.748517+00:00
-- url     : https://prove2.me/submissions/af63dc70-8f77-4cfd-901c-7da7dc282441

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
theorem support_rectangle_w1250_s0_0 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1858094127/10000000000 : ℝ)*x 0 + (6029704047/10000000000 : ℝ)*x 1 + (4793977509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1858094127/10000000000 : ℝ)^8443 ≤ (10838932259867/100000000000000 : ℝ)^6395 := by
    have hnat : (1858094127 : ℕ)^8443*100000000000000^6395 ≤ 10838932259867^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1858094127 10000000000 10838932259867 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6029704047/10000000000 : ℝ)^8443 ≤ (640981889957/1250000000000 : ℝ)^6395 := by
    have hnat : (6029704047 : ℕ)^8443*1250000000000^6395 ≤ 640981889957^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6029704047 10000000000 640981889957 1250000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4793977509/10000000000 : ℝ)^8443 ≤ (189412582601/500000000000 : ℝ)^6395 := by
    have hnat : (4793977509 : ℕ)^8443*500000000000^6395 ≤ 189412582601^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4793977509 10000000000 189412582601 500000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1858094127/10000000000 : ℝ), (6029704047/10000000000 : ℝ), (4793977509/10000000000 : ℝ)] ![(10838932259867/100000000000000 : ℝ), (640981889957/1250000000000 : ℝ), (189412582601/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1858094127/10000000000 : ℝ)|^8443 ≤ (10838932259867/100000000000000 : ℝ)^6395
        have hw : |(-1858094127/10000000000 : ℝ)|=(1858094127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6029704047/10000000000 : ℝ)|^8443 ≤ (640981889957/1250000000000 : ℝ)^6395
        have hw : |(6029704047/10000000000 : ℝ)|=(6029704047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4793977509/10000000000 : ℝ)|^8443 ≤ (189412582601/500000000000 : ℝ)^6395
        have hw : |(4793977509/10000000000 : ℝ)|=(4793977509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s0_1 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1377677203/2500000000 : ℝ)*x 0 + (-1282157133/5000000000 : ℝ)*x 1 + (4793977449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1377677203/2500000000 : ℝ)^8443 ≤ (9106659500907/20000000000000 : ℝ)^6395 := by
    have hnat : (1377677203 : ℕ)^8443*20000000000000^6395 ≤ 9106659500907^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377677203 2500000000 9106659500907 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1282157133/5000000000 : ℝ)^8443 ≤ (16584186585113/100000000000000 : ℝ)^6395 := by
    have hnat : (1282157133 : ℕ)^8443*100000000000000^6395 ≤ 16584186585113^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282157133 5000000000 16584186585113 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4793977449/10000000000 : ℝ)^8443 ≤ (18941257947117/50000000000000 : ℝ)^6395 := by
    have hnat : (4793977449 : ℕ)^8443*50000000000000^6395 ≤ 18941257947117^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4793977449 10000000000 18941257947117 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1377677203/2500000000 : ℝ), (-1282157133/5000000000 : ℝ), (4793977449/10000000000 : ℝ)] ![(9106659500907/20000000000000 : ℝ), (16584186585113/100000000000000 : ℝ), (18941257947117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1377677203/2500000000 : ℝ)|^8443 ≤ (9106659500907/20000000000000 : ℝ)^6395
        have hw : |(1377677203/2500000000 : ℝ)|=(1377677203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1282157133/5000000000 : ℝ)|^8443 ≤ (16584186585113/100000000000000 : ℝ)^6395
        have hw : |(-1282157133/5000000000 : ℝ)|=(1282157133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4793977449/10000000000 : ℝ)|^8443 ≤ (18941257947117/50000000000000 : ℝ)^6395
        have hw : |(4793977449/10000000000 : ℝ)|=(4793977449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s0_2 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5510708729/10000000000 : ℝ)*x 0 + (2396988771/5000000000 : ℝ)*x 1 + (-2564314259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5510708729/10000000000 : ℝ)^8443 ≤ (45533296599103/100000000000000 : ℝ)^6395 := by
    have hnat : (5510708729 : ℕ)^8443*100000000000000^6395 ≤ 45533296599103^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510708729 10000000000 45533296599103 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2396988771/5000000000 : ℝ)^8443 ≤ (236765730403/625000000000 : ℝ)^6395 := by
    have hnat : (2396988771 : ℕ)^8443*625000000000^6395 ≤ 236765730403^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2396988771 5000000000 236765730403 625000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2564314259/10000000000 : ℝ)^8443 ≤ (518255828917/3125000000000 : ℝ)^6395 := by
    have hnat : (2564314259 : ℕ)^8443*3125000000000^6395 ≤ 518255828917^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564314259 10000000000 518255828917 3125000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5510708729/10000000000 : ℝ), (2396988771/5000000000 : ℝ), (-2564314259/10000000000 : ℝ)] ![(45533296599103/100000000000000 : ℝ), (236765730403/625000000000 : ℝ), (518255828917/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5510708729/10000000000 : ℝ)|^8443 ≤ (45533296599103/100000000000000 : ℝ)^6395
        have hw : |(5510708729/10000000000 : ℝ)|=(5510708729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2396988771/5000000000 : ℝ)|^8443 ≤ (236765730403/625000000000 : ℝ)^6395
        have hw : |(2396988771/5000000000 : ℝ)|=(2396988771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2564314259/10000000000 : ℝ)|^8443 ≤ (518255828917/3125000000000 : ℝ)^6395
        have hw : |(-2564314259/10000000000 : ℝ)|=(2564314259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s0_3 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4192393917/10000000000 : ℝ)*x 0 + (779148363/2500000000 : ℝ)*x 1 + (1406806139/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4192393917/10000000000 : ℝ)^8443 ≤ (317362413467/1000000000000 : ℝ)^6395 := by
    have hnat : (4192393917 : ℕ)^8443*1000000000000^6395 ≤ 317362413467^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4192393917 10000000000 317362413467 1000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (779148363/2500000000 : ℝ)^8443 ≤ (21455128708157/100000000000000 : ℝ)^6395 := by
    have hnat : (779148363 : ℕ)^8443*100000000000000^6395 ≤ 21455128708157^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779148363 2500000000 21455128708157 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1406806139/2500000000 : ℝ)^8443 ≤ (11702157481893/25000000000000 : ℝ)^6395 := by
    have hnat : (1406806139 : ℕ)^8443*25000000000000^6395 ≤ 11702157481893^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1406806139 2500000000 11702157481893 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4192393917/10000000000 : ℝ), (779148363/2500000000 : ℝ), (1406806139/2500000000 : ℝ)] ![(317362413467/1000000000000 : ℝ), (21455128708157/100000000000000 : ℝ), (11702157481893/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4192393917/10000000000 : ℝ)|^8443 ≤ (317362413467/1000000000000 : ℝ)^6395
        have hw : |(4192393917/10000000000 : ℝ)|=(4192393917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(779148363/2500000000 : ℝ)|^8443 ≤ (21455128708157/100000000000000 : ℝ)^6395
        have hw : |(779148363/2500000000 : ℝ)|=(779148363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1406806139/2500000000 : ℝ)|^8443 ≤ (11702157481893/25000000000000 : ℝ)^6395
        have hw : |(1406806139/2500000000 : ℝ)|=(1406806139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s0_4 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-931464467/5000000000 : ℝ)*x 0 + (2412897449/5000000000 : ℝ)*x 1 + (5996761807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (931464467/5000000000 : ℝ)^8443 ≤ (5438091503103/50000000000000 : ℝ)^6395 := by
    have hnat : (931464467 : ℕ)^8443*50000000000000^6395 ≤ 5438091503103^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931464467 5000000000 5438091503103 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2412897449/5000000000 : ℝ)^8443 ≤ (38214811831827/100000000000000 : ℝ)^6395 := by
    have hnat : (2412897449 : ℕ)^8443*100000000000000^6395 ≤ 38214811831827^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2412897449 5000000000 38214811831827 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5996761807/10000000000 : ℝ)^8443 ≤ (50909005157603/100000000000000 : ℝ)^6395 := by
    have hnat : (5996761807 : ℕ)^8443*100000000000000^6395 ≤ 50909005157603^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5996761807 10000000000 50909005157603 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-931464467/5000000000 : ℝ), (2412897449/5000000000 : ℝ), (5996761807/10000000000 : ℝ)] ![(5438091503103/50000000000000 : ℝ), (38214811831827/100000000000000 : ℝ), (50909005157603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-931464467/5000000000 : ℝ)|^8443 ≤ (5438091503103/50000000000000 : ℝ)^6395
        have hw : |(-931464467/5000000000 : ℝ)|=(931464467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2412897449/5000000000 : ℝ)|^8443 ≤ (38214811831827/100000000000000 : ℝ)^6395
        have hw : |(2412897449/5000000000 : ℝ)|=(2412897449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5996761807/10000000000 : ℝ)|^8443 ≤ (50909005157603/100000000000000 : ℝ)^6395
        have hw : |(5996761807/10000000000 : ℝ)|=(5996761807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s0_5 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2587225747/5000000000 : ℝ)*x 0 + (-1361527693/10000000000 : ℝ)*x 1 + (119935283/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587225747/5000000000 : ℝ)^8443 ≤ (10475368790133/25000000000000 : ℝ)^6395 := by
    have hnat : (2587225747 : ℕ)^8443*25000000000000^6395 ≤ 10475368790133^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587225747 5000000000 10475368790133 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1361527693/10000000000 : ℝ)^8443 ≤ (7189493408059/100000000000000 : ℝ)^6395 := by
    have hnat : (1361527693 : ℕ)^8443*100000000000000^6395 ≤ 7189493408059^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361527693 10000000000 7189493408059 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119935283/200000000 : ℝ)^8443 ≤ (50909031418307/100000000000000 : ℝ)^6395 := by
    have hnat : (119935283 : ℕ)^8443*100000000000000^6395 ≤ 50909031418307^6395*200000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119935283 200000000 50909031418307 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587225747/5000000000 : ℝ), (-1361527693/10000000000 : ℝ), (119935283/200000000 : ℝ)] ![(10475368790133/25000000000000 : ℝ), (7189493408059/100000000000000 : ℝ), (50909031418307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587225747/5000000000 : ℝ)|^8443 ≤ (10475368790133/25000000000000 : ℝ)^6395
        have hw : |(2587225747/5000000000 : ℝ)|=(2587225747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1361527693/10000000000 : ℝ)|^8443 ≤ (7189493408059/100000000000000 : ℝ)^6395
        have hw : |(-1361527693/10000000000 : ℝ)|=(1361527693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(119935283/200000000 : ℝ)|^8443 ≤ (50909031418307/100000000000000 : ℝ)^6395
        have hw : |(119935283/200000000 : ℝ)|=(119935283/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s0_6 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2587226233/5000000000 : ℝ)*x 0 + (5996762241/10000000000 : ℝ)*x 1 + (-170191159/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587226233/5000000000 : ℝ)^8443 ≤ (41901485552253/100000000000000 : ℝ)^6395 := by
    have hnat : (2587226233 : ℕ)^8443*100000000000000^6395 ≤ 41901485552253^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587226233 5000000000 41901485552253 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5996762241/10000000000 : ℝ)^8443 ≤ (50909010021941/100000000000000 : ℝ)^6395 := by
    have hnat : (5996762241 : ℕ)^8443*100000000000000^6395 ≤ 50909010021941^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5996762241 10000000000 50909010021941 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170191159/1250000000 : ℝ)^8443 ≤ (3594752208053/50000000000000 : ℝ)^6395 := by
    have hnat : (170191159 : ℕ)^8443*50000000000000^6395 ≤ 3594752208053^6395*1250000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170191159 1250000000 3594752208053 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587226233/5000000000 : ℝ), (5996762241/10000000000 : ℝ), (-170191159/1250000000 : ℝ)] ![(41901485552253/100000000000000 : ℝ), (50909010021941/100000000000000 : ℝ), (3594752208053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587226233/5000000000 : ℝ)|^8443 ≤ (41901485552253/100000000000000 : ℝ)^6395
        have hw : |(2587226233/5000000000 : ℝ)|=(2587226233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5996762241/10000000000 : ℝ)|^8443 ≤ (50909010021941/100000000000000 : ℝ)^6395
        have hw : |(5996762241/10000000000 : ℝ)|=(5996762241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-170191159/1250000000 : ℝ)|^8443 ≤ (3594752208053/50000000000000 : ℝ)^6395
        have hw : |(-170191159/1250000000 : ℝ)|=(170191159/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s0_7 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2101109207/5000000000 : ℝ)*x 0 + (5562586489/10000000000 : ℝ)*x 1 + (397939551/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101109207/5000000000 : ℝ)^8443 ≤ (31834466523677/100000000000000 : ℝ)^6395 := by
    have hnat : (2101109207 : ℕ)^8443*100000000000000^6395 ≤ 31834466523677^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101109207 5000000000 31834466523677 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5562586489/10000000000 : ℝ)^8443 ≤ (9220014630087/20000000000000 : ℝ)^6395 := by
    have hnat : (5562586489 : ℕ)^8443*20000000000000^6395 ≤ 9220014630087^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5562586489 10000000000 9220014630087 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (397939551/1250000000 : ℝ)^8443 ≤ (22065460313687/100000000000000 : ℝ)^6395 := by
    have hnat : (397939551 : ℕ)^8443*100000000000000^6395 ≤ 22065460313687^6395*1250000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397939551 1250000000 22065460313687 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2101109207/5000000000 : ℝ), (5562586489/10000000000 : ℝ), (397939551/1250000000 : ℝ)] ![(31834466523677/100000000000000 : ℝ), (9220014630087/20000000000000 : ℝ), (22065460313687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2101109207/5000000000 : ℝ)|^8443 ≤ (31834466523677/100000000000000 : ℝ)^6395
        have hw : |(2101109207/5000000000 : ℝ)|=(2101109207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5562586489/10000000000 : ℝ)|^8443 ≤ (9220014630087/20000000000000 : ℝ)^6395
        have hw : |(5562586489/10000000000 : ℝ)|=(5562586489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(397939551/1250000000 : ℝ)|^8443 ≤ (22065460313687/100000000000000 : ℝ)^6395
        have hw : |(397939551/1250000000 : ℝ)|=(397939551/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1250_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (17/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13703/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4221/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4221 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4221*1^1024 ≤ 0^1024*1^4221 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4221 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4221/1024 : ℝ) ≤ (1144546148933276171/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4221 ≤ (1144546148933276171/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4221*50000000000000000000^1024 ≤ 1144546148933276171^1024*5^4221 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1144546148933276171 50000000000000000000 4221 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1144546148933276171/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4221 := by
      have hnat : (1 : ℕ)^1024*1^4221 ≤ 1^4221*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (51144546148933276171/50000000000000000000 : ℝ) ≤ (39277568515371/39062500000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (51144546148933276171/50000000000000000000 : ℝ)^1024 ≤ (39277568515371/39062500000000 : ℝ)^4221 := by
      have hnat : (51144546148933276171 : ℕ)^1024*39062500000000^4221 ≤ 39277568515371^4221*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51144546148933276171 50000000000000000000 39277568515371 39062500000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39277568515371/39062500000000 : ℝ)) (X := (51144546148933276171/50000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (26144546148933276171/25000000000000000000 : ℝ) ≤ (19746318515371/19531250000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (26144546148933276171/25000000000000000000 : ℝ)^1024 ≤ (19746318515371/19531250000000 : ℝ)^4221 := by
      have hnat : (26144546148933276171 : ℕ)^1024*19531250000000^4221 ≤ 19746318515371^4221*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26144546148933276171 25000000000000000000 19746318515371 19531250000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (19746318515371/19531250000000 : ℝ)) (X := (26144546148933276171/25000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(215068515371/15625000000000 : ℝ)*(0 : ℝ))^(4221/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(215068515371/15625000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1144546148933276171/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(215068515371/15625000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4221/1024 : ℝ) := by
    rw [show (1 : ℝ)+(215068515371/15625000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(39277568515371/39062500000000 : ℝ) by norm_num, show 1+(1144546148933276171/50000000000000000000 : ℝ)+(0 : ℝ)=(51144546148933276171/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1144546148933276171/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(215068515371/15625000000000 : ℝ)*(2/5 : ℝ))^(4221/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(215068515371/15625000000000 : ℝ)*(2/5 : ℝ)=(19746318515371/19531250000000 : ℝ) by norm_num, show 1+2*(1144546148933276171/50000000000000000000 : ℝ)=(26144546148933276171/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(215068515371/15625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (215068515371/15625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(215068515371/15625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (215068515371/15625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(215068515371/15625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (215068515371/15625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1858094127/10000000000 : ℝ)*X 0 0+(6029704047/10000000000 : ℝ)*X 0 1+(4793977509/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1377677203/2500000000 : ℝ)*X 1 0+(-1282157133/5000000000 : ℝ)*X 1 1+(4793977449/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5510708729/10000000000 : ℝ)*X 2 0+(2396988771/5000000000 : ℝ)*X 2 1+(-2564314259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4192393917/10000000000 : ℝ)*X 0 0+(779148363/2500000000 : ℝ)*X 0 1+(1406806139/2500000000 : ℝ)*X 0 2+(4192393917/10000000000 : ℝ)*X 1 0+(779148363/2500000000 : ℝ)*X 1 1+(1406806139/2500000000 : ℝ)*X 1 2+(4192393917/10000000000 : ℝ)*X 2 0+(779148363/2500000000 : ℝ)*X 2 1+(1406806139/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-931464467/5000000000 : ℝ)*X 0 0+(2412897449/5000000000 : ℝ)*X 0 1+(5996761807/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2587225747/5000000000 : ℝ)*X 1 0+(-1361527693/10000000000 : ℝ)*X 1 1+(119935283/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2587226233/5000000000 : ℝ)*X 2 0+(5996762241/10000000000 : ℝ)*X 2 1+(-170191159/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2101109207/5000000000 : ℝ)*X 0 0+(5562586489/10000000000 : ℝ)*X 0 1+(397939551/1250000000 : ℝ)*X 0 2+(2101109207/5000000000 : ℝ)*X 1 0+(5562586489/10000000000 : ℝ)*X 1 1+(397939551/1250000000 : ℝ)*X 1 2+(2101109207/5000000000 : ℝ)*X 2 0+(5562586489/10000000000 : ℝ)*X 2 1+(397939551/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2412120485765645519283/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1018361/2000000000000 : ℝ)*(base1) + (14780933/1562500000000 : ℝ)*(base19) + (871821531/100000000000000 : ℝ)*(base23) + (7746209/12500000000000 : ℝ)*(base24) + (2610787/1250000000000 : ℝ)*(upper3) + (150944348617549/25000000000000 : ℝ)*(major0) + (150944348617549/25000000000000 : ℝ)*(major1) + (150944348617549/25000000000000 : ℝ)*(major2) + (809243733311077/100000000000000 : ℝ)*(sp0) + (809244851096201/100000000000000 : ℝ)*(sp1) + (80924486328471/10000000000000 : ℝ)*(sp2) + (12447099662333/3125000000000 : ℝ)*(sp3) + (422936577/20000000000000 : ℝ)*(sp4) + (81155267/5000000000000 : ℝ)*(sp7) + (398308863218047/100000000000000 : ℝ)*(f.failure) + (101155724634489/12500000000000 : ℝ)*(f.sum) + (1420937833989/3125000000000000000000000000 : ℝ)*base65 + (15206113762307/3125000000000000000000000000 : ℝ)*base67 + (9845091938233/781250000000000000000000000 : ℝ)*base69 + (1696084375733/781250000000000000000000000 : ℝ)*base71 + (3563841787307/1562500000000000000000000000 : ℝ)*base73 + (6245978687693/3125000000000000000000000000 : ℝ)*base76 + (2925277535841/1562500000000000000000000000 : ℝ)*base77 + (699891770679/390625000000000000000000000 : ℝ)*base79 + (19357792943557/1562500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4991669/10000000000000000000000 : ℝ)*base89 + (4991669/10000000000000000000000 : ℝ)*base91 + (4991669/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1980308600384355742461/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (153514121/100000000000000 : ℝ)*(base1) + (725156149/100000000000000 : ℝ)*(base19) + (849981179/100000000000000 : ℝ)*(base23) + (41310737/25000000000000 : ℝ)*(upper3) + (637163908975243/100000000000000 : ℝ)*(major0) + (637163908975243/100000000000000 : ℝ)*(major1) + (637163908975243/100000000000000 : ℝ)*(major2) + (1937884573/100000000000000 : ℝ)*(sp1) + (1390152997/100000000000000 : ℝ)*(sp2) + (411742021/100000000000000 : ℝ)*(sp3) + (34159763581577/4000000000000 : ℝ)*(sp4) + (426995636492291/50000000000000 : ℝ)*(sp5) + (853991695891129/100000000000000 : ℝ)*(sp6) + (420333211052577/100000000000000 : ℝ)*(sp7) + (420333776308719/100000000000000 : ℝ)*(f.failure) + (106749242003163/12500000000000 : ℝ)*(f.sum) + (2395909737513/3125000000000000000000000000 : ℝ)*base66 + (7966780501569/3125000000000000000000000000 : ℝ)*base68 + (14259467289069/3125000000000000000000000000 : ℝ)*base70 + (6899685576569/3125000000000000000000000000 : ℝ)*base72 + (56580725013/3125000000000000000000000000 : ℝ)*base74 + (2907443329681/3125000000000000000000000000 : ℝ)*base75 + (5237548068361/781250000000000000000000000 : ℝ)*base78 + (7829014958597/1562500000000000000000000000 : ℝ)*base80 + (3777542850013/3125000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (91694213/10000000000000000000000 : ℝ)*base89 + (91694213/10000000000000000000000 : ℝ)*base91 + (91694213/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1250_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (17/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13703/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1250_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1250_s1_0 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2054924853/10000000000 : ℝ)*x 0 + (354599797/625000000 : ℝ)*x 1 + (5024090757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2054924853/10000000000 : ℝ)^8443 ≤ (6189972448593/50000000000000 : ℝ)^6395 := by
    have hnat : (2054924853 : ℕ)^8443*50000000000000^6395 ≤ 6189972448593^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054924853 10000000000 6189972448593 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (354599797/625000000 : ℝ)^8443 ≤ (23659283868133/50000000000000 : ℝ)^6395 := by
    have hnat : (354599797 : ℕ)^8443*50000000000000^6395 ≤ 23659283868133^6395*625000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354599797 625000000 23659283868133 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5024090757/10000000000 : ℝ)^8443 ≤ (10075371837437/25000000000000 : ℝ)^6395 := by
    have hnat : (5024090757 : ℕ)^8443*25000000000000^6395 ≤ 10075371837437^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5024090757 10000000000 10075371837437 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2054924853/10000000000 : ℝ), (354599797/625000000 : ℝ), (5024090757/10000000000 : ℝ)] ![(6189972448593/50000000000000 : ℝ), (23659283868133/50000000000000 : ℝ), (10075371837437/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2054924853/10000000000 : ℝ)|^8443 ≤ (6189972448593/50000000000000 : ℝ)^6395
        have hw : |(-2054924853/10000000000 : ℝ)|=(2054924853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(354599797/625000000 : ℝ)|^8443 ≤ (23659283868133/50000000000000 : ℝ)^6395
        have hw : |(354599797/625000000 : ℝ)|=(354599797/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5024090757/10000000000 : ℝ)|^8443 ≤ (10075371837437/25000000000000 : ℝ)^6395
        have hw : |(5024090757/10000000000 : ℝ)|=(5024090757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s1_1 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2706611401/5000000000 : ℝ)*x 0 + (-2403569097/10000000000 : ℝ)*x 1 + (2512045327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706611401/5000000000 : ℝ)^8443 ≤ (1389777015353/3125000000000 : ℝ)^6395 := by
    have hnat : (2706611401 : ℕ)^8443*3125000000000^6395 ≤ 1389777015353^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706611401 5000000000 1389777015353 3125000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2403569097/10000000000 : ℝ)^8443 ≤ (1522564923651/10000000000000 : ℝ)^6395 := by
    have hnat : (2403569097 : ℕ)^8443*10000000000000^6395 ≤ 1522564923651^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2403569097 10000000000 1522564923651 10000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2512045327/5000000000 : ℝ)^8443 ≤ (20150743129459/50000000000000 : ℝ)^6395 := by
    have hnat : (2512045327 : ℕ)^8443*50000000000000^6395 ≤ 20150743129459^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512045327 5000000000 20150743129459 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706611401/5000000000 : ℝ), (-2403569097/10000000000 : ℝ), (2512045327/5000000000 : ℝ)] ![(1389777015353/3125000000000 : ℝ), (1522564923651/10000000000000 : ℝ), (20150743129459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706611401/5000000000 : ℝ)|^8443 ≤ (1389777015353/3125000000000 : ℝ)^6395
        have hw : |(2706611401/5000000000 : ℝ)|=(2706611401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2403569097/10000000000 : ℝ)|^8443 ≤ (1522564923651/10000000000000 : ℝ)^6395
        have hw : |(-2403569097/10000000000 : ℝ)|=(2403569097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2512045327/5000000000 : ℝ)|^8443 ≤ (20150743129459/50000000000000 : ℝ)^6395
        have hw : |(2512045327/5000000000 : ℝ)|=(2512045327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s1_2 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1082644539/2000000000 : ℝ)*x 0 + (2512045377/5000000000 : ℝ)*x 1 + (-240356911/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082644539/2000000000 : ℝ)^8443 ≤ (8894572666141/20000000000000 : ℝ)^6395 := by
    have hnat : (1082644539 : ℕ)^8443*20000000000000^6395 ≤ 8894572666141^6395*2000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082644539 2000000000 8894572666141 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2512045377/5000000000 : ℝ)^8443 ≤ (5037685914747/12500000000000 : ℝ)^6395 := by
    have hnat : (2512045377 : ℕ)^8443*12500000000000^6395 ≤ 5037685914747^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512045377 5000000000 5037685914747 12500000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240356911/1000000000 : ℝ)^8443 ≤ (951603084077/6250000000000 : ℝ)^6395 := by
    have hnat : (240356911 : ℕ)^8443*6250000000000^6395 ≤ 951603084077^6395*1000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240356911 1000000000 951603084077 6250000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082644539/2000000000 : ℝ), (2512045377/5000000000 : ℝ), (-240356911/1000000000 : ℝ)] ![(8894572666141/20000000000000 : ℝ), (5037685914747/12500000000000 : ℝ), (951603084077/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082644539/2000000000 : ℝ)|^8443 ≤ (8894572666141/20000000000000 : ℝ)^6395
        have hw : |(1082644539/2000000000 : ℝ)|=(1082644539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2512045377/5000000000 : ℝ)|^8443 ≤ (5037685914747/12500000000000 : ℝ)^6395
        have hw : |(2512045377/5000000000 : ℝ)|=(2512045377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-240356911/1000000000 : ℝ)|^8443 ≤ (951603084077/6250000000000 : ℝ)^6395
        have hw : |(-240356911/1000000000 : ℝ)|=(240356911/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s1_3 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4308161503/10000000000 : ℝ)*x 0 + (1848449637/5000000000 : ℝ)*x 1 + (501650357/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308161503/10000000000 : ℝ)^8443 ≤ (32898334293677/100000000000000 : ℝ)^6395 := by
    have hnat : (4308161503 : ℕ)^8443*100000000000000^6395 ≤ 32898334293677^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308161503 10000000000 32898334293677 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1848449637/5000000000 : ℝ)^8443 ≤ (26880511628569/100000000000000 : ℝ)^6395 := by
    have hnat : (1848449637 : ℕ)^8443*100000000000000^6395 ≤ 26880511628569^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1848449637 5000000000 26880511628569 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501650357/1000000000 : ℝ)^8443 ≤ (8044230811733/20000000000000 : ℝ)^6395 := by
    have hnat : (501650357 : ℕ)^8443*20000000000000^6395 ≤ 8044230811733^6395*1000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501650357 1000000000 8044230811733 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308161503/10000000000 : ℝ), (1848449637/5000000000 : ℝ), (501650357/1000000000 : ℝ)] ![(32898334293677/100000000000000 : ℝ), (26880511628569/100000000000000 : ℝ), (8044230811733/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308161503/10000000000 : ℝ)|^8443 ≤ (32898334293677/100000000000000 : ℝ)^6395
        have hw : |(4308161503/10000000000 : ℝ)|=(4308161503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1848449637/5000000000 : ℝ)|^8443 ≤ (26880511628569/100000000000000 : ℝ)^6395
        have hw : |(1848449637/5000000000 : ℝ)|=(1848449637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(501650357/1000000000 : ℝ)|^8443 ≤ (8044230811733/20000000000000 : ℝ)^6395
        have hw : |(501650357/1000000000 : ℝ)|=(501650357/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s1_4 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1027795877/5000000000 : ℝ)*x 0 + (5032595683/10000000000 : ℝ)*x 1 + (5664930507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1027795877/5000000000 : ℝ)^8443 ≤ (2477049924603/20000000000000 : ℝ)^6395 := by
    have hnat : (1027795877 : ℕ)^8443*20000000000000^6395 ≤ 2477049924603^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027795877 5000000000 2477049924603 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5032595683/10000000000 : ℝ)^8443 ≤ (20195791937167/50000000000000 : ℝ)^6395 := by
    have hnat : (5032595683 : ℕ)^8443*50000000000000^6395 ≤ 20195791937167^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5032595683 10000000000 20195791937167 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5664930507/10000000000 : ℝ)^8443 ≤ (9444633297641/20000000000000 : ℝ)^6395 := by
    have hnat : (5664930507 : ℕ)^8443*20000000000000^6395 ≤ 9444633297641^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5664930507 10000000000 9444633297641 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1027795877/5000000000 : ℝ), (5032595683/10000000000 : ℝ), (5664930507/10000000000 : ℝ)] ![(2477049924603/20000000000000 : ℝ), (20195791937167/50000000000000 : ℝ), (9444633297641/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1027795877/5000000000 : ℝ)|^8443 ≤ (2477049924603/20000000000000 : ℝ)^6395
        have hw : |(-1027795877/5000000000 : ℝ)|=(1027795877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5032595683/10000000000 : ℝ)|^8443 ≤ (20195791937167/50000000000000 : ℝ)^6395
        have hw : |(5032595683/10000000000 : ℝ)|=(5032595683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5664930507/10000000000 : ℝ)|^8443 ≤ (9444633297641/20000000000000 : ℝ)^6395
        have hw : |(5664930507/10000000000 : ℝ)|=(5664930507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s1_5 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5245827667/10000000000 : ℝ)*x 0 + (-1762729199/10000000000 : ℝ)*x 1 + (5664930771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5245827667/10000000000 : ℝ)^8443 ≤ (8533248633429/20000000000000 : ℝ)^6395 := by
    have hnat : (5245827667 : ℕ)^8443*20000000000000^6395 ≤ 8533248633429^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245827667 10000000000 8533248633429 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1762729199/10000000000 : ℝ)^8443 ≤ (10110587431017/100000000000000 : ℝ)^6395 := by
    have hnat : (1762729199 : ℕ)^8443*100000000000000^6395 ≤ 10110587431017^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1762729199 10000000000 10110587431017 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5664930771/10000000000 : ℝ)^8443 ≤ (5902896174213/12500000000000 : ℝ)^6395 := by
    have hnat : (5664930771 : ℕ)^8443*12500000000000^6395 ≤ 5902896174213^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5664930771 10000000000 5902896174213 12500000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5245827667/10000000000 : ℝ), (-1762729199/10000000000 : ℝ), (5664930771/10000000000 : ℝ)] ![(8533248633429/20000000000000 : ℝ), (10110587431017/100000000000000 : ℝ), (5902896174213/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5245827667/10000000000 : ℝ)|^8443 ≤ (8533248633429/20000000000000 : ℝ)^6395
        have hw : |(5245827667/10000000000 : ℝ)|=(5245827667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1762729199/10000000000 : ℝ)|^8443 ≤ (10110587431017/100000000000000 : ℝ)^6395
        have hw : |(-1762729199/10000000000 : ℝ)|=(1762729199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5664930771/10000000000 : ℝ)|^8443 ≤ (5902896174213/12500000000000 : ℝ)^6395
        have hw : |(5664930771/10000000000 : ℝ)|=(5664930771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s1_6 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5245827593/10000000000 : ℝ)*x 0 + (566493057/1000000000 : ℝ)*x 1 + (-352545919/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5245827593/10000000000 : ℝ)^8443 ≤ (2666640148283/6250000000000 : ℝ)^6395 := by
    have hnat : (5245827593 : ℕ)^8443*6250000000000^6395 ≤ 2666640148283^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245827593 10000000000 2666640148283 6250000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566493057/1000000000 : ℝ)^8443 ≤ (23611583590781/50000000000000 : ℝ)^6395 := by
    have hnat : (566493057 : ℕ)^8443*50000000000000^6395 ≤ 23611583590781^6395*1000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566493057 1000000000 23611583590781 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (352545919/2000000000 : ℝ)^8443 ≤ (505529521489/5000000000000 : ℝ)^6395 := by
    have hnat : (352545919 : ℕ)^8443*5000000000000^6395 ≤ 505529521489^6395*2000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352545919 2000000000 505529521489 5000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5245827593/10000000000 : ℝ), (566493057/1000000000 : ℝ), (-352545919/2000000000 : ℝ)] ![(2666640148283/6250000000000 : ℝ), (23611583590781/50000000000000 : ℝ), (505529521489/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5245827593/10000000000 : ℝ)|^8443 ≤ (2666640148283/6250000000000 : ℝ)^6395
        have hw : |(5245827593/10000000000 : ℝ)|=(5245827593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(566493057/1000000000 : ℝ)|^8443 ≤ (23611583590781/50000000000000 : ℝ)^6395
        have hw : |(566493057/1000000000 : ℝ)|=(566493057/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-352545919/2000000000 : ℝ)|^8443 ≤ (505529521489/5000000000000 : ℝ)^6395
        have hw : |(-352545919/2000000000 : ℝ)|=(352545919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s1_7 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (538689529/1250000000 : ℝ)*x 0 + (312451511/625000000 : ℝ)*x 1 + (46431329/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538689529/1250000000 : ℝ)^8443 ≤ (3291199309121/10000000000000 : ℝ)^6395 := by
    have hnat : (538689529 : ℕ)^8443*10000000000000^6395 ≤ 3291199309121^6395*1250000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538689529 1250000000 3291199309121 10000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (312451511/625000000 : ℝ)^8443 ≤ (10009586181823/25000000000000 : ℝ)^6395 := by
    have hnat : (312451511 : ℕ)^8443*25000000000000^6395 ≤ 10009586181823^6395*625000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312451511 625000000 10009586181823 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46431329/125000000 : ℝ)^8443 ≤ (108198648647/400000000000 : ℝ)^6395 := by
    have hnat : (46431329 : ℕ)^8443*400000000000^6395 ≤ 108198648647^6395*125000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46431329 125000000 108198648647 400000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538689529/1250000000 : ℝ), (312451511/625000000 : ℝ), (46431329/125000000 : ℝ)] ![(3291199309121/10000000000000 : ℝ), (10009586181823/25000000000000 : ℝ), (108198648647/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538689529/1250000000 : ℝ)|^8443 ≤ (3291199309121/10000000000000 : ℝ)^6395
        have hw : |(538689529/1250000000 : ℝ)|=(538689529/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(312451511/625000000 : ℝ)|^8443 ≤ (10009586181823/25000000000000 : ℝ)^6395
        have hw : |(312451511/625000000 : ℝ)|=(312451511/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(46431329/125000000 : ℝ)|^8443 ≤ (108198648647/400000000000 : ℝ)^6395
        have hw : |(46431329/125000000 : ℝ)|=(46431329/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1250_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13703/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (17/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (6233/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3993/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13703/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (17/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13703/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (17/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13703/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (17/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13703/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (17/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13703/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (17/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13703/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (17/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (17/2000 : ℝ) ^ (4221/1024 : ℝ) ≤ (291688444209/100000000000000000000 : ℝ) := by
    have hpowers : (17/2000 : ℝ)^4221 ≤ (291688444209/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17 : ℕ)^4221*100000000000000000000^1024 ≤ 291688444209^1024*2000^4221 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17 2000 291688444209 100000000000000000000 4221 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17/2000 : ℝ)) (X := (291688444209/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13703/50000 : ℝ) ^ (4221/1024 : ℝ) ≤ (602102277283321/125000000000000000 : ℝ) := by
    have hpowers : (13703/50000 : ℝ)^4221 ≤ (602102277283321/125000000000000000 : ℝ)^1024 := by
      have hnat : (13703 : ℕ)^4221*125000000000000000^1024 ≤ 602102277283321^1024*50000^4221 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13703 50000 602102277283321 125000000000000000 4221 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13703/50000 : ℝ)) (X := (602102277283321/125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000291688444209/50000000000000000000 : ℝ) ≤ (5000000007076261/5000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (50000000291688444209/50000000000000000000 : ℝ)^1024 ≤ (5000000007076261/5000000000000000 : ℝ)^4221 := by
      have hnat : (50000000291688444209 : ℕ)^1024*5000000000000000^4221 ≤ 5000000007076261^4221*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000291688444209 50000000000000000000 5000000007076261 5000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000007076261/5000000000000000 : ℝ)) (X := (50000000291688444209/50000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100481682113515101009/100000000000000000000 : ℝ) ≤ (5005832092774703/5000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (100481682113515101009/100000000000000000000 : ℝ)^1024 ≤ (5005832092774703/5000000000000000 : ℝ)^4221 := by
      have hnat : (100481682113515101009 : ℕ)^1024*5000000000000000^4221 ≤ 5005832092774703^4221*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100481682113515101009 100000000000000000000 5005832092774703 5000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005832092774703/5000000000000000 : ℝ)) (X := (100481682113515101009/100000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (63102102277283321/62500000000000000 : ℝ) ≤ (1002332835694629/1000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (63102102277283321/62500000000000000 : ℝ)^1024 ≤ (1002332835694629/1000000000000000 : ℝ)^4221 := by
      have hnat : (63102102277283321 : ℕ)^1024*1000000000000000^4221 ≤ 1002332835694629^4221*62500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63102102277283321 62500000000000000 1002332835694629 1000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1002332835694629/1000000000000000 : ℝ)) (X := (63102102277283321/62500000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(291688444209/100000000000000000000 : ℝ) ≤ ((33192521410557458929/33195000000000000000 : ℝ)+2*(2916042849221/663900000000000 : ℝ)*(17/2000 : ℝ))^(4221/1024 : ℝ) := by
    rw [show (33192521410557458929/33195000000000000000 : ℝ)+2*(2916042849221/663900000000000 : ℝ)*(17/2000 : ℝ)=(5000000007076261/5000000000000000 : ℝ) by norm_num, show 1+2*(291688444209/100000000000000000000 : ℝ)=(50000000291688444209/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(602102277283321/125000000000000000 : ℝ)+(291688444209/100000000000000000000 : ℝ) ≤ ((33192521410557458929/33195000000000000000 : ℝ)+(2916042849221/663900000000000 : ℝ)*((13703/50000 : ℝ)+(17/2000 : ℝ)))^(4221/1024 : ℝ) := by
    rw [show (33192521410557458929/33195000000000000000 : ℝ)+(2916042849221/663900000000000 : ℝ)*((13703/50000 : ℝ)+(17/2000 : ℝ))=(5005832092774703/5000000000000000 : ℝ) by norm_num, show 1+(602102277283321/125000000000000000 : ℝ)+(291688444209/100000000000000000000 : ℝ)=(100481682113515101009/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(602102277283321/125000000000000000 : ℝ) ≤ ((33192521410557458929/33195000000000000000 : ℝ)+2*(2916042849221/663900000000000 : ℝ)*(13703/50000 : ℝ))^(4221/1024 : ℝ) := by
    rw [show (33192521410557458929/33195000000000000000 : ℝ)+2*(2916042849221/663900000000000 : ℝ)*(13703/50000 : ℝ)=(1002332835694629/1000000000000000 : ℝ) by norm_num, show 1+2*(602102277283321/125000000000000000 : ℝ)=(63102102277283321/62500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33192521410557458929/33195000000000000000 : ℝ)*(X 1 0+X 2 0)+(2916042849221/663900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (17/2000 : ℝ)) (hi := (13703/50000 : ℝ)) (c := (33192521410557458929/33195000000000000000 : ℝ)) (alpha := (2916042849221/663900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33192521410557458929/33195000000000000000 : ℝ)*(X 0 1+X 2 1)+(2916042849221/663900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (17/2000 : ℝ)) (hi := (13703/50000 : ℝ)) (c := (33192521410557458929/33195000000000000000 : ℝ)) (alpha := (2916042849221/663900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33192521410557458929/33195000000000000000 : ℝ)*(X 0 2+X 1 2)+(2916042849221/663900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (17/2000 : ℝ)) (hi := (13703/50000 : ℝ)) (c := (33192521410557458929/33195000000000000000 : ℝ)) (alpha := (2916042849221/663900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2054924853/10000000000 : ℝ)*X 0 0+(354599797/625000000 : ℝ)*X 0 1+(5024090757/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2706611401/5000000000 : ℝ)*X 1 0+(-2403569097/10000000000 : ℝ)*X 1 1+(2512045327/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1082644539/2000000000 : ℝ)*X 2 0+(2512045377/5000000000 : ℝ)*X 2 1+(-240356911/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4308161503/10000000000 : ℝ)*X 0 0+(1848449637/5000000000 : ℝ)*X 0 1+(501650357/1000000000 : ℝ)*X 0 2+(4308161503/10000000000 : ℝ)*X 1 0+(1848449637/5000000000 : ℝ)*X 1 1+(501650357/1000000000 : ℝ)*X 1 2+(4308161503/10000000000 : ℝ)*X 2 0+(1848449637/5000000000 : ℝ)*X 2 1+(501650357/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1027795877/5000000000 : ℝ)*X 0 0+(5032595683/10000000000 : ℝ)*X 0 1+(5664930507/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5245827667/10000000000 : ℝ)*X 1 0+(-1762729199/10000000000 : ℝ)*X 1 1+(5664930771/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5245827593/10000000000 : ℝ)*X 2 0+(566493057/1000000000 : ℝ)*X 2 1+(-352545919/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((538689529/1250000000 : ℝ)*X 0 0+(312451511/625000000 : ℝ)*X 0 1+(46431329/125000000 : ℝ)*X 0 2+(538689529/1250000000 : ℝ)*X 1 0+(312451511/625000000 : ℝ)*X 1 1+(46431329/125000000 : ℝ)*X 1 2+(538689529/1250000000 : ℝ)*X 2 0+(312451511/625000000 : ℝ)*X 2 1+(46431329/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (138212409392334810976214739/27662500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56791853/100000000000000 : ℝ)*(base1) + (1050427401/100000000000000 : ℝ)*(base19) + (509997101/50000000000000 : ℝ)*(base23) + (116052901/100000000000000 : ℝ)*(upper3) + (103568083/100000000000000 : ℝ)*(upper5) + (57436292792703/5000000000000 : ℝ)*(major0) + (57436292792703/5000000000000 : ℝ)*(major1) + (57436292792703/5000000000000 : ℝ)*(major2) + (1539637369623821/100000000000000 : ℝ)*(sp0) + (1539641914975061/100000000000000 : ℝ)*(sp1) + (76982097270413/5000000000000 : ℝ)*(sp2) + (151561135221731/20000000000000 : ℝ)*(sp3) + (2826285247/50000000000000 : ℝ)*(sp4) + (177928693/6250000000000 : ℝ)*(sp7) + (189452144939899/25000000000000 : ℝ)*(f.failure) + (769821482701231/50000000000000 : ℝ)*(f.sum) + (18959633967/34578125000000000000000000 : ℝ)*base65 + (98625087296115029/55325000000000000000000000000000 : ℝ)*base67 + (105325901199390029/55325000000000000000000000000000 : ℝ)*base69 + (333123914399540029/55325000000000000000000000000000 : ℝ)*base71 + (10292508072249/2213000000000000000000000000 : ℝ)*base74 + (75926365549215029/55325000000000000000000000000000 : ℝ)*base75 + (410251402681690029/55325000000000000000000000000000 : ℝ)*base77 + (11420646861165029/55325000000000000000000000000000 : ℝ)*base79 + (5037538053173/1106500000000000000000000000 : ℝ)*base82 + (8727927/2500000000000000000000 : ℝ)*base90 + (8727927/2500000000000000000000 : ℝ)*base92 + (8727927/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2095800257389046236925533811/276625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14530177/25000000000000 : ℝ)*(base1) + (743710401/50000000000000 : ℝ)*(base19) + (359605537/25000000000000 : ℝ)*(base23) + (190014779/100000000000000 : ℝ)*(upper3) + (1040471/625000000000 : ℝ)*(upper5) + (1179910799258059/100000000000000 : ℝ)*(major0) + (1179910799258059/100000000000000 : ℝ)*(major1) + (1179910799258059/100000000000000 : ℝ)*(major2) + (904315813/12500000000000 : ℝ)*(sp1) + (6398111469/100000000000000 : ℝ)*(sp2) + (79072013822643/5000000000000 : ℝ)*(sp4) + (1581431496384847/100000000000000 : ℝ)*(sp5) + (197679047724817/12500000000000 : ℝ)*(sp6) + (194595267379791/25000000000000 : ℝ)*(sp7) + (12162205119373/1562500000000 : ℝ)*(f.failure) + (1581440218332153/100000000000000 : ℝ)*(f.sum) + (9826603104479/33195000000000000000000000000 : ℝ)*base65 + (9302521633708708811/3319500000000000000000000000000000 : ℝ)*base67 + (7158229094083291189/3319500000000000000000000000000000 : ℝ)*base70 + (3529549884830791189/3319500000000000000000000000000000 : ℝ)*base72 + (106708079175277/16597500000000000000000000000 : ℝ)*base73 + (5593817235326791189/3319500000000000000000000000000000 : ℝ)*base76 + (24270073506227791189/3319500000000000000000000000000000 : ℝ)*base78 + (134484139528291189/3319500000000000000000000000000000 : ℝ)*base80 + (83792785522889/33195000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1115171/156250000000000000000 : ℝ)*base89 + (1115171/156250000000000000000 : ℝ)*base91 + (1115171/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1250_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13703/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (17/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6233/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3993/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1250_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1250_s2_0 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-13141043/62500000 : ℝ)*x 0 + (1372858369/2500000000 : ℝ)*x 1 + (5175863581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13141043/62500000 : ℝ)^8443 ≤ (2552056657957/20000000000000 : ℝ)^6395 := by
    have hnat : (13141043 : ℕ)^8443*20000000000000^6395 ≤ 2552056657957^6395*62500000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13141043 62500000 2552056657957 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372858369/2500000000 : ℝ)^8443 ≤ (22661572073213/50000000000000 : ℝ)^6395 := by
    have hnat : (1372858369 : ℕ)^8443*50000000000000^6395 ≤ 22661572073213^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372858369 2500000000 22661572073213 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5175863581/10000000000 : ℝ)^8443 ≤ (41916572543227/100000000000000 : ℝ)^6395 := by
    have hnat : (5175863581 : ℕ)^8443*100000000000000^6395 ≤ 41916572543227^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175863581 10000000000 41916572543227 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13141043/62500000 : ℝ), (1372858369/2500000000 : ℝ), (5175863581/10000000000 : ℝ)] ![(2552056657957/20000000000000 : ℝ), (22661572073213/50000000000000 : ℝ), (41916572543227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13141043/62500000 : ℝ)|^8443 ≤ (2552056657957/20000000000000 : ℝ)^6395
        have hw : |(-13141043/62500000 : ℝ)|=(13141043/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1372858369/2500000000 : ℝ)|^8443 ≤ (22661572073213/50000000000000 : ℝ)^6395
        have hw : |(1372858369/2500000000 : ℝ)|=(1372858369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5175863581/10000000000 : ℝ)|^8443 ≤ (41916572543227/100000000000000 : ℝ)^6395
        have hw : |(5175863581/10000000000 : ℝ)|=(5175863581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s2_1 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (536936247/1000000000 : ℝ)*x 0 + (-566496137/2500000000 : ℝ)*x 1 + (2587931831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536936247/1000000000 : ℝ)^8443 ≤ (43997745385297/100000000000000 : ℝ)^6395 := by
    have hnat : (536936247 : ℕ)^8443*100000000000000^6395 ≤ 43997745385297^6395*1000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536936247 1000000000 43997745385297 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566496137/2500000000 : ℝ)^8443 ≤ (7042840592207/50000000000000 : ℝ)^6395 := by
    have hnat : (566496137 : ℕ)^8443*50000000000000^6395 ≤ 7042840592207^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566496137 2500000000 7042840592207 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2587931831/5000000000 : ℝ)^8443 ≤ (41916573409279/100000000000000 : ℝ)^6395 := by
    have hnat : (2587931831 : ℕ)^8443*100000000000000^6395 ≤ 41916573409279^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587931831 5000000000 41916573409279 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536936247/1000000000 : ℝ), (-566496137/2500000000 : ℝ), (2587931831/5000000000 : ℝ)] ![(43997745385297/100000000000000 : ℝ), (7042840592207/50000000000000 : ℝ), (41916573409279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536936247/1000000000 : ℝ)|^8443 ≤ (43997745385297/100000000000000 : ℝ)^6395
        have hw : |(536936247/1000000000 : ℝ)|=(536936247/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-566496137/2500000000 : ℝ)|^8443 ≤ (7042840592207/50000000000000 : ℝ)^6395
        have hw : |(-566496137/2500000000 : ℝ)|=(566496137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2587931831/5000000000 : ℝ)|^8443 ≤ (41916573409279/100000000000000 : ℝ)^6395
        have hw : |(2587931831/5000000000 : ℝ)|=(2587931831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s2_2 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (335585147/625000000 : ℝ)*x 0 + (258793187/500000000 : ℝ)*x 1 + (-1132992301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335585147/625000000 : ℝ)^8443 ≤ (10999436027181/25000000000000 : ℝ)^6395 := by
    have hnat : (335585147 : ℕ)^8443*25000000000000^6395 ≤ 10999436027181^6395*625000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335585147 625000000 10999436027181 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258793187/500000000 : ℝ)^8443 ≤ (5239571780407/12500000000000 : ℝ)^6395 := by
    have hnat : (258793187 : ℕ)^8443*12500000000000^6395 ≤ 5239571780407^6395*500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258793187 500000000 5239571780407 12500000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132992301/5000000000 : ℝ)^8443 ≤ (2817136325517/20000000000000 : ℝ)^6395 := by
    have hnat : (1132992301 : ℕ)^8443*20000000000000^6395 ≤ 2817136325517^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132992301 5000000000 2817136325517 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335585147/625000000 : ℝ), (258793187/500000000 : ℝ), (-1132992301/5000000000 : ℝ)] ![(10999436027181/25000000000000 : ℝ), (5239571780407/12500000000000 : ℝ), (2817136325517/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335585147/625000000 : ℝ)|^8443 ≤ (10999436027181/25000000000000 : ℝ)^6395
        have hw : |(335585147/625000000 : ℝ)|=(335585147/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(258793187/500000000 : ℝ)|^8443 ≤ (5239571780407/12500000000000 : ℝ)^6395
        have hw : |(258793187/500000000 : ℝ)|=(258793187/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1132992301/5000000000 : ℝ)|^8443 ≤ (2817136325517/20000000000000 : ℝ)^6395
        have hw : |(-1132992301/5000000000 : ℝ)|=(1132992301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s2_3 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2170543451/5000000000 : ℝ)*x 0 + (2015979397/5000000000 : ℝ)*x 1 + (4673103317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170543451/5000000000 : ℝ)^8443 ≤ (32451842949/97656250000 : ℝ)^6395 := by
    have hnat : (2170543451 : ℕ)^8443*97656250000^6395 ≤ 32451842949^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170543451 5000000000 32451842949 97656250000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015979397/5000000000 : ℝ)^8443 ≤ (7535681645283/25000000000000 : ℝ)^6395 := by
    have hnat : (2015979397 : ℕ)^8443*25000000000000^6395 ≤ 7535681645283^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015979397 5000000000 7535681645283 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4673103317/10000000000 : ℝ)^8443 ≤ (1831329311133/5000000000000 : ℝ)^6395 := by
    have hnat : (4673103317 : ℕ)^8443*5000000000000^6395 ≤ 1831329311133^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4673103317 10000000000 1831329311133 5000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170543451/5000000000 : ℝ), (2015979397/5000000000 : ℝ), (4673103317/10000000000 : ℝ)] ![(32451842949/97656250000 : ℝ), (7535681645283/25000000000000 : ℝ), (1831329311133/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170543451/5000000000 : ℝ)|^8443 ≤ (32451842949/97656250000 : ℝ)^6395
        have hw : |(2170543451/5000000000 : ℝ)|=(2170543451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2015979397/5000000000 : ℝ)|^8443 ≤ (7535681645283/25000000000000 : ℝ)^6395
        have hw : |(2015979397/5000000000 : ℝ)|=(2015979397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4673103317/10000000000 : ℝ)|^8443 ≤ (1831329311133/5000000000000 : ℝ)^6395
        have hw : |(4673103317/10000000000 : ℝ)|=(4673103317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s2_4 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1051321827/5000000000 : ℝ)*x 0 + (323617567/625000000 : ℝ)*x 1 + (2744698583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051321827/5000000000 : ℝ)^8443 ≤ (12760898443209/100000000000000 : ℝ)^6395 := by
    have hnat : (1051321827 : ℕ)^8443*100000000000000^6395 ≤ 12760898443209^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051321827 5000000000 12760898443209 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (323617567/625000000 : ℝ)^8443 ≤ (10484536228701/25000000000000 : ℝ)^6395 := by
    have hnat : (323617567 : ℕ)^8443*25000000000000^6395 ≤ 10484536228701^6395*625000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323617567 625000000 10484536228701 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2744698583/5000000000 : ℝ)^8443 ≤ (45300956632263/100000000000000 : ℝ)^6395 := by
    have hnat : (2744698583 : ℕ)^8443*100000000000000^6395 ≤ 45300956632263^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744698583 5000000000 45300956632263 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1051321827/5000000000 : ℝ), (323617567/625000000 : ℝ), (2744698583/5000000000 : ℝ)] ![(12760898443209/100000000000000 : ℝ), (10484536228701/25000000000000 : ℝ), (45300956632263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1051321827/5000000000 : ℝ)|^8443 ≤ (12760898443209/100000000000000 : ℝ)^6395
        have hw : |(-1051321827/5000000000 : ℝ)|=(1051321827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(323617567/625000000 : ℝ)|^8443 ≤ (10484536228701/25000000000000 : ℝ)^6395
        have hw : |(323617567/625000000 : ℝ)|=(323617567/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2744698583/5000000000 : ℝ)|^8443 ≤ (45300956632263/100000000000000 : ℝ)^6395
        have hw : |(2744698583/5000000000 : ℝ)|=(2744698583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s2_5 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288734341/10000000000 : ℝ)*x 0 + (-976225401/5000000000 : ℝ)*x 1 + (5489397211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288734341/10000000000 : ℝ)^8443 ≤ (8625516152599/20000000000000 : ℝ)^6395 := by
    have hnat : (5288734341 : ℕ)^8443*20000000000000^6395 ≤ 8625516152599^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288734341 10000000000 8625516152599 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (976225401/5000000000 : ℝ)^8443 ≤ (2892865526287/25000000000000 : ℝ)^6395 := by
    have hnat : (976225401 : ℕ)^8443*25000000000000^6395 ≤ 2892865526287^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976225401 5000000000 2892865526287 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5489397211/10000000000 : ℝ)^8443 ≤ (45300957122551/100000000000000 : ℝ)^6395 := by
    have hnat : (5489397211 : ℕ)^8443*100000000000000^6395 ≤ 45300957122551^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489397211 10000000000 45300957122551 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288734341/10000000000 : ℝ), (-976225401/5000000000 : ℝ), (5489397211/10000000000 : ℝ)] ![(8625516152599/20000000000000 : ℝ), (2892865526287/25000000000000 : ℝ), (45300957122551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288734341/10000000000 : ℝ)|^8443 ≤ (8625516152599/20000000000000 : ℝ)^6395
        have hw : |(5288734341/10000000000 : ℝ)|=(5288734341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-976225401/5000000000 : ℝ)|^8443 ≤ (2892865526287/25000000000000 : ℝ)^6395
        have hw : |(-976225401/5000000000 : ℝ)|=(976225401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5489397211/10000000000 : ℝ)|^8443 ≤ (45300957122551/100000000000000 : ℝ)^6395
        have hw : |(5489397211/10000000000 : ℝ)|=(5489397211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s2_6 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288734493/10000000000 : ℝ)*x 0 + (1097879461/2000000000 : ℝ)*x 1 + (-1952450461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288734493/10000000000 : ℝ)^8443 ≤ (43127582399447/100000000000000 : ℝ)^6395 := by
    have hnat : (5288734493 : ℕ)^8443*100000000000000^6395 ≤ 43127582399447^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288734493 10000000000 43127582399447 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097879461/2000000000 : ℝ)^8443 ≤ (45300958146709/100000000000000 : ℝ)^6395 := by
    have hnat : (1097879461 : ℕ)^8443*100000000000000^6395 ≤ 45300958146709^6395*2000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097879461 2000000000 45300958146709 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1952450461/10000000000 : ℝ)^8443 ≤ (5785729718473/50000000000000 : ℝ)^6395 := by
    have hnat : (1952450461 : ℕ)^8443*50000000000000^6395 ≤ 5785729718473^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952450461 10000000000 5785729718473 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288734493/10000000000 : ℝ), (1097879461/2000000000 : ℝ), (-1952450461/10000000000 : ℝ)] ![(43127582399447/100000000000000 : ℝ), (45300958146709/100000000000000 : ℝ), (5785729718473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288734493/10000000000 : ℝ)|^8443 ≤ (43127582399447/100000000000000 : ℝ)^6395
        have hw : |(5288734493/10000000000 : ℝ)|=(5288734493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097879461/2000000000 : ℝ)|^8443 ≤ (45300958146709/100000000000000 : ℝ)^6395
        have hw : |(1097879461/2000000000 : ℝ)|=(1097879461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1952450461/10000000000 : ℝ)|^8443 ≤ (5785729718473/50000000000000 : ℝ)^6395
        have hw : |(-1952450461/10000000000 : ℝ)|=(1952450461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s2_7 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2170621191/5000000000 : ℝ)*x 0 + (1167251183/2500000000 : ℝ)*x 1 + (100902381/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170621191/5000000000 : ℝ)^8443 ≤ (33232258534029/100000000000000 : ℝ)^6395 := by
    have hnat : (2170621191 : ℕ)^8443*100000000000000^6395 ≤ 33232258534029^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170621191 5000000000 33232258534029 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1167251183/2500000000 : ℝ)^8443 ≤ (228651130707/625000000000 : ℝ)^6395 := by
    have hnat : (1167251183 : ℕ)^8443*625000000000^6395 ≤ 228651130707^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1167251183 2500000000 228651130707 625000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100902381/250000000 : ℝ)^8443 ≤ (7545890132247/25000000000000 : ℝ)^6395 := by
    have hnat : (100902381 : ℕ)^8443*25000000000000^6395 ≤ 7545890132247^6395*250000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100902381 250000000 7545890132247 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170621191/5000000000 : ℝ), (1167251183/2500000000 : ℝ), (100902381/250000000 : ℝ)] ![(33232258534029/100000000000000 : ℝ), (228651130707/625000000000 : ℝ), (7545890132247/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170621191/5000000000 : ℝ)|^8443 ≤ (33232258534029/100000000000000 : ℝ)^6395
        have hw : |(2170621191/5000000000 : ℝ)|=(2170621191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1167251183/2500000000 : ℝ)|^8443 ≤ (228651130707/625000000000 : ℝ)^6395
        have hw : |(1167251183/2500000000 : ℝ)|=(1167251183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(100902381/250000000 : ℝ)|^8443 ≤ (7545890132247/25000000000000 : ℝ)^6395
        have hw : |(100902381/250000000 : ℝ)|=(100902381/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1250_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3993/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6233/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2383/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8101/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3993/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6233/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3993/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6233/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3993/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6233/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3993/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6233/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3993/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6233/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3993/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6233/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6233/100000 : ℝ) ^ (4221/1024 : ℝ) ≤ (1075614898799551/100000000000000000000 : ℝ) := by
    have hpowers : (6233/100000 : ℝ)^4221 ≤ (1075614898799551/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6233 : ℕ)^4221*100000000000000000000^1024 ≤ 1075614898799551^1024*100000^4221 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6233 100000 1075614898799551 100000000000000000000 4221 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6233/100000 : ℝ)) (X := (1075614898799551/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3993/20000 : ℝ) ^ (4221/1024 : ℝ) ≤ (130515146344845021/100000000000000000000 : ℝ) := by
    have hpowers : (3993/20000 : ℝ)^4221 ≤ (130515146344845021/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3993 : ℕ)^4221*100000000000000000000^1024 ≤ 130515146344845021^1024*20000^4221 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3993 20000 130515146344845021 100000000000000000000 4221 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3993/20000 : ℝ)) (X := (130515146344845021/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001075614898799551/50000000000000000000 : ℝ) ≤ (2000010437533129/2000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (50001075614898799551/50000000000000000000 : ℝ)^1024 ≤ (2000010437533129/2000000000000000 : ℝ)^4221 := by
      have hnat : (50001075614898799551 : ℕ)^1024*2000000000000000^4221 ≤ 2000010437533129^4221*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001075614898799551 50000000000000000000 2000010437533129 2000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000010437533129/2000000000000000 : ℝ)) (X := (50001075614898799551/50000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25032897690310911143/25000000000000000000 : ℝ) ≤ (5001595378357223/5000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (25032897690310911143/25000000000000000000 : ℝ)^1024 ≤ (5001595378357223/5000000000000000 : ℝ)^4221 := by
      have hnat : (25032897690310911143 : ℕ)^1024*5000000000000000^4221 ≤ 5001595378357223^4221*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25032897690310911143 25000000000000000000 5001595378357223 5000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001595378357223/5000000000000000 : ℝ)) (X := (25032897690310911143/25000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50130515146344845021/50000000000000000000 : ℝ) ≤ (10006329325763247/10000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (50130515146344845021/50000000000000000000 : ℝ)^1024 ≤ (10006329325763247/10000000000000000 : ℝ)^4221 := by
      have hnat : (50130515146344845021 : ℕ)^1024*10000000000000000^4221 ≤ 10006329325763247^4221*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50130515146344845021 50000000000000000000 10006329325763247 10000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006329325763247/10000000000000000 : ℝ)) (X := (50130515146344845021/50000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1075614898799551/100000000000000000000 : ℝ) ≤ ((68640795619631141937/68660000000000000000 : ℝ)+2*(3138569048801/1373200000000000 : ℝ)*(6233/100000 : ℝ))^(4221/1024 : ℝ) := by
    rw [show (68640795619631141937/68660000000000000000 : ℝ)+2*(3138569048801/1373200000000000 : ℝ)*(6233/100000 : ℝ)=(2000010437533129/2000000000000000 : ℝ) by norm_num, show 1+2*(1075614898799551/100000000000000000000 : ℝ)=(50001075614898799551/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(130515146344845021/100000000000000000000 : ℝ)+(1075614898799551/100000000000000000000 : ℝ) ≤ ((68640795619631141937/68660000000000000000 : ℝ)+(3138569048801/1373200000000000 : ℝ)*((3993/20000 : ℝ)+(6233/100000 : ℝ)))^(4221/1024 : ℝ) := by
    rw [show (68640795619631141937/68660000000000000000 : ℝ)+(3138569048801/1373200000000000 : ℝ)*((3993/20000 : ℝ)+(6233/100000 : ℝ))=(5001595378357223/5000000000000000 : ℝ) by norm_num, show 1+(130515146344845021/100000000000000000000 : ℝ)+(1075614898799551/100000000000000000000 : ℝ)=(25032897690310911143/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(130515146344845021/100000000000000000000 : ℝ) ≤ ((68640795619631141937/68660000000000000000 : ℝ)+2*(3138569048801/1373200000000000 : ℝ)*(3993/20000 : ℝ))^(4221/1024 : ℝ) := by
    rw [show (68640795619631141937/68660000000000000000 : ℝ)+2*(3138569048801/1373200000000000 : ℝ)*(3993/20000 : ℝ)=(10006329325763247/10000000000000000 : ℝ) by norm_num, show 1+2*(130515146344845021/100000000000000000000 : ℝ)=(50130515146344845021/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (68640795619631141937/68660000000000000000 : ℝ)*(X 1 0+X 2 0)+(3138569048801/1373200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (6233/100000 : ℝ)) (hi := (3993/20000 : ℝ)) (c := (68640795619631141937/68660000000000000000 : ℝ)) (alpha := (3138569048801/1373200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (68640795619631141937/68660000000000000000 : ℝ)*(X 0 1+X 2 1)+(3138569048801/1373200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (6233/100000 : ℝ)) (hi := (3993/20000 : ℝ)) (c := (68640795619631141937/68660000000000000000 : ℝ)) (alpha := (3138569048801/1373200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (68640795619631141937/68660000000000000000 : ℝ)*(X 0 2+X 1 2)+(3138569048801/1373200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (6233/100000 : ℝ)) (hi := (3993/20000 : ℝ)) (c := (68640795619631141937/68660000000000000000 : ℝ)) (alpha := (3138569048801/1373200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-13141043/62500000 : ℝ)*X 0 0+(1372858369/2500000000 : ℝ)*X 0 1+(5175863581/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((536936247/1000000000 : ℝ)*X 1 0+(-566496137/2500000000 : ℝ)*X 1 1+(2587931831/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((335585147/625000000 : ℝ)*X 2 0+(258793187/500000000 : ℝ)*X 2 1+(-1132992301/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2170543451/5000000000 : ℝ)*X 0 0+(2015979397/5000000000 : ℝ)*X 0 1+(4673103317/10000000000 : ℝ)*X 0 2+(2170543451/5000000000 : ℝ)*X 1 0+(2015979397/5000000000 : ℝ)*X 1 1+(4673103317/10000000000 : ℝ)*X 1 2+(2170543451/5000000000 : ℝ)*X 2 0+(2015979397/5000000000 : ℝ)*X 2 1+(4673103317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1051321827/5000000000 : ℝ)*X 0 0+(323617567/625000000 : ℝ)*X 0 1+(2744698583/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5288734341/10000000000 : ℝ)*X 1 0+(-976225401/5000000000 : ℝ)*X 1 1+(5489397211/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5288734493/10000000000 : ℝ)*X 2 0+(1097879461/2000000000 : ℝ)*X 2 1+(-1952450461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2170621191/5000000000 : ℝ)*X 0 0+(1167251183/2500000000 : ℝ)*X 0 1+(100902381/250000000 : ℝ)*X 0 2+(2170621191/5000000000 : ℝ)*X 1 0+(1167251183/2500000000 : ℝ)*X 1 1+(100902381/250000000 : ℝ)*X 1 2+(2170621191/5000000000 : ℝ)*X 2 0+(1167251183/2500000000 : ℝ)*X 2 1+(100902381/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3026464902116125985296537089/858250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (581558909/100000000000000 : ℝ)*(base19) + (11939127/2500000000000 : ℝ)*(base23) + (18445229/100000000000000 : ℝ)*(lower2) + (112253277/100000000000000 : ℝ)*(upper3) + (1553323/5000000000000 : ℝ)*(upper5) + (591075167146101/25000000000000 : ℝ)*(major0) + (591075167146101/25000000000000 : ℝ)*(major1) + (591075167146101/25000000000000 : ℝ)*(major2) + (792219489557029/25000000000000 : ℝ)*(sp0) + (3168883563139823/100000000000000 : ℝ)*(sp1) + (792220916783413/25000000000000 : ℝ)*(sp2) + (1559713570272079/100000000000000 : ℝ)*(sp3) + (773308827/12500000000000 : ℝ)*(sp4) + (700930793/20000000000000 : ℝ)*(sp7) + (389929268731511/25000000000000 : ℝ)*(f.failure) + (792221036174683/25000000000000 : ℝ)*(f.sum) + (20687610188859/17165000000000000000000000000 : ℝ)*base66 + (648561644228812363/1716500000000000000000000000000000 : ℝ)*base68 + (2198316050324687637/1716500000000000000000000000000000 : ℝ)*base69 + (94698630424812363/1716500000000000000000000000000000 : ℝ)*base72 + (31261658824071/17165000000000000000000000000 : ℝ)*base73 + (1196748300653687637/1716500000000000000000000000000000 : ℝ)*base75 + (210105949324187637/1716500000000000000000000000000000 : ℝ)*base77 + (19600668021323187637/1716500000000000000000000000000000 : ℝ)*base79 + (8591754399483/8582500000000000000000000000 : ℝ)*base81 + (3012003/2500000000000000000000 : ℝ)*base90 + (3012003/2500000000000000000000 : ℝ)*base92 + (3012003/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (91414658709823251448623/34330000000000000000000000000 : ℝ) := by norm_num
    linear_combination (922839731/100000000000000 : ℝ)*(base19) + (12422501/1000000000000 : ℝ)*(base23) + (67024227/100000000000000 : ℝ)*(upper2) + (74281969/50000000000000 : ℝ)*(upper3) + (2407941/5000000000000 : ℝ)*(upper5) + (1197527675884351/50000000000000 : ℝ)*(major0) + (1197527675884351/50000000000000 : ℝ)*(major1) + (1197527675884351/50000000000000 : ℝ)*(major2) + (1124831303/12500000000000 : ℝ)*(sp1) + (7792858071/50000000000000 : ℝ)*(sp2) + (200631552027479/6250000000000 : ℝ)*(sp4) + (3210094910949509/100000000000000 : ℝ)*(sp5) + (3210088004473421/100000000000000 : ℝ)*(sp6) + (1580005782337023/100000000000000 : ℝ)*(sp7) + (1580005782337023/100000000000000 : ℝ)*(f.failure) + (200631552027479/6250000000000 : ℝ)*(f.sum) + (139495790261749/34330000000000000000000000000 : ℝ)*base66 + (15286382820283677887/3433000000000000000000000000000000 : ℝ)*base67 + (12564619613016322113/3433000000000000000000000000000000 : ℝ)*base70 + (1552317364819322113/3433000000000000000000000000000000 : ℝ)*base72 + (103156486041371/34330000000000000000000000000 : ℝ)*base73 + (6595730702695322113/3433000000000000000000000000000000 : ℝ)*base76 + (791320713276677887/3433000000000000000000000000000000 : ℝ)*base77 + (19802900523142677887/3433000000000000000000000000000000 : ℝ)*base79 + (15554583481999/34330000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (21959221/10000000000000000000000 : ℝ)*base89 + (21959221/10000000000000000000000 : ℝ)*base91 + (21959221/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1250_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3993/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6233/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2383/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8101/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1250_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1250_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2383/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8101/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1250_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1250_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1250_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2383/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8101/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1250_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

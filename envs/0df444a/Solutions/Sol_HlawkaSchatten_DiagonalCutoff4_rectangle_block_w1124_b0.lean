-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1124_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:10:28.077877+00:00
-- url     : https://prove2.me/submissions/0105af5e-abd3-4bbb-b5f0-60e7c11133de

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
theorem support_rectangle_w1124_s0_0 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1897520837/10000000000 : ℝ)*x 0 + (3029249959/5000000000 : ℝ)*x 1 + (59727393/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1897520837/10000000000 : ℝ)^8317 ≤ (11025024843459/100000000000000 : ℝ)^6269 := by
    have hnat : (1897520837 : ℕ)^8317*100000000000000^6269 ≤ 11025024843459^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897520837 10000000000 11025024843459 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3029249959/5000000000 : ℝ)^8317 ≤ (1607372986867/3125000000000 : ℝ)^6269 := by
    have hnat : (3029249959 : ℕ)^8317*3125000000000^6269 ≤ 1607372986867^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3029249959 5000000000 1607372986867 3125000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59727393/125000000 : ℝ)^8317 ≤ (18769519783587/50000000000000 : ℝ)^6269 := by
    have hnat : (59727393 : ℕ)^8317*50000000000000^6269 ≤ 18769519783587^6269*125000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59727393 125000000 18769519783587 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1897520837/10000000000 : ℝ), (3029249959/5000000000 : ℝ), (59727393/125000000 : ℝ)] ![(11025024843459/100000000000000 : ℝ), (1607372986867/3125000000000 : ℝ), (18769519783587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1897520837/10000000000 : ℝ)|^8317 ≤ (11025024843459/100000000000000 : ℝ)^6269
        have hw : |(-1897520837/10000000000 : ℝ)|=(1897520837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3029249959/5000000000 : ℝ)|^8317 ≤ (1607372986867/3125000000000 : ℝ)^6269
        have hw : |(3029249959/5000000000 : ℝ)|=(3029249959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(59727393/125000000 : ℝ)|^8317 ≤ (18769519783587/50000000000000 : ℝ)^6269
        have hw : |(59727393/125000000 : ℝ)|=(59727393/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s0_1 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5517807623/10000000000 : ℝ)*x 0 + (-1316392643/5000000000 : ℝ)*x 1 + (4778191529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5517807623/10000000000 : ℝ)^8317 ≤ (45436521800973/100000000000000 : ℝ)^6269 := by
    have hnat : (5517807623 : ℕ)^8317*100000000000000^6269 ≤ 45436521800973^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517807623 10000000000 45436521800973 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316392643/5000000000 : ℝ)^8317 ≤ (17024437676261/100000000000000 : ℝ)^6269 := by
    have hnat : (1316392643 : ℕ)^8317*100000000000000^6269 ≤ 17024437676261^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316392643 5000000000 17024437676261 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4778191529/10000000000 : ℝ)^8317 ≤ (37539040494811/100000000000000 : ℝ)^6269 := by
    have hnat : (4778191529 : ℕ)^8317*100000000000000^6269 ≤ 37539040494811^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4778191529 10000000000 37539040494811 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5517807623/10000000000 : ℝ), (-1316392643/5000000000 : ℝ), (4778191529/10000000000 : ℝ)] ![(45436521800973/100000000000000 : ℝ), (17024437676261/100000000000000 : ℝ), (37539040494811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5517807623/10000000000 : ℝ)|^8317 ≤ (45436521800973/100000000000000 : ℝ)^6269
        have hw : |(5517807623/10000000000 : ℝ)|=(5517807623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1316392643/5000000000 : ℝ)|^8317 ≤ (17024437676261/100000000000000 : ℝ)^6269
        have hw : |(-1316392643/5000000000 : ℝ)|=(1316392643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4778191529/10000000000 : ℝ)|^8317 ≤ (37539040494811/100000000000000 : ℝ)^6269
        have hw : |(4778191529/10000000000 : ℝ)|=(4778191529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s0_2 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5517807513/10000000000 : ℝ)*x 0 + (597273947/1250000000 : ℝ)*x 1 + (-2632785371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5517807513/10000000000 : ℝ)^8317 ≤ (45436520599263/100000000000000 : ℝ)^6269 := by
    have hnat : (5517807513 : ℕ)^8317*100000000000000^6269 ≤ 45436520599263^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517807513 10000000000 45436520599263 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (597273947/1250000000 : ℝ)^8317 ≤ (37539040984687/100000000000000 : ℝ)^6269 := by
    have hnat : (597273947 : ℕ)^8317*100000000000000^6269 ≤ 37539040984687^6269*1250000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597273947 1250000000 37539040984687 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632785371/10000000000 : ℝ)^8317 ≤ (8512219202729/50000000000000 : ℝ)^6269 := by
    have hnat : (2632785371 : ℕ)^8317*50000000000000^6269 ≤ 8512219202729^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632785371 10000000000 8512219202729 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5517807513/10000000000 : ℝ), (597273947/1250000000 : ℝ), (-2632785371/10000000000 : ℝ)] ![(45436520599263/100000000000000 : ℝ), (37539040984687/100000000000000 : ℝ), (8512219202729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5517807513/10000000000 : ℝ)|^8317 ≤ (45436520599263/100000000000000 : ℝ)^6269
        have hw : |(5517807513/10000000000 : ℝ)|=(5517807513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(597273947/1250000000 : ℝ)|^8317 ≤ (37539040984687/100000000000000 : ℝ)^6269
        have hw : |(597273947/1250000000 : ℝ)|=(597273947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2632785371/10000000000 : ℝ)|^8317 ≤ (8512219202729/50000000000000 : ℝ)^6269
        have hw : |(-2632785371/10000000000 : ℝ)|=(2632785371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s0_3 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (840490129/2000000000 : ℝ)*x 0 + (1560963463/5000000000 : ℝ)*x 1 + (5660077637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840490129/2000000000 : ℝ)^8317 ≤ (31659632608469/100000000000000 : ℝ)^6269 := by
    have hnat : (840490129 : ℕ)^8317*100000000000000^6269 ≤ 31659632608469^6269*2000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840490129 2000000000 31659632608469 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1560963463/5000000000 : ℝ)^8317 ≤ (21343089115441/100000000000000 : ℝ)^6269 := by
    have hnat : (1560963463 : ℕ)^8317*100000000000000^6269 ≤ 21343089115441^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560963463 5000000000 21343089115441 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5660077637/10000000000 : ℝ)^8317 ≤ (46997278259811/100000000000000 : ℝ)^6269 := by
    have hnat : (5660077637 : ℕ)^8317*100000000000000^6269 ≤ 46997278259811^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5660077637 10000000000 46997278259811 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(840490129/2000000000 : ℝ), (1560963463/5000000000 : ℝ), (5660077637/10000000000 : ℝ)] ![(31659632608469/100000000000000 : ℝ), (21343089115441/100000000000000 : ℝ), (46997278259811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(840490129/2000000000 : ℝ)|^8317 ≤ (31659632608469/100000000000000 : ℝ)^6269
        have hw : |(840490129/2000000000 : ℝ)|=(840490129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1560963463/5000000000 : ℝ)|^8317 ≤ (21343089115441/100000000000000 : ℝ)^6269
        have hw : |(1560963463/5000000000 : ℝ)|=(1560963463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5660077637/10000000000 : ℝ)|^8317 ≤ (46997278259811/100000000000000 : ℝ)^6269
        have hw : |(5660077637/10000000000 : ℝ)|=(5660077637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s0_4 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-380544169/2000000000 : ℝ)*x 0 + (962245861/2000000000 : ℝ)*x 1 + (1506075277/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (380544169/2000000000 : ℝ)^8317 ≤ (1383140782419/12500000000000 : ℝ)^6269 := by
    have hnat : (380544169 : ℕ)^8317*12500000000000^6269 ≤ 1383140782419^6269*2000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380544169 2000000000 1383140782419 12500000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (962245861/2000000000 : ℝ)^8317 ≤ (3788377782053/10000000000000 : ℝ)^6269 := by
    have hnat : (962245861 : ℕ)^8317*10000000000000^6269 ≤ 3788377782053^6269*2000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962245861 2000000000 3788377782053 10000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1506075277/2500000000 : ℝ)^8317 ≤ (5105109590863/10000000000000 : ℝ)^6269 := by
    have hnat : (1506075277 : ℕ)^8317*10000000000000^6269 ≤ 5105109590863^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506075277 2500000000 5105109590863 10000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-380544169/2000000000 : ℝ), (962245861/2000000000 : ℝ), (1506075277/2500000000 : ℝ)] ![(1383140782419/12500000000000 : ℝ), (3788377782053/10000000000000 : ℝ), (5105109590863/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-380544169/2000000000 : ℝ)|^8317 ≤ (1383140782419/12500000000000 : ℝ)^6269
        have hw : |(-380544169/2000000000 : ℝ)|=(380544169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(962245861/2000000000 : ℝ)|^8317 ≤ (3788377782053/10000000000000 : ℝ)^6269
        have hw : |(962245861/2000000000 : ℝ)|=(962245861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1506075277/2500000000 : ℝ)|^8317 ≤ (5105109590863/10000000000000 : ℝ)^6269
        have hw : |(1506075277/2500000000 : ℝ)|=(1506075277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s0_5 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5170004997/10000000000 : ℝ)*x 0 + (-1386676593/10000000000 : ℝ)*x 1 + (1506076257/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5170004997/10000000000 : ℝ)^8317 ≤ (2604787140039/6250000000000 : ℝ)^6269 := by
    have hnat : (5170004997 : ℕ)^8317*6250000000000^6269 ≤ 2604787140039^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170004997 10000000000 2604787140039 6250000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1386676593/10000000000 : ℝ)^8317 ≤ (909033220717/12500000000000 : ℝ)^6269 := by
    have hnat : (1386676593 : ℕ)^8317*12500000000000^6269 ≤ 909033220717^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1386676593 10000000000 909033220717 12500000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1506076257/2500000000 : ℝ)^8317 ≤ (25525569989817/50000000000000 : ℝ)^6269 := by
    have hnat : (1506076257 : ℕ)^8317*50000000000000^6269 ≤ 25525569989817^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506076257 2500000000 25525569989817 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5170004997/10000000000 : ℝ), (-1386676593/10000000000 : ℝ), (1506076257/2500000000 : ℝ)] ![(2604787140039/6250000000000 : ℝ), (909033220717/12500000000000 : ℝ), (25525569989817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5170004997/10000000000 : ℝ)|^8317 ≤ (2604787140039/6250000000000 : ℝ)^6269
        have hw : |(5170004997/10000000000 : ℝ)|=(5170004997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1386676593/10000000000 : ℝ)|^8317 ≤ (909033220717/12500000000000 : ℝ)^6269
        have hw : |(-1386676593/10000000000 : ℝ)|=(1386676593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1506076257/2500000000 : ℝ)|^8317 ≤ (25525569989817/50000000000000 : ℝ)^6269
        have hw : |(1506076257/2500000000 : ℝ)|=(1506076257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s0_6 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (517001001/1000000000 : ℝ)*x 0 + (6024301367/10000000000 : ℝ)*x 1 + (-1386674803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517001001/1000000000 : ℝ)^8317 ≤ (41676647853297/100000000000000 : ℝ)^6269 := by
    have hnat : (517001001 : ℕ)^8317*100000000000000^6269 ≤ 41676647853297^6269*1000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517001001 1000000000 41676647853297 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6024301367/10000000000 : ℝ)^8317 ≤ (3190693676279/6250000000000 : ℝ)^6269 := by
    have hnat : (6024301367 : ℕ)^8317*6250000000000^6269 ≤ 3190693676279^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6024301367 10000000000 3190693676279 6250000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1386674803/10000000000 : ℝ)^8317 ≤ (7272253311533/100000000000000 : ℝ)^6269 := by
    have hnat : (1386674803 : ℕ)^8317*100000000000000^6269 ≤ 7272253311533^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1386674803 10000000000 7272253311533 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517001001/1000000000 : ℝ), (6024301367/10000000000 : ℝ), (-1386674803/10000000000 : ℝ)] ![(41676647853297/100000000000000 : ℝ), (3190693676279/6250000000000 : ℝ), (7272253311533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517001001/1000000000 : ℝ)|^8317 ≤ (41676647853297/100000000000000 : ℝ)^6269
        have hw : |(517001001/1000000000 : ℝ)|=(517001001/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6024301367/10000000000 : ℝ)|^8317 ≤ (3190693676279/6250000000000 : ℝ)^6269
        have hw : |(6024301367/10000000000 : ℝ)|=(6024301367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1386674803/10000000000 : ℝ)|^8317 ≤ (7272253311533/100000000000000 : ℝ)^6269
        have hw : |(-1386674803/10000000000 : ℝ)|=(1386674803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s0_7 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4212755903/10000000000 : ℝ)*x 0 + (559458607/1000000000 : ℝ)*x 1 + (3189719149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4212755903/10000000000 : ℝ)^8317 ≤ (15881336129453/50000000000000 : ℝ)^6269 := by
    have hnat : (4212755903 : ℕ)^8317*50000000000000^6269 ≤ 15881336129453^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212755903 10000000000 15881336129453 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559458607/1000000000 : ℝ)^8317 ≤ (46277198857943/100000000000000 : ℝ)^6269 := by
    have hnat : (559458607 : ℕ)^8317*100000000000000^6269 ≤ 46277198857943^6269*1000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559458607 1000000000 46277198857943 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3189719149/10000000000 : ℝ)^8317 ≤ (21960128870521/100000000000000 : ℝ)^6269 := by
    have hnat : (3189719149 : ℕ)^8317*100000000000000^6269 ≤ 21960128870521^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3189719149 10000000000 21960128870521 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4212755903/10000000000 : ℝ), (559458607/1000000000 : ℝ), (3189719149/10000000000 : ℝ)] ![(15881336129453/50000000000000 : ℝ), (46277198857943/100000000000000 : ℝ), (21960128870521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4212755903/10000000000 : ℝ)|^8317 ≤ (15881336129453/50000000000000 : ℝ)^6269
        have hw : |(4212755903/10000000000 : ℝ)|=(4212755903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(559458607/1000000000 : ℝ)|^8317 ≤ (46277198857943/100000000000000 : ℝ)^6269
        have hw : |(559458607/1000000000 : ℝ)|=(559458607/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3189719149/10000000000 : ℝ)|^8317 ≤ (21960128870521/100000000000000 : ℝ)^6269
        have hw : |(3189719149/10000000000 : ℝ)|=(3189719149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1124_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (339/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6971/25000 : ℝ)*pair X 0 0 := by
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
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (2079/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2079 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2079*1^512 ≤ 0^512*1^2079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2079 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2079/512 : ℝ) ≤ (15136517198748643/625000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2079 ≤ (15136517198748643/625000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2079*625000000000000000^512 ≤ 15136517198748643^512*5^2079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 15136517198748643 625000000000000000 2079 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (15136517198748643/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2079 := by
      have hnat : (1 : ℕ)^512*1^2079 ≤ 1^2079*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (640136517198748643/625000000000000000 : ℝ) ≤ (10059106479045187/10000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (640136517198748643/625000000000000000 : ℝ)^512 ≤ (10059106479045187/10000000000000000 : ℝ)^2079 := by
      have hnat : (640136517198748643 : ℕ)^512*10000000000000000^2079 ≤ 10059106479045187^2079*625000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        640136517198748643 625000000000000000 10059106479045187 10000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10059106479045187/10000000000000000 : ℝ)) (X := (640136517198748643/625000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (327636517198748643/312500000000000000 : ℝ) ≤ (5059106479045187/5000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (327636517198748643/312500000000000000 : ℝ)^512 ≤ (5059106479045187/5000000000000000 : ℝ)^2079 := by
      have hnat : (327636517198748643 : ℕ)^512*5000000000000000^2079 ≤ 5059106479045187^2079*312500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        327636517198748643 312500000000000000 5059106479045187 5000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5059106479045187/5000000000000000 : ℝ)) (X := (327636517198748643/312500000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(59106479045187/4000000000000000 : ℝ)*(0 : ℝ))^(2079/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(59106479045187/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15136517198748643/625000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(59106479045187/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2079/512 : ℝ) := by
    rw [show (1 : ℝ)+(59106479045187/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10059106479045187/10000000000000000 : ℝ) by norm_num, show 1+(15136517198748643/625000000000000000 : ℝ)+(0 : ℝ)=(640136517198748643/625000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15136517198748643/625000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(59106479045187/4000000000000000 : ℝ)*(2/5 : ℝ))^(2079/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(59106479045187/4000000000000000 : ℝ)*(2/5 : ℝ)=(5059106479045187/5000000000000000 : ℝ) by norm_num, show 1+2*(15136517198748643/625000000000000000 : ℝ)=(327636517198748643/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(59106479045187/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59106479045187/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(59106479045187/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59106479045187/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(59106479045187/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59106479045187/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1897520837/10000000000 : ℝ)*X 0 0+(3029249959/5000000000 : ℝ)*X 0 1+(59727393/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5517807623/10000000000 : ℝ)*X 1 0+(-1316392643/5000000000 : ℝ)*X 1 1+(4778191529/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5517807513/10000000000 : ℝ)*X 2 0+(597273947/1250000000 : ℝ)*X 2 1+(-2632785371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((840490129/2000000000 : ℝ)*X 0 0+(1560963463/5000000000 : ℝ)*X 0 1+(5660077637/10000000000 : ℝ)*X 0 2+(840490129/2000000000 : ℝ)*X 1 0+(1560963463/5000000000 : ℝ)*X 1 1+(5660077637/10000000000 : ℝ)*X 1 2+(840490129/2000000000 : ℝ)*X 2 0+(1560963463/5000000000 : ℝ)*X 2 1+(5660077637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-380544169/2000000000 : ℝ)*X 0 0+(962245861/2000000000 : ℝ)*X 0 1+(1506075277/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5170004997/10000000000 : ℝ)*X 1 0+(-1386676593/10000000000 : ℝ)*X 1 1+(1506076257/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((517001001/1000000000 : ℝ)*X 2 0+(6024301367/10000000000 : ℝ)*X 2 1+(-1386674803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4212755903/10000000000 : ℝ)*X 0 0+(559458607/1000000000 : ℝ)*X 0 1+(3189719149/10000000000 : ℝ)*X 0 2+(4212755903/10000000000 : ℝ)*X 1 0+(559458607/1000000000 : ℝ)*X 1 1+(3189719149/10000000000 : ℝ)*X 1 2+(4212755903/10000000000 : ℝ)*X 2 0+(559458607/1000000000 : ℝ)*X 2 1+(3189719149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (219142364060219251997289/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28224413/50000000000000 : ℝ)*(base1) + (696459919/50000000000000 : ℝ)*(base19) + (643976367/50000000000000 : ℝ)*(base23) + (89396157/100000000000000 : ℝ)*(base24) + (161658933/50000000000000 : ℝ)*(upper3) + (117506130413151/20000000000000 : ℝ)*(major0) + (117506130413151/20000000000000 : ℝ)*(major1) + (117506130413151/20000000000000 : ℝ)*(major2) + (390533238732033/50000000000000 : ℝ)*(sp0) + (390534054912819/50000000000000 : ℝ)*(sp1) + (390534062698293/50000000000000 : ℝ)*(sp2) + (393989095028517/100000000000000 : ℝ)*(sp3) + (770432559/25000000000000 : ℝ)*(sp4) + (1233645023/50000000000000 : ℝ)*(sp7) + (98497904691847/25000000000000 : ℝ)*(f.failure) + (195267375686369/25000000000000 : ℝ)*(f.sum) + (15658585585763/40000000000000000000000000000 : ℝ)*base66 + (142970665654237/80000000000000000000000000000 : ℝ)*base67 + (226583371174237/80000000000000000000000000000 : ℝ)*base69 + (335066429894237/80000000000000000000000000000 : ℝ)*base71 + (87957511705763/40000000000000000000000000000 : ℝ)*base74 + (482749453254237/80000000000000000000000000000 : ℝ)*base75 + (192817458374237/80000000000000000000000000000 : ℝ)*base77 + (227241091785763/80000000000000000000000000000 : ℝ)*base80 + (15695436974237/40000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (24877931/2500000000000000000000 : ℝ)*base90 + (24877931/2500000000000000000000 : ℝ)*base92 + (24877931/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (74453340933704822119263/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (533896659/100000000000000 : ℝ)*(base13) + (123553517/12500000000000 : ℝ)*(base23) + (26067407/20000000000000 : ℝ)*(base39) + (55442023/50000000000000 : ℝ)*(upper3) + (10911/50000000000000 : ℝ)*(upper4) + (11567869/5000000000000 : ℝ)*(upper5) + (620086990656701/100000000000000 : ℝ)*(major0) + (620086990656701/100000000000000 : ℝ)*(major1) + (310043430159833/50000000000000 : ℝ)*(major2) + (929706539/100000000000000 : ℝ)*(sp2) + (82434967504287/10000000000000 : ℝ)*(sp4) + (824350208939529/100000000000000 : ℝ)*(sp5) + (824348421141889/100000000000000 : ℝ)*(sp6) + (207911771382857/50000000000000 : ℝ)*(sp7) + (207911771382857/50000000000000 : ℝ)*(f.failure) + (206087584819141/25000000000000 : ℝ)*(f.sum) + (331367974704371/400000000000000000000000000000 : ℝ)*base66 + (350325226626229/200000000000000000000000000000 : ℝ)*base68 + (2542729644948087/400000000000000000000000000000 : ℝ)*base69 + (651730591626229/200000000000000000000000000000 : ℝ)*base72 + (60882148895629/400000000000000000000000000000 : ℝ)*base73 + (1177068904148087/400000000000000000000000000000 : ℝ)*base75 + (1490985872251913/400000000000000000000000000000 : ℝ)*base78 + (1275279900548087/400000000000000000000000000000 : ℝ)*base79 + (724693873348087/200000000000000000000000000000 : ℝ)*base81 + (8605339/5000000000000000000000 : ℝ)*base89 + (8605339/5000000000000000000000 : ℝ)*base91 + (8605339/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1124_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (339/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6971/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1124_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1124_s1_0 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-105174409/500000000 : ℝ)*x 0 + (1426585573/2500000000 : ℝ)*x 1 + (4998481233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105174409/500000000 : ℝ)^8317 ≤ (6320093329611/50000000000000 : ℝ)^6269 := by
    have hnat : (105174409 : ℕ)^8317*50000000000000^6269 ≤ 6320093329611^6269*500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105174409 500000000 6320093329611 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1426585573/2500000000 : ℝ)^8317 ≤ (11876900707867/25000000000000 : ℝ)^6269 := by
    have hnat : (1426585573 : ℕ)^8317*25000000000000^6269 ≤ 11876900707867^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426585573 2500000000 11876900707867 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4998481233/10000000000 : ℝ)^8317 ≤ (622690789163/1562500000000 : ℝ)^6269 := by
    have hnat : (4998481233 : ℕ)^8317*1562500000000^6269 ≤ 622690789163^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4998481233 10000000000 622690789163 1562500000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-105174409/500000000 : ℝ), (1426585573/2500000000 : ℝ), (4998481233/10000000000 : ℝ)] ![(6320093329611/50000000000000 : ℝ), (11876900707867/25000000000000 : ℝ), (622690789163/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-105174409/500000000 : ℝ)|^8317 ≤ (6320093329611/50000000000000 : ℝ)^6269
        have hw : |(-105174409/500000000 : ℝ)|=(105174409/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1426585573/2500000000 : ℝ)|^8317 ≤ (11876900707867/25000000000000 : ℝ)^6269
        have hw : |(1426585573/2500000000 : ℝ)|=(1426585573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4998481233/10000000000 : ℝ)|^8317 ≤ (622690789163/1562500000000 : ℝ)^6269
        have hw : |(4998481233/10000000000 : ℝ)|=(4998481233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s1_1 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5420110741/10000000000 : ℝ)*x 0 + (-2485841031/10000000000 : ℝ)*x 1 + (4998480933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420110741/10000000000 : ℝ)^8317 ≤ (44372318099231/100000000000000 : ℝ)^6269 := by
    have hnat : (5420110741 : ℕ)^8317*100000000000000^6269 ≤ 44372318099231^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420110741 10000000000 44372318099231 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2485841031/10000000000 : ℝ)^8317 ≤ (15775474558737/100000000000000 : ℝ)^6269 := by
    have hnat : (2485841031 : ℕ)^8317*100000000000000^6269 ≤ 15775474558737^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2485841031 10000000000 15775474558737 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4998480933/10000000000 : ℝ)^8317 ≤ (622690739581/1562500000000 : ℝ)^6269 := by
    have hnat : (4998480933 : ℕ)^8317*1562500000000^6269 ≤ 622690739581^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4998480933 10000000000 622690739581 1562500000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420110741/10000000000 : ℝ), (-2485841031/10000000000 : ℝ), (4998480933/10000000000 : ℝ)] ![(44372318099231/100000000000000 : ℝ), (15775474558737/100000000000000 : ℝ), (622690739581/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420110741/10000000000 : ℝ)|^8317 ≤ (44372318099231/100000000000000 : ℝ)^6269
        have hw : |(5420110741/10000000000 : ℝ)|=(5420110741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2485841031/10000000000 : ℝ)|^8317 ≤ (15775474558737/100000000000000 : ℝ)^6269
        have hw : |(-2485841031/10000000000 : ℝ)|=(2485841031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4998480933/10000000000 : ℝ)|^8317 ≤ (622690739581/1562500000000 : ℝ)^6269
        have hw : |(4998480933/10000000000 : ℝ)|=(4998480933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s1_2 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2710056167/5000000000 : ℝ)*x 0 + (2499239741/5000000000 : ℝ)*x 1 + (-1242920399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2710056167/5000000000 : ℝ)^8317 ≤ (11093083850227/25000000000000 : ℝ)^6269 := by
    have hnat : (2710056167 : ℕ)^8317*25000000000000^6269 ≤ 11093083850227^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710056167 5000000000 11093083850227 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2499239741/5000000000 : ℝ)^8317 ≤ (39852191985241/100000000000000 : ℝ)^6269 := by
    have hnat : (2499239741 : ℕ)^8317*100000000000000^6269 ≤ 39852191985241^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2499239741 5000000000 39852191985241 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1242920399/5000000000 : ℝ)^8317 ≤ (7887736298517/50000000000000 : ℝ)^6269 := by
    have hnat : (1242920399 : ℕ)^8317*50000000000000^6269 ≤ 7887736298517^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1242920399 5000000000 7887736298517 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2710056167/5000000000 : ℝ), (2499239741/5000000000 : ℝ), (-1242920399/5000000000 : ℝ)] ![(11093083850227/25000000000000 : ℝ), (39852191985241/100000000000000 : ℝ), (7887736298517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2710056167/5000000000 : ℝ)|^8317 ≤ (11093083850227/25000000000000 : ℝ)^6269
        have hw : |(2710056167/5000000000 : ℝ)|=(2710056167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2499239741/5000000000 : ℝ)|^8317 ≤ (39852191985241/100000000000000 : ℝ)^6269
        have hw : |(2499239741/5000000000 : ℝ)|=(2499239741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1242920399/5000000000 : ℝ)|^8317 ≤ (7887736298517/50000000000000 : ℝ)^6269
        have hw : |(-1242920399/5000000000 : ℝ)|=(1242920399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s1_3 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (86379197/200000000 : ℝ)*x 0 + (3673652201/10000000000 : ℝ)*x 1 + (5076951271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86379197/200000000 : ℝ)^8317 ≤ (32829353270499/100000000000000 : ℝ)^6269 := by
    have hnat : (86379197 : ℕ)^8317*100000000000000^6269 ≤ 32829353270499^6269*200000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86379197 200000000 32829353270499 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3673652201/10000000000 : ℝ)^8317 ≤ (13243149452277/50000000000000 : ℝ)^6269 := by
    have hnat : (3673652201 : ℕ)^8317*50000000000000^6269 ≤ 13243149452277^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3673652201 10000000000 13243149452277 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5076951271/10000000000 : ℝ)^8317 ≤ (40684347804621/100000000000000 : ℝ)^6269 := by
    have hnat : (5076951271 : ℕ)^8317*100000000000000^6269 ≤ 40684347804621^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5076951271 10000000000 40684347804621 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86379197/200000000 : ℝ), (3673652201/10000000000 : ℝ), (5076951271/10000000000 : ℝ)] ![(32829353270499/100000000000000 : ℝ), (13243149452277/50000000000000 : ℝ), (40684347804621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86379197/200000000 : ℝ)|^8317 ≤ (32829353270499/100000000000000 : ℝ)^6269
        have hw : |(86379197/200000000 : ℝ)|=(86379197/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3673652201/10000000000 : ℝ)|^8317 ≤ (13243149452277/50000000000000 : ℝ)^6269
        have hw : |(3673652201/10000000000 : ℝ)|=(3673652201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5076951271/10000000000 : ℝ)|^8317 ≤ (40684347804621/100000000000000 : ℝ)^6269
        have hw : |(5076951271/10000000000 : ℝ)|=(5076951271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s1_4 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-526079993/2500000000 : ℝ)*x 0 + (5008212939/10000000000 : ℝ)*x 1 + (1424104119/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526079993/2500000000 : ℝ)^8317 ≤ (12646818355539/100000000000000 : ℝ)^6269 := by
    have hnat : (526079993 : ℕ)^8317*100000000000000^6269 ≤ 12646818355539^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526079993 2500000000 12646818355539 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5008212939/10000000000 : ℝ)^8317 ≤ (19977590144199/50000000000000 : ℝ)^6269 := by
    have hnat : (5008212939 : ℕ)^8317*50000000000000^6269 ≤ 19977590144199^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5008212939 10000000000 19977590144199 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1424104119/2500000000 : ℝ)^8317 ≤ (23699000666731/50000000000000 : ℝ)^6269 := by
    have hnat : (1424104119 : ℕ)^8317*50000000000000^6269 ≤ 23699000666731^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1424104119 2500000000 23699000666731 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-526079993/2500000000 : ℝ), (5008212939/10000000000 : ℝ), (1424104119/2500000000 : ℝ)] ![(12646818355539/100000000000000 : ℝ), (19977590144199/50000000000000 : ℝ), (23699000666731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-526079993/2500000000 : ℝ)|^8317 ≤ (12646818355539/100000000000000 : ℝ)^6269
        have hw : |(-526079993/2500000000 : ℝ)|=(526079993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5008212939/10000000000 : ℝ)|^8317 ≤ (19977590144199/50000000000000 : ℝ)^6269
        have hw : |(5008212939/10000000000 : ℝ)|=(5008212939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1424104119/2500000000 : ℝ)|^8317 ≤ (23699000666731/50000000000000 : ℝ)^6269
        have hw : |(1424104119/2500000000 : ℝ)|=(1424104119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s1_5 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5238792483/10000000000 : ℝ)*x 0 + (-893952449/5000000000 : ℝ)*x 1 + (2848208293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5238792483/10000000000 : ℝ)^8317 ≤ (21206925837151/50000000000000 : ℝ)^6269 := by
    have hnat : (5238792483 : ℕ)^8317*50000000000000^6269 ≤ 21206925837151^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238792483 10000000000 21206925837151 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (893952449/5000000000 : ℝ)^8317 ≤ (10188145755759/100000000000000 : ℝ)^6269 := by
    have hnat : (893952449 : ℕ)^8317*100000000000000^6269 ≤ 10188145755759^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893952449 5000000000 10188145755759 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2848208293/5000000000 : ℝ)^8317 ≤ (47398002547743/100000000000000 : ℝ)^6269 := by
    have hnat : (2848208293 : ℕ)^8317*100000000000000^6269 ≤ 47398002547743^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2848208293 5000000000 47398002547743 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5238792483/10000000000 : ℝ), (-893952449/5000000000 : ℝ), (2848208293/5000000000 : ℝ)] ![(21206925837151/50000000000000 : ℝ), (10188145755759/100000000000000 : ℝ), (47398002547743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5238792483/10000000000 : ℝ)|^8317 ≤ (21206925837151/50000000000000 : ℝ)^6269
        have hw : |(5238792483/10000000000 : ℝ)|=(5238792483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-893952449/5000000000 : ℝ)|^8317 ≤ (10188145755759/100000000000000 : ℝ)^6269
        have hw : |(-893952449/5000000000 : ℝ)|=(893952449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2848208293/5000000000 : ℝ)|^8317 ≤ (47398002547743/100000000000000 : ℝ)^6269
        have hw : |(2848208293/5000000000 : ℝ)|=(2848208293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s1_6 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5238792379/10000000000 : ℝ)*x 0 + (5696416539/10000000000 : ℝ)*x 1 + (-446976279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5238792379/10000000000 : ℝ)^8317 ≤ (42413850557237/100000000000000 : ℝ)^6269 := by
    have hnat : (5238792379 : ℕ)^8317*100000000000000^6269 ≤ 42413850557237^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238792379 10000000000 42413850557237 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5696416539/10000000000 : ℝ)^8317 ≤ (23699001014457/50000000000000 : ℝ)^6269 := by
    have hnat : (5696416539 : ℕ)^8317*50000000000000^6269 ≤ 23699001014457^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5696416539 10000000000 23699001014457 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (446976279/2500000000 : ℝ)^8317 ≤ (10188147403829/100000000000000 : ℝ)^6269 := by
    have hnat : (446976279 : ℕ)^8317*100000000000000^6269 ≤ 10188147403829^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446976279 2500000000 10188147403829 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5238792379/10000000000 : ℝ), (5696416539/10000000000 : ℝ), (-446976279/2500000000 : ℝ)] ![(42413850557237/100000000000000 : ℝ), (23699001014457/50000000000000 : ℝ), (10188147403829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5238792379/10000000000 : ℝ)|^8317 ≤ (42413850557237/100000000000000 : ℝ)^6269
        have hw : |(5238792379/10000000000 : ℝ)|=(5238792379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5696416539/10000000000 : ℝ)|^8317 ≤ (23699001014457/50000000000000 : ℝ)^6269
        have hw : |(5696416539/10000000000 : ℝ)|=(5696416539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-446976279/2500000000 : ℝ)|^8317 ≤ (10188147403829/100000000000000 : ℝ)^6269
        have hw : |(-446976279/2500000000 : ℝ)|=(446976279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s1_7 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (432060611/1000000000 : ℝ)*x 0 + (2528829603/5000000000 : ℝ)*x 1 + (1846664331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432060611/1000000000 : ℝ)^8317 ≤ (32845955906827/100000000000000 : ℝ)^6269 := by
    have hnat : (432060611 : ℕ)^8317*100000000000000^6269 ≤ 32845955906827^6269*1000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432060611 1000000000 32845955906827 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2528829603/5000000000 : ℝ)^8317 ≤ (40479372456107/100000000000000 : ℝ)^6269 := by
    have hnat : (2528829603 : ℕ)^8317*100000000000000^6269 ≤ 40479372456107^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2528829603 5000000000 40479372456107 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1846664331/5000000000 : ℝ)^8317 ≤ (3334333952323/12500000000000 : ℝ)^6269 := by
    have hnat : (1846664331 : ℕ)^8317*12500000000000^6269 ≤ 3334333952323^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846664331 5000000000 3334333952323 12500000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(432060611/1000000000 : ℝ), (2528829603/5000000000 : ℝ), (1846664331/5000000000 : ℝ)] ![(32845955906827/100000000000000 : ℝ), (40479372456107/100000000000000 : ℝ), (3334333952323/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(432060611/1000000000 : ℝ)|^8317 ≤ (32845955906827/100000000000000 : ℝ)^6269
        have hw : |(432060611/1000000000 : ℝ)|=(432060611/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2528829603/5000000000 : ℝ)|^8317 ≤ (40479372456107/100000000000000 : ℝ)^6269
        have hw : |(2528829603/5000000000 : ℝ)|=(2528829603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1846664331/5000000000 : ℝ)|^8317 ≤ (3334333952323/12500000000000 : ℝ)^6269
        have hw : |(1846664331/5000000000 : ℝ)|=(1846664331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1124_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6971/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1387/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20519/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6971/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6971/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6971/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6971/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6971/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (339/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6971/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (339/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (339/100000 : ℝ) ^ (2079/512 : ℝ) ≤ (2339915161/25000000000000000000 : ℝ) := by
    have hpowers : (339/100000 : ℝ)^2079 ≤ (2339915161/25000000000000000000 : ℝ)^512 := by
      have hnat : (339 : ℕ)^2079*25000000000000000000^512 ≤ 2339915161^512*100000^2079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        339 100000 2339915161 25000000000000000000 2079 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (339/100000 : ℝ)) (X := (2339915161/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hpowhi : (6971/25000 : ℝ) ^ (2079/512 : ℝ) ≤ (559549200131432409/100000000000000000000 : ℝ) := by
    have hpowers : (6971/25000 : ℝ)^2079 ≤ (559549200131432409/100000000000000000000 : ℝ)^512 := by
      have hnat : (6971 : ℕ)^2079*100000000000000000000^512 ≤ 559549200131432409^512*25000^2079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6971 25000 559549200131432409 100000000000000000000 2079 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6971/25000 : ℝ)) (X := (559549200131432409/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000002339915161/12500000000000000000 : ℝ) ≤ (2000000000092201/2000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (12500000002339915161/12500000000000000000 : ℝ)^512 ≤ (2000000000092201/2000000000000000 : ℝ)^2079 := by
      have hnat : (12500000002339915161 : ℕ)^512*2000000000000000^2079 ≤ 2000000000092201^2079*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000002339915161 12500000000000000000 2000000000092201 2000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000000092201/2000000000000000 : ℝ)) (X := (12500000002339915161/12500000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100559549209491093053/100000000000000000000 : ℝ) ≤ (10013751180033227/10000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (100559549209491093053/100000000000000000000 : ℝ)^512 ≤ (10013751180033227/10000000000000000 : ℝ)^2079 := by
      have hnat : (100559549209491093053 : ℕ)^512*10000000000000000^2079 ≤ 10013751180033227^2079*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100559549209491093053 100000000000000000000 10013751180033227 10000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013751180033227/10000000000000000 : ℝ)) (X := (100559549209491093053/100000000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50559549200131432409/50000000000000000000 : ℝ) ≤ (10027502359605449/10000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (50559549200131432409/50000000000000000000 : ℝ)^512 ≤ (10027502359605449/10000000000000000 : ℝ)^2079 := by
      have hnat : (50559549200131432409 : ℕ)^512*10000000000000000^2079 ≤ 10027502359605449^2079*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50559549200131432409 50000000000000000000 10027502359605449 10000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10027502359605449/10000000000000000 : ℝ)) (X := (50559549200131432409/50000000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2339915161/25000000000000000000 : ℝ) ≤ ((275440676712948416209/275450000000000000000 : ℝ)+2*(6875589786111/1377250000000000 : ℝ)*(339/100000 : ℝ))^(2079/512 : ℝ) := by
    rw [show (275440676712948416209/275450000000000000000 : ℝ)+2*(6875589786111/1377250000000000 : ℝ)*(339/100000 : ℝ)=(2000000000092201/2000000000000000 : ℝ) by norm_num, show 1+2*(2339915161/25000000000000000000 : ℝ)=(12500000002339915161/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(559549200131432409/100000000000000000000 : ℝ)+(2339915161/25000000000000000000 : ℝ) ≤ ((275440676712948416209/275450000000000000000 : ℝ)+(6875589786111/1377250000000000 : ℝ)*((6971/25000 : ℝ)+(339/100000 : ℝ)))^(2079/512 : ℝ) := by
    rw [show (275440676712948416209/275450000000000000000 : ℝ)+(6875589786111/1377250000000000 : ℝ)*((6971/25000 : ℝ)+(339/100000 : ℝ))=(10013751180033227/10000000000000000 : ℝ) by norm_num, show 1+(559549200131432409/100000000000000000000 : ℝ)+(2339915161/25000000000000000000 : ℝ)=(100559549209491093053/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(559549200131432409/100000000000000000000 : ℝ) ≤ ((275440676712948416209/275450000000000000000 : ℝ)+2*(6875589786111/1377250000000000 : ℝ)*(6971/25000 : ℝ))^(2079/512 : ℝ) := by
    rw [show (275440676712948416209/275450000000000000000 : ℝ)+2*(6875589786111/1377250000000000 : ℝ)*(6971/25000 : ℝ)=(10027502359605449/10000000000000000 : ℝ) by norm_num, show 1+2*(559549200131432409/100000000000000000000 : ℝ)=(50559549200131432409/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (275440676712948416209/275450000000000000000 : ℝ)*(X 1 0+X 2 0)+(6875589786111/1377250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (339/100000 : ℝ)) (hi := (6971/25000 : ℝ)) (c := (275440676712948416209/275450000000000000000 : ℝ)) (alpha := (6875589786111/1377250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (275440676712948416209/275450000000000000000 : ℝ)*(X 0 1+X 2 1)+(6875589786111/1377250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (339/100000 : ℝ)) (hi := (6971/25000 : ℝ)) (c := (275440676712948416209/275450000000000000000 : ℝ)) (alpha := (6875589786111/1377250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (275440676712948416209/275450000000000000000 : ℝ)*(X 0 2+X 1 2)+(6875589786111/1377250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (339/100000 : ℝ)) (hi := (6971/25000 : ℝ)) (c := (275440676712948416209/275450000000000000000 : ℝ)) (alpha := (6875589786111/1377250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-105174409/500000000 : ℝ)*X 0 0+(1426585573/2500000000 : ℝ)*X 0 1+(4998481233/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5420110741/10000000000 : ℝ)*X 1 0+(-2485841031/10000000000 : ℝ)*X 1 1+(4998480933/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2710056167/5000000000 : ℝ)*X 2 0+(2499239741/5000000000 : ℝ)*X 2 1+(-1242920399/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((86379197/200000000 : ℝ)*X 0 0+(3673652201/10000000000 : ℝ)*X 0 1+(5076951271/10000000000 : ℝ)*X 0 2+(86379197/200000000 : ℝ)*X 1 0+(3673652201/10000000000 : ℝ)*X 1 1+(5076951271/10000000000 : ℝ)*X 1 2+(86379197/200000000 : ℝ)*X 2 0+(3673652201/10000000000 : ℝ)*X 2 1+(5076951271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-526079993/2500000000 : ℝ)*X 0 0+(5008212939/10000000000 : ℝ)*X 0 1+(1424104119/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5238792483/10000000000 : ℝ)*X 1 0+(-893952449/5000000000 : ℝ)*X 1 1+(2848208293/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5238792379/10000000000 : ℝ)*X 2 0+(5696416539/10000000000 : ℝ)*X 2 1+(-446976279/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((432060611/1000000000 : ℝ)*X 0 0+(2528829603/5000000000 : ℝ)*X 0 1+(1846664331/5000000000 : ℝ)*X 0 2+(432060611/1000000000 : ℝ)*X 1 0+(2528829603/5000000000 : ℝ)*X 1 1+(1846664331/5000000000 : ℝ)*X 1 2+(432060611/1000000000 : ℝ)*X 2 0+(2528829603/5000000000 : ℝ)*X 2 1+(1846664331/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49787264799208596533229/6886250000000000000000000000 : ℝ) := by norm_num
    linear_combination (365455121/100000000000000 : ℝ)*(base1) + (251877237/20000000000000 : ℝ)*(base19) + (209323773/12500000000000 : ℝ)*(base23) + (1509177/10000000000000 : ℝ)*(upper3) + (103786493/50000000000000 : ℝ)*(upper5) + (53133111931967/5000000000000 : ℝ)*(major0) + (53133111931967/5000000000000 : ℝ)*(major1) + (53133111931967/5000000000000 : ℝ)*(major2) + (353177340498389/25000000000000 : ℝ)*(sp0) + (1412713321325591/100000000000000 : ℝ)*(sp1) + (176589113265199/12500000000000 : ℝ)*(sp2) + (712608065032327/100000000000000 : ℝ)*(sp3) + (5584173341/100000000000000 : ℝ)*(sp4) + (306270253/25000000000000 : ℝ)*(sp7) + (35630482778423/5000000000000 : ℝ)*(f.failure) + (44147330647243/3125000000000 : ℝ)*(f.sum) + (14469059199743/13772500000000000000000000000 : ℝ)*base65 + (8775696026187953103/1377250000000000000000000000000000 : ℝ)*base67 + (4107894699455796897/1377250000000000000000000000000000 : ℝ)*base70 + (4842408507298203103/1377250000000000000000000000000000 : ℝ)*base71 + (67626031806593/13772500000000000000000000000 : ℝ)*base73 + (5833803165543546897/1377250000000000000000000000000000 : ℝ)*base76 + (1721073034870046897/1377250000000000000000000000000000 : ℝ)*base78 + (3597448407778703103/1377250000000000000000000000000000 : ℝ)*base79 + (10505736903671/27545000000000000000000000000 : ℝ)*base81 + (3322779/500000000000000000000 : ℝ)*base90 + (3322779/500000000000000000000 : ℝ)*base92 + (3322779/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (59610492352866604729953/13772500000000000000000000000 : ℝ) := by norm_num
    linear_combination (3103503/10000000000000 : ℝ)*(base1) + (460341021/50000000000000 : ℝ)*(base19) + (872351839/100000000000000 : ℝ)*(base23) + (98154641/100000000000000 : ℝ)*(upper3) + (28226941/25000000000000 : ℝ)*(upper5) + (218601878323459/20000000000000 : ℝ)*(major0) + (218601878323459/20000000000000 : ℝ)*(major1) + (218601878323459/20000000000000 : ℝ)*(major2) + (4246428063/100000000000000 : ℝ)*(sp1) + (460429899/12500000000000 : ℝ)*(sp2) + (1453058546098661/100000000000000 : ℝ)*(sp4) + (726526673976763/50000000000000 : ℝ)*(sp5) + (7265269796363/500000000000 : ℝ)*(sp6) + (183240023215431/25000000000000 : ℝ)*(sp7) + (146592024779351/20000000000000 : ℝ)*(f.failure) + (1453058515063631/100000000000000 : ℝ)*(f.sum) + (8200729179619/13772500000000000000000000000 : ℝ)*base65 + (32613191278943346931/5509000000000000000000000000000000 : ℝ)*base67 + (30499378671465653069/5509000000000000000000000000000000 : ℝ)*base70 + (13617221468078653069/5509000000000000000000000000000000 : ℝ)*base72 + (165369454320463/27545000000000000000000000000 : ℝ)*base73 + (8706706846623346931/5509000000000000000000000000000000 : ℝ)*base75 + (6838065254661653069/5509000000000000000000000000000000 : ℝ)*base78 + (13522218584058346931/5509000000000000000000000000000000 : ℝ)*base79 + (21723887832671/13772500000000000000000000000 : ℝ)*base82 + (16475077/2000000000000000000000 : ℝ)*base89 + (16475077/2000000000000000000000 : ℝ)*base91 + (16475077/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1124_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6971/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1387/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20519/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1124_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1124_s2_0 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-107884651/500000000 : ℝ)*x 0 + (1378566359/2500000000 : ℝ)*x 1 + (206244341/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107884651/500000000 : ℝ)^8317 ≤ (6537065330527/50000000000000 : ℝ)^6269 := by
    have hnat : (107884651 : ℕ)^8317*50000000000000^6269 ≤ 6537065330527^6269*500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107884651 500000000 6537065330527 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1378566359/2500000000 : ℝ)^8317 ≤ (22698914378749/50000000000000 : ℝ)^6269 := by
    have hnat : (1378566359 : ℕ)^8317*50000000000000^6269 ≤ 22698914378749^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378566359 2500000000 22698914378749 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206244341/400000000 : ℝ)^8317 ≤ (10382010140337/25000000000000 : ℝ)^6269 := by
    have hnat : (206244341 : ℕ)^8317*25000000000000^6269 ≤ 10382010140337^6269*400000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206244341 400000000 10382010140337 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107884651/500000000 : ℝ), (1378566359/2500000000 : ℝ), (206244341/400000000 : ℝ)] ![(6537065330527/50000000000000 : ℝ), (22698914378749/50000000000000 : ℝ), (10382010140337/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107884651/500000000 : ℝ)|^8317 ≤ (6537065330527/50000000000000 : ℝ)^6269
        have hw : |(-107884651/500000000 : ℝ)|=(107884651/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1378566359/2500000000 : ℝ)|^8317 ≤ (22698914378749/50000000000000 : ℝ)^6269
        have hw : |(1378566359/2500000000 : ℝ)|=(1378566359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(206244341/400000000 : ℝ)|^8317 ≤ (10382010140337/25000000000000 : ℝ)^6269
        have hw : |(206244341/400000000 : ℝ)|=(206244341/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s2_1 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5374640457/10000000000 : ℝ)*x 0 + (-586007801/2500000000 : ℝ)*x 1 + (2578055043/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374640457/10000000000 : ℝ)^8317 ≤ (5484892554183/12500000000000 : ℝ)^6269 := by
    have hnat : (5374640457 : ℕ)^8317*12500000000000^6269 ≤ 5484892554183^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374640457 10000000000 5484892554183 12500000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (586007801/2500000000 : ℝ)^8317 ≤ (1824100288591/12500000000000 : ℝ)^6269 := by
    have hnat : (586007801 : ℕ)^8317*12500000000000^6269 ≤ 1824100288591^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586007801 2500000000 1824100288591 12500000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2578055043/5000000000 : ℝ)^8317 ≤ (5191007155143/12500000000000 : ℝ)^6269 := by
    have hnat : (2578055043 : ℕ)^8317*12500000000000^6269 ≤ 5191007155143^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2578055043 5000000000 5191007155143 12500000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374640457/10000000000 : ℝ), (-586007801/2500000000 : ℝ), (2578055043/5000000000 : ℝ)] ![(5484892554183/12500000000000 : ℝ), (1824100288591/12500000000000 : ℝ), (5191007155143/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374640457/10000000000 : ℝ)|^8317 ≤ (5484892554183/12500000000000 : ℝ)^6269
        have hw : |(5374640457/10000000000 : ℝ)|=(5374640457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-586007801/2500000000 : ℝ)|^8317 ≤ (1824100288591/12500000000000 : ℝ)^6269
        have hw : |(-586007801/2500000000 : ℝ)|=(586007801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2578055043/5000000000 : ℝ)|^8317 ≤ (5191007155143/12500000000000 : ℝ)^6269
        have hw : |(2578055043/5000000000 : ℝ)|=(2578055043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s2_2 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2687320189/5000000000 : ℝ)*x 0 + (5156110131/10000000000 : ℝ)*x 1 + (-75009/320000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687320189/5000000000 : ℝ)^8317 ≤ (21939569788899/50000000000000 : ℝ)^6269 := by
    have hnat : (2687320189 : ℕ)^8317*50000000000000^6269 ≤ 21939569788899^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687320189 5000000000 21939569788899 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5156110131/10000000000 : ℝ)^8317 ≤ (324437950953/781250000000 : ℝ)^6269 := by
    have hnat : (5156110131 : ℕ)^8317*781250000000^6269 ≤ 324437950953^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5156110131 10000000000 324437950953 781250000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75009/320000 : ℝ)^8317 ≤ (912050168041/6250000000000 : ℝ)^6269 := by
    have hnat : (75009 : ℕ)^8317*6250000000000^6269 ≤ 912050168041^6269*320000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75009 320000 912050168041 6250000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687320189/5000000000 : ℝ), (5156110131/10000000000 : ℝ), (-75009/320000 : ℝ)] ![(21939569788899/50000000000000 : ℝ), (324437950953/781250000000 : ℝ), (912050168041/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687320189/5000000000 : ℝ)|^8317 ≤ (21939569788899/50000000000000 : ℝ)^6269
        have hw : |(2687320189/5000000000 : ℝ)|=(2687320189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5156110131/10000000000 : ℝ)|^8317 ≤ (324437950953/781250000000 : ℝ)^6269
        have hw : |(5156110131/10000000000 : ℝ)|=(5156110131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-75009/320000 : ℝ)|^8317 ≤ (912050168041/6250000000000 : ℝ)^6269
        have hw : |(-75009/320000 : ℝ)|=(75009/320000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s2_3 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4356100147/10000000000 : ℝ)*x 0 + (401548327/1000000000 : ℝ)*x 1 + (4725508527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356100147/10000000000 : ℝ)^8317 ≤ (16602208641907/50000000000000 : ℝ)^6269 := by
    have hnat : (4356100147 : ℕ)^8317*50000000000000^6269 ≤ 16602208641907^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356100147 10000000000 16602208641907 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401548327/1000000000 : ℝ)^8317 ≤ (29804659801567/100000000000000 : ℝ)^6269 := by
    have hnat : (401548327 : ℕ)^8317*100000000000000^6269 ≤ 29804659801567^6269*1000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401548327 1000000000 29804659801567 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4725508527/10000000000 : ℝ)^8317 ≤ (36990922890211/100000000000000 : ℝ)^6269 := by
    have hnat : (4725508527 : ℕ)^8317*100000000000000^6269 ≤ 36990922890211^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4725508527 10000000000 36990922890211 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356100147/10000000000 : ℝ), (401548327/1000000000 : ℝ), (4725508527/10000000000 : ℝ)] ![(16602208641907/50000000000000 : ℝ), (29804659801567/100000000000000 : ℝ), (36990922890211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356100147/10000000000 : ℝ)|^8317 ≤ (16602208641907/50000000000000 : ℝ)^6269
        have hw : |(4356100147/10000000000 : ℝ)|=(4356100147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(401548327/1000000000 : ℝ)|^8317 ≤ (29804659801567/100000000000000 : ℝ)^6269
        have hw : |(401548327/1000000000 : ℝ)|=(401548327/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4725508527/10000000000 : ℝ)|^8317 ≤ (36990922890211/100000000000000 : ℝ)^6269
        have hw : |(4725508527/10000000000 : ℝ)|=(4725508527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s2_4 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2157800741/10000000000 : ℝ)*x 0 + (5158609677/10000000000 : ℝ)*x 1 + (2755869447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157800741/10000000000 : ℝ)^8317 ≤ (817187288527/6250000000000 : ℝ)^6269 := by
    have hnat : (2157800741 : ℕ)^8317*6250000000000^6269 ≤ 817187288527^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157800741 10000000000 817187288527 6250000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5158609677/10000000000 : ℝ)^8317 ≤ (41554768306019/100000000000000 : ℝ)^6269 := by
    have hnat : (5158609677 : ℕ)^8317*100000000000000^6269 ≤ 41554768306019^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5158609677 10000000000 41554768306019 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2755869447/5000000000 : ℝ)^8317 ≤ (45370235062417/100000000000000 : ℝ)^6269 := by
    have hnat : (2755869447 : ℕ)^8317*100000000000000^6269 ≤ 45370235062417^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755869447 5000000000 45370235062417 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2157800741/10000000000 : ℝ), (5158609677/10000000000 : ℝ), (2755869447/5000000000 : ℝ)] ![(817187288527/6250000000000 : ℝ), (41554768306019/100000000000000 : ℝ), (45370235062417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2157800741/10000000000 : ℝ)|^8317 ≤ (817187288527/6250000000000 : ℝ)^6269
        have hw : |(-2157800741/10000000000 : ℝ)|=(2157800741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5158609677/10000000000 : ℝ)|^8317 ≤ (41554768306019/100000000000000 : ℝ)^6269
        have hw : |(5158609677/10000000000 : ℝ)|=(5158609677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2755869447/5000000000 : ℝ)|^8317 ≤ (45370235062417/100000000000000 : ℝ)^6269
        have hw : |(2755869447/5000000000 : ℝ)|=(2755869447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s2_5 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5283876379/10000000000 : ℝ)*x 0 + (-248550093/1250000000 : ℝ)*x 1 + (2755869713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5283876379/10000000000 : ℝ)^8317 ≤ (42898777454629/100000000000000 : ℝ)^6269 := by
    have hnat : (5283876379 : ℕ)^8317*100000000000000^6269 ≤ 42898777454629^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283876379 10000000000 42898777454629 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (248550093/1250000000 : ℝ)^8317 ≤ (11730981663289/100000000000000 : ℝ)^6269 := by
    have hnat : (248550093 : ℕ)^8317*100000000000000^6269 ≤ 11730981663289^6269*1250000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248550093 1250000000 11730981663289 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2755869713/5000000000 : ℝ)^8317 ≤ (9074048174447/20000000000000 : ℝ)^6269 := by
    have hnat : (2755869713 : ℕ)^8317*20000000000000^6269 ≤ 9074048174447^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755869713 5000000000 9074048174447 20000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5283876379/10000000000 : ℝ), (-248550093/1250000000 : ℝ), (2755869713/5000000000 : ℝ)] ![(42898777454629/100000000000000 : ℝ), (11730981663289/100000000000000 : ℝ), (9074048174447/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5283876379/10000000000 : ℝ)|^8317 ≤ (42898777454629/100000000000000 : ℝ)^6269
        have hw : |(5283876379/10000000000 : ℝ)|=(5283876379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-248550093/1250000000 : ℝ)|^8317 ≤ (11730981663289/100000000000000 : ℝ)^6269
        have hw : |(-248550093/1250000000 : ℝ)|=(248550093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2755869713/5000000000 : ℝ)|^8317 ≤ (9074048174447/20000000000000 : ℝ)^6269
        have hw : |(2755869713/5000000000 : ℝ)|=(2755869713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s2_6 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5283875187/10000000000 : ℝ)*x 0 + (5511739313/10000000000 : ℝ)*x 1 + (-1988402541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5283875187/10000000000 : ℝ)^8317 ≤ (2144938230773/5000000000000 : ℝ)^6269 := by
    have hnat : (5283875187 : ℕ)^8317*5000000000000^6269 ≤ 2144938230773^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283875187 10000000000 2144938230773 5000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5511739313/10000000000 : ℝ)^8317 ≤ (22685119819097/50000000000000 : ℝ)^6269 := by
    have hnat : (5511739313 : ℕ)^8317*50000000000000^6269 ≤ 22685119819097^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511739313 10000000000 22685119819097 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1988402541/10000000000 : ℝ)^8317 ≤ (2932748932131/25000000000000 : ℝ)^6269 := by
    have hnat : (1988402541 : ℕ)^8317*25000000000000^6269 ≤ 2932748932131^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988402541 10000000000 2932748932131 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5283875187/10000000000 : ℝ), (5511739313/10000000000 : ℝ), (-1988402541/10000000000 : ℝ)] ![(2144938230773/5000000000000 : ℝ), (22685119819097/50000000000000 : ℝ), (2932748932131/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5283875187/10000000000 : ℝ)|^8317 ≤ (2144938230773/5000000000000 : ℝ)^6269
        have hw : |(5283875187/10000000000 : ℝ)|=(5283875187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5511739313/10000000000 : ℝ)|^8317 ≤ (22685119819097/50000000000000 : ℝ)^6269
        have hw : |(5511739313/10000000000 : ℝ)|=(5511739313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1988402541/10000000000 : ℝ)|^8317 ≤ (2932748932131/25000000000000 : ℝ)^6269
        have hw : |(-1988402541/10000000000 : ℝ)|=(1988402541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s2_7 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089078321/2500000000 : ℝ)*x 0 + (2360275659/5000000000 : ℝ)*x 1 + (804098099/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089078321/2500000000 : ℝ)^8317 ≤ (33206572688181/100000000000000 : ℝ)^6269 := by
    have hnat : (1089078321 : ℕ)^8317*100000000000000^6269 ≤ 33206572688181^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089078321 2500000000 33206572688181 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2360275659/5000000000 : ℝ)^8317 ≤ (36939450085251/100000000000000 : ℝ)^6269 := by
    have hnat : (2360275659 : ℕ)^8317*100000000000000^6269 ≤ 36939450085251^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2360275659 5000000000 36939450085251 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (804098099/2000000000 : ℝ)^8317 ≤ (29853977217469/100000000000000 : ℝ)^6269 := by
    have hnat : (804098099 : ℕ)^8317*100000000000000^6269 ≤ 29853977217469^6269*2000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804098099 2000000000 29853977217469 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089078321/2500000000 : ℝ), (2360275659/5000000000 : ℝ), (804098099/2000000000 : ℝ)] ![(33206572688181/100000000000000 : ℝ), (36939450085251/100000000000000 : ℝ), (29853977217469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089078321/2500000000 : ℝ)|^8317 ≤ (33206572688181/100000000000000 : ℝ)^6269
        have hw : |(1089078321/2500000000 : ℝ)|=(1089078321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2360275659/5000000000 : ℝ)|^8317 ≤ (36939450085251/100000000000000 : ℝ)^6269
        have hw : |(2360275659/5000000000 : ℝ)|=(2360275659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(804098099/2000000000 : ℝ)|^8317 ≤ (29853977217469/100000000000000 : ℝ)^6269
        have hw : |(804098099/2000000000 : ℝ)|=(804098099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1124_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20519/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1387/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2247/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16557/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20519/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1387/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20519/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1387/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20519/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1387/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20519/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1387/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20519/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1387/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20519/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1387/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1387/25000 : ℝ) ^ (2079/512 : ℝ) ≤ (198814110757099/25000000000000000000 : ℝ) := by
    have hpowers : (1387/25000 : ℝ)^2079 ≤ (198814110757099/25000000000000000000 : ℝ)^512 := by
      have hnat : (1387 : ℕ)^2079*25000000000000000000^512 ≤ 198814110757099^512*25000^2079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1387 25000 198814110757099 25000000000000000000 2079 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1387/25000 : ℝ)) (X := (198814110757099/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hpowhi : (20519/100000 : ℝ) ^ (2079/512 : ℝ) ≤ (161056394613537687/100000000000000000000 : ℝ) := by
    have hpowers : (20519/100000 : ℝ)^2079 ≤ (161056394613537687/100000000000000000000 : ℝ)^512 := by
      have hnat : (20519 : ℕ)^2079*100000000000000000000^512 ≤ 161056394613537687^512*100000^2079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20519 100000 161056394613537687 100000000000000000000 2079 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20519/100000 : ℝ)) (X := (161056394613537687/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500198814110757099/12500000000000000000 : ℝ) ≤ (10000039169683333/10000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (12500198814110757099/12500000000000000000 : ℝ)^512 ≤ (10000039169683333/10000000000000000 : ℝ)^2079 := by
      have hnat : (12500198814110757099 : ℕ)^512*10000000000000000^2079 ≤ 10000039169683333^2079*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500198814110757099 12500000000000000000 10000039169683333 10000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000039169683333/10000000000000000 : ℝ)) (X := (12500198814110757099/12500000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100161851651056566083/100000000000000000000 : ℝ) ≤ (5001991763994353/5000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (100161851651056566083/100000000000000000000 : ℝ)^512 ≤ (5001991763994353/5000000000000000 : ℝ)^2079 := by
      have hnat : (100161851651056566083 : ℕ)^512*5000000000000000^2079 ≤ 5001991763994353^2079*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100161851651056566083 100000000000000000000 5001991763994353 5000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001991763994353/5000000000000000 : ℝ)) (X := (100161851651056566083/100000000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50161056394613537687/50000000000000000000 : ℝ) ≤ (10007927886294079/10000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (50161056394613537687/50000000000000000000 : ℝ)^512 ≤ (10007927886294079/10000000000000000 : ℝ)^2079 := by
      have hnat : (50161056394613537687 : ℕ)^512*10000000000000000^2079 ≤ 10007927886294079^2079*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50161056394613537687 50000000000000000000 10007927886294079 10000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007927886294079/10000000000000000 : ℝ)) (X := (50161056394613537687/50000000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(198814110757099/25000000000000000000 : ℝ) ≤ ((29933363961914551907/29942000000000000000 : ℝ)+2*(3944358305373/1497100000000000 : ℝ)*(1387/25000 : ℝ))^(2079/512 : ℝ) := by
    rw [show (29933363961914551907/29942000000000000000 : ℝ)+2*(3944358305373/1497100000000000 : ℝ)*(1387/25000 : ℝ)=(10000039169683333/10000000000000000 : ℝ) by norm_num, show 1+2*(198814110757099/25000000000000000000 : ℝ)=(12500198814110757099/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(161056394613537687/100000000000000000000 : ℝ)+(198814110757099/25000000000000000000 : ℝ) ≤ ((29933363961914551907/29942000000000000000 : ℝ)+(3944358305373/1497100000000000 : ℝ)*((20519/100000 : ℝ)+(1387/25000 : ℝ)))^(2079/512 : ℝ) := by
    rw [show (29933363961914551907/29942000000000000000 : ℝ)+(3944358305373/1497100000000000 : ℝ)*((20519/100000 : ℝ)+(1387/25000 : ℝ))=(5001991763994353/5000000000000000 : ℝ) by norm_num, show 1+(161056394613537687/100000000000000000000 : ℝ)+(198814110757099/25000000000000000000 : ℝ)=(100161851651056566083/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(161056394613537687/100000000000000000000 : ℝ) ≤ ((29933363961914551907/29942000000000000000 : ℝ)+2*(3944358305373/1497100000000000 : ℝ)*(20519/100000 : ℝ))^(2079/512 : ℝ) := by
    rw [show (29933363961914551907/29942000000000000000 : ℝ)+2*(3944358305373/1497100000000000 : ℝ)*(20519/100000 : ℝ)=(10007927886294079/10000000000000000 : ℝ) by norm_num, show 1+2*(161056394613537687/100000000000000000000 : ℝ)=(50161056394613537687/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29933363961914551907/29942000000000000000 : ℝ)*(X 1 0+X 2 0)+(3944358305373/1497100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (1387/25000 : ℝ)) (hi := (20519/100000 : ℝ)) (c := (29933363961914551907/29942000000000000000 : ℝ)) (alpha := (3944358305373/1497100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29933363961914551907/29942000000000000000 : ℝ)*(X 0 1+X 2 1)+(3944358305373/1497100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (1387/25000 : ℝ)) (hi := (20519/100000 : ℝ)) (c := (29933363961914551907/29942000000000000000 : ℝ)) (alpha := (3944358305373/1497100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29933363961914551907/29942000000000000000 : ℝ)*(X 0 2+X 1 2)+(3944358305373/1497100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (1387/25000 : ℝ)) (hi := (20519/100000 : ℝ)) (c := (29933363961914551907/29942000000000000000 : ℝ)) (alpha := (3944358305373/1497100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-107884651/500000000 : ℝ)*X 0 0+(1378566359/2500000000 : ℝ)*X 0 1+(206244341/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5374640457/10000000000 : ℝ)*X 1 0+(-586007801/2500000000 : ℝ)*X 1 1+(2578055043/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2687320189/5000000000 : ℝ)*X 2 0+(5156110131/10000000000 : ℝ)*X 2 1+(-75009/320000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4356100147/10000000000 : ℝ)*X 0 0+(401548327/1000000000 : ℝ)*X 0 1+(4725508527/10000000000 : ℝ)*X 0 2+(4356100147/10000000000 : ℝ)*X 1 0+(401548327/1000000000 : ℝ)*X 1 1+(4725508527/10000000000 : ℝ)*X 1 2+(4356100147/10000000000 : ℝ)*X 2 0+(401548327/1000000000 : ℝ)*X 2 1+(4725508527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2157800741/10000000000 : ℝ)*X 0 0+(5158609677/10000000000 : ℝ)*X 0 1+(2755869447/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5283876379/10000000000 : ℝ)*X 1 0+(-248550093/1250000000 : ℝ)*X 1 1+(2755869713/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5283875187/10000000000 : ℝ)*X 2 0+(5511739313/10000000000 : ℝ)*X 2 1+(-1988402541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089078321/2500000000 : ℝ)*X 0 0+(2360275659/5000000000 : ℝ)*X 0 1+(804098099/2000000000 : ℝ)*X 0 2+(1089078321/2500000000 : ℝ)*X 1 0+(2360275659/5000000000 : ℝ)*X 1 1+(804098099/2000000000 : ℝ)*X 1 2+(1089078321/2500000000 : ℝ)*X 2 0+(2360275659/5000000000 : ℝ)*X 2 1+(804098099/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (521329765913144448148754457/68050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (723817031/100000000000000 : ℝ)*(base19) + (427988263/100000000000000 : ℝ)*(base23) + (11098439/100000000000000 : ℝ)*(upper2) + (46506697/20000000000000 : ℝ)*(upper3) + (14803813/10000000000000 : ℝ)*(upper4) + (2100258273814613/100000000000000 : ℝ)*(major0) + (2100258273814613/100000000000000 : ℝ)*(major1) + (2100258273814613/100000000000000 : ℝ)*(major2) + (349011315843681/12500000000000 : ℝ)*(sp0) + (87253293085853/3125000000000 : ℝ)*(sp1) + (43626651165251/1562500000000 : ℝ)*(sp2) + (704202148090151/50000000000000 : ℝ)*(sp3) + (97348843/625000000000 : ℝ)*(sp4) + (117870371/2000000000000 : ℝ)*(sp7) + (1408410189698853/100000000000000 : ℝ)*(f.failure) + (349013262820541/12500000000000 : ℝ)*(f.sum) + (11809061780089/6805000000000000000000000000 : ℝ)*base65 + (422628062823545181/272200000000000000000000000000000 : ℝ)*base67 + (417065711352345181/272200000000000000000000000000000 : ℝ)*base69 + (1579176645419945181/272200000000000000000000000000000 : ℝ)*base71 + (17082742823979/6805000000000000000000000000 : ℝ)*base73 + (2121298877453145181/272200000000000000000000000000000 : ℝ)*base75 + (202578660404054819/272200000000000000000000000000000 : ℝ)*base78 + (5579884064052345181/272200000000000000000000000000000 : ℝ)*base79 + (1405755730839/6805000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1753169/10000000000000000000000 : ℝ)*base90 + (1753169/10000000000000000000000 : ℝ)*base92 + (1753169/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (729170106641484102616351389/74855000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1792933071/100000000000000 : ℝ)*(base19) + (1296545161/100000000000000 : ℝ)*(base23) + (5160609/2500000000000 : ℝ)*(upper2) + (119025529/100000000000000 : ℝ)*(upper3) + (34233799/12500000000000 : ℝ)*(upper5) + (106506643063091/5000000000000 : ℝ)*(major0) + (106506643063091/5000000000000 : ℝ)*(major1) + (106506643063091/5000000000000 : ℝ)*(major2) + (11758625749/50000000000000 : ℝ)*(sp1) + (4533431447/50000000000000 : ℝ)*(sp2) + (1415910818530501/50000000000000 : ℝ)*(sp4) + (176987270429777/6250000000000 : ℝ)*(sp5) + (1415905636826473/50000000000000 : ℝ)*(sp6) + (1428443760759271/100000000000000 : ℝ)*(sp7) + (1428443760759271/100000000000000 : ℝ)*(f.failure) + (1415910818530501/50000000000000 : ℝ)*(f.sum) + (93076379491/59884000000000000000000000 : ℝ)*base65 + (71593211041495463/149710000000000000000000000000000 : ℝ)*base68 + (25620168874794537/149710000000000000000000000000000 : ℝ)*base69 + (264127759234844537/149710000000000000000000000000000 : ℝ)*base71 + (25246879063467/7485500000000000000000000000 : ℝ)*base73 + (116155960454325463/149710000000000000000000000000000 : ℝ)*base76 + (322525061085644537/149710000000000000000000000000000 : ℝ)*base77 + (1280089145627324537/149710000000000000000000000000000 : ℝ)*base79 + (40440796286683/14971000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (6124917/10000000000000000000000 : ℝ)*base89 + (6124917/10000000000000000000000 : ℝ)*base91 + (6124917/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1124_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20519/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1387/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2247/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16557/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1124_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1124_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2247/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16557/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1124_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1124_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1124_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2247/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16557/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1124_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

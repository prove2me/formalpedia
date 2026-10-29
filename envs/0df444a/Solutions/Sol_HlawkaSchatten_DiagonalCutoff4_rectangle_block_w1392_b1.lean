-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1392_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:26:19.204251+00:00
-- url     : https://prove2.me/submissions/3eb4a4c1-b48d-4444-8773-079ee835edcb

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
theorem support_rectangle_w1392_s3_0 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1000117919/5000000000 : ℝ)*x 0 + (5421205679/10000000000 : ℝ)*x 1 + (5235804947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1000117919/5000000000 : ℝ)^17 ≤ (12190717492513/100000000000000 : ℝ)^13 := by
    have hnat : (1000117919 : ℕ)^17*100000000000000^13 ≤ 12190717492513^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000117919 5000000000 12190717492513 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421205679/10000000000 : ℝ)^17 ≤ (8980680155307/20000000000000 : ℝ)^13 := by
    have hnat : (5421205679 : ℕ)^17*20000000000000^13 ≤ 8980680155307^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421205679 10000000000 8980680155307 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5235804947/10000000000 : ℝ)^17 ≤ (8581176343099/20000000000000 : ℝ)^13 := by
    have hnat : (5235804947 : ℕ)^17*20000000000000^13 ≤ 8581176343099^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235804947 10000000000 8581176343099 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1000117919/5000000000 : ℝ), (5421205679/10000000000 : ℝ), (5235804947/10000000000 : ℝ)] ![(12190717492513/100000000000000 : ℝ), (8980680155307/20000000000000 : ℝ), (8581176343099/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1000117919/5000000000 : ℝ)|^17 ≤ (12190717492513/100000000000000 : ℝ)^13
        have hw : |(-1000117919/5000000000 : ℝ)|=(1000117919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5421205679/10000000000 : ℝ)|^17 ≤ (8980680155307/20000000000000 : ℝ)^13
        have hw : |(5421205679/10000000000 : ℝ)|=(5421205679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5235804947/10000000000 : ℝ)|^17 ≤ (8581176343099/20000000000000 : ℝ)^13
        have hw : |(5235804947/10000000000 : ℝ)|=(5235804947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s3_1 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5350924393/10000000000 : ℝ)*x 0 + (-523719721/2500000000 : ℝ)*x 1 + (5235804991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350924393/10000000000 : ℝ)^17 ≤ (22071835674617/50000000000000 : ℝ)^13 := by
    have hnat : (5350924393 : ℕ)^17*50000000000000^13 ≤ 22071835674617^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350924393 10000000000 22071835674617 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523719721/2500000000 : ℝ)^17 ≤ (3237611612779/25000000000000 : ℝ)^13 := by
    have hnat : (523719721 : ℕ)^17*25000000000000^13 ≤ 3237611612779^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523719721 2500000000 3237611612779 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5235804991/10000000000 : ℝ)^17 ≤ (8581176437401/20000000000000 : ℝ)^13 := by
    have hnat : (5235804991 : ℕ)^17*20000000000000^13 ≤ 8581176437401^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235804991 10000000000 8581176437401 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350924393/10000000000 : ℝ), (-523719721/2500000000 : ℝ), (5235804991/10000000000 : ℝ)] ![(22071835674617/50000000000000 : ℝ), (3237611612779/25000000000000 : ℝ), (8581176437401/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350924393/10000000000 : ℝ)|^17 ≤ (22071835674617/50000000000000 : ℝ)^13
        have hw : |(5350924393/10000000000 : ℝ)|=(5350924393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-523719721/2500000000 : ℝ)|^17 ≤ (3237611612779/25000000000000 : ℝ)^13
        have hw : |(-523719721/2500000000 : ℝ)|=(523719721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5235804991/10000000000 : ℝ)|^17 ≤ (8581176437401/20000000000000 : ℝ)^13
        have hw : |(5235804991/10000000000 : ℝ)|=(5235804991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s3_2 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1337731111/2500000000 : ℝ)*x 0 + (327237809/625000000 : ℝ)*x 1 + (-1047439439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337731111/2500000000 : ℝ)^17 ≤ (11035917974857/25000000000000 : ℝ)^13 := by
    have hnat : (1337731111 : ℕ)^17*25000000000000^13 ≤ 11035917974857^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337731111 2500000000 11035917974857 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327237809/625000000 : ℝ)^17 ≤ (21452940841673/50000000000000 : ℝ)^13 := by
    have hnat : (327237809 : ℕ)^17*50000000000000^13 ≤ 21452940841673^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327237809 625000000 21452940841673 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047439439/5000000000 : ℝ)^17 ≤ (3237611600653/25000000000000 : ℝ)^13 := by
    have hnat : (1047439439 : ℕ)^17*25000000000000^13 ≤ 3237611600653^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047439439 5000000000 3237611600653 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337731111/2500000000 : ℝ), (327237809/625000000 : ℝ), (-1047439439/5000000000 : ℝ)] ![(11035917974857/25000000000000 : ℝ), (21452940841673/50000000000000 : ℝ), (3237611600653/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337731111/2500000000 : ℝ)|^17 ≤ (11035917974857/25000000000000 : ℝ)^13
        have hw : |(1337731111/2500000000 : ℝ)|=(1337731111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327237809/625000000 : ℝ)|^17 ≤ (21452940841673/50000000000000 : ℝ)^13
        have hw : |(327237809/625000000 : ℝ)|=(327237809/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1047439439/5000000000 : ℝ)|^17 ≤ (3237611600653/25000000000000 : ℝ)^13
        have hw : |(-1047439439/5000000000 : ℝ)|=(1047439439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s3_3 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4312913723/10000000000 : ℝ)*x 0 + (823846633/2000000000 : ℝ)*x 1 + (4514885409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312913723/10000000000 : ℝ)^17 ≤ (1331841481559/4000000000000 : ℝ)^13 := by
    have hnat : (4312913723 : ℕ)^17*4000000000000^13 ≤ 1331841481559^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312913723 10000000000 1331841481559 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (823846633/2000000000 : ℝ)^17 ≤ (3135438863811/10000000000000 : ℝ)^13 := by
    have hnat : (823846633 : ℕ)^17*10000000000000^13 ≤ 3135438863811^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823846633 2000000000 3135438863811 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4514885409/10000000000 : ℝ)^17 ≤ (7069914859581/20000000000000 : ℝ)^13 := by
    have hnat : (4514885409 : ℕ)^17*20000000000000^13 ≤ 7069914859581^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514885409 10000000000 7069914859581 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312913723/10000000000 : ℝ), (823846633/2000000000 : ℝ), (4514885409/10000000000 : ℝ)] ![(1331841481559/4000000000000 : ℝ), (3135438863811/10000000000000 : ℝ), (7069914859581/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312913723/10000000000 : ℝ)|^17 ≤ (1331841481559/4000000000000 : ℝ)^13
        have hw : |(4312913723/10000000000 : ℝ)|=(4312913723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(823846633/2000000000 : ℝ)|^17 ≤ (3135438863811/10000000000000 : ℝ)^13
        have hw : |(823846633/2000000000 : ℝ)|=(823846633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4514885409/10000000000 : ℝ)|^17 ≤ (7069914859581/20000000000000 : ℝ)^13
        have hw : |(4514885409/10000000000 : ℝ)|=(4514885409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s3_4 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-250031657/1250000000 : ℝ)*x 0 + (2618278691/5000000000 : ℝ)*x 1 + (677556051/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (250031657/1250000000 : ℝ)^17 ≤ (609542815633/5000000000000 : ℝ)^13 := by
    have hnat : (250031657 : ℕ)^17*5000000000000^13 ≤ 609542815633^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250031657 1250000000 609542815633 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2618278691/5000000000 : ℝ)^17 ≤ (42913945103001/100000000000000 : ℝ)^13 := by
    have hnat : (2618278691 : ℕ)^17*100000000000000^13 ≤ 42913945103001^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618278691 5000000000 42913945103001 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677556051/1250000000 : ℝ)^17 ≤ (44895198566043/100000000000000 : ℝ)^13 := by
    have hnat : (677556051 : ℕ)^17*100000000000000^13 ≤ 44895198566043^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677556051 1250000000 44895198566043 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-250031657/1250000000 : ℝ), (2618278691/5000000000 : ℝ), (677556051/1250000000 : ℝ)] ![(609542815633/5000000000000 : ℝ), (42913945103001/100000000000000 : ℝ), (44895198566043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-250031657/1250000000 : ℝ)|^17 ≤ (609542815633/5000000000000 : ℝ)^13
        have hw : |(-250031657/1250000000 : ℝ)|=(250031657/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2618278691/5000000000 : ℝ)|^17 ≤ (42913945103001/100000000000000 : ℝ)^13
        have hw : |(2618278691/5000000000 : ℝ)|=(2618278691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677556051/1250000000 : ℝ)|^17 ≤ (44895198566043/100000000000000 : ℝ)^13
        have hw : |(677556051/1250000000 : ℝ)|=(677556051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s3_5 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2651452997/5000000000 : ℝ)*x 0 + (-15281879/80000000 : ℝ)*x 1 + (338778057/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651452997/5000000000 : ℝ)^17 ≤ (8725272088681/20000000000000 : ℝ)^13 := by
    have hnat : (2651452997 : ℕ)^17*20000000000000^13 ≤ 8725272088681^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651452997 5000000000 8725272088681 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15281879/80000000 : ℝ)^17 ≤ (2295687103421/20000000000000 : ℝ)^13 := by
    have hnat : (15281879 : ℕ)^17*20000000000000^13 ≤ 2295687103421^13*80000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15281879 80000000 2295687103421 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338778057/625000000 : ℝ)^17 ≤ (5611900503111/12500000000000 : ℝ)^13 := by
    have hnat : (338778057 : ℕ)^17*12500000000000^13 ≤ 5611900503111^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338778057 625000000 5611900503111 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651452997/5000000000 : ℝ), (-15281879/80000000 : ℝ), (338778057/625000000 : ℝ)] ![(8725272088681/20000000000000 : ℝ), (2295687103421/20000000000000 : ℝ), (5611900503111/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651452997/5000000000 : ℝ)|^17 ≤ (8725272088681/20000000000000 : ℝ)^13
        have hw : |(2651452997/5000000000 : ℝ)|=(2651452997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15281879/80000000 : ℝ)|^17 ≤ (2295687103421/20000000000000 : ℝ)^13
        have hw : |(-15281879/80000000 : ℝ)|=(15281879/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338778057/625000000 : ℝ)|^17 ≤ (5611900503111/12500000000000 : ℝ)^13
        have hw : |(338778057/625000000 : ℝ)|=(338778057/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s3_6 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5302907097/10000000000 : ℝ)*x 0 + (2710224009/5000000000 : ℝ)*x 1 + (-955117299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302907097/10000000000 : ℝ)^17 ≤ (1363324134679/3125000000000 : ℝ)^13 := by
    have hnat : (5302907097 : ℕ)^17*3125000000000^13 ≤ 1363324134679^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302907097 10000000000 1363324134679 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2710224009/5000000000 : ℝ)^17 ≤ (2805949646371/6250000000000 : ℝ)^13 := by
    have hnat : (2710224009 : ℕ)^17*6250000000000^13 ≤ 2805949646371^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710224009 5000000000 2805949646371 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (955117299/5000000000 : ℝ)^17 ≤ (11478433340491/100000000000000 : ℝ)^13 := by
    have hnat : (955117299 : ℕ)^17*100000000000000^13 ≤ 11478433340491^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955117299 5000000000 11478433340491 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302907097/10000000000 : ℝ), (2710224009/5000000000 : ℝ), (-955117299/5000000000 : ℝ)] ![(1363324134679/3125000000000 : ℝ), (2805949646371/6250000000000 : ℝ), (11478433340491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302907097/10000000000 : ℝ)|^17 ≤ (1363324134679/3125000000000 : ℝ)^13
        have hw : |(5302907097/10000000000 : ℝ)|=(5302907097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2710224009/5000000000 : ℝ)|^17 ≤ (2805949646371/6250000000000 : ℝ)^13
        have hw : |(2710224009/5000000000 : ℝ)|=(2710224009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-955117299/5000000000 : ℝ)|^17 ≤ (11478433340491/100000000000000 : ℝ)^13
        have hw : |(-955117299/5000000000 : ℝ)|=(955117299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s3_7 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4312950979/10000000000 : ℝ)*x 0 + (4513279273/10000000000 : ℝ)*x 1 + (2060423649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312950979/10000000000 : ℝ)^17 ≤ (33296413157/100000000000 : ℝ)^13 := by
    have hnat : (4312950979 : ℕ)^17*100000000000^13 ≤ 33296413157^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312950979 10000000000 33296413157 100000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4513279273/10000000000 : ℝ)^17 ≤ (35333130521219/100000000000000 : ℝ)^13 := by
    have hnat : (4513279273 : ℕ)^17*100000000000000^13 ≤ 35333130521219^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513279273 10000000000 35333130521219 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2060423649/5000000000 : ℝ)^17 ≤ (1960653519539/6250000000000 : ℝ)^13 := by
    have hnat : (2060423649 : ℕ)^17*6250000000000^13 ≤ 1960653519539^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060423649 5000000000 1960653519539 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312950979/10000000000 : ℝ), (4513279273/10000000000 : ℝ), (2060423649/5000000000 : ℝ)] ![(33296413157/100000000000 : ℝ), (35333130521219/100000000000000 : ℝ), (1960653519539/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312950979/10000000000 : ℝ)|^17 ≤ (33296413157/100000000000 : ℝ)^13
        have hw : |(4312950979/10000000000 : ℝ)|=(4312950979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4513279273/10000000000 : ℝ)|^17 ≤ (35333130521219/100000000000000 : ℝ)^13
        have hw : |(4513279273/10000000000 : ℝ)|=(4513279273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2060423649/5000000000 : ℝ)|^17 ≤ (1960653519539/6250000000000 : ℝ)^13
        have hw : |(2060423649/5000000000 : ℝ)|=(2060423649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1392_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (199/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10161/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2761/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14969/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (199/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10161/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (199/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10161/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (199/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10161/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (199/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10161/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (199/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10161/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (199/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10161/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10161/100000 : ℝ) ^ (4351/1024 : ℝ) ≤ (3015919263604569/50000000000000000000 : ℝ) := by
    have hpowers : (10161/100000 : ℝ)^4351 ≤ (3015919263604569/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10161 : ℕ)^4351*50000000000000000000^1024 ≤ 3015919263604569^1024*100000^4351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10161 100000 3015919263604569 50000000000000000000 4351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10161/100000 : ℝ)) (X := (3015919263604569/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (199/1250 : ℝ) ^ (4351/1024 : ℝ) ≤ (40647830595523937/100000000000000000000 : ℝ) := by
    have hpowers : (199/1250 : ℝ)^4351 ≤ (40647830595523937/100000000000000000000 : ℝ)^1024 := by
      have hnat : (199 : ℕ)^4351*100000000000000000000^1024 ≤ 40647830595523937^1024*1250^4351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        199 1250 40647830595523937 100000000000000000000 4351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (199/1250 : ℝ)) (X := (40647830595523937/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003015919263604569/25000000000000000000 : ℝ) ≤ (10000283903368943/10000000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (25003015919263604569/25000000000000000000 : ℝ)^1024 ≤ (10000283903368943/10000000000000000 : ℝ)^4351 := by
      have hnat : (25003015919263604569 : ℕ)^1024*10000000000000000^4351 ≤ 10000283903368943^4351*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003015919263604569 25000000000000000000 10000283903368943 10000000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283903368943/10000000000000000 : ℝ)) (X := (25003015919263604569/25000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001867186764909323/4000000000000000000 : ℝ) ≤ (10001098401579729/10000000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (4001867186764909323/4000000000000000000 : ℝ)^1024 ≤ (10001098401579729/10000000000000000 : ℝ)^4351 := by
      have hnat : (4001867186764909323 : ℕ)^1024*10000000000000000^4351 ≤ 10001098401579729^4351*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001867186764909323 4000000000000000000 10001098401579729 10000000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001098401579729/10000000000000000 : ℝ)) (X := (4001867186764909323/4000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50040647830595523937/50000000000000000000 : ℝ) ≤ (2000382579958103/2000000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (50040647830595523937/50000000000000000000 : ℝ)^1024 ≤ (2000382579958103/2000000000000000 : ℝ)^4351 := by
      have hnat : (50040647830595523937 : ℕ)^1024*2000000000000000^4351 ≤ 2000382579958103^4351*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50040647830595523937 50000000000000000000 2000382579958103 2000000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000382579958103/2000000000000000 : ℝ)) (X := (50040647830595523937/50000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3015919263604569/50000000000000000000 : ℝ) ≤ ((885770504105571533/886000000000000000 : ℝ)+2*(31326854261/22150000000000 : ℝ)*(10161/100000 : ℝ))^(4351/1024 : ℝ) := by
    rw [show (885770504105571533/886000000000000000 : ℝ)+2*(31326854261/22150000000000 : ℝ)*(10161/100000 : ℝ)=(10000283903368943/10000000000000000 : ℝ) by norm_num, show 1+2*(3015919263604569/50000000000000000000 : ℝ)=(25003015919263604569/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(40647830595523937/100000000000000000000 : ℝ)+(3015919263604569/50000000000000000000 : ℝ) ≤ ((885770504105571533/886000000000000000 : ℝ)+(31326854261/22150000000000 : ℝ)*((199/1250 : ℝ)+(10161/100000 : ℝ)))^(4351/1024 : ℝ) := by
    rw [show (885770504105571533/886000000000000000 : ℝ)+(31326854261/22150000000000 : ℝ)*((199/1250 : ℝ)+(10161/100000 : ℝ))=(10001098401579729/10000000000000000 : ℝ) by norm_num, show 1+(40647830595523937/100000000000000000000 : ℝ)+(3015919263604569/50000000000000000000 : ℝ)=(4001867186764909323/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(40647830595523937/100000000000000000000 : ℝ) ≤ ((885770504105571533/886000000000000000 : ℝ)+2*(31326854261/22150000000000 : ℝ)*(199/1250 : ℝ))^(4351/1024 : ℝ) := by
    rw [show (885770504105571533/886000000000000000 : ℝ)+2*(31326854261/22150000000000 : ℝ)*(199/1250 : ℝ)=(2000382579958103/2000000000000000 : ℝ) by norm_num, show 1+2*(40647830595523937/100000000000000000000 : ℝ)=(50040647830595523937/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (885770504105571533/886000000000000000 : ℝ)*(X 1 0+X 2 0)+(31326854261/22150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (10161/100000 : ℝ)) (hi := (199/1250 : ℝ)) (c := (885770504105571533/886000000000000000 : ℝ)) (alpha := (31326854261/22150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (885770504105571533/886000000000000000 : ℝ)*(X 0 1+X 2 1)+(31326854261/22150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (10161/100000 : ℝ)) (hi := (199/1250 : ℝ)) (c := (885770504105571533/886000000000000000 : ℝ)) (alpha := (31326854261/22150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (885770504105571533/886000000000000000 : ℝ)*(X 0 2+X 1 2)+(31326854261/22150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (10161/100000 : ℝ)) (hi := (199/1250 : ℝ)) (c := (885770504105571533/886000000000000000 : ℝ)) (alpha := (31326854261/22150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1000117919/5000000000 : ℝ)*X 0 0+(5421205679/10000000000 : ℝ)*X 0 1+(5235804947/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350924393/10000000000 : ℝ)*X 1 0+(-523719721/2500000000 : ℝ)*X 1 1+(5235804991/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337731111/2500000000 : ℝ)*X 2 0+(327237809/625000000 : ℝ)*X 2 1+(-1047439439/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4312913723/10000000000 : ℝ)*X 0 0+(823846633/2000000000 : ℝ)*X 0 1+(4514885409/10000000000 : ℝ)*X 0 2+(4312913723/10000000000 : ℝ)*X 1 0+(823846633/2000000000 : ℝ)*X 1 1+(4514885409/10000000000 : ℝ)*X 1 2+(4312913723/10000000000 : ℝ)*X 2 0+(823846633/2000000000 : ℝ)*X 2 1+(4514885409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-250031657/1250000000 : ℝ)*X 0 0+(2618278691/5000000000 : ℝ)*X 0 1+(677556051/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651452997/5000000000 : ℝ)*X 1 0+(-15281879/80000000 : ℝ)*X 1 1+(338778057/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302907097/10000000000 : ℝ)*X 2 0+(2710224009/5000000000 : ℝ)*X 2 1+(-955117299/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4312950979/10000000000 : ℝ)*X 0 0+(4513279273/10000000000 : ℝ)*X 0 1+(2060423649/5000000000 : ℝ)*X 0 2+(4312950979/10000000000 : ℝ)*X 1 0+(4513279273/10000000000 : ℝ)*X 1 1+(2060423649/5000000000 : ℝ)*X 1 2+(4312950979/10000000000 : ℝ)*X 2 0+(4513279273/10000000000 : ℝ)*X 2 1+(2060423649/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (124777071934370870050255503/22150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (167735467/20000000000000 : ℝ)*(base19) + (135406261/20000000000000 : ℝ)*(base23) + (14457623/12500000000000 : ℝ)*(lower2) + (28878373/20000000000000 : ℝ)*(upper3) + (1657271/100000000000000 : ℝ)*(lower4) + (1980309154680697/50000000000000 : ℝ)*(major0) + (1980309154680697/50000000000000 : ℝ)*(major1) + (1980309154680697/50000000000000 : ℝ)*(major2) + (2696869605569921/50000000000000 : ℝ)*(sp0) + (674219184675659/12500000000000 : ℝ)*(sp1) + (2696876819525651/50000000000000 : ℝ)*(sp2) + (1263737816618467/50000000000000 : ℝ)*(sp3) + (3776235691/25000000000000 : ℝ)*(sp4) + (40510171/625000000000 : ℝ)*(sp7) + (1263741057432147/50000000000000 : ℝ)*(f.failure) + (5393754316082607/100000000000000 : ℝ)*(f.sum) + (2763880597931/1107500000000000000000000000 : ℝ)*base66 + (298597731653678501/44300000000000000000000000000000 : ℝ)*base67 + (29431161275121499/44300000000000000000000000000000 : ℝ)*base70 + (226568077072921499/44300000000000000000000000000000 : ℝ)*base72 + (2109143653431/1107500000000000000000000000 : ℝ)*base74 + (408638916118921499/44300000000000000000000000000000 : ℝ)*base76 + (192056902621478501/44300000000000000000000000000000 : ℝ)*base77 + (651902648470921499/44300000000000000000000000000000 : ℝ)*base80 + (7344098119141/1107500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (6537311/500000000000000000000 : ℝ)*base89 + (6537311/500000000000000000000 : ℝ)*base91 + (6537311/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (954425518575931428519/276875000000000000000000000 : ℝ) := by norm_num
    linear_combination (2419119119/100000000000000 : ℝ)*(base19) + (795671177/20000000000000 : ℝ)*(base23) + (224363813/50000000000000 : ℝ)*(upper3) + (31280377/25000000000000 : ℝ)*(lower4) + (305806259/100000000000000 : ℝ)*(upper5) + (1996555486966593/50000000000000 : ℝ)*(major0) + (1996555486966593/50000000000000 : ℝ)*(major1) + (1996555486966593/50000000000000 : ℝ)*(major2) + (10108058259/20000000000000 : ℝ)*(sp1) + (71766153833/100000000000000 : ℝ)*(sp2) + (2719002206556827/50000000000000 : ℝ)*(sp4) + (5437951453703239/100000000000000 : ℝ)*(sp5) + (1087585733720787/20000000000000 : ℝ)*(sp6) + (2548217419848209/100000000000000 : ℝ)*(sp7) + (2548217419848209/100000000000000 : ℝ)*(f.failure) + (2719002206556827/50000000000000 : ℝ)*(f.sum) + (8744594761887/2215000000000000000000000000 : ℝ)*base65 + (60788296148217069/44300000000000000000000000000000 : ℝ)*base67 + (443052713796482931/44300000000000000000000000000000 : ℝ)*base70 + (325846083892117069/44300000000000000000000000000000 : ℝ)*base71 + (2841396654853/553750000000000000000000000 : ℝ)*base73 + (399457813904782931/44300000000000000000000000000000 : ℝ)*base76 + (81033339754317069/44300000000000000000000000000000 : ℝ)*base77 + (228269529633982931/44300000000000000000000000000000 : ℝ)*base80 + (5418865398911/1107500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2698517/1000000000000000000000 : ℝ)*base89 + (2698517/1000000000000000000000 : ℝ)*base91 + (2698517/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1392_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (199/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10161/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2761/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14969/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1392_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1392_s4_0 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2001344371/10000000000 : ℝ)*x 0 + (5411921647/10000000000 : ℝ)*x 1 + (163886243/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2001344371/10000000000 : ℝ)^17 ≤ (3049888289577/25000000000000 : ℝ)^13 := by
    have hnat : (2001344371 : ℕ)^17*25000000000000^13 ≤ 3049888289577^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001344371 10000000000 3049888289577 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411921647/10000000000 : ℝ)^17 ≤ (22401433607999/50000000000000 : ℝ)^13 := by
    have hnat : (5411921647 : ℕ)^17*50000000000000^13 ≤ 22401433607999^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411921647 10000000000 22401433607999 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163886243/312500000 : ℝ)^17 ≤ (21498789807561/50000000000000 : ℝ)^13 := by
    have hnat : (163886243 : ℕ)^17*50000000000000^13 ≤ 21498789807561^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163886243 312500000 21498789807561 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2001344371/10000000000 : ℝ), (5411921647/10000000000 : ℝ), (163886243/312500000 : ℝ)] ![(3049888289577/25000000000000 : ℝ), (22401433607999/50000000000000 : ℝ), (21498789807561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2001344371/10000000000 : ℝ)|^17 ≤ (3049888289577/25000000000000 : ℝ)^13
        have hw : |(-2001344371/10000000000 : ℝ)|=(2001344371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411921647/10000000000 : ℝ)|^17 ≤ (22401433607999/50000000000000 : ℝ)^13
        have hw : |(5411921647/10000000000 : ℝ)|=(5411921647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163886243/312500000 : ℝ)|^17 ≤ (21498789807561/50000000000000 : ℝ)^13
        have hw : |(163886243/312500000 : ℝ)|=(163886243/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s4_1 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5348540127/10000000000 : ℝ)*x 0 + (-2086712557/10000000000 : ℝ)*x 1 + (5244359799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348540127/10000000000 : ℝ)^17 ≤ (44117951398361/100000000000000 : ℝ)^13 := by
    have hnat : (5348540127 : ℕ)^17*100000000000000^13 ≤ 44117951398361^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348540127 10000000000 44117951398361 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2086712557/10000000000 : ℝ)^17 ≤ (402639647461/3125000000000 : ℝ)^13 := by
    have hnat : (2086712557 : ℕ)^17*3125000000000^13 ≤ 402639647461^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086712557 10000000000 402639647461 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244359799/10000000000 : ℝ)^17 ≤ (42997579861717/100000000000000 : ℝ)^13 := by
    have hnat : (5244359799 : ℕ)^17*100000000000000^13 ≤ 42997579861717^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244359799 10000000000 42997579861717 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348540127/10000000000 : ℝ), (-2086712557/10000000000 : ℝ), (5244359799/10000000000 : ℝ)] ![(44117951398361/100000000000000 : ℝ), (402639647461/3125000000000 : ℝ), (42997579861717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348540127/10000000000 : ℝ)|^17 ≤ (44117951398361/100000000000000 : ℝ)^13
        have hw : |(5348540127/10000000000 : ℝ)|=(5348540127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2086712557/10000000000 : ℝ)|^17 ≤ (402639647461/3125000000000 : ℝ)^13
        have hw : |(-2086712557/10000000000 : ℝ)|=(2086712557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244359799/10000000000 : ℝ)|^17 ≤ (42997579861717/100000000000000 : ℝ)^13
        have hw : |(5244359799/10000000000 : ℝ)|=(5244359799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s4_2 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (668567549/1250000000 : ℝ)*x 0 + (65554497/125000000 : ℝ)*x 1 + (-417342451/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668567549/1250000000 : ℝ)^17 ≤ (44117954256817/100000000000000 : ℝ)^13 := by
    have hnat : (668567549 : ℕ)^17*100000000000000^13 ≤ 44117954256817^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668567549 1250000000 44117954256817 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65554497/125000000 : ℝ)^17 ≤ (42997579443577/100000000000000 : ℝ)^13 := by
    have hnat : (65554497 : ℕ)^17*100000000000000^13 ≤ 42997579443577^13*125000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65554497 125000000 42997579443577 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (417342451/2000000000 : ℝ)^17 ≤ (402639571259/3125000000000 : ℝ)^13 := by
    have hnat : (417342451 : ℕ)^17*3125000000000^13 ≤ 402639571259^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417342451 2000000000 402639571259 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668567549/1250000000 : ℝ), (65554497/125000000 : ℝ), (-417342451/2000000000 : ℝ)] ![(44117954256817/100000000000000 : ℝ), (42997579443577/100000000000000 : ℝ), (402639571259/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668567549/1250000000 : ℝ)|^17 ≤ (44117954256817/100000000000000 : ℝ)^13
        have hw : |(668567549/1250000000 : ℝ)|=(668567549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65554497/125000000 : ℝ)|^17 ≤ (42997579443577/100000000000000 : ℝ)^13
        have hw : |(65554497/125000000 : ℝ)|=(65554497/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-417342451/2000000000 : ℝ)|^17 ≤ (402639571259/3125000000000 : ℝ)^13
        have hw : |(-417342451/2000000000 : ℝ)|=(417342451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s4_3 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4313590263/10000000000 : ℝ)*x 0 + (4138184509/10000000000 : ℝ)*x 1 + (4495768797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313590263/10000000000 : ℝ)^17 ≤ (8325716801421/25000000000000 : ℝ)^13 := by
    have hnat : (4313590263 : ℕ)^17*25000000000000^13 ≤ 8325716801421^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313590263 10000000000 8325716801421 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4138184509/10000000000 : ℝ)^17 ≤ (7885789825679/25000000000000 : ℝ)^13 := by
    have hnat : (4138184509 : ℕ)^17*25000000000000^13 ≤ 7885789825679^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4138184509 10000000000 7885789825679 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4495768797/10000000000 : ℝ)^17 ≤ (35153973473913/100000000000000 : ℝ)^13 := by
    have hnat : (4495768797 : ℕ)^17*100000000000000^13 ≤ 35153973473913^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495768797 10000000000 35153973473913 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313590263/10000000000 : ℝ), (4138184509/10000000000 : ℝ), (4495768797/10000000000 : ℝ)] ![(8325716801421/25000000000000 : ℝ), (7885789825679/25000000000000 : ℝ), (35153973473913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313590263/10000000000 : ℝ)|^17 ≤ (8325716801421/25000000000000 : ℝ)^13
        have hw : |(4313590263/10000000000 : ℝ)|=(4313590263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4138184509/10000000000 : ℝ)|^17 ≤ (7885789825679/25000000000000 : ℝ)^13
        have hw : |(4138184509/10000000000 : ℝ)|=(4138184509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4495768797/10000000000 : ℝ)|^17 ≤ (35153973473913/100000000000000 : ℝ)^13
        have hw : |(4495768797/10000000000 : ℝ)|=(4495768797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s4_4 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2001356697/10000000000 : ℝ)*x 0 + (2622487343/5000000000 : ℝ)*x 1 + (5411303561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2001356697/10000000000 : ℝ)^17 ≤ (3049912853077/25000000000000 : ℝ)^13 := by
    have hnat : (2001356697 : ℕ)^17*25000000000000^13 ≤ 3049912853077^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001356697 10000000000 3049912853077 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622487343/5000000000 : ℝ)^17 ≤ (860083450303/2000000000000 : ℝ)^13 := by
    have hnat : (2622487343 : ℕ)^17*2000000000000^13 ≤ 860083450303^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622487343 5000000000 860083450303 2000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411303561/10000000000 : ℝ)^17 ≤ (44796176060041/100000000000000 : ℝ)^13 := by
    have hnat : (5411303561 : ℕ)^17*100000000000000^13 ≤ 44796176060041^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411303561 10000000000 44796176060041 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2001356697/10000000000 : ℝ), (2622487343/5000000000 : ℝ), (5411303561/10000000000 : ℝ)] ![(3049912853077/25000000000000 : ℝ), (860083450303/2000000000000 : ℝ), (44796176060041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2001356697/10000000000 : ℝ)|^17 ≤ (3049912853077/25000000000000 : ℝ)^13
        have hw : |(-2001356697/10000000000 : ℝ)|=(2001356697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622487343/5000000000 : ℝ)|^17 ≤ (860083450303/2000000000000 : ℝ)^13
        have hw : |(2622487343/5000000000 : ℝ)|=(2622487343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411303561/10000000000 : ℝ)|^17 ≤ (44796176060041/100000000000000 : ℝ)^13
        have hw : |(5411303561/10000000000 : ℝ)|=(5411303561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s4_5 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1326285487/2500000000 : ℝ)*x 0 + (-959884209/5000000000 : ℝ)*x 1 + (4227581/7812500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326285487/2500000000 : ℝ)^17 ≤ (2182520844997/5000000000000 : ℝ)^13 := by
    have hnat : (1326285487 : ℕ)^17*5000000000000^13 ≤ 2182520844997^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326285487 2500000000 2182520844997 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (959884209/5000000000 : ℝ)^17 ≤ (11553405734991/100000000000000 : ℝ)^13 := by
    have hnat : (959884209 : ℕ)^17*100000000000000^13 ≤ 11553405734991^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959884209 5000000000 11553405734991 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227581/7812500 : ℝ)^17 ≤ (22398088674133/50000000000000 : ℝ)^13 := by
    have hnat : (4227581 : ℕ)^17*50000000000000^13 ≤ 22398088674133^13*7812500^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227581 7812500 22398088674133 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326285487/2500000000 : ℝ), (-959884209/5000000000 : ℝ), (4227581/7812500 : ℝ)] ![(2182520844997/5000000000000 : ℝ), (11553405734991/100000000000000 : ℝ), (22398088674133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326285487/2500000000 : ℝ)|^17 ≤ (2182520844997/5000000000000 : ℝ)^13
        have hw : |(1326285487/2500000000 : ℝ)|=(1326285487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-959884209/5000000000 : ℝ)|^17 ≤ (11553405734991/100000000000000 : ℝ)^13
        have hw : |(-959884209/5000000000 : ℝ)|=(959884209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227581/7812500 : ℝ)|^17 ≤ (22398088674133/50000000000000 : ℝ)^13
        have hw : |(4227581/7812500 : ℝ)|=(4227581/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s4_6 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1326285471/2500000000 : ℝ)*x 0 + (2705651821/5000000000 : ℝ)*x 1 + (-1919768557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326285471/2500000000 : ℝ)^17 ≤ (10912604052831/25000000000000 : ℝ)^13 := by
    have hnat : (1326285471 : ℕ)^17*25000000000000^13 ≤ 10912604052831^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326285471 2500000000 10912604052831 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705651821/5000000000 : ℝ)^17 ≤ (447961769369/1000000000000 : ℝ)^13 := by
    have hnat : (2705651821 : ℕ)^17*1000000000000^13 ≤ 447961769369^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705651821 5000000000 447961769369 1000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1919768557/10000000000 : ℝ)^17 ≤ (11553406828901/100000000000000 : ℝ)^13 := by
    have hnat : (1919768557 : ℕ)^17*100000000000000^13 ≤ 11553406828901^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919768557 10000000000 11553406828901 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326285471/2500000000 : ℝ), (2705651821/5000000000 : ℝ), (-1919768557/10000000000 : ℝ)] ![(10912604052831/25000000000000 : ℝ), (447961769369/1000000000000 : ℝ), (11553406828901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326285471/2500000000 : ℝ)|^17 ≤ (10912604052831/25000000000000 : ℝ)^13
        have hw : |(1326285471/2500000000 : ℝ)|=(1326285471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705651821/5000000000 : ℝ)|^17 ≤ (447961769369/1000000000000 : ℝ)^13
        have hw : |(2705651821/5000000000 : ℝ)|=(2705651821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1919768557/10000000000 : ℝ)|^17 ≤ (11553406828901/100000000000000 : ℝ)^13
        have hw : |(-1919768557/10000000000 : ℝ)|=(1919768557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s4_7 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4313616443/10000000000 : ℝ)*x 0 + (4494456623/10000000000 : ℝ)*x 1 + (827900787/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313616443/10000000000 : ℝ)^17 ≤ (33303131518579/100000000000000 : ℝ)^13 := by
    have hnat : (4313616443 : ℕ)^17*100000000000000^13 ≤ 33303131518579^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313616443 10000000000 33303131518579 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4494456623/10000000000 : ℝ)^17 ≤ (4392569588099/12500000000000 : ℝ)^13 := by
    have hnat : (4494456623 : ℕ)^17*12500000000000^13 ≤ 4392569588099^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494456623 10000000000 4392569588099 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (827900787/2000000000 : ℝ)^17 ≤ (31556311770501/100000000000000 : ℝ)^13 := by
    have hnat : (827900787 : ℕ)^17*100000000000000^13 ≤ 31556311770501^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827900787 2000000000 31556311770501 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313616443/10000000000 : ℝ), (4494456623/10000000000 : ℝ), (827900787/2000000000 : ℝ)] ![(33303131518579/100000000000000 : ℝ), (4392569588099/12500000000000 : ℝ), (31556311770501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313616443/10000000000 : ℝ)|^17 ≤ (33303131518579/100000000000000 : ℝ)^13
        have hw : |(4313616443/10000000000 : ℝ)|=(4313616443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4494456623/10000000000 : ℝ)|^17 ≤ (4392569588099/12500000000000 : ℝ)^13
        have hw : |(4494456623/10000000000 : ℝ)|=(4494456623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(827900787/2000000000 : ℝ)|^17 ≤ (31556311770501/100000000000000 : ℝ)^13
        have hw : |(827900787/2000000000 : ℝ)|=(827900787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1392_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14969/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2761/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5613/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (591/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14969/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2761/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14969/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2761/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14969/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2761/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14969/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2761/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14969/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2761/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14969/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2761/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2761/25000 : ℝ) ^ (4351/1024 : ℝ) ≤ (1718904046248119/20000000000000000000 : ℝ) := by
    have hpowers : (2761/25000 : ℝ)^4351 ≤ (1718904046248119/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2761 : ℕ)^4351*20000000000000000000^1024 ≤ 1718904046248119^1024*25000^4351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2761 25000 1718904046248119 20000000000000000000 4351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2761/25000 : ℝ)) (X := (1718904046248119/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14969/100000 : ℝ) ^ (4351/1024 : ℝ) ≤ (15643892781649129/50000000000000000000 : ℝ) := by
    have hpowers : (14969/100000 : ℝ)^4351 ≤ (15643892781649129/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14969 : ℕ)^4351*50000000000000000000^1024 ≤ 15643892781649129^1024*100000^4351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14969 100000 15643892781649129 50000000000000000000 4351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14969/100000 : ℝ)) (X := (15643892781649129/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001718904046248119/10000000000000000000 : ℝ) ≤ (1000040451438307/1000000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (10001718904046248119/10000000000000000000 : ℝ)^1024 ≤ (1000040451438307/1000000000000000 : ℝ)^4351 := by
      have hnat : (10001718904046248119 : ℕ)^1024*1000000000000000^4351 ≤ 1000040451438307^4351*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001718904046248119 10000000000000000000 1000040451438307 1000000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000040451438307/1000000000000000 : ℝ)) (X := (10001718904046248119/10000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039882305794538853/100000000000000000000 : ℝ) ≤ (5000469239891683/5000000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (100039882305794538853/100000000000000000000 : ℝ)^1024 ≤ (5000469239891683/5000000000000000 : ℝ)^4351 := by
      have hnat : (100039882305794538853 : ℕ)^1024*5000000000000000^4351 ≤ 5000469239891683^4351*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039882305794538853 100000000000000000000 5000469239891683 5000000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000469239891683/5000000000000000 : ℝ)) (X := (100039882305794538853/100000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015643892781649129/25000000000000000000 : ℝ) ≤ (5000736222591831/5000000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (25015643892781649129/25000000000000000000 : ℝ)^1024 ≤ (5000736222591831/5000000000000000 : ℝ)^4351 := by
      have hnat : (25015643892781649129 : ℕ)^1024*5000000000000000^4351 ≤ 5000736222591831^4351*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015643892781649129 25000000000000000000 5000736222591831 5000000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000736222591831/5000000000000000 : ℝ)) (X := (25015643892781649129/25000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1718904046248119/20000000000000000000 : ℝ) ≤ ((19619896745595905851/19625000000000000000 : ℝ)+2*(66745675037/49062500000000 : ℝ)*(2761/25000 : ℝ))^(4351/1024 : ℝ) := by
    rw [show (19619896745595905851/19625000000000000000 : ℝ)+2*(66745675037/49062500000000 : ℝ)*(2761/25000 : ℝ)=(1000040451438307/1000000000000000 : ℝ) by norm_num, show 1+2*(1718904046248119/20000000000000000000 : ℝ)=(10001718904046248119/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15643892781649129/50000000000000000000 : ℝ)+(1718904046248119/20000000000000000000 : ℝ) ≤ ((19619896745595905851/19625000000000000000 : ℝ)+(66745675037/49062500000000 : ℝ)*((14969/100000 : ℝ)+(2761/25000 : ℝ)))^(4351/1024 : ℝ) := by
    rw [show (19619896745595905851/19625000000000000000 : ℝ)+(66745675037/49062500000000 : ℝ)*((14969/100000 : ℝ)+(2761/25000 : ℝ))=(5000469239891683/5000000000000000 : ℝ) by norm_num, show 1+(15643892781649129/50000000000000000000 : ℝ)+(1718904046248119/20000000000000000000 : ℝ)=(100039882305794538853/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15643892781649129/50000000000000000000 : ℝ) ≤ ((19619896745595905851/19625000000000000000 : ℝ)+2*(66745675037/49062500000000 : ℝ)*(14969/100000 : ℝ))^(4351/1024 : ℝ) := by
    rw [show (19619896745595905851/19625000000000000000 : ℝ)+2*(66745675037/49062500000000 : ℝ)*(14969/100000 : ℝ)=(5000736222591831/5000000000000000 : ℝ) by norm_num, show 1+2*(15643892781649129/50000000000000000000 : ℝ)=(25015643892781649129/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19619896745595905851/19625000000000000000 : ℝ)*(X 1 0+X 2 0)+(66745675037/49062500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (2761/25000 : ℝ)) (hi := (14969/100000 : ℝ)) (c := (19619896745595905851/19625000000000000000 : ℝ)) (alpha := (66745675037/49062500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19619896745595905851/19625000000000000000 : ℝ)*(X 0 1+X 2 1)+(66745675037/49062500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (2761/25000 : ℝ)) (hi := (14969/100000 : ℝ)) (c := (19619896745595905851/19625000000000000000 : ℝ)) (alpha := (66745675037/49062500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19619896745595905851/19625000000000000000 : ℝ)*(X 0 2+X 1 2)+(66745675037/49062500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (2761/25000 : ℝ)) (hi := (14969/100000 : ℝ)) (c := (19619896745595905851/19625000000000000000 : ℝ)) (alpha := (66745675037/49062500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2001344371/10000000000 : ℝ)*X 0 0+(5411921647/10000000000 : ℝ)*X 0 1+(163886243/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348540127/10000000000 : ℝ)*X 1 0+(-2086712557/10000000000 : ℝ)*X 1 1+(5244359799/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668567549/1250000000 : ℝ)*X 2 0+(65554497/125000000 : ℝ)*X 2 1+(-417342451/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4313590263/10000000000 : ℝ)*X 0 0+(4138184509/10000000000 : ℝ)*X 0 1+(4495768797/10000000000 : ℝ)*X 0 2+(4313590263/10000000000 : ℝ)*X 1 0+(4138184509/10000000000 : ℝ)*X 1 1+(4495768797/10000000000 : ℝ)*X 1 2+(4313590263/10000000000 : ℝ)*X 2 0+(4138184509/10000000000 : ℝ)*X 2 1+(4495768797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2001356697/10000000000 : ℝ)*X 0 0+(2622487343/5000000000 : ℝ)*X 0 1+(5411303561/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326285487/2500000000 : ℝ)*X 1 0+(-959884209/5000000000 : ℝ)*X 1 1+(4227581/7812500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326285471/2500000000 : ℝ)*X 2 0+(2705651821/5000000000 : ℝ)*X 2 1+(-1919768557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4313616443/10000000000 : ℝ)*X 0 0+(4494456623/10000000000 : ℝ)*X 0 1+(827900787/2000000000 : ℝ)*X 0 2+(4313616443/10000000000 : ℝ)*X 1 0+(4494456623/10000000000 : ℝ)*X 1 1+(827900787/2000000000 : ℝ)*X 1 2+(4313616443/10000000000 : ℝ)*X 2 0+(4494456623/10000000000 : ℝ)*X 2 1+(827900787/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11024377906727363353107545091/981250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (516209587/25000000000000 : ℝ)*(base19) + (112805851/5000000000000 : ℝ)*(base23) + (55846499/100000000000000 : ℝ)*(lower2) + (82564899/50000000000000 : ℝ)*(upper3) + (255446767/50000000000000 : ℝ)*(upper5) + (4382305479212751/100000000000000 : ℝ)*(major0) + (4382305479212751/100000000000000 : ℝ)*(major1) + (4382305479212751/100000000000000 : ℝ)*(major2) + (1491994402271889/25000000000000 : ℝ)*(sp0) + (298401264754871/5000000000000 : ℝ)*(sp1) + (1492006275954687/25000000000000 : ℝ)*(sp2) + (699141257169163/25000000000000 : ℝ)*(sp3) + (49750848213/100000000000000 : ℝ)*(sp4) + (2274413989/12500000000000 : ℝ)*(sp7) + (699145805997141/25000000000000 : ℝ)*(f.failure) + (746003419991971/12500000000000 : ℝ)*(f.sum) + (85971148057421/19625000000000000000000000000 : ℝ)*base65 + (12245723983934506101/1962500000000000000000000000000000 : ℝ)*base67 + (23650405299147006101/1962500000000000000000000000000000 : ℝ)*base69 + (23293140968109506101/1962500000000000000000000000000000 : ℝ)*base71 + (912409122397/613281250000000000000000000 : ℝ)*base74 + (37955686710809506101/1962500000000000000000000000000000 : ℝ)*base75 + (3902273348959506101/1962500000000000000000000000000000 : ℝ)*base77 + (28148411710059506101/1962500000000000000000000000000000 : ℝ)*base79 + (5851879578537/2453125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (638967/250000000000000000000 : ℝ)*base90 + (638967/250000000000000000000 : ℝ)*base92 + (638967/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1241770011084872008524220611/122656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1775538473/100000000000000 : ℝ)*(base19) + (209423129/12500000000000 : ℝ)*(base23) + (215018169/100000000000000 : ℝ)*(upper3) + (13314247/100000000000000 : ℝ)*(lower4) + (264555739/100000000000000 : ℝ)*(upper5) + (1103682724445837/25000000000000 : ℝ)*(major0) + (1103682724445837/25000000000000 : ℝ)*(major1) + (1103682724445837/25000000000000 : ℝ)*(major2) + (10052293079/25000000000000 : ℝ)*(sp1) + (33764155101/100000000000000 : ℝ)*(sp2) + (1202437168478723/20000000000000 : ℝ)*(sp4) + (240485754307313/4000000000000 : ℝ)*(sp5) + (3006075201426741/50000000000000 : ℝ)*(sp6) + (1408637807853457/50000000000000 : ℝ)*(sp7) + (1408637807853457/50000000000000 : ℝ)*(f.failure) + (1202437168478723/20000000000000 : ℝ)*(f.sum) + (37474294598633/19625000000000000000000000000 : ℝ)*base65 + (4852630895311507713/490625000000000000000000000000000 : ℝ)*base68 + (4361735214064632713/490625000000000000000000000000000 : ℝ)*base70 + (2040482623605257713/490625000000000000000000000000000 : ℝ)*base72 + (408718700539/153320312500000000000000000 : ℝ)*base74 + (3712274034792757713/490625000000000000000000000000000 : ℝ)*base76 + (5648839355905257713/490625000000000000000000000000000 : ℝ)*base78 + (5004391257242287/490625000000000000000000000000000 : ℝ)*base79 + (82273159763617/19625000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3976341/500000000000000000000 : ℝ)*base89 + (3976341/500000000000000000000 : ℝ)*base91 + (3976341/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1392_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14969/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2761/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (591/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1392_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1392_s5_0 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1954611/9765625 : ℝ)*x 0 + (108207619/200000000 : ℝ)*x 1 + (5245783511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1954611/9765625 : ℝ)^17 ≤ (488038657137/4000000000000 : ℝ)^13 := by
    have hnat : (1954611 : ℕ)^17*4000000000000^13 ≤ 488038657137^13*9765625^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954611 9765625 488038657137 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108207619/200000000 : ℝ)^17 ≤ (4478618867369/10000000000000 : ℝ)^13 := by
    have hnat : (108207619 : ℕ)^17*10000000000000^13 ≤ 4478618867369^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108207619 200000000 4478618867369 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245783511/10000000000 : ℝ)^17 ≤ (43012844881933/100000000000000 : ℝ)^13 := by
    have hnat : (5245783511 : ℕ)^17*100000000000000^13 ≤ 43012844881933^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245783511 10000000000 43012844881933 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1954611/9765625 : ℝ), (108207619/200000000 : ℝ), (5245783511/10000000000 : ℝ)] ![(488038657137/4000000000000 : ℝ), (4478618867369/10000000000000 : ℝ), (43012844881933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1954611/9765625 : ℝ)|^17 ≤ (488038657137/4000000000000 : ℝ)^13
        have hw : |(-1954611/9765625 : ℝ)|=(1954611/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108207619/200000000 : ℝ)|^17 ≤ (4478618867369/10000000000000 : ℝ)^13
        have hw : |(108207619/200000000 : ℝ)|=(108207619/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245783511/10000000000 : ℝ)|^17 ≤ (43012844881933/100000000000000 : ℝ)^13
        have hw : |(5245783511/10000000000 : ℝ)|=(5245783511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s5_1 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2674071649/5000000000 : ℝ)*x 0 + (-2085351373/10000000000 : ℝ)*x 1 + (5245783977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674071649/5000000000 : ℝ)^17 ≤ (44113671000939/100000000000000 : ℝ)^13 := by
    have hnat : (2674071649 : ℕ)^17*100000000000000^13 ≤ 44113671000939^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674071649 5000000000 44113671000939 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085351373/10000000000 : ℝ)^17 ≤ (1609184887273/12500000000000 : ℝ)^13 := by
    have hnat : (2085351373 : ℕ)^17*12500000000000^13 ≤ 1609184887273^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085351373 10000000000 1609184887273 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245783977/10000000000 : ℝ)^17 ≤ (43012849878587/100000000000000 : ℝ)^13 := by
    have hnat : (5245783977 : ℕ)^17*100000000000000^13 ≤ 43012849878587^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245783977 10000000000 43012849878587 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674071649/5000000000 : ℝ), (-2085351373/10000000000 : ℝ), (5245783977/10000000000 : ℝ)] ![(44113671000939/100000000000000 : ℝ), (1609184887273/12500000000000 : ℝ), (43012849878587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674071649/5000000000 : ℝ)|^17 ≤ (44113671000939/100000000000000 : ℝ)^13
        have hw : |(2674071649/5000000000 : ℝ)|=(2674071649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2085351373/10000000000 : ℝ)|^17 ≤ (1609184887273/12500000000000 : ℝ)^13
        have hw : |(-2085351373/10000000000 : ℝ)|=(2085351373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245783977/10000000000 : ℝ)|^17 ≤ (43012849878587/100000000000000 : ℝ)^13
        have hw : |(5245783977/10000000000 : ℝ)|=(5245783977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s5_2 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (668517913/1250000000 : ℝ)*x 0 + (5245783789/10000000000 : ℝ)*x 1 + (-417070323/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668517913/1250000000 : ℝ)^17 ≤ (44113671065657/100000000000000 : ℝ)^13 := by
    have hnat : (668517913 : ℕ)^17*100000000000000^13 ≤ 44113671065657^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668517913 1250000000 44113671065657 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245783789/10000000000 : ℝ)^17 ≤ (4301284786277/10000000000000 : ℝ)^13 := by
    have hnat : (5245783789 : ℕ)^17*10000000000000^13 ≤ 4301284786277^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245783789 10000000000 4301284786277 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (417070323/2000000000 : ℝ)^17 ≤ (12873481051793/100000000000000 : ℝ)^13 := by
    have hnat : (417070323 : ℕ)^17*100000000000000^13 ≤ 12873481051793^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417070323 2000000000 12873481051793 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668517913/1250000000 : ℝ), (5245783789/10000000000 : ℝ), (-417070323/2000000000 : ℝ)] ![(44113671065657/100000000000000 : ℝ), (4301284786277/10000000000000 : ℝ), (12873481051793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668517913/1250000000 : ℝ)|^17 ≤ (44113671065657/100000000000000 : ℝ)^13
        have hw : |(668517913/1250000000 : ℝ)|=(668517913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245783789/10000000000 : ℝ)|^17 ≤ (4301284786277/10000000000000 : ℝ)^13
        have hw : |(5245783789/10000000000 : ℝ)|=(5245783789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-417070323/2000000000 : ℝ)|^17 ≤ (12873481051793/100000000000000 : ℝ)^13
        have hw : |(-417070323/2000000000 : ℝ)|=(417070323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s5_3 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4313695801/10000000000 : ℝ)*x 0 + (103533387/250000000 : ℝ)*x 1 + (35098377/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313695801/10000000000 : ℝ)^17 ≤ (33303932718797/100000000000000 : ℝ)^13 := by
    have hnat : (4313695801 : ℕ)^17*100000000000000^13 ≤ 33303932718797^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313695801 10000000000 33303932718797 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103533387/250000000 : ℝ)^17 ≤ (7893642836317/25000000000000 : ℝ)^13 := by
    have hnat : (103533387 : ℕ)^17*25000000000000^13 ≤ 7893642836317^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103533387 250000000 7893642836317 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35098377/78125000 : ℝ)^17 ≤ (35121495923371/100000000000000 : ℝ)^13 := by
    have hnat : (35098377 : ℕ)^17*100000000000000^13 ≤ 35121495923371^13*78125000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35098377 78125000 35121495923371 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313695801/10000000000 : ℝ), (103533387/250000000 : ℝ), (35098377/78125000 : ℝ)] ![(33303932718797/100000000000000 : ℝ), (7893642836317/25000000000000 : ℝ), (35121495923371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313695801/10000000000 : ℝ)|^17 ≤ (33303932718797/100000000000000 : ℝ)^13
        have hw : |(4313695801/10000000000 : ℝ)|=(4313695801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103533387/250000000 : ℝ)|^17 ≤ (7893642836317/25000000000000 : ℝ)^13
        have hw : |(103533387/250000000 : ℝ)|=(103533387/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35098377/78125000 : ℝ)|^17 ≤ (35121495923371/100000000000000 : ℝ)^13
        have hw : |(35098377/78125000 : ℝ)|=(35098377/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s5_4 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2001533327/10000000000 : ℝ)*x 0 + (5246377017/10000000000 : ℝ)*x 1 + (108195689/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2001533327/10000000000 : ℝ)^17 ≤ (12201059399997/100000000000000 : ℝ)^13 := by
    have hnat : (2001533327 : ℕ)^17*100000000000000^13 ≤ 12201059399997^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001533327 10000000000 12201059399997 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246377017/10000000000 : ℝ)^17 ≤ (4301920882149/10000000000000 : ℝ)^13 := by
    have hnat : (5246377017 : ℕ)^17*10000000000000^13 ≤ 4301920882149^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246377017 10000000000 4301920882149 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108195689/200000000 : ℝ)^17 ≤ (895594635221/2000000000000 : ℝ)^13 := by
    have hnat : (108195689 : ℕ)^17*2000000000000^13 ≤ 895594635221^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108195689 200000000 895594635221 2000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2001533327/10000000000 : ℝ), (5246377017/10000000000 : ℝ), (108195689/200000000 : ℝ)] ![(12201059399997/100000000000000 : ℝ), (4301920882149/10000000000000 : ℝ), (895594635221/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2001533327/10000000000 : ℝ)|^17 ≤ (12201059399997/100000000000000 : ℝ)^13
        have hw : |(-2001533327/10000000000 : ℝ)|=(2001533327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246377017/10000000000 : ℝ)|^17 ≤ (4301920882149/10000000000000 : ℝ)^13
        have hw : |(5246377017/10000000000 : ℝ)|=(5246377017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108195689/200000000 : ℝ)|^17 ≤ (895594635221/2000000000000 : ℝ)^13
        have hw : |(108195689/200000000 : ℝ)|=(108195689/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s5_5 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5305513133/10000000000 : ℝ)*x 0 + (-384270159/2000000000 : ℝ)*x 1 + (270489209/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305513133/10000000000 : ℝ)^17 ≤ (43654410752689/100000000000000 : ℝ)^13 := by
    have hnat : (5305513133 : ℕ)^17*100000000000000^13 ≤ 43654410752689^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305513133 10000000000 43654410752689 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (384270159/2000000000 : ℝ)^17 ≤ (11565860391987/100000000000000 : ℝ)^13 := by
    have hnat : (384270159 : ℕ)^17*100000000000000^13 ≤ 11565860391987^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384270159 2000000000 11565860391987 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270489209/500000000 : ℝ)^17 ≤ (1119493220961/2500000000000 : ℝ)^13 := by
    have hnat : (270489209 : ℕ)^17*2500000000000^13 ≤ 1119493220961^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270489209 500000000 1119493220961 2500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305513133/10000000000 : ℝ), (-384270159/2000000000 : ℝ), (270489209/500000000 : ℝ)] ![(43654410752689/100000000000000 : ℝ), (11565860391987/100000000000000 : ℝ), (1119493220961/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305513133/10000000000 : ℝ)|^17 ≤ (43654410752689/100000000000000 : ℝ)^13
        have hw : |(5305513133/10000000000 : ℝ)|=(5305513133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-384270159/2000000000 : ℝ)|^17 ≤ (11565860391987/100000000000000 : ℝ)^13
        have hw : |(-384270159/2000000000 : ℝ)|=(384270159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270489209/500000000 : ℝ)|^17 ≤ (1119493220961/2500000000000 : ℝ)^13
        have hw : |(270489209/500000000 : ℝ)|=(270489209/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s5_6 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5305513289/10000000000 : ℝ)*x 0 + (5409783839/10000000000 : ℝ)*x 1 + (-480337763/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305513289/10000000000 : ℝ)^17 ≤ (21827206215613/50000000000000 : ℝ)^13 := by
    have hnat : (5305513289 : ℕ)^17*50000000000000^13 ≤ 21827206215613^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305513289 10000000000 21827206215613 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409783839/10000000000 : ℝ)^17 ≤ (11194931286823/25000000000000 : ℝ)^13 := by
    have hnat : (5409783839 : ℕ)^17*25000000000000^13 ≤ 11194931286823^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409783839 10000000000 11194931286823 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (480337763/2500000000 : ℝ)^17 ≤ (2891465603763/25000000000000 : ℝ)^13 := by
    have hnat : (480337763 : ℕ)^17*25000000000000^13 ≤ 2891465603763^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480337763 2500000000 2891465603763 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305513289/10000000000 : ℝ), (5409783839/10000000000 : ℝ), (-480337763/2500000000 : ℝ)] ![(21827206215613/50000000000000 : ℝ), (11194931286823/25000000000000 : ℝ), (2891465603763/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305513289/10000000000 : ℝ)|^17 ≤ (21827206215613/50000000000000 : ℝ)^13
        have hw : |(5305513289/10000000000 : ℝ)|=(5305513289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409783839/10000000000 : ℝ)|^17 ≤ (11194931286823/25000000000000 : ℝ)^13
        have hw : |(5409783839/10000000000 : ℝ)|=(5409783839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-480337763/2500000000 : ℝ)|^17 ≤ (2891465603763/25000000000000 : ℝ)^13
        have hw : |(-480337763/2500000000 : ℝ)|=(480337763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s5_7 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1078430241/2500000000 : ℝ)*x 0 + (561415717/1250000000 : ℝ)*x 1 + (414260853/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078430241/2500000000 : ℝ)^17 ≤ (33304186765979/100000000000000 : ℝ)^13 := by
    have hnat : (1078430241 : ℕ)^17*100000000000000^13 ≤ 33304186765979^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078430241 2500000000 33304186765979 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561415717/1250000000 : ℝ)^17 ≤ (35108548755319/100000000000000 : ℝ)^13 := by
    have hnat : (561415717 : ℕ)^17*100000000000000^13 ≤ 35108548755319^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561415717 1250000000 35108548755319 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (414260853/1000000000 : ℝ)^17 ≤ (6317452894407/20000000000000 : ℝ)^13 := by
    have hnat : (414260853 : ℕ)^17*20000000000000^13 ≤ 6317452894407^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414260853 1000000000 6317452894407 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078430241/2500000000 : ℝ), (561415717/1250000000 : ℝ), (414260853/1000000000 : ℝ)] ![(33304186765979/100000000000000 : ℝ), (35108548755319/100000000000000 : ℝ), (6317452894407/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078430241/2500000000 : ℝ)|^17 ≤ (33304186765979/100000000000000 : ℝ)^13
        have hw : |(1078430241/2500000000 : ℝ)|=(1078430241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561415717/1250000000 : ℝ)|^17 ≤ (35108548755319/100000000000000 : ℝ)^13
        have hw : |(561415717/1250000000 : ℝ)|=(561415717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(414260853/1000000000 : ℝ)|^17 ≤ (6317452894407/20000000000000 : ℝ)^13
        have hw : |(414260853/1000000000 : ℝ)|=(414260853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1392_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (591/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11257/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7371/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (591/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5613/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (591/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5613/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (591/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5613/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (591/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5613/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (591/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5613/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (591/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5613/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5613/50000 : ℝ) ^ (4351/1024 : ℝ) ≤ (9212636286433209/100000000000000000000 : ℝ) := by
    have hpowers : (5613/50000 : ℝ)^4351 ≤ (9212636286433209/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5613 : ℕ)^4351*100000000000000000000^1024 ≤ 9212636286433209^1024*50000^4351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5613 50000 9212636286433209 100000000000000000000 4351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5613/50000 : ℝ)) (X := (9212636286433209/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (591/4000 : ℝ) ^ (4351/1024 : ℝ) ≤ (7400189611368793/25000000000000000000 : ℝ) := by
    have hpowers : (591/4000 : ℝ)^4351 ≤ (7400189611368793/25000000000000000000 : ℝ)^1024 := by
      have hnat : (591 : ℕ)^4351*25000000000000000000^1024 ≤ 7400189611368793^1024*4000^4351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        591 4000 7400189611368793 25000000000000000000 4351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (591/4000 : ℝ)) (X := (7400189611368793/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009212636286433209/50000000000000000000 : ℝ) ≤ (2000086720984357/2000000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (50009212636286433209/50000000000000000000 : ℝ)^1024 ≤ (2000086720984357/2000000000000000 : ℝ)^4351 := by
      have hnat : (50009212636286433209 : ℕ)^1024*2000000000000000^4351 ≤ 2000086720984357^4351*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009212636286433209 50000000000000000000 2000086720984357 2000000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000086720984357/2000000000000000 : ℝ)) (X := (50009212636286433209/50000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038813394731908381/100000000000000000000 : ℝ) ≤ (2500228332680177/2500000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (100038813394731908381/100000000000000000000 : ℝ)^1024 ≤ (2500228332680177/2500000000000000 : ℝ)^4351 := by
      have hnat : (100038813394731908381 : ℕ)^1024*2500000000000000^4351 ≤ 2500228332680177^4351*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038813394731908381 100000000000000000000 2500228332680177 2500000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500228332680177/2500000000000000 : ℝ)) (X := (100038813394731908381/100000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507400189611368793/12500000000000000000 : ℝ) ≤ (10001393056519631/10000000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (12507400189611368793/12500000000000000000 : ℝ)^1024 ≤ (10001393056519631/10000000000000000 : ℝ)^4351 := by
      have hnat : (12507400189611368793 : ℕ)^1024*10000000000000000^4351 ≤ 10001393056519631^4351*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507400189611368793 12500000000000000000 10001393056519631 10000000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001393056519631/10000000000000000 : ℝ)) (X := (12507400189611368793/12500000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9212636286433209/100000000000000000000 : ℝ) ≤ ((1689560383820475989/1690000000000000000 : ℝ)+2*(22844085663/16900000000000 : ℝ)*(5613/50000 : ℝ))^(4351/1024 : ℝ) := by
    rw [show (1689560383820475989/1690000000000000000 : ℝ)+2*(22844085663/16900000000000 : ℝ)*(5613/50000 : ℝ)=(2000086720984357/2000000000000000 : ℝ) by norm_num, show 1+2*(9212636286433209/100000000000000000000 : ℝ)=(50009212636286433209/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7400189611368793/25000000000000000000 : ℝ)+(9212636286433209/100000000000000000000 : ℝ) ≤ ((1689560383820475989/1690000000000000000 : ℝ)+(22844085663/16900000000000 : ℝ)*((591/4000 : ℝ)+(5613/50000 : ℝ)))^(4351/1024 : ℝ) := by
    rw [show (1689560383820475989/1690000000000000000 : ℝ)+(22844085663/16900000000000 : ℝ)*((591/4000 : ℝ)+(5613/50000 : ℝ))=(2500228332680177/2500000000000000 : ℝ) by norm_num, show 1+(7400189611368793/25000000000000000000 : ℝ)+(9212636286433209/100000000000000000000 : ℝ)=(100038813394731908381/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7400189611368793/25000000000000000000 : ℝ) ≤ ((1689560383820475989/1690000000000000000 : ℝ)+2*(22844085663/16900000000000 : ℝ)*(591/4000 : ℝ))^(4351/1024 : ℝ) := by
    rw [show (1689560383820475989/1690000000000000000 : ℝ)+2*(22844085663/16900000000000 : ℝ)*(591/4000 : ℝ)=(10001393056519631/10000000000000000 : ℝ) by norm_num, show 1+2*(7400189611368793/25000000000000000000 : ℝ)=(12507400189611368793/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1689560383820475989/1690000000000000000 : ℝ)*(X 1 0+X 2 0)+(22844085663/16900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (591/4000 : ℝ)) (c := (1689560383820475989/1690000000000000000 : ℝ)) (alpha := (22844085663/16900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1689560383820475989/1690000000000000000 : ℝ)*(X 0 1+X 2 1)+(22844085663/16900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (591/4000 : ℝ)) (c := (1689560383820475989/1690000000000000000 : ℝ)) (alpha := (22844085663/16900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1689560383820475989/1690000000000000000 : ℝ)*(X 0 2+X 1 2)+(22844085663/16900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (591/4000 : ℝ)) (c := (1689560383820475989/1690000000000000000 : ℝ)) (alpha := (22844085663/16900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1954611/9765625 : ℝ)*X 0 0+(108207619/200000000 : ℝ)*X 0 1+(5245783511/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674071649/5000000000 : ℝ)*X 1 0+(-2085351373/10000000000 : ℝ)*X 1 1+(5245783977/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668517913/1250000000 : ℝ)*X 2 0+(5245783789/10000000000 : ℝ)*X 2 1+(-417070323/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4313695801/10000000000 : ℝ)*X 0 0+(103533387/250000000 : ℝ)*X 0 1+(35098377/78125000 : ℝ)*X 0 2+(4313695801/10000000000 : ℝ)*X 1 0+(103533387/250000000 : ℝ)*X 1 1+(35098377/78125000 : ℝ)*X 1 2+(4313695801/10000000000 : ℝ)*X 2 0+(103533387/250000000 : ℝ)*X 2 1+(35098377/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2001533327/10000000000 : ℝ)*X 0 0+(5246377017/10000000000 : ℝ)*X 0 1+(108195689/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305513133/10000000000 : ℝ)*X 1 0+(-384270159/2000000000 : ℝ)*X 1 1+(270489209/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305513289/10000000000 : ℝ)*X 2 0+(5409783839/10000000000 : ℝ)*X 2 1+(-480337763/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1078430241/2500000000 : ℝ)*X 0 0+(561415717/1250000000 : ℝ)*X 0 1+(414260853/1000000000 : ℝ)*X 0 2+(1078430241/2500000000 : ℝ)*X 1 0+(561415717/1250000000 : ℝ)*X 1 1+(414260853/1000000000 : ℝ)*X 1 2+(1078430241/2500000000 : ℝ)*X 2 0+(561415717/1250000000 : ℝ)*X 2 1+(414260853/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4710051710844813266880951/845000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (132194339/12500000000000 : ℝ)*(base19) + (6394293/625000000000 : ℝ)*(base23) + (170463891/50000000000000 : ℝ)*(upper3) + (22079187/100000000000000 : ℝ)*(upper4) + (10556951/100000000000000 : ℝ)*(upper5) + (89224368526153/2000000000000 : ℝ)*(major0) + (89224368526153/2000000000000 : ℝ)*(major1) + (89224368526153/2000000000000 : ℝ)*(major2) + (379716733962607/6250000000000 : ℝ)*(sp0) + (6075493818291311/100000000000000 : ℝ)*(sp1) + (3037746926379571/50000000000000 : ℝ)*(sp2) + (1423464212009731/50000000000000 : ℝ)*(sp3) + (27132444311/100000000000000 : ℝ)*(sp4) + (13366948951/100000000000000 : ℝ)*(sp7) + (2846941790968413/100000000000000 : ℝ)*(f.failure) + (3037747437923011/50000000000000 : ℝ)*(f.sum) + (195470009381/169000000000000000000000000 : ℝ)*base65 + (25836753375599683/3380000000000000000000000000000 : ℝ)*base68 + (43374125724979683/3380000000000000000000000000000 : ℝ)*base70 + (30497334384579683/3380000000000000000000000000000 : ℝ)*base72 + (981261141273/169000000000000000000000000 : ℝ)*base73 + (59478436764679683/3380000000000000000000000000000 : ℝ)*base76 + (5065543420779683/3380000000000000000000000000000 : ℝ)*base78 + (4717897878020317/3380000000000000000000000000000 : ℝ)*base79 + (53078646561/84500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (7981969/1000000000000000000000 : ℝ)*base89 + (7981969/1000000000000000000000 : ℝ)*base91 + (7981969/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22897098390370287416113143/84500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (180911101/20000000000000 : ℝ)*(base19) + (1038256841/100000000000000 : ℝ)*(base23) + (10296453/50000000000000 : ℝ)*(lower4) + (77422927/100000000000000 : ℝ)*(upper5) + (4493672001536329/100000000000000 : ℝ)*(major0) + (4493672001536329/100000000000000 : ℝ)*(major1) + (4493672001536329/100000000000000 : ℝ)*(major2) + (1999562491/25000000000000 : ℝ)*(sp0) + (23240877943/100000000000000 : ℝ)*(sp1) + (790985881/6250000000000 : ℝ)*(sp2) + (3059841922417961/50000000000000 : ℝ)*(sp4) + (6119667697652439/100000000000000 : ℝ)*(sp5) + (1529919537263737/25000000000000 : ℝ)*(sp6) + (143382607547719/5000000000000 : ℝ)*(sp7) + (143382607547719/5000000000000 : ℝ)*(f.failure) + (3059845921542943/50000000000000 : ℝ)*(f.sum) + (3043500429277/845000000000000000000000000 : ℝ)*base65 + (417386500857595619/169000000000000000000000000000000 : ℝ)*base68 + (40517134607595619/169000000000000000000000000000000 : ℝ)*base70 + (807429918319404381/169000000000000000000000000000000 : ℝ)*base71 + (898477050207/845000000000000000000000000 : ℝ)*base73 + (175409187370595619/169000000000000000000000000000000 : ℝ)*base76 + (978322759724404381/169000000000000000000000000000000 : ℝ)*base77 + (1596283965355595619/169000000000000000000000000000000 : ℝ)*base80 + (1235462397953/845000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (105853/50000000000000000000 : ℝ)*base90 + (105853/50000000000000000000 : ℝ)*base92 + (105853/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1392_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (591/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1392_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1392_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (199/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10161/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1392_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1392_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1392_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (199/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10161/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1392_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

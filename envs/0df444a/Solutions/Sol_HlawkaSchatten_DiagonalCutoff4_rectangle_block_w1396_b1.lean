-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1396_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:44:02.271449+00:00
-- url     : https://prove2.me/submissions/c959d94c-f021-49dd-8413-65249bc6c755

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
theorem support_rectangle_w1396_s3_0 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-399388039/2000000000 : ℝ)*x 0 + (1084152139/2000000000 : ℝ)*x 1 + (2618062307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399388039/2000000000 : ℝ)^1089 ≤ (6085849433061/50000000000000 : ℝ)^833 := by
    have hnat : (399388039 : ℕ)^1089*50000000000000^833 ≤ 6085849433061^833*2000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399388039 2000000000 6085849433061 50000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084152139/2000000000 : ℝ)^1089 ≤ (22454368841517/50000000000000 : ℝ)^833 := by
    have hnat : (1084152139 : ℕ)^1089*50000000000000^833 ≤ 22454368841517^833*2000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084152139 2000000000 22454368841517 50000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2618062307/5000000000 : ℝ)^1089 ≤ (134123635731/312500000000 : ℝ)^833 := by
    have hnat : (2618062307 : ℕ)^1089*312500000000^833 ≤ 134123635731^833*5000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618062307 5000000000 134123635731 312500000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-399388039/2000000000 : ℝ), (1084152139/2000000000 : ℝ), (2618062307/5000000000 : ℝ)] ![(6085849433061/50000000000000 : ℝ), (22454368841517/50000000000000 : ℝ), (134123635731/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-399388039/2000000000 : ℝ)|^1089 ≤ (6085849433061/50000000000000 : ℝ)^833
        have hw : |(-399388039/2000000000 : ℝ)|=(399388039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084152139/2000000000 : ℝ)|^1089 ≤ (22454368841517/50000000000000 : ℝ)^833
        have hw : |(1084152139/2000000000 : ℝ)|=(1084152139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2618062307/5000000000 : ℝ)|^1089 ≤ (134123635731/312500000000 : ℝ)^833
        have hw : |(2618062307/5000000000 : ℝ)|=(2618062307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1396_s3_1 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5350785833/10000000000 : ℝ)*x 0 + (-1045592423/5000000000 : ℝ)*x 1 + (5236124647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350785833/10000000000 : ℝ)^1089 ≤ (44152374036143/100000000000000 : ℝ)^833 := by
    have hnat : (5350785833 : ℕ)^1089*100000000000000^833 ≤ 44152374036143^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350785833 10000000000 44152374036143 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045592423/5000000000 : ℝ)^1089 ≤ (12928062168163/100000000000000 : ℝ)^833 := by
    have hnat : (1045592423 : ℕ)^1089*100000000000000^833 ≤ 12928062168163^833*5000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045592423 5000000000 12928062168163 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236124647/10000000000 : ℝ)^1089 ≤ (5364945473443/12500000000000 : ℝ)^833 := by
    have hnat : (5236124647 : ℕ)^1089*12500000000000^833 ≤ 5364945473443^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236124647 10000000000 5364945473443 12500000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350785833/10000000000 : ℝ), (-1045592423/5000000000 : ℝ), (5236124647/10000000000 : ℝ)] ![(44152374036143/100000000000000 : ℝ), (12928062168163/100000000000000 : ℝ), (5364945473443/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350785833/10000000000 : ℝ)|^1089 ≤ (44152374036143/100000000000000 : ℝ)^833
        have hw : |(5350785833/10000000000 : ℝ)|=(5350785833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1045592423/5000000000 : ℝ)|^1089 ≤ (12928062168163/100000000000000 : ℝ)^833
        have hw : |(-1045592423/5000000000 : ℝ)|=(1045592423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236124647/10000000000 : ℝ)|^1089 ≤ (5364945473443/12500000000000 : ℝ)^833
        have hw : |(5236124647/10000000000 : ℝ)|=(5236124647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1396_s3_2 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1337696489/2500000000 : ℝ)*x 0 + (261806227/500000000 : ℝ)*x 1 + (-2091184823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337696489/2500000000 : ℝ)^1089 ≤ (44152375363001/100000000000000 : ℝ)^833 := by
    have hnat : (1337696489 : ℕ)^1089*100000000000000^833 ≤ 44152375363001^833*2500000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337696489 2500000000 44152375363001 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261806227/500000000 : ℝ)^1089 ≤ (2682472665059/6250000000000 : ℝ)^833 := by
    have hnat : (261806227 : ℕ)^1089*6250000000000^833 ≤ 2682472665059^833*500000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261806227 500000000 2682472665059 6250000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2091184823/10000000000 : ℝ)^1089 ≤ (517122479291/4000000000000 : ℝ)^833 := by
    have hnat : (2091184823 : ℕ)^1089*4000000000000^833 ≤ 517122479291^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091184823 10000000000 517122479291 4000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337696489/2500000000 : ℝ), (261806227/500000000 : ℝ), (-2091184823/10000000000 : ℝ)] ![(44152375363001/100000000000000 : ℝ), (2682472665059/6250000000000 : ℝ), (517122479291/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337696489/2500000000 : ℝ)|^1089 ≤ (44152375363001/100000000000000 : ℝ)^833
        have hw : |(1337696489/2500000000 : ℝ)|=(1337696489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261806227/500000000 : ℝ)|^1089 ≤ (2682472665059/6250000000000 : ℝ)^833
        have hw : |(261806227/500000000 : ℝ)|=(261806227/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2091184823/10000000000 : ℝ)|^1089 ≤ (517122479291/4000000000000 : ℝ)^833
        have hw : |(-2091184823/10000000000 : ℝ)|=(2091184823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1396_s3_3 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2155956937/5000000000 : ℝ)*x 0 + (411872863/1000000000 : ℝ)*x 1 + (4513333677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155956937/5000000000 : ℝ)^1089 ≤ (1664814386511/5000000000000 : ℝ)^833 := by
    have hnat : (2155956937 : ℕ)^1089*5000000000000^833 ≤ 1664814386511^833*5000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155956937 5000000000 1664814386511 5000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (411872863/1000000000 : ℝ)^1089 ≤ (1567982006407/5000000000000 : ℝ)^833 := by
    have hnat : (411872863 : ℕ)^1089*5000000000000^833 ≤ 1567982006407^833*1000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411872863 1000000000 1567982006407 5000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4513333677/10000000000 : ℝ)^1089 ≤ (35344072123357/100000000000000 : ℝ)^833 := by
    have hnat : (4513333677 : ℕ)^1089*100000000000000^833 ≤ 35344072123357^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513333677 10000000000 35344072123357 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155956937/5000000000 : ℝ), (411872863/1000000000 : ℝ), (4513333677/10000000000 : ℝ)] ![(1664814386511/5000000000000 : ℝ), (1567982006407/5000000000000 : ℝ), (35344072123357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155956937/5000000000 : ℝ)|^1089 ≤ (1664814386511/5000000000000 : ℝ)^833
        have hw : |(2155956937/5000000000 : ℝ)|=(2155956937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(411872863/1000000000 : ℝ)|^1089 ≤ (1567982006407/5000000000000 : ℝ)^833
        have hw : |(411872863/1000000000 : ℝ)|=(411872863/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4513333677/10000000000 : ℝ)|^1089 ≤ (35344072123357/100000000000000 : ℝ)^833
        have hw : |(4513333677/10000000000 : ℝ)|=(4513333677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1396_s3_4 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-399391463/2000000000 : ℝ)*x 0 + (5236872501/10000000000 : ℝ)*x 1 + (5420008103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399391463/2000000000 : ℝ)^1089 ≤ (12171835284647/100000000000000 : ℝ)^833 := by
    have hnat : (399391463 : ℕ)^1089*100000000000000^833 ≤ 12171835284647^833*2000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399391463 2000000000 12171835284647 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5236872501/10000000000 : ℝ)^1089 ≤ (42927577883777/100000000000000 : ℝ)^833 := by
    have hnat : (5236872501 : ℕ)^1089*100000000000000^833 ≤ 42927577883777^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236872501 10000000000 42927577883777 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420008103/10000000000 : ℝ)^1089 ≤ (4490058681573/10000000000000 : ℝ)^833 := by
    have hnat : (5420008103 : ℕ)^1089*10000000000000^833 ≤ 4490058681573^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420008103 10000000000 4490058681573 10000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-399391463/2000000000 : ℝ), (5236872501/10000000000 : ℝ), (5420008103/10000000000 : ℝ)] ![(12171835284647/100000000000000 : ℝ), (42927577883777/100000000000000 : ℝ), (4490058681573/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-399391463/2000000000 : ℝ)|^1089 ≤ (12171835284647/100000000000000 : ℝ)^833
        have hw : |(-399391463/2000000000 : ℝ)|=(399391463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5236872501/10000000000 : ℝ)|^1089 ≤ (42927577883777/100000000000000 : ℝ)^833
        have hw : |(5236872501/10000000000 : ℝ)|=(5236872501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420008103/10000000000 : ℝ)|^1089 ≤ (4490058681573/10000000000000 : ℝ)^833
        have hw : |(5420008103/10000000000 : ℝ)|=(5420008103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1396_s3_5 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1060589101/2000000000 : ℝ)*x 0 + (-381460167/2000000000 : ℝ)*x 1 + (1084001723/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060589101/2000000000 : ℝ)^1089 ≤ (43637008691137/100000000000000 : ℝ)^833 := by
    have hnat : (1060589101 : ℕ)^1089*100000000000000^833 ≤ 43637008691137^833*2000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060589101 2000000000 43637008691137 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (381460167/2000000000 : ℝ)^1089 ≤ (11462398931237/100000000000000 : ℝ)^833 := by
    have hnat : (381460167 : ℕ)^1089*100000000000000^833 ≤ 11462398931237^833*2000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381460167 2000000000 11462398931237 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084001723/2000000000 : ℝ)^1089 ≤ (44900592360773/100000000000000 : ℝ)^833 := by
    have hnat : (1084001723 : ℕ)^1089*100000000000000^833 ≤ 44900592360773^833*2000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084001723 2000000000 44900592360773 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060589101/2000000000 : ℝ), (-381460167/2000000000 : ℝ), (1084001723/2000000000 : ℝ)] ![(43637008691137/100000000000000 : ℝ), (11462398931237/100000000000000 : ℝ), (44900592360773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060589101/2000000000 : ℝ)|^1089 ≤ (43637008691137/100000000000000 : ℝ)^833
        have hw : |(1060589101/2000000000 : ℝ)|=(1060589101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-381460167/2000000000 : ℝ)|^1089 ≤ (11462398931237/100000000000000 : ℝ)^833
        have hw : |(-381460167/2000000000 : ℝ)|=(381460167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084001723/2000000000 : ℝ)|^1089 ≤ (44900592360773/100000000000000 : ℝ)^833
        have hw : |(1084001723/2000000000 : ℝ)|=(1084001723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1396_s3_6 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1325736643/2500000000 : ℝ)*x 0 + (5420007803/10000000000 : ℝ)*x 1 + (-953650247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325736643/2500000000 : ℝ)^1089 ≤ (43637020169637/100000000000000 : ℝ)^833 := by
    have hnat : (1325736643 : ℕ)^1089*100000000000000^833 ≤ 43637020169637^833*2500000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325736643 2500000000 43637020169637 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5420007803/10000000000 : ℝ)^1089 ≤ (44900583566681/100000000000000 : ℝ)^833 := by
    have hnat : (5420007803 : ℕ)^1089*100000000000000^833 ≤ 44900583566681^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420007803 10000000000 44900583566681 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (953650247/5000000000 : ℝ)^1089 ≤ (2865599063027/25000000000000 : ℝ)^833 := by
    have hnat : (953650247 : ℕ)^1089*25000000000000^833 ≤ 2865599063027^833*5000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953650247 5000000000 2865599063027 25000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325736643/2500000000 : ℝ), (5420007803/10000000000 : ℝ), (-953650247/5000000000 : ℝ)] ![(43637020169637/100000000000000 : ℝ), (44900583566681/100000000000000 : ℝ), (2865599063027/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325736643/2500000000 : ℝ)|^1089 ≤ (43637020169637/100000000000000 : ℝ)^833
        have hw : |(1325736643/2500000000 : ℝ)|=(1325736643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5420007803/10000000000 : ℝ)|^1089 ≤ (44900583566681/100000000000000 : ℝ)^833
        have hw : |(5420007803/10000000000 : ℝ)|=(5420007803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-953650247/5000000000 : ℝ)|^1089 ≤ (2865599063027/25000000000000 : ℝ)^833
        have hw : |(-953650247/5000000000 : ℝ)|=(953650247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1396_s3_7 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (134748457/312500000 : ℝ)*x 0 + (563966857/1250000000 : ℝ)*x 1 + (4120335587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134748457/312500000 : ℝ)^1089 ≤ (6659331744783/20000000000000 : ℝ)^833 := by
    have hnat : (134748457 : ℕ)^1089*20000000000000^833 ≤ 6659331744783^833*312500000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134748457 312500000 6659331744783 20000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563966857/1250000000 : ℝ)^1089 ≤ (35327704778933/100000000000000 : ℝ)^833 := by
    have hnat : (563966857 : ℕ)^1089*100000000000000^833 ≤ 35327704778933^833*1250000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563966857 1250000000 35327704778933 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4120335587/10000000000 : ℝ)^1089 ≤ (6275127296819/20000000000000 : ℝ)^833 := by
    have hnat : (4120335587 : ℕ)^1089*20000000000000^833 ≤ 6275127296819^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4120335587 10000000000 6275127296819 20000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134748457/312500000 : ℝ), (563966857/1250000000 : ℝ), (4120335587/10000000000 : ℝ)] ![(6659331744783/20000000000000 : ℝ), (35327704778933/100000000000000 : ℝ), (6275127296819/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134748457/312500000 : ℝ)|^1089 ≤ (6659331744783/20000000000000 : ℝ)^833
        have hw : |(134748457/312500000 : ℝ)|=(134748457/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563966857/1250000000 : ℝ)|^1089 ≤ (35327704778933/100000000000000 : ℝ)^833
        have hw : |(563966857/1250000000 : ℝ)|=(563966857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4120335587/10000000000 : ℝ)|^1089 ≤ (6275127296819/20000000000000 : ℝ)^833
        have hw : |(4120335587/10000000000 : ℝ)|=(4120335587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1396_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31372059/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7953/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1273/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11057/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7483/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7953/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1273/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7953/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1273/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7953/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1273/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7953/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1273/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7953/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1273/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7953/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1273/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1273/12500 : ℝ) ^ (4355/1024 : ℝ) ≤ (754495552611401/12500000000000000000 : ℝ) := by
    have hpowers : (1273/12500 : ℝ)^4355 ≤ (754495552611401/12500000000000000000 : ℝ)^1024 := by
      have hnat : (1273 : ℕ)^4355*12500000000000000000^1024 ≤ 754495552611401^1024*12500^4355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1273 12500 754495552611401 12500000000000000000 4355 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1273/12500 : ℝ)) (X := (754495552611401/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4355 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7953/50000 : ℝ) ^ (4355/1024 : ℝ) ≤ (20103190333998693/50000000000000000000 : ℝ) := by
    have hpowers : (7953/50000 : ℝ)^4355 ≤ (20103190333998693/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7953 : ℕ)^4355*50000000000000000000^1024 ≤ 20103190333998693^1024*50000^4355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7953 50000 20103190333998693 50000000000000000000 4355 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7953/50000 : ℝ)) (X := (20103190333998693/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4355 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250754495552611401/6250000000000000000 : ℝ) ≤ (5000141918306223/5000000000000000 : ℝ) ^ (4355/1024 : ℝ) := by
    have hpowers : (6250754495552611401/6250000000000000000 : ℝ)^1024 ≤ (5000141918306223/5000000000000000 : ℝ)^4355 := by
      have hnat : (6250754495552611401 : ℕ)^1024*5000000000000000^4355 ≤ 5000141918306223^4355*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250754495552611401 6250000000000000000 5000141918306223 5000000000000000 1024 4355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000141918306223/5000000000000000 : ℝ)) (X := (6250754495552611401/6250000000000000000 : ℝ)) (by norm_num) 4355 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023121172544444297/50000000000000000000 : ℝ) ≤ (2000217422684671/2000000000000000 : ℝ) ^ (4355/1024 : ℝ) := by
    have hpowers : (50023121172544444297/50000000000000000000 : ℝ)^1024 ≤ (2000217422684671/2000000000000000 : ℝ)^4355 := by
      have hnat : (50023121172544444297 : ℕ)^1024*2000000000000000^4355 ≤ 2000217422684671^4355*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023121172544444297 50000000000000000000 2000217422684671 2000000000000000 1024 4355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000217422684671/2000000000000000 : ℝ)) (X := (50023121172544444297/50000000000000000000 : ℝ)) (by norm_num) 4355 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25020103190333998693/25000000000000000000 : ℝ) ≤ (1250236298779283/1250000000000000 : ℝ) ^ (4355/1024 : ℝ) := by
    have hpowers : (25020103190333998693/25000000000000000000 : ℝ)^1024 ≤ (1250236298779283/1250000000000000 : ℝ)^4355 := by
      have hnat : (25020103190333998693 : ℕ)^1024*1250000000000000^4355 ≤ 1250236298779283^4355*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25020103190333998693 25000000000000000000 1250236298779283 1250000000000000 1024 4355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250236298779283/1250000000000000 : ℝ)) (X := (25020103190333998693/25000000000000000000 : ℝ)) (by norm_num) 4355 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(754495552611401/12500000000000000000 : ℝ) ≤ ((114410525942023643/114440000000000000 : ℝ)+2*(803276810909/572200000000000 : ℝ)*(1273/12500 : ℝ))^(4355/1024 : ℝ) := by
    rw [show (114410525942023643/114440000000000000 : ℝ)+2*(803276810909/572200000000000 : ℝ)*(1273/12500 : ℝ)=(5000141918306223/5000000000000000 : ℝ) by norm_num, show 1+2*(754495552611401/12500000000000000000 : ℝ)=(6250754495552611401/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20103190333998693/50000000000000000000 : ℝ)+(754495552611401/12500000000000000000 : ℝ) ≤ ((114410525942023643/114440000000000000 : ℝ)+(803276810909/572200000000000 : ℝ)*((7953/50000 : ℝ)+(1273/12500 : ℝ)))^(4355/1024 : ℝ) := by
    rw [show (114410525942023643/114440000000000000 : ℝ)+(803276810909/572200000000000 : ℝ)*((7953/50000 : ℝ)+(1273/12500 : ℝ))=(2000217422684671/2000000000000000 : ℝ) by norm_num, show 1+(20103190333998693/50000000000000000000 : ℝ)+(754495552611401/12500000000000000000 : ℝ)=(50023121172544444297/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20103190333998693/50000000000000000000 : ℝ) ≤ ((114410525942023643/114440000000000000 : ℝ)+2*(803276810909/572200000000000 : ℝ)*(7953/50000 : ℝ))^(4355/1024 : ℝ) := by
    rw [show (114410525942023643/114440000000000000 : ℝ)+2*(803276810909/572200000000000 : ℝ)*(7953/50000 : ℝ)=(1250236298779283/1250000000000000 : ℝ) by norm_num, show 1+2*(20103190333998693/50000000000000000000 : ℝ)=(25020103190333998693/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (114410525942023643/114440000000000000 : ℝ)*(X 1 0+X 2 0)+(803276810909/572200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4355/1024 : ℝ)) (lo := (1273/12500 : ℝ)) (hi := (7953/50000 : ℝ)) (c := (114410525942023643/114440000000000000 : ℝ)) (alpha := (803276810909/572200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (114410525942023643/114440000000000000 : ℝ)*(X 0 1+X 2 1)+(803276810909/572200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4355/1024 : ℝ)) (lo := (1273/12500 : ℝ)) (hi := (7953/50000 : ℝ)) (c := (114410525942023643/114440000000000000 : ℝ)) (alpha := (803276810909/572200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (114410525942023643/114440000000000000 : ℝ)*(X 0 2+X 1 2)+(803276810909/572200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4355/1024 : ℝ)) (lo := (1273/12500 : ℝ)) (hi := (7953/50000 : ℝ)) (c := (114410525942023643/114440000000000000 : ℝ)) (alpha := (803276810909/572200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-399388039/2000000000 : ℝ)*X 0 0+(1084152139/2000000000 : ℝ)*X 0 1+(2618062307/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350785833/10000000000 : ℝ)*X 1 0+(-1045592423/5000000000 : ℝ)*X 1 1+(5236124647/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337696489/2500000000 : ℝ)*X 2 0+(261806227/500000000 : ℝ)*X 2 1+(-2091184823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2155956937/5000000000 : ℝ)*X 0 0+(411872863/1000000000 : ℝ)*X 0 1+(4513333677/10000000000 : ℝ)*X 0 2+(2155956937/5000000000 : ℝ)*X 1 0+(411872863/1000000000 : ℝ)*X 1 1+(4513333677/10000000000 : ℝ)*X 1 2+(2155956937/5000000000 : ℝ)*X 2 0+(411872863/1000000000 : ℝ)*X 2 1+(4513333677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-399391463/2000000000 : ℝ)*X 0 0+(5236872501/10000000000 : ℝ)*X 0 1+(5420008103/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060589101/2000000000 : ℝ)*X 1 0+(-381460167/2000000000 : ℝ)*X 1 1+(1084001723/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325736643/2500000000 : ℝ)*X 2 0+(5420007803/10000000000 : ℝ)*X 2 1+(-953650247/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((134748457/312500000 : ℝ)*X 0 0+(563966857/1250000000 : ℝ)*X 0 1+(4120335587/10000000000 : ℝ)*X 0 2+(134748457/312500000 : ℝ)*X 1 0+(563966857/1250000000 : ℝ)*X 1 1+(4120335587/10000000000 : ℝ)*X 1 2+(134748457/312500000 : ℝ)*X 2 0+(563966857/1250000000 : ℝ)*X 2 1+(4120335587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23674642118263190023093617/2861000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (721336101/50000000000000 : ℝ)*(base19) + (1378998829/100000000000000 : ℝ)*(base23) + (50344217/50000000000000 : ℝ)*(lower2) + (212370687/100000000000000 : ℝ)*(upper3) + (23711869/20000000000000 : ℝ)*(upper5) + (1987579094801691/50000000000000 : ℝ)*(major0) + (1987579094801691/50000000000000 : ℝ)*(major1) + (1987579094801691/50000000000000 : ℝ)*(major2) + (5416086376697271/100000000000000 : ℝ)*(sp0) + (1083222346432949/20000000000000 : ℝ)*(sp1) + (5416111795838117/100000000000000 : ℝ)*(sp2) + (253418995754757/10000000000000 : ℝ)*(sp3) + (1071925587/4000000000000 : ℝ)*(sp4) + (6485495227/50000000000000 : ℝ)*(sp7) + (2534202928538023/100000000000000 : ℝ)*(f.failure) + (2708056587418473/50000000000000 : ℝ)*(f.sum) + (19824021416289/14305000000000000000000000000 : ℝ)*base65 + (41582296536363887/5722000000000000000000000000000 : ℝ)*base68 + (112437719900849887/5722000000000000000000000000000 : ℝ)*base70 + (97828714355237887/5722000000000000000000000000000 : ℝ)*base72 + (50581338557649/14305000000000000000000000000 : ℝ)*base73 + (74806729960161887/5722000000000000000000000000000 : ℝ)*base76 + (27591320377011887/5722000000000000000000000000000 : ℝ)*base78 + (51744286212883887/5722000000000000000000000000000 : ℝ)*base80 + (15100668677733/7152500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1299357/2000000000000000000000 : ℝ)*base89 + (1299357/2000000000000000000000 : ℝ)*base91 + (1299357/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4067041429050379501313439/2861000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1812818283/100000000000000 : ℝ)*(base19) + (824600879/25000000000000 : ℝ)*(base23) + (394623787/100000000000000 : ℝ)*(upper3) + (96583933/100000000000000 : ℝ)*(lower4) + (230445083/100000000000000 : ℝ)*(upper5) + (2003844242431809/50000000000000 : ℝ)*(major0) + (2003844242431809/50000000000000 : ℝ)*(major1) + (2003844242431809/50000000000000 : ℝ)*(major2) + (19447582561/50000000000000 : ℝ)*(sp1) + (30796951623/50000000000000 : ℝ)*(sp2) + (2730217803327657/50000000000000 : ℝ)*(sp4) + (546039489867191/10000000000000 : ℝ)*(sp5) + (5460370714348553/100000000000000 : ℝ)*(sp6) + (2554941315687069/100000000000000 : ℝ)*(sp7) + (2554941315687069/100000000000000 : ℝ)*(f.failure) + (2730217803327657/50000000000000 : ℝ)*(f.sum) + (2532247220851/14305000000000000000000000000 : ℝ)*base65 + (17381276457220387/5722000000000000000000000000000 : ℝ)*base67 + (48716406953613/5722000000000000000000000000000 : ℝ)*base70 + (11114743162632387/5722000000000000000000000000000 : ℝ)*base71 + (32947469479229/14305000000000000000000000000 : ℝ)*base74 + (79547409254322387/5722000000000000000000000000000 : ℝ)*base75 + (1578788030480387/5722000000000000000000000000000 : ℝ)*base77 + (14752878080149613/5722000000000000000000000000000 : ℝ)*base80 + (9486977917/7152500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (5794929/2000000000000000000000 : ℝ)*base90 + (5794929/2000000000000000000000 : ℝ)*base92 + (5794929/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1396_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31372059/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7953/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1273/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11057/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7483/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1396_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1396_s4_0 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1998024403/10000000000 : ℝ)*x 0 + (541166359/1000000000 : ℝ)*x 1 + (2622254201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1998024403/10000000000 : ℝ)^1089 ≤ (12180338947891/100000000000000 : ℝ)^833 := by
    have hnat : (1998024403 : ℕ)^1089*100000000000000^833 ≤ 12180338947891^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1998024403 10000000000 12180338947891 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541166359/1000000000 : ℝ)^1089 ≤ (2800639735881/6250000000000 : ℝ)^833 := by
    have hnat : (541166359 : ℕ)^1089*6250000000000^833 ≤ 2800639735881^833*1000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541166359 1000000000 2800639735881 6250000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622254201/5000000000 : ℝ)^1089 ≤ (43009425269773/100000000000000 : ℝ)^833 := by
    have hnat : (2622254201 : ℕ)^1089*100000000000000^833 ≤ 43009425269773^833*5000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622254201 5000000000 43009425269773 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1998024403/10000000000 : ℝ), (541166359/1000000000 : ℝ), (2622254201/5000000000 : ℝ)] ![(12180338947891/100000000000000 : ℝ), (2800639735881/6250000000000 : ℝ), (43009425269773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1998024403/10000000000 : ℝ)|^1089 ≤ (12180338947891/100000000000000 : ℝ)^833
        have hw : |(-1998024403/10000000000 : ℝ)|=(1998024403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541166359/1000000000 : ℝ)|^1089 ≤ (2800639735881/6250000000000 : ℝ)^833
        have hw : |(541166359/1000000000 : ℝ)|=(541166359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622254201/5000000000 : ℝ)|^1089 ≤ (43009425269773/100000000000000 : ℝ)^833
        have hw : |(2622254201/5000000000 : ℝ)|=(2622254201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1396_s4_1 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (534844817/1000000000 : ℝ)*x 0 + (-520795307/2500000000 : ℝ)*x 1 + (2622254303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534844817/1000000000 : ℝ)^1089 ≤ (22063579136569/50000000000000 : ℝ)^833 := by
    have hnat : (534844817 : ℕ)^1089*50000000000000^833 ≤ 22063579136569^833*1000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534844817 1000000000 22063579136569 50000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520795307/2500000000 : ℝ)^1089 ≤ (6431707126419/50000000000000 : ℝ)^833 := by
    have hnat : (520795307 : ℕ)^1089*50000000000000^833 ≤ 6431707126419^833*2500000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520795307 2500000000 6431707126419 50000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622254303/5000000000 : ℝ)^1089 ≤ (43009427456889/100000000000000 : ℝ)^833 := by
    have hnat : (2622254303 : ℕ)^1089*100000000000000^833 ≤ 43009427456889^833*5000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622254303 5000000000 43009427456889 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534844817/1000000000 : ℝ), (-520795307/2500000000 : ℝ), (2622254303/5000000000 : ℝ)] ![(22063579136569/50000000000000 : ℝ), (6431707126419/50000000000000 : ℝ), (43009427456889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534844817/1000000000 : ℝ)|^1089 ≤ (22063579136569/50000000000000 : ℝ)^833
        have hw : |(534844817/1000000000 : ℝ)|=(534844817/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-520795307/2500000000 : ℝ)|^1089 ≤ (6431707126419/50000000000000 : ℝ)^833
        have hw : |(-520795307/2500000000 : ℝ)|=(520795307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622254303/5000000000 : ℝ)|^1089 ≤ (43009427456889/100000000000000 : ℝ)^833
        have hw : |(2622254303/5000000000 : ℝ)|=(2622254303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1396_s4_2 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5348448709/10000000000 : ℝ)*x 0 + (1048901747/2000000000 : ℝ)*x 1 + (-130198771/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348448709/10000000000 : ℝ)^1089 ≤ (44127164086801/100000000000000 : ℝ)^833 := by
    have hnat : (5348448709 : ℕ)^1089*100000000000000^833 ≤ 44127164086801^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348448709 10000000000 44127164086801 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048901747/2000000000 : ℝ)^1089 ≤ (43009428839919/100000000000000 : ℝ)^833 := by
    have hnat : (1048901747 : ℕ)^1089*100000000000000^833 ≤ 43009428839919^833*2000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048901747 2000000000 43009428839919 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130198771/625000000 : ℝ)^1089 ≤ (12863407052101/100000000000000 : ℝ)^833 := by
    have hnat : (130198771 : ℕ)^1089*100000000000000^833 ≤ 12863407052101^833*625000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130198771 625000000 12863407052101 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348448709/10000000000 : ℝ), (1048901747/2000000000 : ℝ), (-130198771/625000000 : ℝ)] ![(44127164086801/100000000000000 : ℝ), (43009428839919/100000000000000 : ℝ), (12863407052101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348448709/10000000000 : ℝ)|^1089 ≤ (44127164086801/100000000000000 : ℝ)^833
        have hw : |(5348448709/10000000000 : ℝ)|=(5348448709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048901747/2000000000 : ℝ)|^1089 ≤ (43009428839919/100000000000000 : ℝ)^833
        have hw : |(1048901747/2000000000 : ℝ)|=(1048901747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-130198771/625000000 : ℝ)|^1089 ≤ (12863407052101/100000000000000 : ℝ)^833
        have hw : |(-130198771/625000000 : ℝ)|=(130198771/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1396_s4_3 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (539072017/1250000000 : ℝ)*x 0 + (2068663927/5000000000 : ℝ)*x 1 + (4494572551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539072017/1250000000 : ℝ)^1089 ≤ (3330297345819/10000000000000 : ℝ)^833 := by
    have hnat : (539072017 : ℕ)^1089*10000000000000^833 ≤ 3330297345819^833*1250000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539072017 1250000000 3330297345819 10000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2068663927/5000000000 : ℝ)^1089 ≤ (6308980441457/20000000000000 : ℝ)^833 := by
    have hnat : (2068663927 : ℕ)^1089*20000000000000^833 ≤ 6308980441457^833*5000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068663927 5000000000 6308980441457 20000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4494572551/10000000000 : ℝ)^1089 ≤ (3515212431297/10000000000000 : ℝ)^833 := by
    have hnat : (4494572551 : ℕ)^1089*10000000000000^833 ≤ 3515212431297^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494572551 10000000000 3515212431297 10000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539072017/1250000000 : ℝ), (2068663927/5000000000 : ℝ), (4494572551/10000000000 : ℝ)] ![(3330297345819/10000000000000 : ℝ), (6308980441457/20000000000000 : ℝ), (3515212431297/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539072017/1250000000 : ℝ)|^1089 ≤ (3330297345819/10000000000000 : ℝ)^833
        have hw : |(539072017/1250000000 : ℝ)|=(539072017/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2068663927/5000000000 : ℝ)|^1089 ≤ (6308980441457/20000000000000 : ℝ)^833
        have hw : |(2068663927/5000000000 : ℝ)|=(2068663927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4494572551/10000000000 : ℝ)|^1089 ≤ (3515212431297/10000000000000 : ℝ)^833
        have hw : |(4494572551/10000000000 : ℝ)|=(4494572551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1396_s4_4 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1998036397/10000000000 : ℝ)*x 0 + (2622560973/5000000000 : ℝ)*x 1 + (5411047081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1998036397/10000000000 : ℝ)^1089 ≤ (5947477801/48828125000 : ℝ)^833 := by
    have hnat : (1998036397 : ℕ)^1089*48828125000^833 ≤ 5947477801^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1998036397 10000000000 5947477801 48828125000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622560973/5000000000 : ℝ)^1089 ≤ (43016003290721/100000000000000 : ℝ)^833 := by
    have hnat : (2622560973 : ℕ)^1089*100000000000000^833 ≤ 43016003290721^833*5000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622560973 5000000000 43016003290721 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411047081/10000000000 : ℝ)^1089 ≤ (44803562159319/100000000000000 : ℝ)^833 := by
    have hnat : (5411047081 : ℕ)^1089*100000000000000^833 ≤ 44803562159319^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411047081 10000000000 44803562159319 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1998036397/10000000000 : ℝ), (2622560973/5000000000 : ℝ), (5411047081/10000000000 : ℝ)] ![(5947477801/48828125000 : ℝ), (43016003290721/100000000000000 : ℝ), (44803562159319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1998036397/10000000000 : ℝ)|^1089 ≤ (5947477801/48828125000 : ℝ)^833
        have hw : |(-1998036397/10000000000 : ℝ)|=(1998036397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622560973/5000000000 : ℝ)|^1089 ≤ (43016003290721/100000000000000 : ℝ)^833
        have hw : |(2622560973/5000000000 : ℝ)|=(2622560973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411047081/10000000000 : ℝ)|^1089 ≤ (44803562159319/100000000000000 : ℝ)^833
        have hw : |(5411047081/10000000000 : ℝ)|=(5411047081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1396_s4_5 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (66314217/125000000 : ℝ)*x 0 + (-383328461/2000000000 : ℝ)*x 1 + (541104719/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66314217/125000000 : ℝ)^1089 ≤ (21830294787691/50000000000000 : ℝ)^833 := by
    have hnat : (66314217 : ℕ)^1089*50000000000000^833 ≤ 21830294787691^833*125000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66314217 125000000 21830294787691 50000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (383328461/2000000000 : ℝ)^1089 ≤ (5767923533597/50000000000000 : ℝ)^833 := by
    have hnat : (383328461 : ℕ)^1089*50000000000000^833 ≤ 5767923533597^833*2000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383328461 2000000000 5767923533597 50000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541104719/1000000000 : ℝ)^1089 ≤ (22401781669603/50000000000000 : ℝ)^833 := by
    have hnat : (541104719 : ℕ)^1089*50000000000000^833 ≤ 22401781669603^833*1000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541104719 1000000000 22401781669603 50000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66314217/125000000 : ℝ), (-383328461/2000000000 : ℝ), (541104719/1000000000 : ℝ)] ![(21830294787691/50000000000000 : ℝ), (5767923533597/50000000000000 : ℝ), (22401781669603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66314217/125000000 : ℝ)|^1089 ≤ (21830294787691/50000000000000 : ℝ)^833
        have hw : |(66314217/125000000 : ℝ)|=(66314217/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-383328461/2000000000 : ℝ)|^1089 ≤ (5767923533597/50000000000000 : ℝ)^833
        have hw : |(-383328461/2000000000 : ℝ)|=(383328461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541104719/1000000000 : ℝ)|^1089 ≤ (22401781669603/50000000000000 : ℝ)^833
        have hw : |(541104719/1000000000 : ℝ)|=(541104719/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1396_s4_6 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305137319/10000000000 : ℝ)*x 0 + (2705523573/5000000000 : ℝ)*x 1 + (-958321211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305137319/10000000000 : ℝ)^1089 ≤ (43660589134259/100000000000000 : ℝ)^833 := by
    have hnat : (5305137319 : ℕ)^1089*100000000000000^833 ≤ 43660589134259^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305137319 10000000000 43660589134259 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705523573/5000000000 : ℝ)^1089 ≤ (44803562862921/100000000000000 : ℝ)^833 := by
    have hnat : (2705523573 : ℕ)^1089*100000000000000^833 ≤ 44803562862921^833*5000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705523573 5000000000 44803562862921 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (958321211/5000000000 : ℝ)^1089 ≤ (11535847987807/100000000000000 : ℝ)^833 := by
    have hnat : (958321211 : ℕ)^1089*100000000000000^833 ≤ 11535847987807^833*5000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958321211 5000000000 11535847987807 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305137319/10000000000 : ℝ), (2705523573/5000000000 : ℝ), (-958321211/5000000000 : ℝ)] ![(43660589134259/100000000000000 : ℝ), (44803562862921/100000000000000 : ℝ), (11535847987807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305137319/10000000000 : ℝ)|^1089 ≤ (43660589134259/100000000000000 : ℝ)^833
        have hw : |(5305137319/10000000000 : ℝ)|=(5305137319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705523573/5000000000 : ℝ)|^1089 ≤ (44803562862921/100000000000000 : ℝ)^833
        have hw : |(2705523573/5000000000 : ℝ)|=(2705523573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-958321211/5000000000 : ℝ)|^1089 ≤ (11535847987807/100000000000000 : ℝ)^833
        have hw : |(-958321211/5000000000 : ℝ)|=(958321211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1396_s4_7 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1078150423/2500000000 : ℝ)*x 0 + (2246631041/5000000000 : ℝ)*x 1 + (2069323049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078150423/2500000000 : ℝ)^1089 ≤ (4162903932473/12500000000000 : ℝ)^833 := by
    have hnat : (1078150423 : ℕ)^1089*12500000000000^833 ≤ 4162903932473^833*2500000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078150423 2500000000 4162903932473 12500000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246631041/5000000000 : ℝ)^1089 ≤ (17569362950129/50000000000000 : ℝ)^833 := by
    have hnat : (2246631041 : ℕ)^1089*50000000000000^833 ≤ 17569362950129^833*5000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246631041 5000000000 17569362950129 50000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2069323049/5000000000 : ℝ)^1089 ≤ (31558042625603/100000000000000 : ℝ)^833 := by
    have hnat : (2069323049 : ℕ)^1089*100000000000000^833 ≤ 31558042625603^833*5000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069323049 5000000000 31558042625603 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078150423/2500000000 : ℝ), (2246631041/5000000000 : ℝ), (2069323049/5000000000 : ℝ)] ![(4162903932473/12500000000000 : ℝ), (17569362950129/50000000000000 : ℝ), (31558042625603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078150423/2500000000 : ℝ)|^1089 ≤ (4162903932473/12500000000000 : ℝ)^833
        have hw : |(1078150423/2500000000 : ℝ)|=(1078150423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246631041/5000000000 : ℝ)|^1089 ≤ (17569362950129/50000000000000 : ℝ)^833
        have hw : |(2246631041/5000000000 : ℝ)|=(2246631041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2069323049/5000000000 : ℝ)|^1089 ≤ (31558042625603/100000000000000 : ℝ)^833
        have hw : |(2069323049/5000000000 : ℝ)|=(2069323049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1396_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31372059/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7483/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11057/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2809/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1847/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7483/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11057/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7483/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11057/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7483/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11057/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7483/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11057/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7483/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11057/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7483/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11057/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11057/100000 : ℝ) ^ (4355/1024 : ℝ) ≤ (535225429437809/6250000000000000000 : ℝ) := by
    have hpowers : (11057/100000 : ℝ)^4355 ≤ (535225429437809/6250000000000000000 : ℝ)^1024 := by
      have hnat : (11057 : ℕ)^4355*6250000000000000000^1024 ≤ 535225429437809^1024*100000^4355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11057 100000 535225429437809 6250000000000000000 4355 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11057/100000 : ℝ)) (X := (535225429437809/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4355 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7483/50000 : ℝ) ^ (4355/1024 : ℝ) ≤ (15515033609243891/50000000000000000000 : ℝ) := by
    have hpowers : (7483/50000 : ℝ)^4355 ≤ (15515033609243891/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7483 : ℕ)^4355*50000000000000000000^1024 ≤ 15515033609243891^1024*50000^4355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7483 50000 15515033609243891 50000000000000000000 4355 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7483/50000 : ℝ)) (X := (15515033609243891/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4355 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125535225429437809/3125000000000000000 : ℝ) ≤ (2000080537856377/2000000000000000 : ℝ) ^ (4355/1024 : ℝ) := by
    have hpowers : (3125535225429437809/3125000000000000000 : ℝ)^1024 ≤ (2000080537856377/2000000000000000 : ℝ)^4355 := by
      have hnat : (3125535225429437809 : ℕ)^1024*2000000000000000^4355 ≤ 2000080537856377^4355*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125535225429437809 3125000000000000000 2000080537856377 2000000000000000 1024 4355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000080537856377/2000000000000000 : ℝ)) (X := (3125535225429437809/3125000000000000000 : ℝ)) (by norm_num) 4355 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019796837044746363/50000000000000000000 : ℝ) ≤ (5000465416584961/5000000000000000 : ℝ) ^ (4355/1024 : ℝ) := by
    have hpowers : (50019796837044746363/50000000000000000000 : ℝ)^1024 ≤ (5000465416584961/5000000000000000 : ℝ)^4355 := by
      have hnat : (50019796837044746363 : ℕ)^1024*5000000000000000^4355 ≤ 5000465416584961^4355*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019796837044746363 50000000000000000000 5000465416584961 5000000000000000 1024 4355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000465416584961/5000000000000000 : ℝ)) (X := (50019796837044746363/50000000000000000000 : ℝ)) (by norm_num) 4355 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015515033609243891/25000000000000000000 : ℝ) ≤ (10001458977057959/10000000000000000 : ℝ) ^ (4355/1024 : ℝ) := by
    have hpowers : (25015515033609243891/25000000000000000000 : ℝ)^1024 ≤ (10001458977057959/10000000000000000 : ℝ)^4355 := by
      have hnat : (25015515033609243891 : ℕ)^1024*10000000000000000^4355 ≤ 10001458977057959^4355*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015515033609243891 25000000000000000000 10001458977057959 10000000000000000 1024 4355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001458977057959/10000000000000000 : ℝ)) (X := (25015515033609243891/25000000000000000000 : ℝ)) (by norm_num) 4355 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(535225429437809/6250000000000000000 : ℝ) ≤ ((13026631579487612749/13030000000000000000 : ℝ)+2*(176047962679/130300000000000 : ℝ)*(11057/100000 : ℝ))^(4355/1024 : ℝ) := by
    rw [show (13026631579487612749/13030000000000000000 : ℝ)+2*(176047962679/130300000000000 : ℝ)*(11057/100000 : ℝ)=(2000080537856377/2000000000000000 : ℝ) by norm_num, show 1+2*(535225429437809/6250000000000000000 : ℝ)=(3125535225429437809/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15515033609243891/50000000000000000000 : ℝ)+(535225429437809/6250000000000000000 : ℝ) ≤ ((13026631579487612749/13030000000000000000 : ℝ)+(176047962679/130300000000000 : ℝ)*((7483/50000 : ℝ)+(11057/100000 : ℝ)))^(4355/1024 : ℝ) := by
    rw [show (13026631579487612749/13030000000000000000 : ℝ)+(176047962679/130300000000000 : ℝ)*((7483/50000 : ℝ)+(11057/100000 : ℝ))=(5000465416584961/5000000000000000 : ℝ) by norm_num, show 1+(15515033609243891/50000000000000000000 : ℝ)+(535225429437809/6250000000000000000 : ℝ)=(50019796837044746363/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15515033609243891/50000000000000000000 : ℝ) ≤ ((13026631579487612749/13030000000000000000 : ℝ)+2*(176047962679/130300000000000 : ℝ)*(7483/50000 : ℝ))^(4355/1024 : ℝ) := by
    rw [show (13026631579487612749/13030000000000000000 : ℝ)+2*(176047962679/130300000000000 : ℝ)*(7483/50000 : ℝ)=(10001458977057959/10000000000000000 : ℝ) by norm_num, show 1+2*(15515033609243891/50000000000000000000 : ℝ)=(25015515033609243891/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13026631579487612749/13030000000000000000 : ℝ)*(X 1 0+X 2 0)+(176047962679/130300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4355/1024 : ℝ)) (lo := (11057/100000 : ℝ)) (hi := (7483/50000 : ℝ)) (c := (13026631579487612749/13030000000000000000 : ℝ)) (alpha := (176047962679/130300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13026631579487612749/13030000000000000000 : ℝ)*(X 0 1+X 2 1)+(176047962679/130300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4355/1024 : ℝ)) (lo := (11057/100000 : ℝ)) (hi := (7483/50000 : ℝ)) (c := (13026631579487612749/13030000000000000000 : ℝ)) (alpha := (176047962679/130300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13026631579487612749/13030000000000000000 : ℝ)*(X 0 2+X 1 2)+(176047962679/130300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4355/1024 : ℝ)) (lo := (11057/100000 : ℝ)) (hi := (7483/50000 : ℝ)) (c := (13026631579487612749/13030000000000000000 : ℝ)) (alpha := (176047962679/130300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1998024403/10000000000 : ℝ)*X 0 0+(541166359/1000000000 : ℝ)*X 0 1+(2622254201/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534844817/1000000000 : ℝ)*X 1 0+(-520795307/2500000000 : ℝ)*X 1 1+(2622254303/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348448709/10000000000 : ℝ)*X 2 0+(1048901747/2000000000 : ℝ)*X 2 1+(-130198771/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((539072017/1250000000 : ℝ)*X 0 0+(2068663927/5000000000 : ℝ)*X 0 1+(4494572551/10000000000 : ℝ)*X 0 2+(539072017/1250000000 : ℝ)*X 1 0+(2068663927/5000000000 : ℝ)*X 1 1+(4494572551/10000000000 : ℝ)*X 1 2+(539072017/1250000000 : ℝ)*X 2 0+(2068663927/5000000000 : ℝ)*X 2 1+(4494572551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1998036397/10000000000 : ℝ)*X 0 0+(2622560973/5000000000 : ℝ)*X 0 1+(5411047081/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((66314217/125000000 : ℝ)*X 1 0+(-383328461/2000000000 : ℝ)*X 1 1+(541104719/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305137319/10000000000 : ℝ)*X 2 0+(2705523573/5000000000 : ℝ)*X 2 1+(-958321211/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1078150423/2500000000 : ℝ)*X 0 0+(2246631041/5000000000 : ℝ)*X 0 1+(2069323049/5000000000 : ℝ)*X 0 2+(1078150423/2500000000 : ℝ)*X 1 0+(2246631041/5000000000 : ℝ)*X 1 1+(2069323049/5000000000 : ℝ)*X 1 2+(1078150423/2500000000 : ℝ)*X 2 0+(2246631041/5000000000 : ℝ)*X 2 1+(2069323049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (376332981216062399943672561/65150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1784732913/100000000000000 : ℝ)*(base19) + (2479708543/100000000000000 : ℝ)*(base23) + (1701843/20000000000000 : ℝ)*(lower2) + (756039311/100000000000000 : ℝ)*(upper5) + (439091166479063/10000000000000 : ℝ)*(major0) + (439091166479063/10000000000000 : ℝ)*(major1) + (439091166479063/10000000000000 : ℝ)*(major2) + (1495625400646601/25000000000000 : ℝ)*(sp0) + (5982558108970843/100000000000000 : ℝ)*(sp1) + (5982570748487703/100000000000000 : ℝ)*(sp2) + (1399614988551643/50000000000000 : ℝ)*(sp3) + (35812804921/50000000000000 : ℝ)*(sp4) + (13334492491/100000000000000 : ℝ)*(sp5) + (3986346957/20000000000000 : ℝ)*(sp7) + (349906238604759/12500000000000 : ℝ)*(f.failure) + (2991286614098123/50000000000000 : ℝ)*(f.sum) + (72852621067/162875000000000000000000000 : ℝ)*base66 + (35720450706274187/130300000000000000000000000000000 : ℝ)*base67 + (708447035579725813/130300000000000000000000000000000 : ℝ)*base70 + (974695678697725813/130300000000000000000000000000000 : ℝ)*base72 + (10258555177089/1303000000000000000000000000 : ℝ)*base73 + (1270077501781125813/130300000000000000000000000000000 : ℝ)*base76 + (2582917481414825813/130300000000000000000000000000000 : ℝ)*base78 + (536077296172374187/130300000000000000000000000000000 : ℝ)*base79 + (426484683923/130300000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2028781/250000000000000000000 : ℝ)*base89 + (2028781/250000000000000000000 : ℝ)*base91 + (2028781/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (348579450064388067022493499/40718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (296869493/20000000000000 : ℝ)*(base19) + (1400764767/100000000000000 : ℝ)*(base23) + (88963617/50000000000000 : ℝ)*(upper3) + (155323/3125000000000 : ℝ)*(lower4) + (55436199/25000000000000 : ℝ)*(upper5) + (552922901156417/12500000000000 : ℝ)*(major0) + (552922901156417/12500000000000 : ℝ)*(major1) + (552922901156417/12500000000000 : ℝ)*(major2) + (1067554973/3125000000000 : ℝ)*(sp1) + (28481001739/100000000000000 : ℝ)*(sp2) + (1205363058275973/20000000000000 : ℝ)*(sp4) + (376673727829579/6250000000000 : ℝ)*(sp5) + (75334817620167/1250000000000 : ℝ)*(sp6) + (1409975420883703/50000000000000 : ℝ)*(sp7) + (1409975420883703/50000000000000 : ℝ)*(f.failure) + (1205363058275973/20000000000000 : ℝ)*(f.sum) + (19243967234561/6515000000000000000000000000 : ℝ)*base66 + (782742326593410333/162875000000000000000000000000000 : ℝ)*base67 + (631760150920714667/162875000000000000000000000000000 : ℝ)*base70 + (1039610431480339667/162875000000000000000000000000000 : ℝ)*base72 + (4549841644579/1628750000000000000000000000 : ℝ)*base74 + (1255576044649839667/162875000000000000000000000000000 : ℝ)*base76 + (1740422895004464667/162875000000000000000000000000000 : ℝ)*base78 + (812315910382214667/162875000000000000000000000000000 : ℝ)*base80 + (332901982421/1628750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2654477/1000000000000000000000 : ℝ)*base89 + (2654477/1000000000000000000000 : ℝ)*base91 + (2654477/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1396_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31372059/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7483/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11057/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2809/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1396_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1396_s5_0 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1998194611/10000000000 : ℝ)*x 0 + (2705081837/5000000000 : ℝ)*x 1 + (5245896201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1998194611/10000000000 : ℝ)^1089 ≤ (380677983461/3125000000000 : ℝ)^833 := by
    have hnat : (1998194611 : ℕ)^1089*3125000000000^833 ≤ 380677983461^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1998194611 10000000000 380677983461 3125000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705081837/5000000000 : ℝ)^1089 ≤ (44793999822197/100000000000000 : ℝ)^833 := by
    have hnat : (2705081837 : ℕ)^1089*100000000000000^833 ≤ 44793999822197^833*5000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705081837 5000000000 44793999822197 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245896201/10000000000 : ℝ)^1089 ≤ (10756076172077/25000000000000 : ℝ)^833 := by
    have hnat : (5245896201 : ℕ)^1089*25000000000000^833 ≤ 10756076172077^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245896201 10000000000 10756076172077 25000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1998194611/10000000000 : ℝ), (2705081837/5000000000 : ℝ), (5245896201/10000000000 : ℝ)] ![(380677983461/3125000000000 : ℝ), (44793999822197/100000000000000 : ℝ), (10756076172077/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1998194611/10000000000 : ℝ)|^1089 ≤ (380677983461/3125000000000 : ℝ)^833
        have hw : |(-1998194611/10000000000 : ℝ)|=(1998194611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705081837/5000000000 : ℝ)|^1089 ≤ (44793999822197/100000000000000 : ℝ)^833
        have hw : |(2705081837/5000000000 : ℝ)|=(2705081837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245896201/10000000000 : ℝ)|^1089 ≤ (10756076172077/25000000000000 : ℝ)^833
        have hw : |(5245896201/10000000000 : ℝ)|=(5245896201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1396_s5_1 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (213922501/400000000 : ℝ)*x 0 + (-1040926803/5000000000 : ℝ)*x 1 + (5245896069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213922501/400000000 : ℝ)^1089 ≤ (44122998746209/100000000000000 : ℝ)^833 := by
    have hnat : (213922501 : ℕ)^1089*100000000000000^833 ≤ 44122998746209^833*400000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213922501 400000000 44122998746209 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040926803/5000000000 : ℝ)^1089 ≤ (12852697974557/100000000000000 : ℝ)^833 := by
    have hnat : (1040926803 : ℕ)^1089*100000000000000^833 ≤ 12852697974557^833*5000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040926803 5000000000 12852697974557 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245896069/10000000000 : ℝ)^1089 ≤ (43024303273/100000000000 : ℝ)^833 := by
    have hnat : (5245896069 : ℕ)^1089*100000000000^833 ≤ 43024303273^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245896069 10000000000 43024303273 100000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213922501/400000000 : ℝ), (-1040926803/5000000000 : ℝ), (5245896069/10000000000 : ℝ)] ![(44122998746209/100000000000000 : ℝ), (12852697974557/100000000000000 : ℝ), (43024303273/100000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213922501/400000000 : ℝ)|^1089 ≤ (44122998746209/100000000000000 : ℝ)^833
        have hw : |(213922501/400000000 : ℝ)|=(213922501/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1040926803/5000000000 : ℝ)|^1089 ≤ (12852697974557/100000000000000 : ℝ)^833
        have hw : |(-1040926803/5000000000 : ℝ)|=(1040926803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245896069/10000000000 : ℝ)|^1089 ≤ (43024303273/100000000000 : ℝ)^833
        have hw : |(5245896069/10000000000 : ℝ)|=(5245896069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1396_s5_2 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2674031127/5000000000 : ℝ)*x 0 + (262294811/500000000 : ℝ)*x 1 + (-1040926883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674031127/5000000000 : ℝ)^1089 ≤ (1378843619477/3125000000000 : ℝ)^833 := by
    have hnat : (2674031127 : ℕ)^1089*3125000000000^833 ≤ 1378843619477^833*5000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674031127 5000000000 1378843619477 3125000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262294811/500000000 : ℝ)^1089 ≤ (43024304892027/100000000000000 : ℝ)^833 := by
    have hnat : (262294811 : ℕ)^1089*100000000000000^833 ≤ 43024304892027^833*500000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262294811 500000000 43024304892027 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040926883/5000000000 : ℝ)^1089 ≤ (3213174816479/25000000000000 : ℝ)^833 := by
    have hnat : (1040926883 : ℕ)^1089*25000000000000^833 ≤ 3213174816479^833*5000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040926883 5000000000 3213174816479 25000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674031127/5000000000 : ℝ), (262294811/500000000 : ℝ), (-1040926883/5000000000 : ℝ)] ![(1378843619477/3125000000000 : ℝ), (43024304892027/100000000000000 : ℝ), (3213174816479/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674031127/5000000000 : ℝ)|^1089 ≤ (1378843619477/3125000000000 : ℝ)^833
        have hw : |(2674031127/5000000000 : ℝ)|=(2674031127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262294811/500000000 : ℝ)|^1089 ≤ (43024304892027/100000000000000 : ℝ)^833
        have hw : |(262294811/500000000 : ℝ)|=(262294811/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1040926883/5000000000 : ℝ)|^1089 ≤ (3213174816479/25000000000000 : ℝ)^833
        have hw : |(-1040926883/5000000000 : ℝ)|=(1040926883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1396_s5_3 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1078169513/2500000000 : ℝ)*x 0 + (1035100317/2500000000 : ℝ)*x 1 + (4491475077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078169513/2500000000 : ℝ)^1089 ≤ (1665200117897/5000000000000 : ℝ)^833 := by
    have hnat : (1078169513 : ℕ)^1089*5000000000000^833 ≤ 1665200117897^833*2500000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078169513 2500000000 1665200117897 5000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035100317/2500000000 : ℝ)^1089 ≤ (7893885093133/25000000000000 : ℝ)^833 := by
    have hnat : (1035100317 : ℕ)^1089*25000000000000^833 ≤ 7893885093133^833*2500000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035100317 2500000000 7893885093133 25000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491475077/10000000000 : ℝ)^1089 ≤ (35120457254209/100000000000000 : ℝ)^833 := by
    have hnat : (4491475077 : ℕ)^1089*100000000000000^833 ≤ 35120457254209^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491475077 10000000000 35120457254209 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078169513/2500000000 : ℝ), (1035100317/2500000000 : ℝ), (4491475077/10000000000 : ℝ)] ![(1665200117897/5000000000000 : ℝ), (7893885093133/25000000000000 : ℝ), (35120457254209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078169513/2500000000 : ℝ)|^1089 ≤ (1665200117897/5000000000000 : ℝ)^833
        have hw : |(1078169513/2500000000 : ℝ)|=(1078169513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035100317/2500000000 : ℝ)|^1089 ≤ (7893885093133/25000000000000 : ℝ)^833
        have hw : |(1035100317/2500000000 : ℝ)|=(1035100317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491475077/10000000000 : ℝ)|^1089 ≤ (35120457254209/100000000000000 : ℝ)^833
        have hw : |(4491475077/10000000000 : ℝ)|=(4491475077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1396_s5_4 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1998206369/10000000000 : ℝ)*x 0 + (5246488551/10000000000 : ℝ)*x 1 + (5409568233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1998206369/10000000000 : ℝ)^1089 ≤ (12181789180913/100000000000000 : ℝ)^833 := by
    have hnat : (1998206369 : ℕ)^1089*100000000000000^833 ≤ 12181789180913^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1998206369 10000000000 12181789180913 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246488551/10000000000 : ℝ)^1089 ≤ (2151532799669/5000000000000 : ℝ)^833 := by
    have hnat : (5246488551 : ℕ)^1089*5000000000000^833 ≤ 2151532799669^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246488551 10000000000 2151532799669 5000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409568233/10000000000 : ℝ)^1089 ≤ (44787554810519/100000000000000 : ℝ)^833 := by
    have hnat : (5409568233 : ℕ)^1089*100000000000000^833 ≤ 44787554810519^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409568233 10000000000 44787554810519 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1998206369/10000000000 : ℝ), (5246488551/10000000000 : ℝ), (5409568233/10000000000 : ℝ)] ![(12181789180913/100000000000000 : ℝ), (2151532799669/5000000000000 : ℝ), (44787554810519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1998206369/10000000000 : ℝ)|^1089 ≤ (12181789180913/100000000000000 : ℝ)^833
        have hw : |(-1998206369/10000000000 : ℝ)|=(1998206369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246488551/10000000000 : ℝ)|^1089 ≤ (2151532799669/5000000000000 : ℝ)^833
        have hw : |(5246488551/10000000000 : ℝ)|=(5246488551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409568233/10000000000 : ℝ)|^1089 ≤ (44787554810519/100000000000000 : ℝ)^833
        have hw : |(5409568233/10000000000 : ℝ)|=(5409568233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1396_s5_5 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (265274969/500000000 : ℝ)*x 0 + (-959090811/5000000000 : ℝ)*x 1 + (5409568223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265274969/500000000 : ℝ)^1089 ≤ (43664484624683/100000000000000 : ℝ)^833 := by
    have hnat : (265274969 : ℕ)^1089*100000000000000^833 ≤ 43664484624683^833*500000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265274969 500000000 43664484624683 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (959090811/5000000000 : ℝ)^1089 ≤ (11547960659341/100000000000000 : ℝ)^833 := by
    have hnat : (959090811 : ℕ)^1089*100000000000000^833 ≤ 11547960659341^833*5000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959090811 5000000000 11547960659341 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409568223/10000000000 : ℝ)^1089 ≤ (22393777351141/50000000000000 : ℝ)^833 := by
    have hnat : (5409568223 : ℕ)^1089*50000000000000^833 ≤ 22393777351141^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409568223 10000000000 22393777351141 50000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265274969/500000000 : ℝ), (-959090811/5000000000 : ℝ), (5409568223/10000000000 : ℝ)] ![(43664484624683/100000000000000 : ℝ), (11547960659341/100000000000000 : ℝ), (22393777351141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265274969/500000000 : ℝ)|^1089 ≤ (43664484624683/100000000000000 : ℝ)^833
        have hw : |(265274969/500000000 : ℝ)|=(265274969/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-959090811/5000000000 : ℝ)|^1089 ≤ (11547960659341/100000000000000 : ℝ)^833
        have hw : |(-959090811/5000000000 : ℝ)|=(959090811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409568223/10000000000 : ℝ)|^1089 ≤ (22393777351141/50000000000000 : ℝ)^833
        have hw : |(5409568223/10000000000 : ℝ)|=(5409568223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1396_s5_6 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652749693/5000000000 : ℝ)*x 0 + (216382729/400000000 : ℝ)*x 1 + (-1918181611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652749693/5000000000 : ℝ)^1089 ≤ (43664484689239/100000000000000 : ℝ)^833 := by
    have hnat : (2652749693 : ℕ)^1089*100000000000000^833 ≤ 43664484689239^833*5000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652749693 5000000000 43664484689239 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216382729/400000000 : ℝ)^1089 ≤ (44787554723929/100000000000000 : ℝ)^833 := by
    have hnat : (216382729 : ℕ)^1089*100000000000000^833 ≤ 44787554723929^833*400000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216382729 400000000 44787554723929 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1918181611/10000000000 : ℝ)^1089 ≤ (5773980286383/50000000000000 : ℝ)^833 := by
    have hnat : (1918181611 : ℕ)^1089*50000000000000^833 ≤ 5773980286383^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918181611 10000000000 5773980286383 50000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652749693/5000000000 : ℝ), (216382729/400000000 : ℝ), (-1918181611/10000000000 : ℝ)] ![(43664484689239/100000000000000 : ℝ), (44787554723929/100000000000000 : ℝ), (5773980286383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652749693/5000000000 : ℝ)|^1089 ≤ (43664484689239/100000000000000 : ℝ)^833
        have hw : |(2652749693/5000000000 : ℝ)|=(2652749693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216382729/400000000 : ℝ)|^1089 ≤ (44787554723929/100000000000000 : ℝ)^833
        have hw : |(216382729/400000000 : ℝ)|=(216382729/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1918181611/10000000000 : ℝ)|^1089 ≤ (5773980286383/50000000000000 : ℝ)^833
        have hw : |(-1918181611/10000000000 : ℝ)|=(1918181611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1396_s5_7 (p : ℝ) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ)) (x : Fin 3 → ℝ) :
    (862540663/2000000000 : ℝ)*x 0 + (4490208787/10000000000 : ℝ)*x 1 + (4141673933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862540663/2000000000 : ℝ)^1089 ≤ (3330425740339/10000000000000 : ℝ)^833 := by
    have hnat : (862540663 : ℕ)^1089*10000000000000^833 ≤ 3330425740339^833*2000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862540663 2000000000 3330425740339 10000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4490208787/10000000000 : ℝ)^1089 ≤ (35107513257111/100000000000000 : ℝ)^833 := by
    have hnat : (4490208787 : ℕ)^1089*100000000000000^833 ≤ 35107513257111^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490208787 10000000000 35107513257111 100000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4141673933/10000000000 : ℝ)^1089 ≤ (15794114663637/50000000000000 : ℝ)^833 := by
    have hnat : (4141673933 : ℕ)^1089*50000000000000^833 ≤ 15794114663637^833*10000000000^1089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4141673933 10000000000 15794114663637 50000000000000 1089 833 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1089/256 : ℝ)) 1089 833 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862540663/2000000000 : ℝ), (4490208787/10000000000 : ℝ), (4141673933/10000000000 : ℝ)] ![(3330425740339/10000000000000 : ℝ), (35107513257111/100000000000000 : ℝ), (15794114663637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862540663/2000000000 : ℝ)|^1089 ≤ (3330425740339/10000000000000 : ℝ)^833
        have hw : |(862540663/2000000000 : ℝ)|=(862540663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4490208787/10000000000 : ℝ)|^1089 ≤ (35107513257111/100000000000000 : ℝ)^833
        have hw : |(4490208787/10000000000 : ℝ)|=(4490208787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4141673933/10000000000 : ℝ)|^1089 ≤ (15794114663637/50000000000000 : ℝ)^833
        have hw : |(4141673933/10000000000 : ℝ)|=(4141673933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1396_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31372059/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2809/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5633/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1843/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1847/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2809/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1847/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2809/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1847/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2809/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1847/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2809/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1847/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2809/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1847/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2809/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2809/25000 : ℝ) ^ (4355/1024 : ℝ) ≤ (458446274811109/5000000000000000000 : ℝ) := by
    have hpowers : (2809/25000 : ℝ)^4355 ≤ (458446274811109/5000000000000000000 : ℝ)^1024 := by
      have hnat : (2809 : ℕ)^4355*5000000000000000000^1024 ≤ 458446274811109^1024*25000^4355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2809 25000 458446274811109 5000000000000000000 4355 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2809/25000 : ℝ)) (X := (458446274811109/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4355 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1847/12500 : ℝ) ^ (4355/1024 : ℝ) ≤ (3673616563522917/12500000000000000000 : ℝ) := by
    have hpowers : (1847/12500 : ℝ)^4355 ≤ (3673616563522917/12500000000000000000 : ℝ)^1024 := by
      have hnat : (1847 : ℕ)^4355*12500000000000000000^1024 ≤ 3673616563522917^1024*12500^4355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1847 12500 3673616563522917 12500000000000000000 4355 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1847/12500 : ℝ)) (X := (3673616563522917/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4355 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500458446274811109/2500000000000000000 : ℝ) ≤ (10000431151381327/10000000000000000 : ℝ) ^ (4355/1024 : ℝ) := by
    have hpowers : (2500458446274811109/2500000000000000000 : ℝ)^1024 ≤ (10000431151381327/10000000000000000 : ℝ)^4355 := by
      have hnat : (2500458446274811109 : ℕ)^1024*10000000000000000^4355 ≤ 10000431151381327^4355*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500458446274811109 2500000000000000000 10000431151381327 10000000000000000 1024 4355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000431151381327/10000000000000000 : ℝ)) (X := (2500458446274811109/2500000000000000000 : ℝ)) (by norm_num) 4355 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009639464501101379/25000000000000000000 : ℝ) ≤ (10000906485092591/10000000000000000 : ℝ) ^ (4355/1024 : ℝ) := by
    have hpowers : (25009639464501101379/25000000000000000000 : ℝ)^1024 ≤ (10000906485092591/10000000000000000 : ℝ)^4355 := by
      have hnat : (25009639464501101379 : ℕ)^1024*10000000000000000^4355 ≤ 10000906485092591^4355*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009639464501101379 25000000000000000000 10000906485092591 10000000000000000 1024 4355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000906485092591/10000000000000000 : ℝ)) (X := (25009639464501101379/25000000000000000000 : ℝ)) (by norm_num) 4355 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253673616563522917/6250000000000000000 : ℝ) ≤ (2000276363760771/2000000000000000 : ℝ) ^ (4355/1024 : ℝ) := by
    have hpowers : (6253673616563522917/6250000000000000000 : ℝ)^1024 ≤ (2000276363760771/2000000000000000 : ℝ)^4355 := by
      have hnat : (6253673616563522917 : ℕ)^1024*2000000000000000^4355 ≤ 2000276363760771^4355*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253673616563522917 6250000000000000000 2000276363760771 2000000000000000 1024 4355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000276363760771/2000000000000000 : ℝ)) (X := (6253673616563522917/6250000000000000000 : ℝ)) (by norm_num) 4355 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(458446274811109/5000000000000000000 : ℝ) ≤ ((8847711144182593243/8850000000000000000 : ℝ)+2*(14854178477/11062500000000 : ℝ)*(2809/25000 : ℝ))^(4355/1024 : ℝ) := by
    rw [show (8847711144182593243/8850000000000000000 : ℝ)+2*(14854178477/11062500000000 : ℝ)*(2809/25000 : ℝ)=(10000431151381327/10000000000000000 : ℝ) by norm_num, show 1+2*(458446274811109/5000000000000000000 : ℝ)=(2500458446274811109/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3673616563522917/12500000000000000000 : ℝ)+(458446274811109/5000000000000000000 : ℝ) ≤ ((8847711144182593243/8850000000000000000 : ℝ)+(14854178477/11062500000000 : ℝ)*((1847/12500 : ℝ)+(2809/25000 : ℝ)))^(4355/1024 : ℝ) := by
    rw [show (8847711144182593243/8850000000000000000 : ℝ)+(14854178477/11062500000000 : ℝ)*((1847/12500 : ℝ)+(2809/25000 : ℝ))=(10000906485092591/10000000000000000 : ℝ) by norm_num, show 1+(3673616563522917/12500000000000000000 : ℝ)+(458446274811109/5000000000000000000 : ℝ)=(25009639464501101379/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3673616563522917/12500000000000000000 : ℝ) ≤ ((8847711144182593243/8850000000000000000 : ℝ)+2*(14854178477/11062500000000 : ℝ)*(1847/12500 : ℝ))^(4355/1024 : ℝ) := by
    rw [show (8847711144182593243/8850000000000000000 : ℝ)+2*(14854178477/11062500000000 : ℝ)*(1847/12500 : ℝ)=(2000276363760771/2000000000000000 : ℝ) by norm_num, show 1+2*(3673616563522917/12500000000000000000 : ℝ)=(6253673616563522917/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8847711144182593243/8850000000000000000 : ℝ)*(X 1 0+X 2 0)+(14854178477/11062500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4355/1024 : ℝ)) (lo := (2809/25000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (8847711144182593243/8850000000000000000 : ℝ)) (alpha := (14854178477/11062500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8847711144182593243/8850000000000000000 : ℝ)*(X 0 1+X 2 1)+(14854178477/11062500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4355/1024 : ℝ)) (lo := (2809/25000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (8847711144182593243/8850000000000000000 : ℝ)) (alpha := (14854178477/11062500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8847711144182593243/8850000000000000000 : ℝ)*(X 0 2+X 1 2)+(14854178477/11062500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4355/1024 : ℝ)) (lo := (2809/25000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (8847711144182593243/8850000000000000000 : ℝ)) (alpha := (14854178477/11062500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1998194611/10000000000 : ℝ)*X 0 0+(2705081837/5000000000 : ℝ)*X 0 1+(5245896201/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213922501/400000000 : ℝ)*X 1 0+(-1040926803/5000000000 : ℝ)*X 1 1+(5245896069/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674031127/5000000000 : ℝ)*X 2 0+(262294811/500000000 : ℝ)*X 2 1+(-1040926883/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1078169513/2500000000 : ℝ)*X 0 0+(1035100317/2500000000 : ℝ)*X 0 1+(4491475077/10000000000 : ℝ)*X 0 2+(1078169513/2500000000 : ℝ)*X 1 0+(1035100317/2500000000 : ℝ)*X 1 1+(4491475077/10000000000 : ℝ)*X 1 2+(1078169513/2500000000 : ℝ)*X 2 0+(1035100317/2500000000 : ℝ)*X 2 1+(4491475077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1998206369/10000000000 : ℝ)*X 0 0+(5246488551/10000000000 : ℝ)*X 0 1+(5409568233/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265274969/500000000 : ℝ)*X 1 0+(-959090811/5000000000 : ℝ)*X 1 1+(5409568223/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652749693/5000000000 : ℝ)*X 2 0+(216382729/400000000 : ℝ)*X 2 1+(-1918181611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((862540663/2000000000 : ℝ)*X 0 0+(4490208787/10000000000 : ℝ)*X 0 1+(4141673933/10000000000 : ℝ)*X 0 2+(862540663/2000000000 : ℝ)*X 1 0+(4490208787/10000000000 : ℝ)*X 1 1+(4141673933/10000000000 : ℝ)*X 1 2+(862540663/2000000000 : ℝ)*X 2 0+(4490208787/10000000000 : ℝ)*X 2 1+(4141673933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1396_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (350258594319217720746451409/73750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (469337669/50000000000000 : ℝ)*(base19) + (598504543/100000000000000 : ℝ)*(base23) + (31476569/25000000000000 : ℝ)*(upper3) + (9469/20000000000000 : ℝ)*(lower4) + (2234023383100079/50000000000000 : ℝ)*(major0) + (2234023383100079/50000000000000 : ℝ)*(major1) + (2234023383100079/50000000000000 : ℝ)*(major2) + (1217530881403803/20000000000000 : ℝ)*(sp0) + (6087668131356029/100000000000000 : ℝ)*(sp1) + (6087664478140559/100000000000000 : ℝ)*(sp2) + (284841372595961/10000000000000 : ℝ)*(sp3) + (3579837/24414062500 : ℝ)*(sp4) + (798677253/20000000000000 : ℝ)*(sp6) + (2115620071/20000000000000 : ℝ)*(sp7) + (712106076014991/25000000000000 : ℝ)*(f.failure) + (6087669070031367/100000000000000 : ℝ)*(f.sum) + (447954241957/1106250000000000000000000000 : ℝ)*base65 + (2834310782867066197/442500000000000000000000000000000 : ℝ)*base67 + (5328057459984566197/442500000000000000000000000000000 : ℝ)*base69 + (7890969867339566197/442500000000000000000000000000000 : ℝ)*base71 + (14355254942747/4425000000000000000000000000 : ℝ)*base74 + (822755228259566197/442500000000000000000000000000000 : ℝ)*base75 + (6747116194772066197/442500000000000000000000000000000 : ℝ)*base77 + (4222710490089566197/442500000000000000000000000000000 : ℝ)*base79 + (7687031672843/1106250000000000000000000000 : ℝ)*base82 + (7463531/500000000000000000000 : ℝ)*base90 + (7463531/500000000000000000000 : ℝ)*base92 + (7463531/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3006785336172698603559/1475000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76900863/20000000000000 : ℝ)*(base19) + (439013823/100000000000000 : ℝ)*(base23) + (21355147/50000000000000 : ℝ)*(upper3) + (804903/4000000000000 : ℝ)*(lower4) + (44849759/100000000000000 : ℝ)*(upper5) + (2250281226553563/50000000000000 : ℝ)*(major0) + (2250281226553563/50000000000000 : ℝ)*(major1) + (2250281226553563/50000000000000 : ℝ)*(major2) + (243745297/3125000000000 : ℝ)*(sp1) + (9002417643/100000000000000 : ℝ)*(sp2) + (6131971460025957/100000000000000 : ℝ)*(sp4) + (3065981637836069/50000000000000 : ℝ)*(sp5) + (6131962018594491/100000000000000 : ℝ)*(sp6) + (143457668911917/5000000000000 : ℝ)*(sp7) + (143457668911917/5000000000000 : ℝ)*(f.failure) + (6131971460025957/100000000000000 : ℝ)*(f.sum) + (77631045947/1475000000000000000000000000 : ℝ)*base65 + (79393351874891603/147500000000000000000000000000000 : ℝ)*base67 + (504146636940108397/147500000000000000000000000000000 : ℝ)*base70 + (1258597257057391603/147500000000000000000000000000000 : ℝ)*base71 + (43425773049/11523437500000000000000000 : ℝ)*base73 + (824789005867608397/147500000000000000000000000000000 : ℝ)*base76 + (723036880377391603/147500000000000000000000000000000 : ℝ)*base77 + (567444243255108397/147500000000000000000000000000000 : ℝ)*base80 + (6939409632203/1475000000000000000000000000 : ℝ)*base82 + (72897/100000000000000000000 : ℝ)*base90 + (72897/100000000000000000000 : ℝ)*base92 + (72897/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1396_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31372059/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2809/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5633/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1843/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1396_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1396_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31372059/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7953/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1273/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5633/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1843/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1396_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1396_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1396_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4355/1024 : ℝ) ≤ p) (hpb : p ≤ (1089/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31372059/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7953/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1273/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5633/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1843/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1396_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

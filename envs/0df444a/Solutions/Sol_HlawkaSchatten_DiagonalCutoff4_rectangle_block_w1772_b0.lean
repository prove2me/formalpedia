-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1772_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:34:07.836987+00:00
-- url     : https://prove2.me/submissions/b79aa534-1749-46e2-a8bf-28152090d921

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
theorem support_rectangle_w1772_s0_0 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-107099327/1000000000 : ℝ)*x 0 + (2813801869/5000000000 : ℝ)*x 1 + (4948349831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107099327/1000000000 : ℝ)^6143 ≤ (6850246252493/100000000000000 : ℝ)^5119 := by
    have hnat : (107099327 : ℕ)^6143*100000000000000^5119 ≤ 6850246252493^5119*1000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107099327 1000000000 6850246252493 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2813801869/5000000000 : ℝ)^6143 ≤ (50162417263397/100000000000000 : ℝ)^5119 := by
    have hnat : (2813801869 : ℕ)^6143*100000000000000^5119 ≤ 50162417263397^5119*5000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2813801869 5000000000 50162417263397 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4948349831/10000000000 : ℝ)^6143 ≤ (21493668234123/50000000000000 : ℝ)^5119 := by
    have hnat : (4948349831 : ℕ)^6143*50000000000000^5119 ≤ 21493668234123^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4948349831 10000000000 21493668234123 50000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107099327/1000000000 : ℝ), (2813801869/5000000000 : ℝ), (4948349831/10000000000 : ℝ)] ![(6850246252493/100000000000000 : ℝ), (50162417263397/100000000000000 : ℝ), (21493668234123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107099327/1000000000 : ℝ)|^6143 ≤ (6850246252493/100000000000000 : ℝ)^5119
        have hw : |(-107099327/1000000000 : ℝ)|=(107099327/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2813801869/5000000000 : ℝ)|^6143 ≤ (50162417263397/100000000000000 : ℝ)^5119
        have hw : |(2813801869/5000000000 : ℝ)|=(2813801869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4948349831/10000000000 : ℝ)|^6143 ≤ (21493668234123/50000000000000 : ℝ)^5119
        have hw : |(4948349831/10000000000 : ℝ)|=(4948349831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1772_s0_1 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338978769/2500000000 : ℝ)*x 0 + (-718144307/5000000000 : ℝ)*x 1 + (2474175007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338978769/2500000000 : ℝ)^6143 ≤ (47270459516407/100000000000000 : ℝ)^5119 := by
    have hnat : (1338978769 : ℕ)^6143*100000000000000^5119 ≤ 47270459516407^5119*2500000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338978769 2500000000 47270459516407 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (718144307/5000000000 : ℝ)^6143 ≤ (974220209667/10000000000000 : ℝ)^5119 := by
    have hnat : (718144307 : ℕ)^6143*10000000000000^5119 ≤ 974220209667^5119*5000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      718144307 5000000000 974220209667 10000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2474175007/5000000000 : ℝ)^6143 ≤ (42987338376019/100000000000000 : ℝ)^5119 := by
    have hnat : (2474175007 : ℕ)^6143*100000000000000^5119 ≤ 42987338376019^5119*5000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2474175007 5000000000 42987338376019 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338978769/2500000000 : ℝ), (-718144307/5000000000 : ℝ), (2474175007/5000000000 : ℝ)] ![(47270459516407/100000000000000 : ℝ), (974220209667/10000000000000 : ℝ), (42987338376019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338978769/2500000000 : ℝ)|^6143 ≤ (47270459516407/100000000000000 : ℝ)^5119
        have hw : |(1338978769/2500000000 : ℝ)|=(1338978769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-718144307/5000000000 : ℝ)|^6143 ≤ (974220209667/10000000000000 : ℝ)^5119
        have hw : |(-718144307/5000000000 : ℝ)|=(718144307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2474175007/5000000000 : ℝ)|^6143 ≤ (42987338376019/100000000000000 : ℝ)^5119
        have hw : |(2474175007/5000000000 : ℝ)|=(2474175007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1772_s0_2 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071183109/2000000000 : ℝ)*x 0 + (197933993/400000000 : ℝ)*x 1 + (-718144123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071183109/2000000000 : ℝ)^6143 ≤ (47270464483753/100000000000000 : ℝ)^5119 := by
    have hnat : (1071183109 : ℕ)^6143*100000000000000^5119 ≤ 47270464483753^5119*2000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071183109 2000000000 47270464483753 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (197933993/400000000 : ℝ)^6143 ≤ (671677131339/1562500000000 : ℝ)^5119 := by
    have hnat : (197933993 : ℕ)^6143*1562500000000^5119 ≤ 671677131339^5119*400000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197933993 400000000 671677131339 1562500000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (718144123/5000000000 : ℝ)^6143 ≤ (2435549775311/25000000000000 : ℝ)^5119 := by
    have hnat : (718144123 : ℕ)^6143*25000000000000^5119 ≤ 2435549775311^5119*5000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      718144123 5000000000 2435549775311 25000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071183109/2000000000 : ℝ), (197933993/400000000 : ℝ), (-718144123/5000000000 : ℝ)] ![(47270464483753/100000000000000 : ℝ), (671677131339/1562500000000 : ℝ), (2435549775311/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071183109/2000000000 : ℝ)|^6143 ≤ (47270464483753/100000000000000 : ℝ)^5119
        have hw : |(1071183109/2000000000 : ℝ)|=(1071183109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(197933993/400000000 : ℝ)|^6143 ≤ (671677131339/1562500000000 : ℝ)^5119
        have hw : |(197933993/400000000 : ℝ)|=(197933993/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-718144123/5000000000 : ℝ)|^6143 ≤ (2435549775311/25000000000000 : ℝ)^5119
        have hw : |(-718144123/5000000000 : ℝ)|=(718144123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1772_s0_3 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (783396627/2000000000 : ℝ)*x 0 + (698107147/2500000000 : ℝ)*x 1 + (522541943/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (783396627/2000000000 : ℝ)^6143 ≤ (32473278602289/100000000000000 : ℝ)^5119 := by
    have hnat : (783396627 : ℕ)^6143*100000000000000^5119 ≤ 32473278602289^5119*2000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      783396627 2000000000 32473278602289 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (698107147/2500000000 : ℝ)^6143 ≤ (5408749321803/25000000000000 : ℝ)^5119 := by
    have hnat : (698107147 : ℕ)^6143*25000000000000^5119 ≤ 5408749321803^5119*2500000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698107147 2500000000 5408749321803 25000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522541943/1000000000 : ℝ)^6143 ≤ (11472931024129/25000000000000 : ℝ)^5119 := by
    have hnat : (522541943 : ℕ)^6143*25000000000000^5119 ≤ 11472931024129^5119*1000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522541943 1000000000 11472931024129 25000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(783396627/2000000000 : ℝ), (698107147/2500000000 : ℝ), (522541943/1000000000 : ℝ)] ![(32473278602289/100000000000000 : ℝ), (5408749321803/25000000000000 : ℝ), (11472931024129/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(783396627/2000000000 : ℝ)|^6143 ≤ (32473278602289/100000000000000 : ℝ)^5119
        have hw : |(783396627/2000000000 : ℝ)|=(783396627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(698107147/2500000000 : ℝ)|^6143 ≤ (5408749321803/25000000000000 : ℝ)^5119
        have hw : |(698107147/2500000000 : ℝ)|=(698107147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522541943/1000000000 : ℝ)|^6143 ≤ (11472931024129/25000000000000 : ℝ)^5119
        have hw : |(522541943/1000000000 : ℝ)|=(522541943/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1772_s0_4 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1072702379/10000000000 : ℝ)*x 0 + (621025799/1250000000 : ℝ)*x 1 + (2803504841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072702379/10000000000 : ℝ)^6143 ≤ (857920857231/12500000000000 : ℝ)^5119 := by
    have hnat : (1072702379 : ℕ)^6143*12500000000000^5119 ≤ 857920857231^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072702379 10000000000 857920857231 12500000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (621025799/1250000000 : ℝ)^6143 ≤ (8638884770901/20000000000000 : ℝ)^5119 := by
    have hnat : (621025799 : ℕ)^6143*20000000000000^5119 ≤ 8638884770901^5119*1250000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621025799 1250000000 8638884770901 20000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2803504841/5000000000 : ℝ)^6143 ≤ (49942209270911/100000000000000 : ℝ)^5119 := by
    have hnat : (2803504841 : ℕ)^6143*100000000000000^5119 ≤ 49942209270911^5119*5000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2803504841 5000000000 49942209270911 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1072702379/10000000000 : ℝ), (621025799/1250000000 : ℝ), (2803504841/5000000000 : ℝ)] ![(857920857231/12500000000000 : ℝ), (8638884770901/20000000000000 : ℝ), (49942209270911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1072702379/10000000000 : ℝ)|^6143 ≤ (857920857231/12500000000000 : ℝ)^5119
        have hw : |(-1072702379/10000000000 : ℝ)|=(1072702379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(621025799/1250000000 : ℝ)|^6143 ≤ (8638884770901/20000000000000 : ℝ)^5119
        have hw : |(621025799/1250000000 : ℝ)|=(621025799/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2803504841/5000000000 : ℝ)|^6143 ≤ (49942209270911/100000000000000 : ℝ)^5119
        have hw : |(2803504841/5000000000 : ℝ)|=(2803504841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1772_s0_5 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5178003269/10000000000 : ℝ)*x 0 + (-777628937/10000000000 : ℝ)*x 1 + (140175239/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5178003269/10000000000 : ℝ)^6143 ≤ (2837028077639/6250000000000 : ℝ)^5119 := by
    have hnat : (5178003269 : ℕ)^6143*6250000000000^5119 ≤ 2837028077639^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178003269 10000000000 2837028077639 6250000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (777628937/10000000000 : ℝ)^6143 ≤ (933068555123/20000000000000 : ℝ)^5119 := by
    have hnat : (777628937 : ℕ)^6143*20000000000000^5119 ≤ 933068555123^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777628937 10000000000 933068555123 20000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140175239/250000000 : ℝ)^6143 ≤ (49942207966869/100000000000000 : ℝ)^5119 := by
    have hnat : (140175239 : ℕ)^6143*100000000000000^5119 ≤ 49942207966869^5119*250000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140175239 250000000 49942207966869 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5178003269/10000000000 : ℝ), (-777628937/10000000000 : ℝ), (140175239/250000000 : ℝ)] ![(2837028077639/6250000000000 : ℝ), (933068555123/20000000000000 : ℝ), (49942207966869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5178003269/10000000000 : ℝ)|^6143 ≤ (2837028077639/6250000000000 : ℝ)^5119
        have hw : |(5178003269/10000000000 : ℝ)|=(5178003269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-777628937/10000000000 : ℝ)|^6143 ≤ (933068555123/20000000000000 : ℝ)^5119
        have hw : |(-777628937/10000000000 : ℝ)|=(777628937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140175239/250000000 : ℝ)|^6143 ≤ (49942207966869/100000000000000 : ℝ)^5119
        have hw : |(140175239/250000000 : ℝ)|=(140175239/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1772_s0_6 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2589001599/5000000000 : ℝ)*x 0 + (5607009631/10000000000 : ℝ)*x 1 + (-155525787/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2589001599/5000000000 : ℝ)^6143 ≤ (45392448495303/100000000000000 : ℝ)^5119 := by
    have hnat : (2589001599 : ℕ)^6143*100000000000000^5119 ≤ 45392448495303^5119*5000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589001599 5000000000 45392448495303 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5607009631/10000000000 : ℝ)^6143 ≤ (49942208725779/100000000000000 : ℝ)^5119 := by
    have hnat : (5607009631 : ℕ)^6143*100000000000000^5119 ≤ 49942208725779^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5607009631 10000000000 49942208725779 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (155525787/2000000000 : ℝ)^6143 ≤ (18223995161/390625000000 : ℝ)^5119 := by
    have hnat : (155525787 : ℕ)^6143*390625000000^5119 ≤ 18223995161^5119*2000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155525787 2000000000 18223995161 390625000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2589001599/5000000000 : ℝ), (5607009631/10000000000 : ℝ), (-155525787/2000000000 : ℝ)] ![(45392448495303/100000000000000 : ℝ), (49942208725779/100000000000000 : ℝ), (18223995161/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2589001599/5000000000 : ℝ)|^6143 ≤ (45392448495303/100000000000000 : ℝ)^5119
        have hw : |(2589001599/5000000000 : ℝ)|=(2589001599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5607009631/10000000000 : ℝ)|^6143 ≤ (49942208725779/100000000000000 : ℝ)^5119
        have hw : |(5607009631/10000000000 : ℝ)|=(5607009631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-155525787/2000000000 : ℝ)|^6143 ≤ (18223995161/390625000000 : ℝ)^5119
        have hw : |(-155525787/2000000000 : ℝ)|=(155525787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1772_s0_7 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (31384839/80000000 : ℝ)*x 0 + (2577148973/5000000000 : ℝ)*x 1 + (35827409/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31384839/80000000 : ℝ)^6143 ≤ (32534191962497/100000000000000 : ℝ)^5119 := by
    have hnat : (31384839 : ℕ)^6143*100000000000000^5119 ≤ 32534191962497^5119*80000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31384839 80000000 32534191962497 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2577148973/5000000000 : ℝ)^6143 ≤ (22571591516813/50000000000000 : ℝ)^5119 := by
    have hnat : (2577148973 : ℕ)^6143*50000000000000^5119 ≤ 22571591516813^5119*5000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2577148973 5000000000 22571591516813 50000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35827409/125000000 : ℝ)^6143 ≤ (22322624978633/100000000000000 : ℝ)^5119 := by
    have hnat : (35827409 : ℕ)^6143*100000000000000^5119 ≤ 22322624978633^5119*125000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35827409 125000000 22322624978633 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(31384839/80000000 : ℝ), (2577148973/5000000000 : ℝ), (35827409/125000000 : ℝ)] ![(32534191962497/100000000000000 : ℝ), (22571591516813/50000000000000 : ℝ), (22322624978633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(31384839/80000000 : ℝ)|^6143 ≤ (32534191962497/100000000000000 : ℝ)^5119
        have hw : |(31384839/80000000 : ℝ)|=(31384839/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2577148973/5000000000 : ℝ)|^6143 ≤ (22571591516813/50000000000000 : ℝ)^5119
        have hw : |(2577148973/5000000000 : ℝ)|=(2577148973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35827409/125000000 : ℝ)|^6143 ≤ (22322624978633/100000000000000 : ℝ)^5119
        have hw : |(35827409/125000000 : ℝ)|=(35827409/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1772_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (229093047/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3111/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20967/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (6111/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^6111 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^6111*1^1024 ≤ 0^1024*1^6111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 6111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 6111 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (6111/1024 : ℝ) ≤ (105468846254771493/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^6111 ≤ (105468846254771493/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^6111*25000000000000000000^1024 ≤ 105468846254771493^1024*5^6111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 105468846254771493 25000000000000000000 6111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (105468846254771493/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6111 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (6111/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^6111 := by
      have hnat : (1 : ℕ)^1024*1^6111 ≤ 1^6111*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 6111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 6111 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25105468846254771493/25000000000000000000 : ℝ) ≤ (5003528422409499/5000000000000000 : ℝ) ^ (6111/1024 : ℝ) := by
    have hpowers : (25105468846254771493/25000000000000000000 : ℝ)^1024 ≤ (5003528422409499/5000000000000000 : ℝ)^6111 := by
      have hnat : (25105468846254771493 : ℕ)^1024*5000000000000000^6111 ≤ 5003528422409499^6111*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25105468846254771493 25000000000000000000 5003528422409499 5000000000000000 1024 6111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003528422409499/5000000000000000 : ℝ)) (X := (25105468846254771493/25000000000000000000 : ℝ)) (by norm_num) 6111 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12605468846254771493/12500000000000000000 : ℝ) ≤ (2503528422409499/2500000000000000 : ℝ) ^ (6111/1024 : ℝ) := by
    have hpowers : (12605468846254771493/12500000000000000000 : ℝ)^1024 ≤ (2503528422409499/2500000000000000 : ℝ)^6111 := by
      have hnat : (12605468846254771493 : ℕ)^1024*2500000000000000^6111 ≤ 2503528422409499^6111*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12605468846254771493 12500000000000000000 2503528422409499 2500000000000000 1024 6111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503528422409499/2500000000000000 : ℝ)) (X := (12605468846254771493/12500000000000000000 : ℝ)) (by norm_num) 6111 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(3528422409499/2000000000000000 : ℝ)*(0 : ℝ))^(6111/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3528422409499/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(105468846254771493/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(3528422409499/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(6111/1024 : ℝ) := by
    rw [show (1 : ℝ)+(3528422409499/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5003528422409499/5000000000000000 : ℝ) by norm_num, show 1+(105468846254771493/25000000000000000000 : ℝ)+(0 : ℝ)=(25105468846254771493/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(105468846254771493/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(3528422409499/2000000000000000 : ℝ)*(2/5 : ℝ))^(6111/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3528422409499/2000000000000000 : ℝ)*(2/5 : ℝ)=(2503528422409499/2500000000000000 : ℝ) by norm_num, show 1+2*(105468846254771493/25000000000000000000 : ℝ)=(12605468846254771493/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(3528422409499/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6111/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3528422409499/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(3528422409499/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6111/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3528422409499/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(3528422409499/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6111/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3528422409499/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-107099327/1000000000 : ℝ)*X 0 0+(2813801869/5000000000 : ℝ)*X 0 1+(4948349831/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338978769/2500000000 : ℝ)*X 1 0+(-718144307/5000000000 : ℝ)*X 1 1+(2474175007/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071183109/2000000000 : ℝ)*X 2 0+(197933993/400000000 : ℝ)*X 2 1+(-718144123/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((783396627/2000000000 : ℝ)*X 0 0+(698107147/2500000000 : ℝ)*X 0 1+(522541943/1000000000 : ℝ)*X 0 2+(783396627/2000000000 : ℝ)*X 1 0+(698107147/2500000000 : ℝ)*X 1 1+(522541943/1000000000 : ℝ)*X 1 2+(783396627/2000000000 : ℝ)*X 2 0+(698107147/2500000000 : ℝ)*X 2 1+(522541943/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1072702379/10000000000 : ℝ)*X 0 0+(621025799/1250000000 : ℝ)*X 0 1+(2803504841/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5178003269/10000000000 : ℝ)*X 1 0+(-777628937/10000000000 : ℝ)*X 1 1+(140175239/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2589001599/5000000000 : ℝ)*X 2 0+(5607009631/10000000000 : ℝ)*X 2 1+(-155525787/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((31384839/80000000 : ℝ)*X 0 0+(2577148973/5000000000 : ℝ)*X 0 1+(35827409/125000000 : ℝ)*X 0 2+(31384839/80000000 : ℝ)*X 1 0+(2577148973/5000000000 : ℝ)*X 1 1+(35827409/125000000 : ℝ)*X 1 2+(31384839/80000000 : ℝ)*X 2 0+(2577148973/5000000000 : ℝ)*X 2 1+(35827409/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57214027404017290515249/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20664757/20000000000000 : ℝ)*(base1) + (62874317/4000000000000 : ℝ)*(base19) + (1700775213/100000000000000 : ℝ)*(base23) + (39657667/25000000000000 : ℝ)*(upper3) + (85488267/25000000000000 : ℝ)*(upper5) + (117702528560361/12500000000000 : ℝ)*(major0) + (117702528560361/12500000000000 : ℝ)*(major1) + (117702528560361/12500000000000 : ℝ)*(major2) + (1472210108035639/100000000000000 : ℝ)*(sp0) + (294443542552523/20000000000000 : ℝ)*(sp1) + (736108791922663/50000000000000 : ℝ)*(sp2) + (411018932079427/100000000000000 : ℝ)*(sp3) + (4639954343/50000000000000 : ℝ)*(sp4) + (915900267/50000000000000 : ℝ)*(sp7) + (411020867203747/100000000000000 : ℝ)*(f.failure) + (73610964231027/5000000000000 : ℝ)*(f.sum) + (19593864131639/12500000000000000000000000000 : ℝ)*base65 + (149960737919139/25000000000000000000000000000 : ℝ)*base67 + (382385682494139/25000000000000000000000000000 : ℝ)*base69 + (116569515394139/25000000000000000000000000000 : ℝ)*base71 + (2448323394139/12500000000000000000000000000 : ℝ)*base73 + (196175638769139/25000000000000000000000000000 : ℝ)*base75 + (238786792144139/25000000000000000000000000000 : ℝ)*base77 + (277360026519139/25000000000000000000000000000 : ℝ)*base79 + (49121520094139/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (29952891/10000000000000000000000 : ℝ)*base90 + (29952891/10000000000000000000000 : ℝ)*base92 + (29952891/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (212973552176143675628091/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (131614189/10000000000000 : ℝ)*(base19) + (1313313817/100000000000000 : ℝ)*(base23) + (124358827/100000000000000 : ℝ)*(base32) + (15399641/6250000000000 : ℝ)*(upper3) + (143918587/100000000000000 : ℝ)*(upper5) + (1001234461689197/100000000000000 : ℝ)*(major0) + (1001234461689197/100000000000000 : ℝ)*(major1) + (1001234461689197/100000000000000 : ℝ)*(major2) + (4747329993/100000000000000 : ℝ)*(sp1) + (5289725237/100000000000000 : ℝ)*(sp2) + (195678241140759/12500000000000 : ℝ)*(sp4) + (391354966413547/25000000000000 : ℝ)*(sp5) + (782709663043509/50000000000000 : ℝ)*(sp6) + (437042585928751/100000000000000 : ℝ)*(sp7) + (437042710287579/100000000000000 : ℝ)*(f.failure) + (195678241140759/12500000000000 : ℝ)*(f.sum) + (168140814782303/100000000000000000000000000000 : ℝ)*base65 + (1697504864482303/200000000000000000000000000000 : ℝ)*base67 + (19180033682303/200000000000000000000000000000 : ℝ)*base69 + (1631889165482303/200000000000000000000000000000 : ℝ)*base71 + (339583639682303/100000000000000000000000000000 : ℝ)*base73 + (1300864418082303/200000000000000000000000000000 : ℝ)*base75 + (1009053627682303/200000000000000000000000000000 : ℝ)*base77 + (1618934532682303/200000000000000000000000000000 : ℝ)*base79 + (425071860317697/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (19363213/10000000000000000000000 : ℝ)*base89 + (19363213/10000000000000000000000 : ℝ)*base91 + (19363213/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1772_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (229093047/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3111/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20967/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1772_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1772_s1_0 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1100948451/10000000000 : ℝ)*x 0 + (111003309/200000000 : ℝ)*x 1 + (5005514469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100948451/10000000000 : ℝ)^6143 ≤ (11329296061/160000000000 : ℝ)^5119 := by
    have hnat : (1100948451 : ℕ)^6143*160000000000^5119 ≤ 11329296061^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100948451 10000000000 11329296061 160000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111003309/200000000 : ℝ)^6143 ≤ (24667613199639/50000000000000 : ℝ)^5119 := by
    have hnat : (111003309 : ℕ)^6143*50000000000000^5119 ≤ 24667613199639^5119*200000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111003309 200000000 24667613199639 50000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5005514469/10000000000 : ℝ)^6143 ≤ (21791981777011/50000000000000 : ℝ)^5119 := by
    have hnat : (5005514469 : ℕ)^6143*50000000000000^5119 ≤ 21791981777011^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5005514469 10000000000 21791981777011 50000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1100948451/10000000000 : ℝ), (111003309/200000000 : ℝ), (5005514469/10000000000 : ℝ)] ![(11329296061/160000000000 : ℝ), (24667613199639/50000000000000 : ℝ), (21791981777011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1100948451/10000000000 : ℝ)|^6143 ≤ (11329296061/160000000000 : ℝ)^5119
        have hw : |(-1100948451/10000000000 : ℝ)|=(1100948451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(111003309/200000000 : ℝ)|^6143 ≤ (24667613199639/50000000000000 : ℝ)^5119
        have hw : |(111003309/200000000 : ℝ)|=(111003309/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5005514469/10000000000 : ℝ)|^6143 ≤ (21791981777011/50000000000000 : ℝ)^5119
        have hw : |(5005514469/10000000000 : ℝ)|=(5005514469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1772_s1_1 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2667639843/5000000000 : ℝ)*x 0 + (-1389678493/10000000000 : ℝ)*x 1 + (5005514421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2667639843/5000000000 : ℝ)^6143 ≤ (11762996770779/25000000000000 : ℝ)^5119 := by
    have hnat : (2667639843 : ℕ)^6143*25000000000000^5119 ≤ 11762996770779^5119*5000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2667639843 5000000000 11762996770779 25000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1389678493/10000000000 : ℝ)^6143 ≤ (234101246313/2500000000000 : ℝ)^5119 := by
    have hnat : (1389678493 : ℕ)^6143*2500000000000^5119 ≤ 234101246313^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389678493 10000000000 234101246313 2500000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5005514421/10000000000 : ℝ)^6143 ≤ (43583963052471/100000000000000 : ℝ)^5119 := by
    have hnat : (5005514421 : ℕ)^6143*100000000000000^5119 ≤ 43583963052471^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5005514421 10000000000 43583963052471 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2667639843/5000000000 : ℝ), (-1389678493/10000000000 : ℝ), (5005514421/10000000000 : ℝ)] ![(11762996770779/25000000000000 : ℝ), (234101246313/2500000000000 : ℝ), (43583963052471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2667639843/5000000000 : ℝ)|^6143 ≤ (11762996770779/25000000000000 : ℝ)^5119
        have hw : |(2667639843/5000000000 : ℝ)|=(2667639843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1389678493/10000000000 : ℝ)|^6143 ≤ (234101246313/2500000000000 : ℝ)^5119
        have hw : |(-1389678493/10000000000 : ℝ)|=(1389678493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5005514421/10000000000 : ℝ)|^6143 ≤ (43583963052471/100000000000000 : ℝ)^5119
        have hw : |(5005514421/10000000000 : ℝ)|=(5005514421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1772_s1_2 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1067055927/2000000000 : ℝ)*x 0 + (5005514439/10000000000 : ℝ)*x 1 + (-173709817/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067055927/2000000000 : ℝ)^6143 ≤ (23525993271687/50000000000000 : ℝ)^5119 := by
    have hnat : (1067055927 : ℕ)^6143*50000000000000^5119 ≤ 23525993271687^5119*2000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067055927 2000000000 23525993271687 50000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5005514439/10000000000 : ℝ)^6143 ≤ (43583963240553/100000000000000 : ℝ)^5119 := by
    have hnat : (5005514439 : ℕ)^6143*100000000000000^5119 ≤ 43583963240553^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5005514439 10000000000 43583963240553 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (173709817/1250000000 : ℝ)^6143 ≤ (4682025100113/50000000000000 : ℝ)^5119 := by
    have hnat : (173709817 : ℕ)^6143*50000000000000^5119 ≤ 4682025100113^5119*1250000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173709817 1250000000 4682025100113 50000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1067055927/2000000000 : ℝ), (5005514439/10000000000 : ℝ), (-173709817/1250000000 : ℝ)] ![(23525993271687/50000000000000 : ℝ), (43583963240553/100000000000000 : ℝ), (4682025100113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1067055927/2000000000 : ℝ)|^6143 ≤ (23525993271687/50000000000000 : ℝ)^5119
        have hw : |(1067055927/2000000000 : ℝ)|=(1067055927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5005514439/10000000000 : ℝ)|^6143 ≤ (43583963240553/100000000000000 : ℝ)^5119
        have hw : |(5005514439/10000000000 : ℝ)|=(5005514439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-173709817/1250000000 : ℝ)|^6143 ≤ (4682025100113/50000000000000 : ℝ)^5119
        have hw : |(-173709817/1250000000 : ℝ)|=(173709817/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1772_s1_3 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1974046491/5000000000 : ℝ)*x 0 + (3031419399/10000000000 : ℝ)*x 1 + (2491141591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1974046491/5000000000 : ℝ)^6143 ≤ (16391514484949/50000000000000 : ℝ)^5119 := by
    have hnat : (1974046491 : ℕ)^6143*50000000000000^5119 ≤ 16391514484949^5119*5000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1974046491 5000000000 16391514484949 50000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3031419399/10000000000 : ℝ)^6143 ≤ (1492227350489/6250000000000 : ℝ)^5119 := by
    have hnat : (3031419399 : ℕ)^6143*6250000000000^5119 ≤ 1492227350489^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3031419399 10000000000 1492227350489 6250000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2491141591/5000000000 : ℝ)^6143 ≤ (8668266681651/20000000000000 : ℝ)^5119 := by
    have hnat : (2491141591 : ℕ)^6143*20000000000000^5119 ≤ 8668266681651^5119*5000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2491141591 5000000000 8668266681651 20000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1974046491/5000000000 : ℝ), (3031419399/10000000000 : ℝ), (2491141591/5000000000 : ℝ)] ![(16391514484949/50000000000000 : ℝ), (1492227350489/6250000000000 : ℝ), (8668266681651/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1974046491/5000000000 : ℝ)|^6143 ≤ (16391514484949/50000000000000 : ℝ)^5119
        have hw : |(1974046491/5000000000 : ℝ)|=(1974046491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3031419399/10000000000 : ℝ)|^6143 ≤ (1492227350489/6250000000000 : ℝ)^5119
        have hw : |(3031419399/10000000000 : ℝ)|=(3031419399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2491141591/5000000000 : ℝ)|^6143 ≤ (8668266681651/20000000000000 : ℝ)^5119
        have hw : |(2491141591/5000000000 : ℝ)|=(2491141591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1772_s1_4 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1101822021/10000000000 : ℝ)*x 0 + (2509134091/5000000000 : ℝ)*x 1 + (5537034137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1101822021/10000000000 : ℝ)^6143 ≤ (7087552888359/100000000000000 : ℝ)^5119 := by
    have hnat : (1101822021 : ℕ)^6143*100000000000000^5119 ≤ 7087552888359^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101822021 10000000000 7087552888359 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2509134091/5000000000 : ℝ)^6143 ≤ (4371726062757/10000000000000 : ℝ)^5119 := by
    have hnat : (2509134091 : ℕ)^6143*10000000000000^5119 ≤ 4371726062757^5119*5000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2509134091 5000000000 4371726062757 10000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5537034137/10000000000 : ℝ)^6143 ≤ (1537349577147/3125000000000 : ℝ)^5119 := by
    have hnat : (5537034137 : ℕ)^6143*3125000000000^5119 ≤ 1537349577147^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5537034137 10000000000 1537349577147 3125000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1101822021/10000000000 : ℝ), (2509134091/5000000000 : ℝ), (5537034137/10000000000 : ℝ)] ![(7087552888359/100000000000000 : ℝ), (4371726062757/10000000000000 : ℝ), (1537349577147/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1101822021/10000000000 : ℝ)|^6143 ≤ (7087552888359/100000000000000 : ℝ)^5119
        have hw : |(-1101822021/10000000000 : ℝ)|=(1101822021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2509134091/5000000000 : ℝ)|^6143 ≤ (4371726062757/10000000000000 : ℝ)^5119
        have hw : |(2509134091/5000000000 : ℝ)|=(2509134091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5537034137/10000000000 : ℝ)|^6143 ≤ (1537349577147/3125000000000 : ℝ)^5119
        have hw : |(5537034137/10000000000 : ℝ)|=(5537034137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1772_s1_5 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596670457/5000000000 : ℝ)*x 0 + (-858158171/10000000000 : ℝ)*x 1 + (5537034031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596670457/5000000000 : ℝ)^6143 ≤ (45553849383159/100000000000000 : ℝ)^5119 := by
    have hnat : (2596670457 : ℕ)^6143*100000000000000^5119 ≤ 45553849383159^5119*5000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596670457 5000000000 45553849383159 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (858158171/10000000000 : ℝ)^6143 ≤ (1312741314093/25000000000000 : ℝ)^5119 := by
    have hnat : (858158171 : ℕ)^6143*25000000000000^5119 ≤ 1312741314093^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858158171 10000000000 1312741314093 25000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5537034031/10000000000 : ℝ)^6143 ≤ (49195185338527/100000000000000 : ℝ)^5119 := by
    have hnat : (5537034031 : ℕ)^6143*100000000000000^5119 ≤ 49195185338527^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5537034031 10000000000 49195185338527 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596670457/5000000000 : ℝ), (-858158171/10000000000 : ℝ), (5537034031/10000000000 : ℝ)] ![(45553849383159/100000000000000 : ℝ), (1312741314093/25000000000000 : ℝ), (49195185338527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596670457/5000000000 : ℝ)|^6143 ≤ (45553849383159/100000000000000 : ℝ)^5119
        have hw : |(2596670457/5000000000 : ℝ)|=(2596670457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-858158171/10000000000 : ℝ)|^6143 ≤ (1312741314093/25000000000000 : ℝ)^5119
        have hw : |(-858158171/10000000000 : ℝ)|=(858158171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5537034031/10000000000 : ℝ)|^6143 ≤ (49195185338527/100000000000000 : ℝ)^5119
        have hw : |(5537034031/10000000000 : ℝ)|=(5537034031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1772_s1_6 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (649167531/1250000000 : ℝ)*x 0 + (1384258613/2500000000 : ℝ)*x 1 + (-171631703/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649167531/1250000000 : ℝ)^6143 ≤ (45553842372677/100000000000000 : ℝ)^5119 := by
    have hnat : (649167531 : ℕ)^6143*100000000000000^5119 ≤ 45553842372677^5119*1250000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649167531 1250000000 45553842372677 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1384258613/2500000000 : ℝ)^6143 ≤ (49195189827251/100000000000000 : ℝ)^5119 := by
    have hnat : (1384258613 : ℕ)^6143*100000000000000^5119 ≤ 49195189827251^5119*2500000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1384258613 2500000000 49195189827251 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171631703/2000000000 : ℝ)^6143 ≤ (656370972791/12500000000000 : ℝ)^5119 := by
    have hnat : (171631703 : ℕ)^6143*12500000000000^5119 ≤ 656370972791^5119*2000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171631703 2000000000 656370972791 12500000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649167531/1250000000 : ℝ), (1384258613/2500000000 : ℝ), (-171631703/2000000000 : ℝ)] ![(45553842372677/100000000000000 : ℝ), (49195189827251/100000000000000 : ℝ), (656370972791/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649167531/1250000000 : ℝ)|^6143 ≤ (45553842372677/100000000000000 : ℝ)^5119
        have hw : |(649167531/1250000000 : ℝ)|=(649167531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1384258613/2500000000 : ℝ)|^6143 ≤ (49195189827251/100000000000000 : ℝ)^5119
        have hw : |(1384258613/2500000000 : ℝ)|=(1384258613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-171631703/2000000000 : ℝ)|^6143 ≤ (656370972791/12500000000000 : ℝ)^5119
        have hw : |(-171631703/2000000000 : ℝ)|=(171631703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1772_s1_7 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3951223299/10000000000 : ℝ)*x 0 + (197464289/400000000 : ℝ)*x 1 + (1539224441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3951223299/10000000000 : ℝ)^6143 ≤ (32814223600177/100000000000000 : ℝ)^5119 := by
    have hnat : (3951223299 : ℕ)^6143*100000000000000^5119 ≤ 32814223600177^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3951223299 10000000000 32814223600177 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (197464289/400000000 : ℝ)^6143 ≤ (5358118628227/12500000000000 : ℝ)^5119 := by
    have hnat : (197464289 : ℕ)^6143*12500000000000^5119 ≤ 5358118628227^5119*400000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197464289 400000000 5358118628227 12500000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1539224441/5000000000 : ℝ)^6143 ≤ (6080206838621/25000000000000 : ℝ)^5119 := by
    have hnat : (1539224441 : ℕ)^6143*25000000000000^5119 ≤ 6080206838621^5119*5000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1539224441 5000000000 6080206838621 25000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3951223299/10000000000 : ℝ), (197464289/400000000 : ℝ), (1539224441/5000000000 : ℝ)] ![(32814223600177/100000000000000 : ℝ), (5358118628227/12500000000000 : ℝ), (6080206838621/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3951223299/10000000000 : ℝ)|^6143 ≤ (32814223600177/100000000000000 : ℝ)^5119
        have hw : |(3951223299/10000000000 : ℝ)|=(3951223299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(197464289/400000000 : ℝ)|^6143 ≤ (5358118628227/12500000000000 : ℝ)^5119
        have hw : |(197464289/400000000 : ℝ)|=(197464289/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1539224441/5000000000 : ℝ)|^6143 ≤ (6080206838621/25000000000000 : ℝ)^5119
        have hw : |(1539224441/5000000000 : ℝ)|=(1539224441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1772_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (229093047/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20967/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3111/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (3767/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19283/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20967/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3111/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20967/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3111/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20967/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3111/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20967/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3111/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20967/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3111/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20967/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3111/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3111/50000 : ℝ) ^ (6111/1024 : ℝ) ≤ (6345232363379/100000000000000000000 : ℝ) := by
    have hpowers : (3111/50000 : ℝ)^6111 ≤ (6345232363379/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3111 : ℕ)^6111*100000000000000000000^1024 ≤ 6345232363379^1024*50000^6111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3111 50000 6345232363379 100000000000000000000 6111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3111/50000 : ℝ)) (X := (6345232363379/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6111 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20967/100000 : ℝ) ^ (6111/1024 : ℝ) ≤ (2233687083255439/25000000000000000000 : ℝ) := by
    have hpowers : (20967/100000 : ℝ)^6111 ≤ (2233687083255439/25000000000000000000 : ℝ)^1024 := by
      have hnat : (20967 : ℕ)^6111*25000000000000000000^1024 ≤ 2233687083255439^1024*100000^6111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20967 100000 2233687083255439 25000000000000000000 6111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20967/100000 : ℝ)) (X := (2233687083255439/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6111 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000006345232363379/50000000000000000000 : ℝ) ≤ (10000000212649897/10000000000000000 : ℝ) ^ (6111/1024 : ℝ) := by
    have hpowers : (50000006345232363379/50000000000000000000 : ℝ)^1024 ≤ (10000000212649897/10000000000000000 : ℝ)^6111 := by
      have hnat : (50000006345232363379 : ℕ)^1024*10000000000000000^6111 ≤ 10000000212649897^6111*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000006345232363379 50000000000000000000 10000000212649897 10000000000000000 1024 6111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000212649897/10000000000000000 : ℝ)) (X := (50000006345232363379/50000000000000000000 : ℝ)) (by norm_num) 6111 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20001788218713077027/20000000000000000000 : ℝ) ≤ (625009363585243/625000000000000 : ℝ) ^ (6111/1024 : ℝ) := by
    have hpowers : (20001788218713077027/20000000000000000000 : ℝ)^1024 ≤ (625009363585243/625000000000000 : ℝ)^6111 := by
      have hnat : (20001788218713077027 : ℕ)^1024*625000000000000^6111 ≤ 625009363585243^6111*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20001788218713077027 20000000000000000000 625009363585243 625000000000000 1024 6111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625009363585243/625000000000000 : ℝ)) (X := (20001788218713077027/20000000000000000000 : ℝ)) (by norm_num) 6111 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12502233687083255439/12500000000000000000 : ℝ) ≤ (10000299422077879/10000000000000000 : ℝ) ^ (6111/1024 : ℝ) := by
    have hpowers : (12502233687083255439/12500000000000000000 : ℝ)^1024 ≤ (10000299422077879/10000000000000000 : ℝ)^6111 := by
      have hnat : (12502233687083255439 : ℕ)^1024*10000000000000000^6111 ≤ 10000299422077879^6111*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502233687083255439 12500000000000000000 10000299422077879 10000000000000000 1024 6111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000299422077879/10000000000000000 : ℝ)) (X := (12502233687083255439/12500000000000000000 : ℝ)) (by norm_num) 6111 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6345232363379/100000000000000000000 : ℝ) ≤ ((49149380484820609087/49150000000000000000 : ℝ)+2*(49868237997/491500000000000 : ℝ)*(3111/50000 : ℝ))^(6111/1024 : ℝ) := by
    rw [show (49149380484820609087/49150000000000000000 : ℝ)+2*(49868237997/491500000000000 : ℝ)*(3111/50000 : ℝ)=(10000000212649897/10000000000000000 : ℝ) by norm_num, show 1+2*(6345232363379/100000000000000000000 : ℝ)=(50000006345232363379/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2233687083255439/25000000000000000000 : ℝ)+(6345232363379/100000000000000000000 : ℝ) ≤ ((49149380484820609087/49150000000000000000 : ℝ)+(49868237997/491500000000000 : ℝ)*((20967/100000 : ℝ)+(3111/50000 : ℝ)))^(6111/1024 : ℝ) := by
    rw [show (49149380484820609087/49150000000000000000 : ℝ)+(49868237997/491500000000000 : ℝ)*((20967/100000 : ℝ)+(3111/50000 : ℝ))=(625009363585243/625000000000000 : ℝ) by norm_num, show 1+(2233687083255439/25000000000000000000 : ℝ)+(6345232363379/100000000000000000000 : ℝ)=(20001788218713077027/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2233687083255439/25000000000000000000 : ℝ) ≤ ((49149380484820609087/49150000000000000000 : ℝ)+2*(49868237997/491500000000000 : ℝ)*(20967/100000 : ℝ))^(6111/1024 : ℝ) := by
    rw [show (49149380484820609087/49150000000000000000 : ℝ)+2*(49868237997/491500000000000 : ℝ)*(20967/100000 : ℝ)=(10000299422077879/10000000000000000 : ℝ) by norm_num, show 1+2*(2233687083255439/25000000000000000000 : ℝ)=(12502233687083255439/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (49149380484820609087/49150000000000000000 : ℝ)*(X 1 0+X 2 0)+(49868237997/491500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6111/1024 : ℝ)) (lo := (3111/50000 : ℝ)) (hi := (20967/100000 : ℝ)) (c := (49149380484820609087/49150000000000000000 : ℝ)) (alpha := (49868237997/491500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (49149380484820609087/49150000000000000000 : ℝ)*(X 0 1+X 2 1)+(49868237997/491500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6111/1024 : ℝ)) (lo := (3111/50000 : ℝ)) (hi := (20967/100000 : ℝ)) (c := (49149380484820609087/49150000000000000000 : ℝ)) (alpha := (49868237997/491500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (49149380484820609087/49150000000000000000 : ℝ)*(X 0 2+X 1 2)+(49868237997/491500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6111/1024 : ℝ)) (lo := (3111/50000 : ℝ)) (hi := (20967/100000 : ℝ)) (c := (49149380484820609087/49150000000000000000 : ℝ)) (alpha := (49868237997/491500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1100948451/10000000000 : ℝ)*X 0 0+(111003309/200000000 : ℝ)*X 0 1+(5005514469/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2667639843/5000000000 : ℝ)*X 1 0+(-1389678493/10000000000 : ℝ)*X 1 1+(5005514421/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1067055927/2000000000 : ℝ)*X 2 0+(5005514439/10000000000 : ℝ)*X 2 1+(-173709817/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1974046491/5000000000 : ℝ)*X 0 0+(3031419399/10000000000 : ℝ)*X 0 1+(2491141591/5000000000 : ℝ)*X 0 2+(1974046491/5000000000 : ℝ)*X 1 0+(3031419399/10000000000 : ℝ)*X 1 1+(2491141591/5000000000 : ℝ)*X 1 2+(1974046491/5000000000 : ℝ)*X 2 0+(3031419399/10000000000 : ℝ)*X 2 1+(2491141591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1101822021/10000000000 : ℝ)*X 0 0+(2509134091/5000000000 : ℝ)*X 0 1+(5537034137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2596670457/5000000000 : ℝ)*X 1 0+(-858158171/10000000000 : ℝ)*X 1 1+(5537034031/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((649167531/1250000000 : ℝ)*X 2 0+(1384258613/2500000000 : ℝ)*X 2 1+(-171631703/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3951223299/10000000000 : ℝ)*X 0 0+(197464289/400000000 : ℝ)*X 0 1+(1539224441/5000000000 : ℝ)*X 0 2+(3951223299/10000000000 : ℝ)*X 1 0+(197464289/400000000 : ℝ)*X 1 1+(1539224441/5000000000 : ℝ)*X 1 2+(3951223299/10000000000 : ℝ)*X 2 0+(197464289/400000000 : ℝ)*X 2 1+(1539224441/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3144698945338639013408767251/1228750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (370623593/100000000000000 : ℝ)*(base19) + (85975031/25000000000000 : ℝ)*(base23) + (4893907/100000000000000 : ℝ)*(lower2) + (86948767/100000000000000 : ℝ)*(upper3) + (59939409/100000000000000 : ℝ)*(upper5) + (587159067082197/50000000000000 : ℝ)*(major0) + (587159067082197/50000000000000 : ℝ)*(major1) + (587159067082197/50000000000000 : ℝ)*(major2) + (918020050064449/50000000000000 : ℝ)*(sp0) + (1836041410452539/100000000000000 : ℝ)*(sp1) + (229505179647001/12500000000000 : ℝ)*(sp2) + (512593874740893/100000000000000 : ℝ)*(sp3) + (840473617/50000000000000 : ℝ)*(sp4) + (52720287/10000000000000 : ℝ)*(sp7) + (512594401943763/100000000000000 : ℝ)*(f.failure) + (459010445269033/25000000000000 : ℝ)*(f.sum) + (38920542970009/12287500000000000000000000000 : ℝ)*base65 + (5384077832962475861/2457500000000000000000000000000000 : ℝ)*base68 + (10128044043469975861/2457500000000000000000000000000000 : ℝ)*base70 + (14579802157699975861/2457500000000000000000000000000000 : ℝ)*base72 + (12553030386017/6143750000000000000000000000 : ℝ)*base73 + (8267256251262475861/2457500000000000000000000000000000 : ℝ)*base76 + (9662773063844975861/2457500000000000000000000000000000 : ℝ)*base78 + (3415858277942475861/2457500000000000000000000000000000 : ℝ)*base80 + (8289722881383/6143750000000000000000000000 : ℝ)*base82 + (11684139/10000000000000000000000 : ℝ)*base90 + (11684139/10000000000000000000000 : ℝ)*base92 + (11684139/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2655112562799450939141581649/307187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (977283/80000000000 : ℝ)*(base19) + (617931539/50000000000000 : ℝ)*(base23) + (1715351/500000000000 : ℝ)*(upper3) + (9739747/10000000000000 : ℝ)*(lower4) + (154113453548897/12500000000000 : ℝ)*(major0) + (154113453548897/12500000000000 : ℝ)*(major1) + (154113453548897/12500000000000 : ℝ)*(major2) + (3418394079/100000000000000 : ℝ)*(sp1) + (3061493221/50000000000000 : ℝ)*(sp2) + (232103297/50000000000000 : ℝ)*(sp3) + (963823013083999/50000000000000 : ℝ)*(sp4) + (1927641386170169/100000000000000 : ℝ)*(sp5) + (963819333659239/50000000000000 : ℝ)*(sp6) + (538168478297879/100000000000000 : ℝ)*(sp7) + (538168942504473/100000000000000 : ℝ)*(f.failure) + (963823013083999/50000000000000 : ℝ)*(f.sum) + (34411185362147/24575000000000000000000000000 : ℝ)*base65 + (2909618005513552039/614375000000000000000000000000000 : ℝ)*base67 + (201306357272927039/614375000000000000000000000000000 : ℝ)*base69 + (4492833276341052039/614375000000000000000000000000000 : ℝ)*base71 + (853365136847/24575000000000000000000000000 : ℝ)*base73 + (1809379609225427039/614375000000000000000000000000000 : ℝ)*base75 + (2926276829102302039/614375000000000000000000000000000 : ℝ)*base77 + (2526001974129802039/614375000000000000000000000000000 : ℝ)*base79 + (12460447913291/3071875000000000000000000000 : ℝ)*base82 + (69300769/10000000000000000000000 : ℝ)*base90 + (69300769/10000000000000000000000 : ℝ)*base92 + (69300769/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1772_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (229093047/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20967/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3111/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3767/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19283/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1772_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1772_s2_0 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-137670501/1250000000 : ℝ)*x 0 + (5549118487/10000000000 : ℝ)*x 1 + (2503138147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (137670501/1250000000 : ℝ)^6143 ≤ (1416803495329/20000000000000 : ℝ)^5119 := by
    have hnat : (137670501 : ℕ)^6143*20000000000000^5119 ≤ 1416803495329^5119*1250000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137670501 1250000000 1416803495329 20000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5549118487/10000000000 : ℝ)^6143 ≤ (6165507318181/12500000000000 : ℝ)^5119 := by
    have hnat : (5549118487 : ℕ)^6143*12500000000000^5119 ≤ 6165507318181^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5549118487 10000000000 6165507318181 12500000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2503138147/5000000000 : ℝ)^6143 ≤ (1743676958401/4000000000000 : ℝ)^5119 := by
    have hnat : (2503138147 : ℕ)^6143*4000000000000^5119 ≤ 1743676958401^5119*5000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2503138147 5000000000 1743676958401 4000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-137670501/1250000000 : ℝ), (5549118487/10000000000 : ℝ), (2503138147/5000000000 : ℝ)] ![(1416803495329/20000000000000 : ℝ), (6165507318181/12500000000000 : ℝ), (1743676958401/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-137670501/1250000000 : ℝ)|^6143 ≤ (1416803495329/20000000000000 : ℝ)^5119
        have hw : |(-137670501/1250000000 : ℝ)|=(137670501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5549118487/10000000000 : ℝ)|^6143 ≤ (6165507318181/12500000000000 : ℝ)^5119
        have hw : |(5549118487/10000000000 : ℝ)|=(5549118487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2503138147/5000000000 : ℝ)|^6143 ≤ (1743676958401/4000000000000 : ℝ)^5119
        have hw : |(2503138147/5000000000 : ℝ)|=(2503138147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1772_s2_1 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5334985009/10000000000 : ℝ)*x 0 + (-1389079631/10000000000 : ℝ)*x 1 + (2503138147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5334985009/10000000000 : ℝ)^6143 ≤ (23524434240373/50000000000000 : ℝ)^5119 := by
    have hnat : (5334985009 : ℕ)^6143*50000000000000^5119 ≤ 23524434240373^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5334985009 10000000000 23524434240373 50000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1389079631/10000000000 : ℝ)^6143 ≤ (1169900942519/12500000000000 : ℝ)^5119 := by
    have hnat : (1389079631 : ℕ)^6143*12500000000000^5119 ≤ 1169900942519^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389079631 10000000000 1169900942519 12500000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2503138147/5000000000 : ℝ)^6143 ≤ (1743676958401/4000000000000 : ℝ)^5119 := by
    have hnat : (2503138147 : ℕ)^6143*4000000000000^5119 ≤ 1743676958401^5119*5000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2503138147 5000000000 1743676958401 4000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5334985009/10000000000 : ℝ), (-1389079631/10000000000 : ℝ), (2503138147/5000000000 : ℝ)] ![(23524434240373/50000000000000 : ℝ), (1169900942519/12500000000000 : ℝ), (1743676958401/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5334985009/10000000000 : ℝ)|^6143 ≤ (23524434240373/50000000000000 : ℝ)^5119
        have hw : |(5334985009/10000000000 : ℝ)|=(5334985009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1389079631/10000000000 : ℝ)|^6143 ≤ (1169900942519/12500000000000 : ℝ)^5119
        have hw : |(-1389079631/10000000000 : ℝ)|=(1389079631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2503138147/5000000000 : ℝ)|^6143 ≤ (1743676958401/4000000000000 : ℝ)^5119
        have hw : |(2503138147/5000000000 : ℝ)|=(2503138147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1772_s2_2 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5334985009/10000000000 : ℝ)*x 0 + (1001255259/2000000000 : ℝ)*x 1 + (-1389079631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5334985009/10000000000 : ℝ)^6143 ≤ (23524434240373/50000000000000 : ℝ)^5119 := by
    have hnat : (5334985009 : ℕ)^6143*50000000000000^5119 ≤ 23524434240373^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5334985009 10000000000 23524434240373 50000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1001255259/2000000000 : ℝ)^6143 ≤ (21795961985237/50000000000000 : ℝ)^5119 := by
    have hnat : (1001255259 : ℕ)^6143*50000000000000^5119 ≤ 21795961985237^5119*2000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001255259 2000000000 21795961985237 50000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1389079631/10000000000 : ℝ)^6143 ≤ (1169900942519/12500000000000 : ℝ)^5119 := by
    have hnat : (1389079631 : ℕ)^6143*12500000000000^5119 ≤ 1169900942519^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389079631 10000000000 1169900942519 12500000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5334985009/10000000000 : ℝ), (1001255259/2000000000 : ℝ), (-1389079631/10000000000 : ℝ)] ![(23524434240373/50000000000000 : ℝ), (21795961985237/50000000000000 : ℝ), (1169900942519/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5334985009/10000000000 : ℝ)|^6143 ≤ (23524434240373/50000000000000 : ℝ)^5119
        have hw : |(5334985009/10000000000 : ℝ)|=(5334985009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1001255259/2000000000 : ℝ)|^6143 ≤ (21795961985237/50000000000000 : ℝ)^5119
        have hw : |(1001255259/2000000000 : ℝ)|=(1001255259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1389079631/10000000000 : ℝ)|^6143 ≤ (1169900942519/12500000000000 : ℝ)^5119
        have hw : |(-1389079631/10000000000 : ℝ)|=(1389079631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1772_s2_3 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1974231089/5000000000 : ℝ)*x 0 + (3034634283/10000000000 : ℝ)*x 1 + (4979019529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1974231089/5000000000 : ℝ)^6143 ≤ (8196676967807/25000000000000 : ℝ)^5119 := by
    have hnat : (1974231089 : ℕ)^6143*25000000000000^5119 ≤ 8196676967807^5119*5000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1974231089 5000000000 8196676967807 25000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3034634283/10000000000 : ℝ)^6143 ≤ (23906026558017/100000000000000 : ℝ)^5119 := by
    have hnat : (3034634283 : ℕ)^6143*100000000000000^5119 ≤ 23906026558017^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3034634283 10000000000 23906026558017 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4979019529/10000000000 : ℝ)^6143 ≤ (10826816388843/25000000000000 : ℝ)^5119 := by
    have hnat : (4979019529 : ℕ)^6143*25000000000000^5119 ≤ 10826816388843^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4979019529 10000000000 10826816388843 25000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1974231089/5000000000 : ℝ), (3034634283/10000000000 : ℝ), (4979019529/10000000000 : ℝ)] ![(8196676967807/25000000000000 : ℝ), (23906026558017/100000000000000 : ℝ), (10826816388843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1974231089/5000000000 : ℝ)|^6143 ≤ (8196676967807/25000000000000 : ℝ)^5119
        have hw : |(1974231089/5000000000 : ℝ)|=(1974231089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3034634283/10000000000 : ℝ)|^6143 ≤ (23906026558017/100000000000000 : ℝ)^5119
        have hw : |(3034634283/10000000000 : ℝ)|=(3034634283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4979019529/10000000000 : ℝ)|^6143 ≤ (10826816388843/25000000000000 : ℝ)^5119
        have hw : |(4979019529/10000000000 : ℝ)|=(4979019529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1772_s2_4 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1102229183/10000000000 : ℝ)*x 0 + (200757749/400000000 : ℝ)*x 1 + (692009617/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102229183/10000000000 : ℝ)^6143 ≤ (1772674006753/25000000000000 : ℝ)^5119 := by
    have hnat : (1102229183 : ℕ)^6143*25000000000000^5119 ≤ 1772674006753^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102229183 10000000000 1772674006753 25000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200757749/400000000 : ℝ)^6143 ≤ (2732770190233/6250000000000 : ℝ)^5119 := by
    have hnat : (200757749 : ℕ)^6143*6250000000000^5119 ≤ 2732770190233^5119*400000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200757749 400000000 2732770190233 6250000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (692009617/1250000000 : ℝ)^6143 ≤ (49184980918351/100000000000000 : ℝ)^5119 := by
    have hnat : (692009617 : ℕ)^6143*100000000000000^5119 ≤ 49184980918351^5119*1250000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692009617 1250000000 49184980918351 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1102229183/10000000000 : ℝ), (200757749/400000000 : ℝ), (692009617/1250000000 : ℝ)] ![(1772674006753/25000000000000 : ℝ), (2732770190233/6250000000000 : ℝ), (49184980918351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1102229183/10000000000 : ℝ)|^6143 ≤ (1772674006753/25000000000000 : ℝ)^5119
        have hw : |(-1102229183/10000000000 : ℝ)|=(1102229183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(200757749/400000000 : ℝ)|^6143 ≤ (2732770190233/6250000000000 : ℝ)^5119
        have hw : |(200757749/400000000 : ℝ)|=(200757749/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(692009617/1250000000 : ℝ)|^6143 ≤ (49184980918351/100000000000000 : ℝ)^5119
        have hw : |(692009617/1250000000 : ℝ)|=(692009617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1772_s2_5 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596764189/5000000000 : ℝ)*x 0 + (-85927899/1000000000 : ℝ)*x 1 + (692009617/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596764189/5000000000 : ℝ)^6143 ≤ (22777911341503/50000000000000 : ℝ)^5119 := by
    have hnat : (2596764189 : ℕ)^6143*50000000000000^5119 ≤ 22777911341503^5119*5000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596764189 5000000000 22777911341503 50000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85927899/1000000000 : ℝ)^6143 ≤ (5259196384891/100000000000000 : ℝ)^5119 := by
    have hnat : (85927899 : ℕ)^6143*100000000000000^5119 ≤ 5259196384891^5119*1000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85927899 1000000000 5259196384891 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (692009617/1250000000 : ℝ)^6143 ≤ (49184980918351/100000000000000 : ℝ)^5119 := by
    have hnat : (692009617 : ℕ)^6143*100000000000000^5119 ≤ 49184980918351^5119*1250000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692009617 1250000000 49184980918351 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596764189/5000000000 : ℝ), (-85927899/1000000000 : ℝ), (692009617/1250000000 : ℝ)] ![(22777911341503/50000000000000 : ℝ), (5259196384891/100000000000000 : ℝ), (49184980918351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596764189/5000000000 : ℝ)|^6143 ≤ (22777911341503/50000000000000 : ℝ)^5119
        have hw : |(2596764189/5000000000 : ℝ)|=(2596764189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-85927899/1000000000 : ℝ)|^6143 ≤ (5259196384891/100000000000000 : ℝ)^5119
        have hw : |(-85927899/1000000000 : ℝ)|=(85927899/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(692009617/1250000000 : ℝ)|^6143 ≤ (49184980918351/100000000000000 : ℝ)^5119
        have hw : |(692009617/1250000000 : ℝ)|=(692009617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1772_s2_6 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596764189/5000000000 : ℝ)*x 0 + (692009617/1250000000 : ℝ)*x 1 + (-859278989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596764189/5000000000 : ℝ)^6143 ≤ (22777911341503/50000000000000 : ℝ)^5119 := by
    have hnat : (2596764189 : ℕ)^6143*50000000000000^5119 ≤ 22777911341503^5119*5000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596764189 5000000000 22777911341503 50000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (692009617/1250000000 : ℝ)^6143 ≤ (49184980918351/100000000000000 : ℝ)^5119 := by
    have hnat : (692009617 : ℕ)^6143*100000000000000^5119 ≤ 49184980918351^5119*1250000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692009617 1250000000 49184980918351 100000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (859278989/10000000000 : ℝ)^6143 ≤ (2629598188773/50000000000000 : ℝ)^5119 := by
    have hnat : (859278989 : ℕ)^6143*50000000000000^5119 ≤ 2629598188773^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859278989 10000000000 2629598188773 50000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596764189/5000000000 : ℝ), (692009617/1250000000 : ℝ), (-859278989/10000000000 : ℝ)] ![(22777911341503/50000000000000 : ℝ), (49184980918351/100000000000000 : ℝ), (2629598188773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596764189/5000000000 : ℝ)|^6143 ≤ (22777911341503/50000000000000 : ℝ)^5119
        have hw : |(2596764189/5000000000 : ℝ)|=(2596764189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(692009617/1250000000 : ℝ)|^6143 ≤ (49184980918351/100000000000000 : ℝ)^5119
        have hw : |(692009617/1250000000 : ℝ)|=(692009617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-859278989/10000000000 : ℝ)|^6143 ≤ (2629598188773/50000000000000 : ℝ)^5119
        have hw : |(-859278989/10000000000 : ℝ)|=(859278989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1772_s2_7 (p : ℝ) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (493945139/1250000000 : ℝ)*x 0 + (4933646553/10000000000 : ℝ)*x 1 + (385168413/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (493945139/1250000000 : ℝ)^6143 ≤ (6563518062513/20000000000000 : ℝ)^5119 := by
    have hnat : (493945139 : ℕ)^6143*20000000000000^5119 ≤ 6563518062513^5119*1250000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493945139 1250000000 6563518062513 20000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4933646553/10000000000 : ℝ)^6143 ≤ (10708525143679/25000000000000 : ℝ)^5119 := by
    have hnat : (4933646553 : ℕ)^6143*25000000000000^5119 ≤ 10708525143679^5119*10000000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4933646553 10000000000 10708525143679 25000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (385168413/1250000000 : ℝ)^6143 ≤ (12174154549159/50000000000000 : ℝ)^5119 := by
    have hnat : (385168413 : ℕ)^6143*50000000000000^5119 ≤ 12174154549159^5119*1250000000^6143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385168413 1250000000 12174154549159 50000000000000 6143 5119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6143/1024 : ℝ)) 6143 5119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(493945139/1250000000 : ℝ), (4933646553/10000000000 : ℝ), (385168413/1250000000 : ℝ)] ![(6563518062513/20000000000000 : ℝ), (10708525143679/25000000000000 : ℝ), (12174154549159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(493945139/1250000000 : ℝ)|^6143 ≤ (6563518062513/20000000000000 : ℝ)^5119
        have hw : |(493945139/1250000000 : ℝ)|=(493945139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4933646553/10000000000 : ℝ)|^6143 ≤ (10708525143679/25000000000000 : ℝ)^5119
        have hw : |(4933646553/10000000000 : ℝ)|=(4933646553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(385168413/1250000000 : ℝ)|^6143 ≤ (12174154549159/50000000000000 : ℝ)^5119
        have hw : |(385168413/1250000000 : ℝ)|=(385168413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1772_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (229093047/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19283/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3767/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (7551/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (963/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19283/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3767/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19283/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3767/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19283/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3767/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19283/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3767/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19283/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3767/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19283/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3767/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3767/50000 : ℝ) ^ (6111/1024 : ℝ) ≤ (1242290936539/6250000000000000000 : ℝ) := by
    have hpowers : (3767/50000 : ℝ)^6111 ≤ (1242290936539/6250000000000000000 : ℝ)^1024 := by
      have hnat : (3767 : ℕ)^6111*6250000000000000000^1024 ≤ 1242290936539^1024*50000^6111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3767 50000 1242290936539 6250000000000000000 6111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3767/50000 : ℝ)) (X := (1242290936539/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 6111 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19283/100000 : ℝ) ^ (6111/1024 : ℝ) ≤ (1084211397962367/20000000000000000000 : ℝ) := by
    have hpowers : (19283/100000 : ℝ)^6111 ≤ (1084211397962367/20000000000000000000 : ℝ)^1024 := by
      have hnat : (19283 : ℕ)^6111*20000000000000000000^1024 ≤ 1084211397962367^1024*100000^6111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19283 100000 1084211397962367 20000000000000000000 6111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19283/100000 : ℝ)) (X := (1084211397962367/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6111 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125001242290936539/3125000000000000000 : ℝ) ≤ (10000000666132919/10000000000000000 : ℝ) ^ (6111/1024 : ℝ) := by
    have hpowers : (3125001242290936539/3125000000000000000 : ℝ)^1024 ≤ (10000000666132919/10000000000000000 : ℝ)^6111 := by
      have hnat : (3125001242290936539 : ℕ)^1024*10000000000000000^6111 ≤ 10000000666132919^6111*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125001242290936539 3125000000000000000 10000000666132919 10000000000000000 1024 6111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000666132919/10000000000000000 : ℝ)) (X := (3125001242290936539/3125000000000000000 : ℝ)) (by norm_num) 6111 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100005440933644796459/100000000000000000000 : ℝ) ≤ (625005698115983/625000000000000 : ℝ) ^ (6111/1024 : ℝ) := by
    have hpowers : (100005440933644796459/100000000000000000000 : ℝ)^1024 ≤ (625005698115983/625000000000000 : ℝ)^6111 := by
      have hnat : (100005440933644796459 : ℕ)^1024*625000000000000^6111 ≤ 625005698115983^6111*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100005440933644796459 100000000000000000000 625005698115983 625000000000000 1024 6111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625005698115983/625000000000000 : ℝ)) (X := (100005440933644796459/100000000000000000000 : ℝ)) (by norm_num) 6111 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10001084211397962367/10000000000000000000 : ℝ) ≤ (10000181673578537/10000000000000000 : ℝ) ^ (6111/1024 : ℝ) := by
    have hpowers : (10001084211397962367/10000000000000000000 : ℝ)^1024 ≤ (10000181673578537/10000000000000000 : ℝ)^6111 := by
      have hnat : (10001084211397962367 : ℕ)^1024*10000000000000000^6111 ≤ 10000181673578537^6111*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001084211397962367 10000000000000000000 10000181673578537 10000000000000000 1024 6111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000181673578537/10000000000000000 : ℝ)) (X := (10001084211397962367/10000000000000000000 : ℝ)) (by norm_num) 6111 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1242290936539/6250000000000000000 : ℝ) ≤ ((117488644116300379319/117490000000000000000 : ℝ)+2*(90503722809/1174900000000000 : ℝ)*(3767/50000 : ℝ))^(6111/1024 : ℝ) := by
    rw [show (117488644116300379319/117490000000000000000 : ℝ)+2*(90503722809/1174900000000000 : ℝ)*(3767/50000 : ℝ)=(10000000666132919/10000000000000000 : ℝ) by norm_num, show 1+2*(1242290936539/6250000000000000000 : ℝ)=(3125001242290936539/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1084211397962367/20000000000000000000 : ℝ)+(1242290936539/6250000000000000000 : ℝ) ≤ ((117488644116300379319/117490000000000000000 : ℝ)+(90503722809/1174900000000000 : ℝ)*((19283/100000 : ℝ)+(3767/50000 : ℝ)))^(6111/1024 : ℝ) := by
    rw [show (117488644116300379319/117490000000000000000 : ℝ)+(90503722809/1174900000000000 : ℝ)*((19283/100000 : ℝ)+(3767/50000 : ℝ))=(625005698115983/625000000000000 : ℝ) by norm_num, show 1+(1084211397962367/20000000000000000000 : ℝ)+(1242290936539/6250000000000000000 : ℝ)=(100005440933644796459/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1084211397962367/20000000000000000000 : ℝ) ≤ ((117488644116300379319/117490000000000000000 : ℝ)+2*(90503722809/1174900000000000 : ℝ)*(19283/100000 : ℝ))^(6111/1024 : ℝ) := by
    rw [show (117488644116300379319/117490000000000000000 : ℝ)+2*(90503722809/1174900000000000 : ℝ)*(19283/100000 : ℝ)=(10000181673578537/10000000000000000 : ℝ) by norm_num, show 1+2*(1084211397962367/20000000000000000000 : ℝ)=(10001084211397962367/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (117488644116300379319/117490000000000000000 : ℝ)*(X 1 0+X 2 0)+(90503722809/1174900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6111/1024 : ℝ)) (lo := (3767/50000 : ℝ)) (hi := (19283/100000 : ℝ)) (c := (117488644116300379319/117490000000000000000 : ℝ)) (alpha := (90503722809/1174900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (117488644116300379319/117490000000000000000 : ℝ)*(X 0 1+X 2 1)+(90503722809/1174900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6111/1024 : ℝ)) (lo := (3767/50000 : ℝ)) (hi := (19283/100000 : ℝ)) (c := (117488644116300379319/117490000000000000000 : ℝ)) (alpha := (90503722809/1174900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (117488644116300379319/117490000000000000000 : ℝ)*(X 0 2+X 1 2)+(90503722809/1174900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6111/1024 : ℝ)) (lo := (3767/50000 : ℝ)) (hi := (19283/100000 : ℝ)) (c := (117488644116300379319/117490000000000000000 : ℝ)) (alpha := (90503722809/1174900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-137670501/1250000000 : ℝ)*X 0 0+(5549118487/10000000000 : ℝ)*X 0 1+(2503138147/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5334985009/10000000000 : ℝ)*X 1 0+(-1389079631/10000000000 : ℝ)*X 1 1+(2503138147/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5334985009/10000000000 : ℝ)*X 2 0+(1001255259/2000000000 : ℝ)*X 2 1+(-1389079631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1974231089/5000000000 : ℝ)*X 0 0+(3034634283/10000000000 : ℝ)*X 0 1+(4979019529/10000000000 : ℝ)*X 0 2+(1974231089/5000000000 : ℝ)*X 1 0+(3034634283/10000000000 : ℝ)*X 1 1+(4979019529/10000000000 : ℝ)*X 1 2+(1974231089/5000000000 : ℝ)*X 2 0+(3034634283/10000000000 : ℝ)*X 2 1+(4979019529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1102229183/10000000000 : ℝ)*X 0 0+(200757749/400000000 : ℝ)*X 0 1+(692009617/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2596764189/5000000000 : ℝ)*X 1 0+(-85927899/1000000000 : ℝ)*X 1 1+(692009617/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2596764189/5000000000 : ℝ)*X 2 0+(692009617/1250000000 : ℝ)*X 2 1+(-859278989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((493945139/1250000000 : ℝ)*X 0 0+(4933646553/10000000000 : ℝ)*X 0 1+(385168413/1250000000 : ℝ)*X 0 2+(493945139/1250000000 : ℝ)*X 1 0+(4933646553/10000000000 : ℝ)*X 1 1+(385168413/1250000000 : ℝ)*X 1 2+(493945139/1250000000 : ℝ)*X 2 0+(4933646553/10000000000 : ℝ)*X 2 1+(385168413/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1772_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20202445075166125269604648353/2937250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (920891853/100000000000000 : ℝ)*(base19) + (87312597/10000000000000 : ℝ)*(base23) + (25483027/100000000000000 : ℝ)*(lower2) + (41596731/25000000000000 : ℝ)*(upper3) + (8201387/6250000000000 : ℝ)*(upper5) + (1178235883473171/100000000000000 : ℝ)*(major0) + (1178235883473171/100000000000000 : ℝ)*(major1) + (1178235883473171/100000000000000 : ℝ)*(major2) + (460540370891617/25000000000000 : ℝ)*(sp0) + (921083051068043/50000000000000 : ℝ)*(sp1) + (184216614990197/10000000000000 : ℝ)*(sp2) + (514302830145797/100000000000000 : ℝ)*(sp3) + (173108171/3125000000000 : ℝ)*(sp4) + (1684505479/100000000000000 : ℝ)*(sp7) + (128576128662819/25000000000000 : ℝ)*(f.failure) + (92108351151397/5000000000000 : ℝ)*(f.sum) + (28253195746809/58745000000000000000000000000 : ℝ)*base65 + (10121694216247650549/11749000000000000000000000000000000 : ℝ)*base67 + (7233788288943349451/11749000000000000000000000000000000 : ℝ)*base70 + (61176342395481650549/11749000000000000000000000000000000 : ℝ)*base71 + (43167846056801/58745000000000000000000000000 : ℝ)*base74 + (136312839611956650549/11749000000000000000000000000000000 : ℝ)*base75 + (1472236795437650549/11749000000000000000000000000000000 : ℝ)*base77 + (10837865860781650549/11749000000000000000000000000000000 : ℝ)*base79 + (32917046614529/14686250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (34680507/2500000000000000000000 : ℝ)*base90 + (34680507/2500000000000000000000 : ℝ)*base92 + (34680507/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43805515792562816281353/11749000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18840697/4000000000000 : ℝ)*(base19) + (100509141/20000000000000 : ℝ)*(base23) + (12725761/10000000000000 : ℝ)*(lower1) + (83000943/100000000000000 : ℝ)*(upper3) + (2752131/20000000000000 : ℝ)*(lower4) + (78493701/100000000000000 : ℝ)*(upper5) + (123680204553783/10000000000000 : ℝ)*(major0) + (123680204553783/10000000000000 : ℝ)*(major1) + (123680204553783/10000000000000 : ℝ)*(major2) + (184766651/100000000000000 : ℝ)*(sp2) + (96686754808051/5000000000000 : ℝ)*(sp4) + (483433656285899/25000000000000 : ℝ)*(sp5) + (241716801106083/12500000000000 : ℝ)*(sp6) + (4217725551821/781250000000 : ℝ)*(sp7) + (4217725551821/781250000000 : ℝ)*(f.failure) + (96686754808051/5000000000000 : ℝ)*(f.sum) + (2928400934709/1174900000000000000000000000 : ℝ)*base65 + (7545923904497513777/1174900000000000000000000000000000 : ℝ)*base67 + (930138728971686223/1174900000000000000000000000000000 : ℝ)*base70 + (2811519812404486223/1174900000000000000000000000000000 : ℝ)*base72 + (26902847344259/5874500000000000000000000000 : ℝ)*base73 + (27411758667058086223/1174900000000000000000000000000000 : ℝ)*base76 + (2019017431526813777/1174900000000000000000000000000000 : ℝ)*base77 + (1466930152127413777/1174900000000000000000000000000000 : ℝ)*base79 + (24569424670081/11749000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (398913/78125000000000000000 : ℝ)*base90 + (398913/78125000000000000000 : ℝ)*base92 + (398913/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1772_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (229093047/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19283/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3767/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7551/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (963/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1772_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1772_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (229093047/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7551/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (963/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1772_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1772_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1772_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (6111/1024 : ℝ) ≤ p) (hpb : p ≤ (6143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (229093047/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7551/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (963/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1772_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

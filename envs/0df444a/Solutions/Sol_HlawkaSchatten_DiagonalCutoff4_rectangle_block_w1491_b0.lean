-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1491_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:15:44.223995+00:00
-- url     : https://prove2.me/submissions/056a26f7-5e46-47f2-ba37-fde92eafa4dc

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
theorem support_rectangle_w1491_s0_0 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-213541887/1250000000 : ℝ)*x 0 + (1185836321/2000000000 : ℝ)*x 1 + (605779109/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213541887/1250000000 : ℝ)^4479 ≤ (1011862475331/10000000000000 : ℝ)^3455 := by
    have hnat : (213541887 : ℕ)^4479*10000000000000^3455 ≤ 1011862475331^3455*1250000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213541887 1250000000 1011862475331 10000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1185836321/2000000000 : ℝ)^4479 ≤ (2031301841161/4000000000000 : ℝ)^3455 := by
    have hnat : (1185836321 : ℕ)^4479*4000000000000^3455 ≤ 2031301841161^3455*2000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1185836321 2000000000 2031301841161 4000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (605779109/1250000000 : ℝ)^4479 ≤ (39098829203429/100000000000000 : ℝ)^3455 := by
    have hnat : (605779109 : ℕ)^4479*100000000000000^3455 ≤ 39098829203429^3455*1250000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605779109 1250000000 39098829203429 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-213541887/1250000000 : ℝ), (1185836321/2000000000 : ℝ), (605779109/1250000000 : ℝ)] ![(1011862475331/10000000000000 : ℝ), (2031301841161/4000000000000 : ℝ), (39098829203429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-213541887/1250000000 : ℝ)|^4479 ≤ (1011862475331/10000000000000 : ℝ)^3455
        have hw : |(-213541887/1250000000 : ℝ)|=(213541887/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1185836321/2000000000 : ℝ)|^4479 ≤ (2031301841161/4000000000000 : ℝ)^3455
        have hw : |(1185836321/2000000000 : ℝ)|=(1185836321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(605779109/1250000000 : ℝ)|^4479 ≤ (39098829203429/100000000000000 : ℝ)^3455
        have hw : |(605779109/1250000000 : ℝ)|=(605779109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s0_1 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5482564057/10000000000 : ℝ)*x 0 + (-2317012341/10000000000 : ℝ)*x 1 + (4846232887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5482564057/10000000000 : ℝ)^4479 ≤ (22939987443561/50000000000000 : ℝ)^3455 := by
    have hnat : (5482564057 : ℕ)^4479*50000000000000^3455 ≤ 22939987443561^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482564057 10000000000 22939987443561 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2317012341/10000000000 : ℝ)^4479 ≤ (1502119573833/10000000000000 : ℝ)^3455 := by
    have hnat : (2317012341 : ℕ)^4479*10000000000000^3455 ≤ 1502119573833^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2317012341 10000000000 1502119573833 10000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4846232887/10000000000 : ℝ)^4479 ≤ (7819765872063/20000000000000 : ℝ)^3455 := by
    have hnat : (4846232887 : ℕ)^4479*20000000000000^3455 ≤ 7819765872063^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4846232887 10000000000 7819765872063 20000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5482564057/10000000000 : ℝ), (-2317012341/10000000000 : ℝ), (4846232887/10000000000 : ℝ)] ![(22939987443561/50000000000000 : ℝ), (1502119573833/10000000000000 : ℝ), (7819765872063/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5482564057/10000000000 : ℝ)|^4479 ≤ (22939987443561/50000000000000 : ℝ)^3455
        have hw : |(5482564057/10000000000 : ℝ)|=(5482564057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2317012341/10000000000 : ℝ)|^4479 ≤ (1502119573833/10000000000000 : ℝ)^3455
        have hw : |(-2317012341/10000000000 : ℝ)|=(2317012341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4846232887/10000000000 : ℝ)|^4479 ≤ (7819765872063/20000000000000 : ℝ)^3455
        have hw : |(4846232887/10000000000 : ℝ)|=(4846232887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s0_2 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5482564053/10000000000 : ℝ)*x 0 + (1211558229/2500000000 : ℝ)*x 1 + (-231701231/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5482564053/10000000000 : ℝ)^4479 ≤ (2867498427733/6250000000000 : ℝ)^3455 := by
    have hnat : (5482564053 : ℕ)^4479*6250000000000^3455 ≤ 2867498427733^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482564053 10000000000 2867498427733 6250000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1211558229/2500000000 : ℝ)^4479 ≤ (39098829663627/100000000000000 : ℝ)^3455 := by
    have hnat : (1211558229 : ℕ)^4479*100000000000000^3455 ≤ 39098829663627^3455*2500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1211558229 2500000000 39098829663627 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (231701231/1000000000 : ℝ)^4479 ≤ (469412358681/3125000000000 : ℝ)^3455 := by
    have hnat : (231701231 : ℕ)^4479*3125000000000^3455 ≤ 469412358681^3455*1000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231701231 1000000000 469412358681 3125000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5482564053/10000000000 : ℝ), (1211558229/2500000000 : ℝ), (-231701231/1000000000 : ℝ)] ![(2867498427733/6250000000000 : ℝ), (39098829663627/100000000000000 : ℝ), (469412358681/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5482564053/10000000000 : ℝ)|^4479 ≤ (2867498427733/6250000000000 : ℝ)^3455
        have hw : |(5482564053/10000000000 : ℝ)|=(5482564053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1211558229/2500000000 : ℝ)|^4479 ≤ (39098829663627/100000000000000 : ℝ)^3455
        have hw : |(1211558229/2500000000 : ℝ)|=(1211558229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-231701231/1000000000 : ℝ)|^4479 ≤ (469412358681/3125000000000 : ℝ)^3455
        have hw : |(-231701231/1000000000 : ℝ)|=(231701231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s0_3 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (51885689/125000000 : ℝ)*x 0 + (3091299159/10000000000 : ℝ)*x 1 + (5510683241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51885689/125000000 : ℝ)^4479 ≤ (15993017384417/50000000000000 : ℝ)^3455 := by
    have hnat : (51885689 : ℕ)^4479*50000000000000^3455 ≤ 15993017384417^3455*125000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51885689 125000000 15993017384417 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091299159/10000000000 : ℝ)^4479 ≤ (21828705826357/100000000000000 : ℝ)^3455 := by
    have hnat : (3091299159 : ℕ)^4479*100000000000000^3455 ≤ 21828705826357^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091299159 10000000000 21828705826357 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5510683241/10000000000 : ℝ)^4479 ≤ (23092629689989/50000000000000 : ℝ)^3455 := by
    have hnat : (5510683241 : ℕ)^4479*50000000000000^3455 ≤ 23092629689989^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510683241 10000000000 23092629689989 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(51885689/125000000 : ℝ), (3091299159/10000000000 : ℝ), (5510683241/10000000000 : ℝ)] ![(15993017384417/50000000000000 : ℝ), (21828705826357/100000000000000 : ℝ), (23092629689989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(51885689/125000000 : ℝ)|^4479 ≤ (15993017384417/50000000000000 : ℝ)^3455
        have hw : |(51885689/125000000 : ℝ)|=(51885689/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091299159/10000000000 : ℝ)|^4479 ≤ (21828705826357/100000000000000 : ℝ)^3455
        have hw : |(3091299159/10000000000 : ℝ)|=(3091299159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5510683241/10000000000 : ℝ)|^4479 ≤ (23092629689989/50000000000000 : ℝ)^3455
        have hw : |(5510683241/10000000000 : ℝ)|=(5510683241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s0_4 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-53501221/312500000 : ℝ)*x 0 + (2436981329/5000000000 : ℝ)*x 1 + (5900455713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53501221/312500000 : ℝ)^4479 ≤ (634192199837/6250000000000 : ℝ)^3455 := by
    have hnat : (53501221 : ℕ)^4479*6250000000000^3455 ≤ 634192199837^3455*312500000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53501221 312500000 634192199837 6250000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2436981329/5000000000 : ℝ)^4479 ≤ (39389102181547/100000000000000 : ℝ)^3455 := by
    have hnat : (2436981329 : ℕ)^4479*100000000000000^3455 ≤ 39389102181547^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2436981329 5000000000 39389102181547 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5900455713/10000000000 : ℝ)^4479 ≤ (25231911303851/50000000000000 : ℝ)^3455 := by
    have hnat : (5900455713 : ℕ)^4479*50000000000000^3455 ≤ 25231911303851^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5900455713 10000000000 25231911303851 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53501221/312500000 : ℝ), (2436981329/5000000000 : ℝ), (5900455713/10000000000 : ℝ)] ![(634192199837/6250000000000 : ℝ), (39389102181547/100000000000000 : ℝ), (25231911303851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53501221/312500000 : ℝ)|^4479 ≤ (634192199837/6250000000000 : ℝ)^3455
        have hw : |(-53501221/312500000 : ℝ)|=(53501221/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2436981329/5000000000 : ℝ)|^4479 ≤ (39389102181547/100000000000000 : ℝ)^3455
        have hw : |(2436981329/5000000000 : ℝ)|=(2436981329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5900455713/10000000000 : ℝ)|^4479 ≤ (25231911303851/50000000000000 : ℝ)^3455
        have hw : |(5900455713/10000000000 : ℝ)|=(5900455713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s0_5 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5186800917/10000000000 : ℝ)*x 0 + (-1262789419/10000000000 : ℝ)*x 1 + (2950227883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5186800917/10000000000 : ℝ)^4479 ≤ (8539470173007/20000000000000 : ℝ)^3455 := by
    have hnat : (5186800917 : ℕ)^4479*20000000000000^3455 ≤ 8539470173007^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186800917 10000000000 8539470173007 20000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1262789419/10000000000 : ℝ)^4479 ≤ (3419412965767/50000000000000 : ℝ)^3455 := by
    have hnat : (1262789419 : ℕ)^4479*50000000000000^3455 ≤ 3419412965767^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262789419 10000000000 3419412965767 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2950227883/5000000000 : ℝ)^4479 ≤ (50463823195331/100000000000000 : ℝ)^3455 := by
    have hnat : (2950227883 : ℕ)^4479*100000000000000^3455 ≤ 50463823195331^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2950227883 5000000000 50463823195331 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5186800917/10000000000 : ℝ), (-1262789419/10000000000 : ℝ), (2950227883/5000000000 : ℝ)] ![(8539470173007/20000000000000 : ℝ), (3419412965767/50000000000000 : ℝ), (50463823195331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5186800917/10000000000 : ℝ)|^4479 ≤ (8539470173007/20000000000000 : ℝ)^3455
        have hw : |(5186800917/10000000000 : ℝ)|=(5186800917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1262789419/10000000000 : ℝ)|^4479 ≤ (3419412965767/50000000000000 : ℝ)^3455
        have hw : |(-1262789419/10000000000 : ℝ)|=(1262789419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2950227883/5000000000 : ℝ)|^4479 ≤ (50463823195331/100000000000000 : ℝ)^3455
        have hw : |(2950227883/5000000000 : ℝ)|=(2950227883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s0_6 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1296700243/2500000000 : ℝ)*x 0 + (2950227823/5000000000 : ℝ)*x 1 + (-315697381/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1296700243/2500000000 : ℝ)^4479 ≤ (2134867572599/5000000000000 : ℝ)^3455 := by
    have hnat : (1296700243 : ℕ)^4479*5000000000000^3455 ≤ 2134867572599^3455*2500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296700243 2500000000 2134867572599 5000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2950227823/5000000000 : ℝ)^4479 ≤ (1009276437297/2000000000000 : ℝ)^3455 := by
    have hnat : (2950227823 : ℕ)^4479*2000000000000^3455 ≤ 1009276437297^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2950227823 5000000000 1009276437297 2000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315697381/2500000000 : ℝ)^4479 ≤ (6838826668713/100000000000000 : ℝ)^3455 := by
    have hnat : (315697381 : ℕ)^4479*100000000000000^3455 ≤ 6838826668713^3455*2500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315697381 2500000000 6838826668713 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1296700243/2500000000 : ℝ), (2950227823/5000000000 : ℝ), (-315697381/2500000000 : ℝ)] ![(2134867572599/5000000000000 : ℝ), (1009276437297/2000000000000 : ℝ), (6838826668713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1296700243/2500000000 : ℝ)|^4479 ≤ (2134867572599/5000000000000 : ℝ)^3455
        have hw : |(1296700243/2500000000 : ℝ)|=(1296700243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2950227823/5000000000 : ℝ)|^4479 ≤ (1009276437297/2000000000000 : ℝ)^3455
        have hw : |(2950227823/5000000000 : ℝ)|=(2950227823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-315697381/2500000000 : ℝ)|^4479 ≤ (6838826668713/100000000000000 : ℝ)^3455
        have hw : |(-315697381/2500000000 : ℝ)|=(315697381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s0_7 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2079565193/5000000000 : ℝ)*x 0 + (340545809/625000000 : ℝ)*x 1 + (788868711/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079565193/5000000000 : ℝ)^4479 ≤ (32068727251591/100000000000000 : ℝ)^3455 := by
    have hnat : (2079565193 : ℕ)^4479*100000000000000^3455 ≤ 32068727251591^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079565193 5000000000 32068727251591 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340545809/625000000 : ℝ)^4479 ≤ (45513291816617/100000000000000 : ℝ)^3455 := by
    have hnat : (340545809 : ℕ)^4479*100000000000000^3455 ≤ 45513291816617^3455*625000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340545809 625000000 45513291816617 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (788868711/2500000000 : ℝ)^4479 ≤ (1120899046041/5000000000000 : ℝ)^3455 := by
    have hnat : (788868711 : ℕ)^4479*5000000000000^3455 ≤ 1120899046041^3455*2500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788868711 2500000000 1120899046041 5000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2079565193/5000000000 : ℝ), (340545809/625000000 : ℝ), (788868711/2500000000 : ℝ)] ![(32068727251591/100000000000000 : ℝ), (45513291816617/100000000000000 : ℝ), (1120899046041/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2079565193/5000000000 : ℝ)|^4479 ≤ (32068727251591/100000000000000 : ℝ)^3455
        have hw : |(2079565193/5000000000 : ℝ)|=(2079565193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340545809/625000000 : ℝ)|^4479 ≤ (45513291816617/100000000000000 : ℝ)^3455
        have hw : |(340545809/625000000 : ℝ)|=(340545809/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(788868711/2500000000 : ℝ)|^4479 ≤ (1120899046041/5000000000000 : ℝ)^3455
        have hw : |(788868711/2500000000 : ℝ)|=(788868711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1491_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2553/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25759/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4477/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4477 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4477*1^1024 ≤ 0^1024*1^4477 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4477 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4477/1024 : ℝ) ≤ (1820448099939375697/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4477 ≤ (1820448099939375697/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4477*100000000000000000000^1024 ≤ 1820448099939375697^1024*5^4477 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1820448099939375697 100000000000000000000 4477 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1820448099939375697/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4477 := by
      have hnat : (1 : ℕ)^1024*1^4477 ≤ 1^4477*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101820448099939375697/100000000000000000000 : ℝ) ≤ (5020674457105007/5000000000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (101820448099939375697/100000000000000000000 : ℝ)^1024 ≤ (5020674457105007/5000000000000000 : ℝ)^4477 := by
      have hnat : (101820448099939375697 : ℕ)^1024*5000000000000000^4477 ≤ 5020674457105007^4477*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101820448099939375697 100000000000000000000 5020674457105007 5000000000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5020674457105007/5000000000000000 : ℝ)) (X := (101820448099939375697/100000000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51820448099939375697/50000000000000000000 : ℝ) ≤ (2520674457105007/2500000000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (51820448099939375697/50000000000000000000 : ℝ)^1024 ≤ (2520674457105007/2500000000000000 : ℝ)^4477 := by
      have hnat : (51820448099939375697 : ℕ)^1024*2500000000000000^4477 ≤ 2520674457105007^4477*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51820448099939375697 50000000000000000000 2520674457105007 2500000000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2520674457105007/2500000000000000 : ℝ)) (X := (51820448099939375697/50000000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(20674457105007/2000000000000000 : ℝ)*(0 : ℝ))^(4477/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(20674457105007/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1820448099939375697/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(20674457105007/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4477/1024 : ℝ) := by
    rw [show (1 : ℝ)+(20674457105007/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5020674457105007/5000000000000000 : ℝ) by norm_num, show 1+(1820448099939375697/100000000000000000000 : ℝ)+(0 : ℝ)=(101820448099939375697/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1820448099939375697/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(20674457105007/2000000000000000 : ℝ)*(2/5 : ℝ))^(4477/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(20674457105007/2000000000000000 : ℝ)*(2/5 : ℝ)=(2520674457105007/2500000000000000 : ℝ) by norm_num, show 1+2*(1820448099939375697/100000000000000000000 : ℝ)=(51820448099939375697/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(20674457105007/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (20674457105007/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(20674457105007/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (20674457105007/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(20674457105007/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (20674457105007/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-213541887/1250000000 : ℝ)*X 0 0+(1185836321/2000000000 : ℝ)*X 0 1+(605779109/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5482564057/10000000000 : ℝ)*X 1 0+(-2317012341/10000000000 : ℝ)*X 1 1+(4846232887/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5482564053/10000000000 : ℝ)*X 2 0+(1211558229/2500000000 : ℝ)*X 2 1+(-231701231/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((51885689/125000000 : ℝ)*X 0 0+(3091299159/10000000000 : ℝ)*X 0 1+(5510683241/10000000000 : ℝ)*X 0 2+(51885689/125000000 : ℝ)*X 1 0+(3091299159/10000000000 : ℝ)*X 1 1+(5510683241/10000000000 : ℝ)*X 1 2+(51885689/125000000 : ℝ)*X 2 0+(3091299159/10000000000 : ℝ)*X 2 1+(5510683241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-53501221/312500000 : ℝ)*X 0 0+(2436981329/5000000000 : ℝ)*X 0 1+(5900455713/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5186800917/10000000000 : ℝ)*X 1 0+(-1262789419/10000000000 : ℝ)*X 1 1+(2950227883/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1296700243/2500000000 : ℝ)*X 2 0+(2950227823/5000000000 : ℝ)*X 2 1+(-315697381/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2079565193/5000000000 : ℝ)*X 0 0+(340545809/625000000 : ℝ)*X 0 1+(788868711/2500000000 : ℝ)*X 0 2+(2079565193/5000000000 : ℝ)*X 1 0+(340545809/625000000 : ℝ)*X 1 1+(788868711/2500000000 : ℝ)*X 1 2+(2079565193/5000000000 : ℝ)*X 2 0+(340545809/625000000 : ℝ)*X 2 1+(788868711/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (410839782806086138930233/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2069703/5000000000000 : ℝ)*(base1) + (915723009/100000000000000 : ℝ)*(base19) + (457524651/50000000000000 : ℝ)*(base23) + (54868879/50000000000000 : ℝ)*(upper3) + (59066503/50000000000000 : ℝ)*(upper5) + (668371146560227/100000000000000 : ℝ)*(major0) + (668371146560227/100000000000000 : ℝ)*(major1) + (668371146560227/100000000000000 : ℝ)*(major2) + (923407778976957/100000000000000 : ℝ)*(sp0) + (923410080460753/100000000000000 : ℝ)*(sp1) + (46170504056723/5000000000000 : ℝ)*(sp2) + (41332970282151/10000000000000 : ℝ)*(sp3) + (1629300433/50000000000000 : ℝ)*(sp4) + (353943631/25000000000000 : ℝ)*(sp7) + (206665579995047/50000000000000 : ℝ)*(f.failure) + (461705498091881/50000000000000 : ℝ)*(f.sum) + (114078764756589/100000000000000000000000000000 : ℝ)*base65 + (111704723043411/200000000000000000000000000000 : ℝ)*base68 + (749944636843411/200000000000000000000000000000 : ℝ)*base70 + (136074111756589/200000000000000000000000000000 : ℝ)*base71 + (128240991456589/100000000000000000000000000000 : ℝ)*base73 + (933854173356589/200000000000000000000000000000 : ℝ)*base75 + (155648180043411/200000000000000000000000000000 : ℝ)*base78 + (1228265767556589/200000000000000000000000000000 : ℝ)*base79 + (64409967843411/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (7668291/5000000000000000000000 : ℝ)*base90 + (7668291/5000000000000000000000 : ℝ)*base92 + (7668291/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7359017264300846217/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1630648333/100000000000000 : ℝ)*(base19) + (1652304033/100000000000000 : ℝ)*(base23) + (68440657/50000000000000 : ℝ)*(base32) + (49116061/20000000000000 : ℝ)*(upper3) + (158606973/100000000000000 : ℝ)*(upper5) + (352562738313979/50000000000000 : ℝ)*(major0) + (352562738313979/50000000000000 : ℝ)*(major1) + (352562738313979/50000000000000 : ℝ)*(major2) + (507571037/12500000000000 : ℝ)*(sp1) + (4259185633/100000000000000 : ℝ)*(sp2) + (121773761997969/12500000000000 : ℝ)*(sp4) + (487092202383561/50000000000000 : ℝ)*(sp5) + (487092092247043/50000000000000 : ℝ)*(sp6) + (43606047509027/10000000000000 : ℝ)*(sp7) + (851680882757/195312500000 : ℝ)*(f.failure) + (121773761997969/12500000000000 : ℝ)*(f.sum) + (50642764807147/50000000000000000000000000000 : ℝ)*base66 + (312237769392853/100000000000000000000000000000 : ℝ)*base67 + (21022233392853/100000000000000000000000000000 : ℝ)*base69 + (541363342392853/100000000000000000000000000000 : ℝ)*base71 + (203045052307147/50000000000000000000000000000 : ℝ)*base74 + (917692150592853/100000000000000000000000000000 : ℝ)*base75 + (448511902892853/100000000000000000000000000000 : ℝ)*base77 + (75390512592853/100000000000000000000000000000 : ℝ)*base79 + (250066990307147/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1949/4882812500000000000 : ℝ)*base90 + (1949/4882812500000000000 : ℝ)*base92 + (1949/4882812500000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1491_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2553/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25759/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1491_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1491_s1_0 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-933862753/5000000000 : ℝ)*x 0 + (44679059/80000000 : ℝ)*x 1 + (5088180201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (933862753/5000000000 : ℝ)^4479 ≤ (5679542035121/50000000000000 : ℝ)^3455 := by
    have hnat : (933862753 : ℕ)^4479*50000000000000^3455 ≤ 5679542035121^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933862753 5000000000 5679542035121 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44679059/80000000 : ℝ)^4479 ≤ (46993038771633/100000000000000 : ℝ)^3455 := by
    have hnat : (44679059 : ℕ)^4479*100000000000000^3455 ≤ 46993038771633^3455*80000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44679059 80000000 46993038771633 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5088180201/10000000000 : ℝ)^4479 ≤ (41647877141617/100000000000000 : ℝ)^3455 := by
    have hnat : (5088180201 : ℕ)^4479*100000000000000^3455 ≤ 41647877141617^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5088180201 10000000000 41647877141617 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-933862753/5000000000 : ℝ), (44679059/80000000 : ℝ), (5088180201/10000000000 : ℝ)] ![(5679542035121/50000000000000 : ℝ), (46993038771633/100000000000000 : ℝ), (41647877141617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-933862753/5000000000 : ℝ)|^4479 ≤ (5679542035121/50000000000000 : ℝ)^3455
        have hw : |(-933862753/5000000000 : ℝ)|=(933862753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(44679059/80000000 : ℝ)|^4479 ≤ (46993038771633/100000000000000 : ℝ)^3455
        have hw : |(44679059/80000000 : ℝ)|=(44679059/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5088180201/10000000000 : ℝ)|^4479 ≤ (41647877141617/100000000000000 : ℝ)^3455
        have hw : |(5088180201/10000000000 : ℝ)|=(5088180201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s1_1 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (673812149/1250000000 : ℝ)*x 0 + (-2129979197/10000000000 : ℝ)*x 1 + (5088179117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (673812149/1250000000 : ℝ)^4479 ≤ (44883676502327/100000000000000 : ℝ)^3455 := by
    have hnat : (673812149 : ℕ)^4479*100000000000000^3455 ≤ 44883676502327^3455*1250000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673812149 1250000000 44883676502327 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2129979197/10000000000 : ℝ)^4479 ≤ (13468457846261/100000000000000 : ℝ)^3455 := by
    have hnat : (2129979197 : ℕ)^4479*100000000000000^3455 ≤ 13468457846261^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129979197 10000000000 13468457846261 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5088179117/10000000000 : ℝ)^4479 ≤ (20823932819553/50000000000000 : ℝ)^3455 := by
    have hnat : (5088179117 : ℕ)^4479*50000000000000^3455 ≤ 20823932819553^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5088179117 10000000000 20823932819553 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(673812149/1250000000 : ℝ), (-2129979197/10000000000 : ℝ), (5088179117/10000000000 : ℝ)] ![(44883676502327/100000000000000 : ℝ), (13468457846261/100000000000000 : ℝ), (20823932819553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(673812149/1250000000 : ℝ)|^4479 ≤ (44883676502327/100000000000000 : ℝ)^3455
        have hw : |(673812149/1250000000 : ℝ)|=(673812149/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2129979197/10000000000 : ℝ)|^4479 ≤ (13468457846261/100000000000000 : ℝ)^3455
        have hw : |(-2129979197/10000000000 : ℝ)|=(2129979197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5088179117/10000000000 : ℝ)|^4479 ≤ (20823932819553/50000000000000 : ℝ)^3455
        have hw : |(5088179117/10000000000 : ℝ)|=(5088179117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s1_2 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1347624109/2500000000 : ℝ)*x 0 + (5088179683/10000000000 : ℝ)*x 1 + (-106498973/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347624109/2500000000 : ℝ)^4479 ≤ (44883668341871/100000000000000 : ℝ)^3455 := by
    have hnat : (1347624109 : ℕ)^4479*100000000000000^3455 ≤ 44883668341871^3455*2500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347624109 2500000000 44883668341871 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5088179683/10000000000 : ℝ)^4479 ≤ (41647871645029/100000000000000 : ℝ)^3455 := by
    have hnat : (5088179683 : ℕ)^4479*100000000000000^3455 ≤ 41647871645029^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5088179683 10000000000 41647871645029 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106498973/500000000 : ℝ)^4479 ≤ (538738400087/4000000000000 : ℝ)^3455 := by
    have hnat : (106498973 : ℕ)^4479*4000000000000^3455 ≤ 538738400087^3455*500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106498973 500000000 538738400087 4000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1347624109/2500000000 : ℝ), (5088179683/10000000000 : ℝ), (-106498973/500000000 : ℝ)] ![(44883668341871/100000000000000 : ℝ), (41647871645029/100000000000000 : ℝ), (538738400087/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1347624109/2500000000 : ℝ)|^4479 ≤ (44883668341871/100000000000000 : ℝ)^3455
        have hw : |(1347624109/2500000000 : ℝ)|=(1347624109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5088179683/10000000000 : ℝ)|^4479 ≤ (41647871645029/100000000000000 : ℝ)^3455
        have hw : |(5088179683/10000000000 : ℝ)|=(5088179683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-106498973/500000000 : ℝ)|^4479 ≤ (538738400087/4000000000000 : ℝ)^3455
        have hw : |(-106498973/500000000 : ℝ)|=(106498973/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s1_3 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4257264909/10000000000 : ℝ)*x 0 + (373348753/1000000000 : ℝ)*x 1 + (4843156609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4257264909/10000000000 : ℝ)^4479 ≤ (8263264817817/25000000000000 : ℝ)^3455 := by
    have hnat : (4257264909 : ℕ)^4479*25000000000000^3455 ≤ 8263264817817^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4257264909 10000000000 8263264817817 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (373348753/1000000000 : ℝ)^4479 ≤ (6970070819501/25000000000000 : ℝ)^3455 := by
    have hnat : (373348753 : ℕ)^4479*25000000000000^3455 ≤ 6970070819501^3455*1000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373348753 1000000000 6970070819501 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4843156609/10000000000 : ℝ)^4479 ≤ (3906665742379/10000000000000 : ℝ)^3455 := by
    have hnat : (4843156609 : ℕ)^4479*10000000000000^3455 ≤ 3906665742379^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4843156609 10000000000 3906665742379 10000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4257264909/10000000000 : ℝ), (373348753/1000000000 : ℝ), (4843156609/10000000000 : ℝ)] ![(8263264817817/25000000000000 : ℝ), (6970070819501/25000000000000 : ℝ), (3906665742379/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4257264909/10000000000 : ℝ)|^4479 ≤ (8263264817817/25000000000000 : ℝ)^3455
        have hw : |(4257264909/10000000000 : ℝ)|=(4257264909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(373348753/1000000000 : ℝ)|^4479 ≤ (6970070819501/25000000000000 : ℝ)^3455
        have hw : |(373348753/1000000000 : ℝ)|=(373348753/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4843156609/10000000000 : ℝ)|^4479 ≤ (3906665742379/10000000000000 : ℝ)^3455
        have hw : |(4843156609/10000000000 : ℝ)|=(4843156609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s1_4 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-233508791/1250000000 : ℝ)*x 0 + (636737709/1250000000 : ℝ)*x 1 + (1785301/3200000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (233508791/1250000000 : ℝ)^4479 ≤ (5680901412777/50000000000000 : ℝ)^3455 := by
    have hnat : (233508791 : ℕ)^4479*50000000000000^3455 ≤ 5680901412777^3455*1250000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233508791 1250000000 5680901412777 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (636737709/1250000000 : ℝ)^4479 ≤ (41708598774441/100000000000000 : ℝ)^3455 := by
    have hnat : (636737709 : ℕ)^4479*100000000000000^3455 ≤ 41708598774441^3455*1250000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      636737709 1250000000 41708598774441 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1785301/3200000 : ℝ)^4479 ≤ (23464799189971/50000000000000 : ℝ)^3455 := by
    have hnat : (1785301 : ℕ)^4479*50000000000000^3455 ≤ 23464799189971^3455*3200000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1785301 3200000 23464799189971 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-233508791/1250000000 : ℝ), (636737709/1250000000 : ℝ), (1785301/3200000 : ℝ)] ![(5680901412777/50000000000000 : ℝ), (41708598774441/100000000000000 : ℝ), (23464799189971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-233508791/1250000000 : ℝ)|^4479 ≤ (5680901412777/50000000000000 : ℝ)^3455
        have hw : |(-233508791/1250000000 : ℝ)|=(233508791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(636737709/1250000000 : ℝ)|^4479 ≤ (41708598774441/100000000000000 : ℝ)^3455
        have hw : |(636737709/1250000000 : ℝ)|=(636737709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1785301/3200000 : ℝ)|^4479 ≤ (23464799189971/50000000000000 : ℝ)^3455
        have hw : |(1785301/3200000 : ℝ)|=(1785301/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s1_5 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5260008941/10000000000 : ℝ)*x 0 + (-1639092761/10000000000 : ℝ)*x 1 + (1115813141/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260008941/10000000000 : ℝ)^4479 ≤ (5435029374623/12500000000000 : ℝ)^3455 := by
    have hnat : (5260008941 : ℕ)^4479*12500000000000^3455 ≤ 5435029374623^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260008941 10000000000 5435029374623 12500000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1639092761/10000000000 : ℝ)^4479 ≤ (9590165746901/100000000000000 : ℝ)^3455 := by
    have hnat : (1639092761 : ℕ)^4479*100000000000000^3455 ≤ 9590165746901^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1639092761 10000000000 9590165746901 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1115813141/2000000000 : ℝ)^4479 ≤ (5866199906541/12500000000000 : ℝ)^3455 := by
    have hnat : (1115813141 : ℕ)^4479*12500000000000^3455 ≤ 5866199906541^3455*2000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115813141 2000000000 5866199906541 12500000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260008941/10000000000 : ℝ), (-1639092761/10000000000 : ℝ), (1115813141/2000000000 : ℝ)] ![(5435029374623/12500000000000 : ℝ), (9590165746901/100000000000000 : ℝ), (5866199906541/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260008941/10000000000 : ℝ)|^4479 ≤ (5435029374623/12500000000000 : ℝ)^3455
        have hw : |(5260008941/10000000000 : ℝ)|=(5260008941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1639092761/10000000000 : ℝ)|^4479 ≤ (9590165746901/100000000000000 : ℝ)^3455
        have hw : |(-1639092761/10000000000 : ℝ)|=(1639092761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1115813141/2000000000 : ℝ)|^4479 ≤ (5866199906541/12500000000000 : ℝ)^3455
        have hw : |(1115813141/2000000000 : ℝ)|=(1115813141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s1_6 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2630004449/5000000000 : ℝ)*x 0 + (55790657/100000000 : ℝ)*x 1 + (-409773207/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2630004449/5000000000 : ℝ)^4479 ≤ (4348023453619/10000000000000 : ℝ)^3455 := by
    have hnat : (2630004449 : ℕ)^4479*10000000000000^3455 ≤ 4348023453619^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630004449 5000000000 4348023453619 10000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55790657/100000000 : ℝ)^4479 ≤ (11732399799451/25000000000000 : ℝ)^3455 := by
    have hnat : (55790657 : ℕ)^4479*25000000000000^3455 ≤ 11732399799451^3455*100000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55790657 100000000 11732399799451 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (409773207/2500000000 : ℝ)^4479 ≤ (1198770781887/12500000000000 : ℝ)^3455 := by
    have hnat : (409773207 : ℕ)^4479*12500000000000^3455 ≤ 1198770781887^3455*2500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409773207 2500000000 1198770781887 12500000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2630004449/5000000000 : ℝ), (55790657/100000000 : ℝ), (-409773207/2500000000 : ℝ)] ![(4348023453619/10000000000000 : ℝ), (11732399799451/25000000000000 : ℝ), (1198770781887/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2630004449/5000000000 : ℝ)|^4479 ≤ (4348023453619/10000000000000 : ℝ)^3455
        have hw : |(2630004449/5000000000 : ℝ)|=(2630004449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(55790657/100000000 : ℝ)|^4479 ≤ (11732399799451/25000000000000 : ℝ)^3455
        have hw : |(55790657/100000000 : ℝ)|=(55790657/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-409773207/2500000000 : ℝ)|^4479 ≤ (1198770781887/12500000000000 : ℝ)^3455
        have hw : |(-409773207/2500000000 : ℝ)|=(409773207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s1_7 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4258034559/10000000000 : ℝ)*x 0 + (966074817/2000000000 : ℝ)*x 1 + (187324131/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4258034559/10000000000 : ℝ)^4479 ≤ (8265201502487/25000000000000 : ℝ)^3455 := by
    have hnat : (4258034559 : ℕ)^4479*25000000000000^3455 ≤ 8265201502487^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4258034559 10000000000 8265201502487 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (966074817/2000000000 : ℝ)^4479 ≤ (38933041761309/100000000000000 : ℝ)^3455 := by
    have hnat : (966074817 : ℕ)^4479*100000000000000^3455 ≤ 38933041761309^3455*2000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966074817 2000000000 38933041761309 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187324131/500000000 : ℝ)^4479 ≤ (1400307610553/5000000000000 : ℝ)^3455 := by
    have hnat : (187324131 : ℕ)^4479*5000000000000^3455 ≤ 1400307610553^3455*500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187324131 500000000 1400307610553 5000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4258034559/10000000000 : ℝ), (966074817/2000000000 : ℝ), (187324131/500000000 : ℝ)] ![(8265201502487/25000000000000 : ℝ), (38933041761309/100000000000000 : ℝ), (1400307610553/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4258034559/10000000000 : ℝ)|^4479 ≤ (8265201502487/25000000000000 : ℝ)^3455
        have hw : |(4258034559/10000000000 : ℝ)|=(4258034559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(966074817/2000000000 : ℝ)|^4479 ≤ (38933041761309/100000000000000 : ℝ)^3455
        have hw : |(966074817/2000000000 : ℝ)|=(966074817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(187324131/500000000 : ℝ)|^4479 ≤ (1400307610553/5000000000000 : ℝ)^3455
        have hw : |(187324131/500000000 : ℝ)|=(187324131/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1491_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2553/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1613/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18567/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2553/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2553/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2553/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2553/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2553/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2553/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2553/100000 : ℝ) ^ (4477/1024 : ℝ) ≤ (2170421854287/20000000000000000000 : ℝ) := by
    have hpowers : (2553/100000 : ℝ)^4477 ≤ (2170421854287/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2553 : ℕ)^4477*20000000000000000000^1024 ≤ 2170421854287^1024*100000^4477 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2553 100000 2170421854287 20000000000000000000 4477 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2553/100000 : ℝ)) (X := (2170421854287/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25759/100000 : ℝ) ^ (4477/1024 : ℝ) ≤ (265790935063210859/100000000000000000000 : ℝ) := by
    have hpowers : (25759/100000 : ℝ)^4477 ≤ (265790935063210859/100000000000000000000 : ℝ)^1024 := by
      have hnat : (25759 : ℕ)^4477*100000000000000000000^1024 ≤ 265790935063210859^1024*100000^4477 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25759 100000 265790935063210859 100000000000000000000 4477 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25759/100000 : ℝ)) (X := (265790935063210859/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000002170421854287/10000000000000000000 : ℝ) ≤ (10000000496428813/10000000000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (10000002170421854287/10000000000000000000 : ℝ)^1024 ≤ (10000000496428813/10000000000000000 : ℝ)^4477 := by
      have hnat : (10000002170421854287 : ℕ)^1024*10000000000000000^4477 ≤ 10000000496428813^4477*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000002170421854287 10000000000000000000 10000000496428813 10000000000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000496428813/10000000000000000 : ℝ)) (X := (10000002170421854287/10000000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50132900893586241147/50000000000000000000 : ℝ) ≤ (2001214663716157/2000000000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (50132900893586241147/50000000000000000000 : ℝ)^1024 ≤ (2001214663716157/2000000000000000 : ℝ)^4477 := by
      have hnat : (50132900893586241147 : ℕ)^1024*2000000000000000^4477 ≤ 2001214663716157^4477*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50132900893586241147 50000000000000000000 2001214663716157 2000000000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001214663716157/2000000000000000 : ℝ)) (X := (50132900893586241147/50000000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50265790935063210859/50000000000000000000 : ℝ) ≤ (10012146140732757/10000000000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (50265790935063210859/50000000000000000000 : ℝ)^1024 ≤ (10012146140732757/10000000000000000 : ℝ)^4477 := by
      have hnat : (50265790935063210859 : ℕ)^1024*10000000000000000^4477 ≤ 10012146140732757^4477*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50265790935063210859 50000000000000000000 10012146140732757 10000000000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012146140732757/10000000000000000 : ℝ)) (X := (50265790935063210859/50000000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2170421854287/20000000000000000000 : ℝ) ≤ ((116014501845109532723/116030000000000000000 : ℝ)+2*(1518205537993/580150000000000 : ℝ)*(2553/100000 : ℝ))^(4477/1024 : ℝ) := by
    rw [show (116014501845109532723/116030000000000000000 : ℝ)+2*(1518205537993/580150000000000 : ℝ)*(2553/100000 : ℝ)=(10000000496428813/10000000000000000 : ℝ) by norm_num, show 1+2*(2170421854287/20000000000000000000 : ℝ)=(10000002170421854287/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(265790935063210859/100000000000000000000 : ℝ)+(2170421854287/20000000000000000000 : ℝ) ≤ ((116014501845109532723/116030000000000000000 : ℝ)+(1518205537993/580150000000000 : ℝ)*((25759/100000 : ℝ)+(2553/100000 : ℝ)))^(4477/1024 : ℝ) := by
    rw [show (116014501845109532723/116030000000000000000 : ℝ)+(1518205537993/580150000000000 : ℝ)*((25759/100000 : ℝ)+(2553/100000 : ℝ))=(2001214663716157/2000000000000000 : ℝ) by norm_num, show 1+(265790935063210859/100000000000000000000 : ℝ)+(2170421854287/20000000000000000000 : ℝ)=(50132900893586241147/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(265790935063210859/100000000000000000000 : ℝ) ≤ ((116014501845109532723/116030000000000000000 : ℝ)+2*(1518205537993/580150000000000 : ℝ)*(25759/100000 : ℝ))^(4477/1024 : ℝ) := by
    rw [show (116014501845109532723/116030000000000000000 : ℝ)+2*(1518205537993/580150000000000 : ℝ)*(25759/100000 : ℝ)=(10012146140732757/10000000000000000 : ℝ) by norm_num, show 1+2*(265790935063210859/100000000000000000000 : ℝ)=(50265790935063210859/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (116014501845109532723/116030000000000000000 : ℝ)*(X 1 0+X 2 0)+(1518205537993/580150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (2553/100000 : ℝ)) (hi := (25759/100000 : ℝ)) (c := (116014501845109532723/116030000000000000000 : ℝ)) (alpha := (1518205537993/580150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (116014501845109532723/116030000000000000000 : ℝ)*(X 0 1+X 2 1)+(1518205537993/580150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (2553/100000 : ℝ)) (hi := (25759/100000 : ℝ)) (c := (116014501845109532723/116030000000000000000 : ℝ)) (alpha := (1518205537993/580150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (116014501845109532723/116030000000000000000 : ℝ)*(X 0 2+X 1 2)+(1518205537993/580150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (2553/100000 : ℝ)) (hi := (25759/100000 : ℝ)) (c := (116014501845109532723/116030000000000000000 : ℝ)) (alpha := (1518205537993/580150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-933862753/5000000000 : ℝ)*X 0 0+(44679059/80000000 : ℝ)*X 0 1+(5088180201/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((673812149/1250000000 : ℝ)*X 1 0+(-2129979197/10000000000 : ℝ)*X 1 1+(5088179117/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1347624109/2500000000 : ℝ)*X 2 0+(5088179683/10000000000 : ℝ)*X 2 1+(-106498973/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4257264909/10000000000 : ℝ)*X 0 0+(373348753/1000000000 : ℝ)*X 0 1+(4843156609/10000000000 : ℝ)*X 0 2+(4257264909/10000000000 : ℝ)*X 1 0+(373348753/1000000000 : ℝ)*X 1 1+(4843156609/10000000000 : ℝ)*X 1 2+(4257264909/10000000000 : ℝ)*X 2 0+(373348753/1000000000 : ℝ)*X 2 1+(4843156609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-233508791/1250000000 : ℝ)*X 0 0+(636737709/1250000000 : ℝ)*X 0 1+(1785301/3200000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5260008941/10000000000 : ℝ)*X 1 0+(-1639092761/10000000000 : ℝ)*X 1 1+(1115813141/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2630004449/5000000000 : ℝ)*X 2 0+(55790657/100000000 : ℝ)*X 2 1+(-409773207/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4258034559/10000000000 : ℝ)*X 0 0+(966074817/2000000000 : ℝ)*X 0 1+(187324131/500000000 : ℝ)*X 0 2+(4258034559/10000000000 : ℝ)*X 1 0+(966074817/2000000000 : ℝ)*X 1 1+(187324131/500000000 : ℝ)*X 1 2+(4258034559/10000000000 : ℝ)*X 2 0+(966074817/2000000000 : ℝ)*X 2 1+(187324131/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27386584829858012160642606561/2900750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93418211/50000000000000 : ℝ)*(base1) + (1634765491/100000000000000 : ℝ)*(base19) + (1352408067/100000000000000 : ℝ)*(base23) + (53413251/20000000000000 : ℝ)*(upper3) + (81417113/100000000000000 : ℝ)*(upper5) + (1457233632535831/100000000000000 : ℝ)*(major0) + (1457233632535831/100000000000000 : ℝ)*(major1) + (1457233632535831/100000000000000 : ℝ)*(major2) + (2013286555753799/100000000000000 : ℝ)*(sp0) + (1006644634354513/50000000000000 : ℝ)*(sp1) + (40265791021329/2000000000000 : ℝ)*(sp2) + (225293086051639/25000000000000 : ℝ)*(sp3) + (226727857/5000000000000 : ℝ)*(sp4) + (3515847219/100000000000000 : ℝ)*(sp7) + (225294011722549/25000000000000 : ℝ)*(f.failure) + (2013290903474517/100000000000000 : ℝ)*(f.sum) + (118342676967799/58015000000000000000000000000 : ℝ)*base66 + (20651435099598902187/11603000000000000000000000000000000 : ℝ)*base68 + (38329961563152097813/11603000000000000000000000000000000 : ℝ)*base69 + (35065674094750097813/11603000000000000000000000000000000 : ℝ)*base71 + (231569888892229/58015000000000000000000000000 : ℝ)*base74 + (31739875932523097813/11603000000000000000000000000000000 : ℝ)*base75 + (28032896130326097813/11603000000000000000000000000000000 : ℝ)*base77 + (5188392004466097813/11603000000000000000000000000000000 : ℝ)*base79 + (3284716350803/29007500000000000000000000000 : ℝ)*base81 + (21818697/2500000000000000000000 : ℝ)*base90 + (21818697/2500000000000000000000 : ℝ)*base92 + (21818697/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (233009345350751925154457247/116030000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (414062831/100000000000000 : ℝ)*(base19) + (412214929/100000000000000 : ℝ)*(base23) + (69865701/100000000000000 : ℝ)*(upper3) + (207961/5000000000000 : ℝ)*(lower4) + (10403967/100000000000000 : ℝ)*(upper5) + (29837599584537/2000000000000 : ℝ)*(major0) + (29837599584537/2000000000000 : ℝ)*(major1) + (29837599584537/2000000000000 : ℝ)*(major2) + (660427599/25000000000000 : ℝ)*(sp1) + (146385537/5000000000000 : ℝ)*(sp2) + (1030579001249467/50000000000000 : ℝ)*(sp4) + (2061154946725707/100000000000000 : ℝ)*(sp5) + (128822166410829/6250000000000 : ℝ)*(sp6) + (461300944507683/50000000000000 : ℝ)*(sp7) + (461300944507683/50000000000000 : ℝ)*(f.failure) + (1030579001249467/50000000000000 : ℝ)*(f.sum) + (14012589833947/5801500000000000000000000000 : ℝ)*base65 + (171915719533024251/232060000000000000000000000000000 : ℝ)*base67 + (689740444545695749/232060000000000000000000000000000 : ℝ)*base70 + (368776822763724251/232060000000000000000000000000000 : ℝ)*base71 + (2899690891993/11603000000000000000000000000 : ℝ)*base74 + (57617130590715749/232060000000000000000000000000000 : ℝ)*base76 + (1154051295304144251/232060000000000000000000000000000 : ℝ)*base77 + (1144822031474704251/232060000000000000000000000000000 : ℝ)*base79 + (13619733610941/2900750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (9851601/5000000000000000000000 : ℝ)*base89 + (9851601/5000000000000000000000 : ℝ)*base91 + (9851601/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1491_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2553/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1613/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18567/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1491_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1491_s2_0 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1894766673/10000000000 : ℝ)*x 0 + (1092991429/2000000000 : ℝ)*x 1 + (1038125719/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1894766673/10000000000 : ℝ)^4479 ≤ (462909627739/4000000000000 : ℝ)^3455 := by
    have hnat : (1894766673 : ℕ)^4479*4000000000000^3455 ≤ 462909627739^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1894766673 10000000000 462909627739 4000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092991429/2000000000 : ℝ)^4479 ≤ (45689056053407/100000000000000 : ℝ)^3455 := by
    have hnat : (1092991429 : ℕ)^4479*100000000000000^3455 ≤ 45689056053407^3455*2000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092991429 2000000000 45689056053407 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038125719/2000000000 : ℝ)^4479 ≤ (2136910161681/5000000000000 : ℝ)^3455 := by
    have hnat : (1038125719 : ℕ)^4479*5000000000000^3455 ≤ 2136910161681^3455*2000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038125719 2000000000 2136910161681 5000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1894766673/10000000000 : ℝ), (1092991429/2000000000 : ℝ), (1038125719/2000000000 : ℝ)] ![(462909627739/4000000000000 : ℝ), (45689056053407/100000000000000 : ℝ), (2136910161681/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1894766673/10000000000 : ℝ)|^4479 ≤ (462909627739/4000000000000 : ℝ)^3455
        have hw : |(-1894766673/10000000000 : ℝ)|=(1894766673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1092991429/2000000000 : ℝ)|^4479 ≤ (45689056053407/100000000000000 : ℝ)^3455
        have hw : |(1092991429/2000000000 : ℝ)|=(1092991429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1038125719/2000000000 : ℝ)|^4479 ≤ (2136910161681/5000000000000 : ℝ)^3455
        have hw : |(1038125719/2000000000 : ℝ)|=(1038125719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s2_1 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8375361/15625000 : ℝ)*x 0 + (-2036171633/10000000000 : ℝ)*x 1 + (1297657059/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8375361/15625000 : ℝ)^4479 ≤ (44557248177959/100000000000000 : ℝ)^3455 := by
    have hnat : (8375361 : ℕ)^4479*100000000000000^3455 ≤ 44557248177959^3455*15625000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8375361 15625000 44557248177959 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2036171633/10000000000 : ℝ)^4479 ≤ (2540910481869/20000000000000 : ℝ)^3455 := by
    have hnat : (2036171633 : ℕ)^4479*20000000000000^3455 ≤ 2540910481869^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036171633 10000000000 2540910481869 20000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1297657059/2500000000 : ℝ)^4479 ≤ (8547639880327/20000000000000 : ℝ)^3455 := by
    have hnat : (1297657059 : ℕ)^4479*20000000000000^3455 ≤ 8547639880327^3455*2500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297657059 2500000000 8547639880327 20000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8375361/15625000 : ℝ), (-2036171633/10000000000 : ℝ), (1297657059/2500000000 : ℝ)] ![(44557248177959/100000000000000 : ℝ), (2540910481869/20000000000000 : ℝ), (8547639880327/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8375361/15625000 : ℝ)|^4479 ≤ (44557248177959/100000000000000 : ℝ)^3455
        have hw : |(8375361/15625000 : ℝ)|=(8375361/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2036171633/10000000000 : ℝ)|^4479 ≤ (2540910481869/20000000000000 : ℝ)^3455
        have hw : |(-2036171633/10000000000 : ℝ)|=(2036171633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1297657059/2500000000 : ℝ)|^4479 ≤ (8547639880327/20000000000000 : ℝ)^3455
        have hw : |(1297657059/2500000000 : ℝ)|=(1297657059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s2_2 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5360231131/10000000000 : ℝ)*x 0 + (5190627919/10000000000 : ℝ)*x 1 + (-203617193/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360231131/10000000000 : ℝ)^4479 ≤ (22278624579299/50000000000000 : ℝ)^3455 := by
    have hnat : (5360231131 : ℕ)^4479*50000000000000^3455 ≤ 22278624579299^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360231131 10000000000 22278624579299 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5190627919/10000000000 : ℝ)^4479 ≤ (42738196017961/100000000000000 : ℝ)^3455 := by
    have hnat : (5190627919 : ℕ)^4479*100000000000000^3455 ≤ 42738196017961^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190627919 10000000000 42738196017961 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (203617193/1000000000 : ℝ)^4479 ≤ (2540910962337/20000000000000 : ℝ)^3455 := by
    have hnat : (203617193 : ℕ)^4479*20000000000000^3455 ≤ 2540910962337^3455*1000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203617193 1000000000 2540910962337 20000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360231131/10000000000 : ℝ), (5190627919/10000000000 : ℝ), (-203617193/1000000000 : ℝ)] ![(22278624579299/50000000000000 : ℝ), (42738196017961/100000000000000 : ℝ), (2540910962337/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360231131/10000000000 : ℝ)|^4479 ≤ (22278624579299/50000000000000 : ℝ)^3455
        have hw : |(5360231131/10000000000 : ℝ)|=(5360231131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5190627919/10000000000 : ℝ)|^4479 ≤ (42738196017961/100000000000000 : ℝ)^3455
        have hw : |(5190627919/10000000000 : ℝ)|=(5190627919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-203617193/1000000000 : ℝ)|^4479 ≤ (2540910962337/20000000000000 : ℝ)^3455
        have hw : |(-203617193/1000000000 : ℝ)|=(203617193/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s2_3 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2138300463/5000000000 : ℝ)*x 0 + (3979641341/10000000000 : ℝ)*x 1 + (2296255631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138300463/5000000000 : ℝ)^4479 ≤ (33247807231517/100000000000000 : ℝ)^3455 := by
    have hnat : (2138300463 : ℕ)^4479*100000000000000^3455 ≤ 33247807231517^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138300463 5000000000 33247807231517 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3979641341/10000000000 : ℝ)^4479 ≤ (30286204917871/100000000000000 : ℝ)^3455 := by
    have hnat : (3979641341 : ℕ)^4479*100000000000000^3455 ≤ 30286204917871^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979641341 10000000000 30286204917871 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2296255631/5000000000 : ℝ)^4479 ≤ (18232993913339/50000000000000 : ℝ)^3455 := by
    have hnat : (2296255631 : ℕ)^4479*50000000000000^3455 ≤ 18232993913339^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296255631 5000000000 18232993913339 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2138300463/5000000000 : ℝ), (3979641341/10000000000 : ℝ), (2296255631/5000000000 : ℝ)] ![(33247807231517/100000000000000 : ℝ), (30286204917871/100000000000000 : ℝ), (18232993913339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2138300463/5000000000 : ℝ)|^4479 ≤ (33247807231517/100000000000000 : ℝ)^3455
        have hw : |(2138300463/5000000000 : ℝ)|=(2138300463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3979641341/10000000000 : ℝ)|^4479 ≤ (30286204917871/100000000000000 : ℝ)^3455
        have hw : |(3979641341/10000000000 : ℝ)|=(3979641341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2296255631/5000000000 : ℝ)|^4479 ≤ (18232993913339/50000000000000 : ℝ)^3455
        have hw : |(2296255631/5000000000 : ℝ)|=(2296255631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s2_4 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-189482331/1000000000 : ℝ)*x 0 + (51923849/100000000 : ℝ)*x 1 + (5463185897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (189482331/1000000000 : ℝ)^4479 ≤ (289329728629/2500000000000 : ℝ)^3455 := by
    have hnat : (189482331 : ℕ)^4479*2500000000000^3455 ≤ 289329728629^3455*1000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189482331 1000000000 289329728629 2500000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51923849/100000000 : ℝ)^4479 ≤ (21378475532259/50000000000000 : ℝ)^3455 := by
    have hnat : (51923849 : ℕ)^4479*50000000000000^3455 ≤ 21378475532259^3455*100000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51923849 100000000 21378475532259 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5463185897/10000000000 : ℝ)^4479 ≤ (45669859779103/100000000000000 : ℝ)^3455 := by
    have hnat : (5463185897 : ℕ)^4479*100000000000000^3455 ≤ 45669859779103^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463185897 10000000000 45669859779103 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-189482331/1000000000 : ℝ), (51923849/100000000 : ℝ), (5463185897/10000000000 : ℝ)] ![(289329728629/2500000000000 : ℝ), (21378475532259/50000000000000 : ℝ), (45669859779103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-189482331/1000000000 : ℝ)|^4479 ≤ (289329728629/2500000000000 : ℝ)^3455
        have hw : |(-189482331/1000000000 : ℝ)|=(189482331/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(51923849/100000000 : ℝ)|^4479 ≤ (21378475532259/50000000000000 : ℝ)^3455
        have hw : |(51923849/100000000 : ℝ)|=(51923849/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5463185897/10000000000 : ℝ)|^4479 ≤ (45669859779103/100000000000000 : ℝ)^3455
        have hw : |(5463185897/10000000000 : ℝ)|=(5463185897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s2_5 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644213721/5000000000 : ℝ)*x 0 + (-1763613917/10000000000 : ℝ)*x 1 + (1365796861/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644213721/5000000000 : ℝ)^4479 ≤ (43785015170483/100000000000000 : ℝ)^3455 := by
    have hnat : (2644213721 : ℕ)^4479*100000000000000^3455 ≤ 43785015170483^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644213721 5000000000 43785015170483 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1763613917/10000000000 : ℝ)^4479 ≤ (10545108268493/100000000000000 : ℝ)^3455 := by
    have hnat : (1763613917 : ℕ)^4479*100000000000000^3455 ≤ 10545108268493^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1763613917 10000000000 10545108268493 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365796861/2500000000 : ℝ)^4479 ≤ (22834938272119/50000000000000 : ℝ)^3455 := by
    have hnat : (1365796861 : ℕ)^4479*50000000000000^3455 ≤ 22834938272119^3455*2500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365796861 2500000000 22834938272119 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644213721/5000000000 : ℝ), (-1763613917/10000000000 : ℝ), (1365796861/2500000000 : ℝ)] ![(43785015170483/100000000000000 : ℝ), (10545108268493/100000000000000 : ℝ), (22834938272119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644213721/5000000000 : ℝ)|^4479 ≤ (43785015170483/100000000000000 : ℝ)^3455
        have hw : |(2644213721/5000000000 : ℝ)|=(2644213721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1763613917/10000000000 : ℝ)|^4479 ≤ (10545108268493/100000000000000 : ℝ)^3455
        have hw : |(-1763613917/10000000000 : ℝ)|=(1763613917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365796861/2500000000 : ℝ)|^4479 ≤ (22834938272119/50000000000000 : ℝ)^3455
        have hw : |(1365796861/2500000000 : ℝ)|=(1365796861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s2_6 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644214333/5000000000 : ℝ)*x 0 + (2731592601/5000000000 : ℝ)*x 1 + (-1763615357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644214333/5000000000 : ℝ)^4479 ≤ (10946257077001/25000000000000 : ℝ)^3455 := by
    have hnat : (2644214333 : ℕ)^4479*25000000000000^3455 ≤ 10946257077001^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644214333 5000000000 10946257077001 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2731592601/5000000000 : ℝ)^4479 ≤ (5708731530907/12500000000000 : ℝ)^3455 := by
    have hnat : (2731592601 : ℕ)^4479*12500000000000^3455 ≤ 5708731530907^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731592601 5000000000 5708731530907 12500000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1763615357/10000000000 : ℝ)^4479 ≤ (263627985763/2500000000000 : ℝ)^3455 := by
    have hnat : (1763615357 : ℕ)^4479*2500000000000^3455 ≤ 263627985763^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1763615357 10000000000 263627985763 2500000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644214333/5000000000 : ℝ), (2731592601/5000000000 : ℝ), (-1763615357/10000000000 : ℝ)] ![(10946257077001/25000000000000 : ℝ), (5708731530907/12500000000000 : ℝ), (263627985763/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644214333/5000000000 : ℝ)|^4479 ≤ (10946257077001/25000000000000 : ℝ)^3455
        have hw : |(2644214333/5000000000 : ℝ)|=(2644214333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2731592601/5000000000 : ℝ)|^4479 ≤ (5708731530907/12500000000000 : ℝ)^3455
        have hw : |(2731592601/5000000000 : ℝ)|=(2731592601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1763615357/10000000000 : ℝ)|^4479 ≤ (263627985763/2500000000000 : ℝ)^3455
        have hw : |(-1763615357/10000000000 : ℝ)|=(1763615357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s2_7 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534591639/1250000000 : ℝ)*x 0 + (2294296303/5000000000 : ℝ)*x 1 + (3983593801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534591639/1250000000 : ℝ)^4479 ≤ (33249139478493/100000000000000 : ℝ)^3455 := by
    have hnat : (534591639 : ℕ)^4479*100000000000000^3455 ≤ 33249139478493^3455*1250000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534591639 1250000000 33249139478493 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2294296303/5000000000 : ℝ)^4479 ≤ (9106413882011/25000000000000 : ℝ)^3455 := by
    have hnat : (2294296303 : ℕ)^4479*25000000000000^3455 ≤ 9106413882011^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2294296303 5000000000 9106413882011 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3983593801/10000000000 : ℝ)^4479 ≤ (30325204981567/100000000000000 : ℝ)^3455 := by
    have hnat : (3983593801 : ℕ)^4479*100000000000000^3455 ≤ 30325204981567^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3983593801 10000000000 30325204981567 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534591639/1250000000 : ℝ), (2294296303/5000000000 : ℝ), (3983593801/10000000000 : ℝ)] ![(33249139478493/100000000000000 : ℝ), (9106413882011/25000000000000 : ℝ), (30325204981567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534591639/1250000000 : ℝ)|^4479 ≤ (33249139478493/100000000000000 : ℝ)^3455
        have hw : |(534591639/1250000000 : ℝ)|=(534591639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2294296303/5000000000 : ℝ)|^4479 ≤ (9106413882011/25000000000000 : ℝ)^3455
        have hw : |(2294296303/5000000000 : ℝ)|=(2294296303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3983593801/10000000000 : ℝ)|^4479 ≤ (30325204981567/100000000000000 : ℝ)^3455
        have hw : |(3983593801/10000000000 : ℝ)|=(3983593801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1491_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18567/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1613/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5139/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8041/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18567/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1613/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18567/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1613/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18567/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1613/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18567/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1613/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18567/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1613/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18567/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1613/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1613/20000 : ℝ) ^ (4477/1024 : ℝ) ≤ (103628079865531/6250000000000000000 : ℝ) := by
    have hpowers : (1613/20000 : ℝ)^4477 ≤ (103628079865531/6250000000000000000 : ℝ)^1024 := by
      have hnat : (1613 : ℕ)^4477*6250000000000000000^1024 ≤ 103628079865531^1024*20000^4477 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1613 20000 103628079865531 6250000000000000000 4477 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1613/20000 : ℝ)) (X := (103628079865531/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18567/100000 : ℝ) ^ (4477/1024 : ℝ) ≤ (31758315854861759/50000000000000000000 : ℝ) := by
    have hpowers : (18567/100000 : ℝ)^4477 ≤ (31758315854861759/50000000000000000000 : ℝ)^1024 := by
      have hnat : (18567 : ℕ)^4477*50000000000000000000^1024 ≤ 31758315854861759^1024*100000^4477 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18567 100000 31758315854861759 50000000000000000000 4477 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18567/100000 : ℝ)) (X := (31758315854861759/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125103628079865531/3125000000000000000 : ℝ) ≤ (1250009480794889/1250000000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (3125103628079865531/3125000000000000000 : ℝ)^1024 ≤ (1250009480794889/1250000000000000 : ℝ)^4477 := by
      have hnat : (3125103628079865531 : ℕ)^1024*1250000000000000^4477 ≤ 1250009480794889^4477*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125103628079865531 3125000000000000000 1250009480794889 1250000000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250009480794889/1250000000000000 : ℝ)) (X := (3125103628079865531/3125000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50032587340493786007/50000000000000000000 : ℝ) ≤ (500074516535357/500000000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (50032587340493786007/50000000000000000000 : ℝ)^1024 ≤ (500074516535357/500000000000000 : ℝ)^4477 := by
      have hnat : (50032587340493786007 : ℕ)^1024*500000000000000^4477 ≤ 500074516535357^4477*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032587340493786007 50000000000000000000 500074516535357 500000000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500074516535357/500000000000000 : ℝ)) (X := (50032587340493786007/50000000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25031758315854861759/25000000000000000000 : ℝ) ≤ (156295387735237/156250000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (25031758315854861759/25000000000000000000 : ℝ)^1024 ≤ (156295387735237/156250000000000 : ℝ)^4477 := by
      have hnat : (25031758315854861759 : ℕ)^1024*156250000000000^4477 ≤ 156295387735237^4477*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25031758315854861759 25000000000000000000 156295387735237 156250000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156295387735237/156250000000000 : ℝ)) (X := (25031758315854861759/25000000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(103628079865531/6250000000000000000 : ℝ) ≤ ((13124747613241212823/13127500000000000000 : ℝ)+2*(353621087007/262550000000000 : ℝ)*(1613/20000 : ℝ))^(4477/1024 : ℝ) := by
    rw [show (13124747613241212823/13127500000000000000 : ℝ)+2*(353621087007/262550000000000 : ℝ)*(1613/20000 : ℝ)=(1250009480794889/1250000000000000 : ℝ) by norm_num, show 1+2*(103628079865531/6250000000000000000 : ℝ)=(3125103628079865531/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31758315854861759/50000000000000000000 : ℝ)+(103628079865531/6250000000000000000 : ℝ) ≤ ((13124747613241212823/13127500000000000000 : ℝ)+(353621087007/262550000000000 : ℝ)*((18567/100000 : ℝ)+(1613/20000 : ℝ)))^(4477/1024 : ℝ) := by
    rw [show (13124747613241212823/13127500000000000000 : ℝ)+(353621087007/262550000000000 : ℝ)*((18567/100000 : ℝ)+(1613/20000 : ℝ))=(500074516535357/500000000000000 : ℝ) by norm_num, show 1+(31758315854861759/50000000000000000000 : ℝ)+(103628079865531/6250000000000000000 : ℝ)=(50032587340493786007/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31758315854861759/50000000000000000000 : ℝ) ≤ ((13124747613241212823/13127500000000000000 : ℝ)+2*(353621087007/262550000000000 : ℝ)*(18567/100000 : ℝ))^(4477/1024 : ℝ) := by
    rw [show (13124747613241212823/13127500000000000000 : ℝ)+2*(353621087007/262550000000000 : ℝ)*(18567/100000 : ℝ)=(156295387735237/156250000000000 : ℝ) by norm_num, show 1+2*(31758315854861759/50000000000000000000 : ℝ)=(25031758315854861759/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13124747613241212823/13127500000000000000 : ℝ)*(X 1 0+X 2 0)+(353621087007/262550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (1613/20000 : ℝ)) (hi := (18567/100000 : ℝ)) (c := (13124747613241212823/13127500000000000000 : ℝ)) (alpha := (353621087007/262550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13124747613241212823/13127500000000000000 : ℝ)*(X 0 1+X 2 1)+(353621087007/262550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (1613/20000 : ℝ)) (hi := (18567/100000 : ℝ)) (c := (13124747613241212823/13127500000000000000 : ℝ)) (alpha := (353621087007/262550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13124747613241212823/13127500000000000000 : ℝ)*(X 0 2+X 1 2)+(353621087007/262550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (1613/20000 : ℝ)) (hi := (18567/100000 : ℝ)) (c := (13124747613241212823/13127500000000000000 : ℝ)) (alpha := (353621087007/262550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1894766673/10000000000 : ℝ)*X 0 0+(1092991429/2000000000 : ℝ)*X 0 1+(1038125719/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((8375361/15625000 : ℝ)*X 1 0+(-2036171633/10000000000 : ℝ)*X 1 1+(1297657059/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5360231131/10000000000 : ℝ)*X 2 0+(5190627919/10000000000 : ℝ)*X 2 1+(-203617193/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2138300463/5000000000 : ℝ)*X 0 0+(3979641341/10000000000 : ℝ)*X 0 1+(2296255631/5000000000 : ℝ)*X 0 2+(2138300463/5000000000 : ℝ)*X 1 0+(3979641341/10000000000 : ℝ)*X 1 1+(2296255631/5000000000 : ℝ)*X 1 2+(2138300463/5000000000 : ℝ)*X 2 0+(3979641341/10000000000 : ℝ)*X 2 1+(2296255631/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-189482331/1000000000 : ℝ)*X 0 0+(51923849/100000000 : ℝ)*X 0 1+(5463185897/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644213721/5000000000 : ℝ)*X 1 0+(-1763613917/10000000000 : ℝ)*X 1 1+(1365796861/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644214333/5000000000 : ℝ)*X 2 0+(2731592601/5000000000 : ℝ)*X 2 1+(-1763615357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((534591639/1250000000 : ℝ)*X 0 0+(2294296303/5000000000 : ℝ)*X 0 1+(3983593801/10000000000 : ℝ)*X 0 2+(534591639/1250000000 : ℝ)*X 1 0+(2294296303/5000000000 : ℝ)*X 1 1+(3983593801/10000000000 : ℝ)*X 1 2+(534591639/1250000000 : ℝ)*X 2 0+(2294296303/5000000000 : ℝ)*X 2 1+(3983593801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3952792135641107750079/13127500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1073076339/100000000000000 : ℝ)*(base19) + (1267618623/100000000000000 : ℝ)*(base23) + (117223983/100000000000000 : ℝ)*(upper2) + (127525951/100000000000000 : ℝ)*(upper3) + (46116921/100000000000000 : ℝ)*(upper4) + (1319241428441423/50000000000000 : ℝ)*(major0) + (1319241428441423/50000000000000 : ℝ)*(major1) + (1319241428441423/50000000000000 : ℝ)*(major2) + (1822638612770629/50000000000000 : ℝ)*(sp0) + (3645285607011187/100000000000000 : ℝ)*(sp1) + (1822642706234451/50000000000000 : ℝ)*(sp2) + (1631672797151121/100000000000000 : ℝ)*(sp3) + (2363636567/25000000000000 : ℝ)*(sp4) + (3113245057/50000000000000 : ℝ)*(sp7) + (326335804728247/20000000000000 : ℝ)*(f.failure) + (1822643340043763/50000000000000 : ℝ)*(f.sum) + (93163095573/205117187500000000000000000 : ℝ)*base65 + (1699860435283107871/656375000000000000000000000000000 : ℝ)*base68 + (3511344486247732871/656375000000000000000000000000000 : ℝ)*base70 + (1152151072830767129/656375000000000000000000000000000 : ℝ)*base71 + (12324800793237/13127500000000000000000000000 : ℝ)*base73 + (105691093463482871/656375000000000000000000000000000 : ℝ)*base76 + (2540289888558017129/656375000000000000000000000000000 : ℝ)*base77 + (4387011251550892129/656375000000000000000000000000000 : ℝ)*base79 + (6340259464617/3281875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (9007891/2000000000000000000000 : ℝ)*base90 + (9007891/2000000000000000000000 : ℝ)*base92 + (9007891/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2041735945348108699041457227/164093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2570391423/100000000000000 : ℝ)*(base23) + (382679/6250000000000 : ℝ)*(lower2) + (451833507/100000000000000 : ℝ)*(upper3) + (419817701/50000000000000 : ℝ)*(lower4) + (668205692851033/25000000000000 : ℝ)*(major0) + (668205692851033/25000000000000 : ℝ)*(major1) + (668205692851033/25000000000000 : ℝ)*(major2) + (2190932929/50000000000000 : ℝ)*(sp1) + (3666095521/25000000000000 : ℝ)*(sp2) + (1117541837/12500000000000 : ℝ)*(sp3) + (1846364882366783/50000000000000 : ℝ)*(sp4) + (923181345716927/25000000000000 : ℝ)*(sp5) + (3692712529960059/100000000000000 : ℝ)*(sp6) + (16529064229901/1000000000000 : ℝ)*(sp7) + (413228840831199/25000000000000 : ℝ)*(f.failure) + (1846364882366783/50000000000000 : ℝ)*(f.sum) + (29990035262583/6563750000000000000000000000 : ℝ)*base66 + (1509134181958553841/328187500000000000000000000000000 : ℝ)*base68 + (5867567173103428841/328187500000000000000000000000000 : ℝ)*base70 + (4578433479309553841/328187500000000000000000000000000 : ℝ)*base72 + (478980572709/13127500000000000000000000000 : ℝ)*base73 + (2002866006268303841/328187500000000000000000000000000 : ℝ)*base76 + (3765591589219071159/328187500000000000000000000000000 : ℝ)*base77 + (16392805827715571159/328187500000000000000000000000000 : ℝ)*base79 + (99047824376747/26255000000000000000000000000 : ℝ)*base82 + (6562853/2500000000000000000000 : ℝ)*base89 + (6562853/2500000000000000000000 : ℝ)*base91 + (6562853/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1491_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18567/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1613/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5139/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8041/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1491_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1491_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5139/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8041/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1491_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1491_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1491_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5139/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8041/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1491_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

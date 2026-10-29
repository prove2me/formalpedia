-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1446_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:58:14.700405+00:00
-- url     : https://prove2.me/submissions/88767fcb-d6fa-4b66-8648-ba20f3e7b071

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
theorem support_rectangle_w1446_s6_0 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-3914841/20000000 : ℝ)*x 0 + (540734507/1000000000 : ℝ)*x 1 + (5247271151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3914841/20000000 : ℝ)^2203 ≤ (5972974611927/50000000000000 : ℝ)^1691 := by
    have hnat : (3914841 : ℕ)^2203*50000000000000^1691 ≤ 5972974611927^1691*20000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3914841 20000000 5972974611927 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540734507/1000000000 : ℝ)^2203 ≤ (22444356862661/50000000000000 : ℝ)^1691 := by
    have hnat : (540734507 : ℕ)^2203*50000000000000^1691 ≤ 22444356862661^1691*1000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540734507 1000000000 22444356862661 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247271151/10000000000 : ℝ)^2203 ≤ (21582668520901/50000000000000 : ℝ)^1691 := by
    have hnat : (5247271151 : ℕ)^2203*50000000000000^1691 ≤ 21582668520901^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247271151 10000000000 21582668520901 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3914841/20000000 : ℝ), (540734507/1000000000 : ℝ), (5247271151/10000000000 : ℝ)] ![(5972974611927/50000000000000 : ℝ), (22444356862661/50000000000000 : ℝ), (21582668520901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3914841/20000000 : ℝ)|^2203 ≤ (5972974611927/50000000000000 : ℝ)^1691
        have hw : |(-3914841/20000000 : ℝ)|=(3914841/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540734507/1000000000 : ℝ)|^2203 ≤ (22444356862661/50000000000000 : ℝ)^1691
        have hw : |(540734507/1000000000 : ℝ)|=(540734507/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247271151/10000000000 : ℝ)|^2203 ≤ (21582668520901/50000000000000 : ℝ)^1691
        have hw : |(5247271151/10000000000 : ℝ)|=(5247271151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s6_1 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5346963463/10000000000 : ℝ)*x 0 + (-1019452961/5000000000 : ℝ)*x 1 + (5247271433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346963463/10000000000 : ℝ)^2203 ≤ (1382399915973/3125000000000 : ℝ)^1691 := by
    have hnat : (5346963463 : ℕ)^2203*3125000000000^1691 ≤ 1382399915973^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346963463 10000000000 1382399915973 3125000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1019452961/5000000000 : ℝ)^2203 ≤ (12597862614989/100000000000000 : ℝ)^1691 := by
    have hnat : (1019452961 : ℕ)^2203*100000000000000^1691 ≤ 12597862614989^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019452961 5000000000 12597862614989 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247271433/10000000000 : ℝ)^2203 ≤ (43165340063991/100000000000000 : ℝ)^1691 := by
    have hnat : (5247271433 : ℕ)^2203*100000000000000^1691 ≤ 43165340063991^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247271433 10000000000 43165340063991 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346963463/10000000000 : ℝ), (-1019452961/5000000000 : ℝ), (5247271433/10000000000 : ℝ)] ![(1382399915973/3125000000000 : ℝ), (12597862614989/100000000000000 : ℝ), (43165340063991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346963463/10000000000 : ℝ)|^2203 ≤ (1382399915973/3125000000000 : ℝ)^1691
        have hw : |(5346963463/10000000000 : ℝ)|=(5346963463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1019452961/5000000000 : ℝ)|^2203 ≤ (12597862614989/100000000000000 : ℝ)^1691
        have hw : |(-1019452961/5000000000 : ℝ)|=(1019452961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247271433/10000000000 : ℝ)|^2203 ≤ (43165340063991/100000000000000 : ℝ)^1691
        have hw : |(5247271433/10000000000 : ℝ)|=(5247271433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s6_2 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5346965463/10000000000 : ℝ)*x 0 + (209890823/400000000 : ℝ)*x 1 + (-1019452193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346965463/10000000000 : ℝ)^2203 ≤ (44236818867593/100000000000000 : ℝ)^1691 := by
    have hnat : (5346965463 : ℕ)^2203*100000000000000^1691 ≤ 44236818867593^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346965463 10000000000 44236818867593 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209890823/400000000 : ℝ)^2203 ≤ (2158266543441/5000000000000 : ℝ)^1691 := by
    have hnat : (209890823 : ℕ)^2203*5000000000000^1691 ≤ 2158266543441^1691*400000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209890823 400000000 2158266543441 5000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1019452193/5000000000 : ℝ)^2203 ≤ (12597850250911/100000000000000 : ℝ)^1691 := by
    have hnat : (1019452193 : ℕ)^2203*100000000000000^1691 ≤ 12597850250911^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019452193 5000000000 12597850250911 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346965463/10000000000 : ℝ), (209890823/400000000 : ℝ), (-1019452193/5000000000 : ℝ)] ![(44236818867593/100000000000000 : ℝ), (2158266543441/5000000000000 : ℝ), (12597850250911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346965463/10000000000 : ℝ)|^2203 ≤ (44236818867593/100000000000000 : ℝ)^1691
        have hw : |(5346965463/10000000000 : ℝ)|=(5346965463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209890823/400000000 : ℝ)|^2203 ≤ (2158266543441/5000000000000 : ℝ)^1691
        have hw : |(209890823/400000000 : ℝ)|=(209890823/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1019452193/5000000000 : ℝ)|^2203 ≤ (12597850250911/100000000000000 : ℝ)^1691
        have hw : |(-1019452193/5000000000 : ℝ)|=(1019452193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s6_3 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1075035411/2500000000 : ℝ)*x 0 + (4129063771/10000000000 : ℝ)*x 1 + (559689863/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075035411/2500000000 : ℝ)^2203 ≤ (266439660159/800000000000 : ℝ)^1691 := by
    have hnat : (1075035411 : ℕ)^2203*800000000000^1691 ≤ 266439660159^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075035411 2500000000 266439660159 800000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4129063771/10000000000 : ℝ)^2203 ≤ (15794626549729/50000000000000 : ℝ)^1691 := by
    have hnat : (4129063771 : ℕ)^2203*50000000000000^1691 ≤ 15794626549729^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129063771 10000000000 15794626549729 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559689863/1250000000 : ℝ)^2203 ≤ (140423157491/400000000000 : ℝ)^1691 := by
    have hnat : (559689863 : ℕ)^2203*400000000000^1691 ≤ 140423157491^1691*1250000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559689863 1250000000 140423157491 400000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075035411/2500000000 : ℝ), (4129063771/10000000000 : ℝ), (559689863/1250000000 : ℝ)] ![(266439660159/800000000000 : ℝ), (15794626549729/50000000000000 : ℝ), (140423157491/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075035411/2500000000 : ℝ)|^2203 ≤ (266439660159/800000000000 : ℝ)^1691
        have hw : |(1075035411/2500000000 : ℝ)|=(1075035411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4129063771/10000000000 : ℝ)|^2203 ≤ (15794626549729/50000000000000 : ℝ)^1691
        have hw : |(4129063771/10000000000 : ℝ)|=(4129063771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(559689863/1250000000 : ℝ)|^2203 ≤ (140423157491/400000000000 : ℝ)^1691
        have hw : |(559689863/1250000000 : ℝ)|=(559689863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s6_4 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1957430747/10000000000 : ℝ)*x 0 + (5247848859/10000000000 : ℝ)*x 1 + (2703382521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1957430747/10000000000 : ℝ)^2203 ≤ (11946030695127/100000000000000 : ℝ)^1691 := by
    have hnat : (1957430747 : ℕ)^2203*100000000000000^1691 ≤ 11946030695127^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1957430747 10000000000 11946030695127 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247848859/10000000000 : ℝ)^2203 ≤ (43171528431483/100000000000000 : ℝ)^1691 := by
    have hnat : (5247848859 : ℕ)^2203*100000000000000^1691 ≤ 43171528431483^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247848859 10000000000 43171528431483 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703382521/5000000000 : ℝ)^2203 ≤ (44882440861323/100000000000000 : ℝ)^1691 := by
    have hnat : (2703382521 : ℕ)^2203*100000000000000^1691 ≤ 44882440861323^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703382521 5000000000 44882440861323 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1957430747/10000000000 : ℝ), (5247848859/10000000000 : ℝ), (2703382521/5000000000 : ℝ)] ![(11946030695127/100000000000000 : ℝ), (43171528431483/100000000000000 : ℝ), (44882440861323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1957430747/10000000000 : ℝ)|^2203 ≤ (11946030695127/100000000000000 : ℝ)^1691
        have hw : |(-1957430747/10000000000 : ℝ)|=(1957430747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247848859/10000000000 : ℝ)|^2203 ≤ (43171528431483/100000000000000 : ℝ)^1691
        have hw : |(5247848859/10000000000 : ℝ)|=(5247848859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703382521/5000000000 : ℝ)|^2203 ≤ (44882440861323/100000000000000 : ℝ)^1691
        have hw : |(2703382521/5000000000 : ℝ)|=(2703382521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s6_5 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305281341/10000000000 : ℝ)*x 0 + (-1879410759/10000000000 : ℝ)*x 1 + (5406764897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305281341/10000000000 : ℝ)^2203 ≤ (43788069072813/100000000000000 : ℝ)^1691 := by
    have hnat : (5305281341 : ℕ)^2203*100000000000000^1691 ≤ 43788069072813^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305281341 10000000000 43788069072813 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1879410759/10000000000 : ℝ)^2203 ≤ (2265898323447/20000000000000 : ℝ)^1691 := by
    have hnat : (1879410759 : ℕ)^2203*20000000000000^1691 ≤ 2265898323447^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1879410759 10000000000 2265898323447 20000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406764897/10000000000 : ℝ)^2203 ≤ (5610304911651/12500000000000 : ℝ)^1691 := by
    have hnat : (5406764897 : ℕ)^2203*12500000000000^1691 ≤ 5610304911651^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406764897 10000000000 5610304911651 12500000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305281341/10000000000 : ℝ), (-1879410759/10000000000 : ℝ), (5406764897/10000000000 : ℝ)] ![(43788069072813/100000000000000 : ℝ), (2265898323447/20000000000000 : ℝ), (5610304911651/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305281341/10000000000 : ℝ)|^2203 ≤ (43788069072813/100000000000000 : ℝ)^1691
        have hw : |(5305281341/10000000000 : ℝ)|=(5305281341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1879410759/10000000000 : ℝ)|^2203 ≤ (2265898323447/20000000000000 : ℝ)^1691
        have hw : |(-1879410759/10000000000 : ℝ)|=(1879410759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406764897/10000000000 : ℝ)|^2203 ≤ (5610304911651/12500000000000 : ℝ)^1691
        have hw : |(5406764897/10000000000 : ℝ)|=(5406764897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s6_6 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652640857/5000000000 : ℝ)*x 0 + (1351691093/2500000000 : ℝ)*x 1 + (-469852743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652640857/5000000000 : ℝ)^2203 ≤ (43788073083577/100000000000000 : ℝ)^1691 := by
    have hnat : (2652640857 : ℕ)^2203*100000000000000^1691 ≤ 43788073083577^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652640857 5000000000 43788073083577 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351691093/2500000000 : ℝ)^2203 ≤ (44882433615551/100000000000000 : ℝ)^1691 := by
    have hnat : (1351691093 : ℕ)^2203*100000000000000^1691 ≤ 44882433615551^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351691093 2500000000 44882433615551 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (469852743/2500000000 : ℝ)^2203 ≤ (354046665313/3125000000000 : ℝ)^1691 := by
    have hnat : (469852743 : ℕ)^2203*3125000000000^1691 ≤ 354046665313^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469852743 2500000000 354046665313 3125000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652640857/5000000000 : ℝ), (1351691093/2500000000 : ℝ), (-469852743/2500000000 : ℝ)] ![(43788073083577/100000000000000 : ℝ), (44882433615551/100000000000000 : ℝ), (354046665313/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652640857/5000000000 : ℝ)|^2203 ≤ (43788073083577/100000000000000 : ℝ)^1691
        have hw : |(2652640857/5000000000 : ℝ)|=(2652640857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351691093/2500000000 : ℝ)|^2203 ≤ (44882433615551/100000000000000 : ℝ)^1691
        have hw : |(1351691093/2500000000 : ℝ)|=(1351691093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-469852743/2500000000 : ℝ)|^2203 ≤ (354046665313/3125000000000 : ℝ)^1691
        have hw : |(-469852743/2500000000 : ℝ)|=(469852743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s6_7 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4300164901/10000000000 : ℝ)*x 0 + (4476260223/10000000000 : ℝ)*x 1 + (1032582513/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300164901/10000000000 : ℝ)^2203 ≤ (8326298046589/25000000000000 : ℝ)^1691 := by
    have hnat : (4300164901 : ℕ)^2203*25000000000000^1691 ≤ 8326298046589^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300164901 10000000000 8326298046589 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4476260223/10000000000 : ℝ)^2203 ≤ (7018586653633/20000000000000 : ℝ)^1691 := by
    have hnat : (4476260223 : ℕ)^2203*20000000000000^1691 ≤ 7018586653633^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476260223 10000000000 7018586653633 20000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032582513/2500000000 : ℝ)^2203 ≤ (31601874539499/100000000000000 : ℝ)^1691 := by
    have hnat : (1032582513 : ℕ)^2203*100000000000000^1691 ≤ 31601874539499^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032582513 2500000000 31601874539499 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300164901/10000000000 : ℝ), (4476260223/10000000000 : ℝ), (1032582513/2500000000 : ℝ)] ![(8326298046589/25000000000000 : ℝ), (7018586653633/20000000000000 : ℝ), (31601874539499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300164901/10000000000 : ℝ)|^2203 ≤ (8326298046589/25000000000000 : ℝ)^1691
        have hw : |(4300164901/10000000000 : ℝ)|=(4300164901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4476260223/10000000000 : ℝ)|^2203 ≤ (7018586653633/20000000000000 : ℝ)^1691
        have hw : |(4476260223/10000000000 : ℝ)|=(4476260223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032582513/2500000000 : ℝ)|^2203 ≤ (31601874539499/100000000000000 : ℝ)^1691
        have hw : |(1032582513/2500000000 : ℝ)|=(1032582513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1446_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5687/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7383/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11371/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11371/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11371/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11371/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11371/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11371/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11371/100000 : ℝ) ^ (4405/1024 : ℝ) ≤ (2168775086694031/25000000000000000000 : ℝ) := by
    have hpowers : (11371/100000 : ℝ)^4405 ≤ (2168775086694031/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11371 : ℕ)^4405*25000000000000000000^1024 ≤ 2168775086694031^1024*100000^4405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11371 100000 2168775086694031 25000000000000000000 4405 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11371/100000 : ℝ)) (X := (2168775086694031/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14769/100000 : ℝ) ^ (4405/1024 : ℝ) ≤ (3339331829771679/12500000000000000000 : ℝ) := by
    have hpowers : (14769/100000 : ℝ)^4405 ≤ (3339331829771679/12500000000000000000 : ℝ)^1024 := by
      have hnat : (14769 : ℕ)^4405*12500000000000000000^1024 ≤ 3339331829771679^1024*100000^4405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14769 100000 3339331829771679 12500000000000000000 4405 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14769/100000 : ℝ)) (X := (3339331829771679/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502168775086694031/12500000000000000000 : ℝ) ≤ (2000080660261743/2000000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (12502168775086694031/12500000000000000000 : ℝ)^1024 ≤ (2000080660261743/2000000000000000 : ℝ)^4405 := by
      have hnat : (12502168775086694031 : ℕ)^1024*2000000000000000^4405 ≤ 2000080660261743^4405*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502168775086694031 12500000000000000000 2000080660261743 2000000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000080660261743/2000000000000000 : ℝ)) (X := (12502168775086694031/12500000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008847438746237389/25000000000000000000 : ℝ) ≤ (1000082256954203/1000000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (25008847438746237389/25000000000000000000 : ℝ)^1024 ≤ (1000082256954203/1000000000000000 : ℝ)^4405 := by
      have hnat : (25008847438746237389 : ℕ)^1024*1000000000000000^4405 ≤ 1000082256954203^4405*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008847438746237389 25000000000000000000 1000082256954203 1000000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000082256954203/1000000000000000 : ℝ)) (X := (25008847438746237389/25000000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253339331829771679/6250000000000000000 : ℝ) ≤ (2000248367555069/2000000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (6253339331829771679/6250000000000000000 : ℝ)^1024 ≤ (2000248367555069/2000000000000000 : ℝ)^4405 := by
      have hnat : (6253339331829771679 : ℕ)^1024*2000000000000000^4405 ≤ 2000248367555069^4405*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253339331829771679 6250000000000000000 2000248367555069 2000000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000248367555069/2000000000000000 : ℝ)) (X := (6253339331829771679/6250000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2168775086694031/25000000000000000000 : ℝ) ≤ ((13270248210814439/13273437500000000 : ℝ)+2*(83853646663/67960000000000 : ℝ)*(11371/100000 : ℝ))^(4405/1024 : ℝ) := by
    rw [show (13270248210814439/13273437500000000 : ℝ)+2*(83853646663/67960000000000 : ℝ)*(11371/100000 : ℝ)=(2000080660261743/2000000000000000 : ℝ) by norm_num, show 1+2*(2168775086694031/25000000000000000000 : ℝ)=(12502168775086694031/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3339331829771679/12500000000000000000 : ℝ)+(2168775086694031/25000000000000000000 : ℝ) ≤ ((13270248210814439/13273437500000000 : ℝ)+(83853646663/67960000000000 : ℝ)*((14769/100000 : ℝ)+(11371/100000 : ℝ)))^(4405/1024 : ℝ) := by
    rw [show (13270248210814439/13273437500000000 : ℝ)+(83853646663/67960000000000 : ℝ)*((14769/100000 : ℝ)+(11371/100000 : ℝ))=(1000082256954203/1000000000000000 : ℝ) by norm_num, show 1+(3339331829771679/12500000000000000000 : ℝ)+(2168775086694031/25000000000000000000 : ℝ)=(25008847438746237389/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3339331829771679/12500000000000000000 : ℝ) ≤ ((13270248210814439/13273437500000000 : ℝ)+2*(83853646663/67960000000000 : ℝ)*(14769/100000 : ℝ))^(4405/1024 : ℝ) := by
    rw [show (13270248210814439/13273437500000000 : ℝ)+2*(83853646663/67960000000000 : ℝ)*(14769/100000 : ℝ)=(2000248367555069/2000000000000000 : ℝ) by norm_num, show 1+2*(3339331829771679/12500000000000000000 : ℝ)=(6253339331829771679/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13270248210814439/13273437500000000 : ℝ)*(X 1 0+X 2 0)+(83853646663/67960000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (11371/100000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (13270248210814439/13273437500000000 : ℝ)) (alpha := (83853646663/67960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13270248210814439/13273437500000000 : ℝ)*(X 0 1+X 2 1)+(83853646663/67960000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (11371/100000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (13270248210814439/13273437500000000 : ℝ)) (alpha := (83853646663/67960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13270248210814439/13273437500000000 : ℝ)*(X 0 2+X 1 2)+(83853646663/67960000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (11371/100000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (13270248210814439/13273437500000000 : ℝ)) (alpha := (83853646663/67960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-3914841/20000000 : ℝ)*X 0 0+(540734507/1000000000 : ℝ)*X 0 1+(5247271151/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346963463/10000000000 : ℝ)*X 1 0+(-1019452961/5000000000 : ℝ)*X 1 1+(5247271433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346965463/10000000000 : ℝ)*X 2 0+(209890823/400000000 : ℝ)*X 2 1+(-1019452193/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1075035411/2500000000 : ℝ)*X 0 0+(4129063771/10000000000 : ℝ)*X 0 1+(559689863/1250000000 : ℝ)*X 0 2+(1075035411/2500000000 : ℝ)*X 1 0+(4129063771/10000000000 : ℝ)*X 1 1+(559689863/1250000000 : ℝ)*X 1 2+(1075035411/2500000000 : ℝ)*X 2 0+(4129063771/10000000000 : ℝ)*X 2 1+(559689863/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1957430747/10000000000 : ℝ)*X 0 0+(5247848859/10000000000 : ℝ)*X 0 1+(2703382521/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305281341/10000000000 : ℝ)*X 1 0+(-1879410759/10000000000 : ℝ)*X 1 1+(5406764897/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652640857/5000000000 : ℝ)*X 2 0+(1351691093/2500000000 : ℝ)*X 2 1+(-469852743/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4300164901/10000000000 : ℝ)*X 0 0+(4476260223/10000000000 : ℝ)*X 0 1+(1032582513/2500000000 : ℝ)*X 0 2+(4300164901/10000000000 : ℝ)*X 1 0+(4476260223/10000000000 : ℝ)*X 1 1+(1032582513/2500000000 : ℝ)*X 1 2+(4300164901/10000000000 : ℝ)*X 2 0+(4476260223/10000000000 : ℝ)*X 2 1+(1032582513/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36570042458748191157337479/5309375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (66436849/5000000000000 : ℝ)*(base19) + (1784561839/50000000000000 : ℝ)*(base23) + (172589449/100000000000000 : ℝ)*(upper4) + (612483711/50000000000000 : ℝ)*(upper5) + (2279270017622193/50000000000000 : ℝ)*(major0) + (2279270017622193/50000000000000 : ℝ)*(major1) + (2279270017622193/50000000000000 : ℝ)*(major2) + (3123560275241307/50000000000000 : ℝ)*(sp0) + (1249433972416363/20000000000000 : ℝ)*(sp1) + (3123598334663861/50000000000000 : ℝ)*(sp2) + (2869848554026887/100000000000000 : ℝ)*(sp3) + (15937593757/20000000000000 : ℝ)*(sp4) + (14523816303/50000000000000 : ℝ)*(sp5) + (31048416333/100000000000000 : ℝ)*(sp7) + (143493980122161/5000000000000 : ℝ)*(f.failure) + (31236001192257/500000000000 : ℝ)*(f.sum) + (11503698543/2718400000000000000000000 : ℝ)*base66 + (91232632548106257/10618750000000000000000000000000 : ℝ)*base67 + (54785032376337507/10618750000000000000000000000000 : ℝ)*base69 + (5358998501137493/10618750000000000000000000000000 : ℝ)*base72 + (1348183869689/1699000000000000000000000000 : ℝ)*base74 + (142057282675581243/10618750000000000000000000000000 : ℝ)*base76 + (77406349835081257/10618750000000000000000000000000 : ℝ)*base77 + (13090304094075007/10618750000000000000000000000000 : ℝ)*base79 + (1741851887969/1699000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (2312571/500000000000000000000 : ℝ)*base89 + (2312571/500000000000000000000 : ℝ)*base91 + (2312571/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12248966759556803143720767/1327343750000000000000000000000 : ℝ) := by norm_num
    linear_combination (2116385087/100000000000000 : ℝ)*(base19) + (2688650119/100000000000000 : ℝ)*(base23) + (63981367/10000000000000 : ℝ)*(lower1) + (60529181/100000000000000 : ℝ)*(upper3) + (116066133/100000000000000 : ℝ)*(lower4) + (179187719/50000000000000 : ℝ)*(upper5) + (1147916397659747/25000000000000 : ℝ)*(major0) + (1147916397659747/25000000000000 : ℝ)*(major1) + (1147916397659747/25000000000000 : ℝ)*(major2) + (2263665491/20000000000000 : ℝ)*(sp1) + (1573149177309817/25000000000000 : ℝ)*(sp4) + (3146291637263363/50000000000000 : ℝ)*(sp5) + (6292594020589149/100000000000000 : ℝ)*(sp6) + (2890734164432709/100000000000000 : ℝ)*(sp7) + (2890734164432709/100000000000000 : ℝ)*(f.failure) + (1573149177309817/25000000000000 : ℝ)*(f.sum) + (671613603993/339800000000000000000000000 : ℝ)*base66 + (1709160902718183/331835937500000000000000000000 : ℝ)*base67 + (20612536361805947/5309375000000000000000000000000 : ℝ)*base70 + (76790517781443447/5309375000000000000000000000000 : ℝ)*base72 + (555225138397/339800000000000000000000000 : ℝ)*base73 + (22213226339848589/2654687500000000000000000000000 : ℝ)*base75 + (15863508069067893/1327343750000000000000000000000 : ℝ)*base78 + (1845395367604259/663671875000000000000000000000 : ℝ)*base80 + (5690757004281/849500000000000000000000000 : ℝ)*base81 + (52486999/10000000000000000000000 : ℝ)*base89 + (52486999/10000000000000000000000 : ℝ)*base91 + (52486999/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1446_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1446_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1446_s7_0 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-489355837/2500000000 : ℝ)*x 0 + (1081464923/2000000000 : ℝ)*x 1 + (65591121/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (489355837/2500000000 : ℝ)^2203 ≤ (298649296689/2500000000000 : ℝ)^1691 := by
    have hnat : (489355837 : ℕ)^2203*2500000000000^1691 ≤ 298649296689^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489355837 2500000000 298649296689 2500000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081464923/2000000000 : ℝ)^2203 ≤ (44888492505927/100000000000000 : ℝ)^1691 := by
    have hnat : (1081464923 : ℕ)^2203*100000000000000^1691 ≤ 44888492505927^1691*2000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081464923 2000000000 44888492505927 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65591121/125000000 : ℝ)^2203 ≤ (69064856987/160000000000 : ℝ)^1691 := by
    have hnat : (65591121 : ℕ)^2203*160000000000^1691 ≤ 69064856987^1691*125000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65591121 125000000 69064856987 160000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-489355837/2500000000 : ℝ), (1081464923/2000000000 : ℝ), (65591121/125000000 : ℝ)] ![(298649296689/2500000000000 : ℝ), (44888492505927/100000000000000 : ℝ), (69064856987/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-489355837/2500000000 : ℝ)|^2203 ≤ (298649296689/2500000000000 : ℝ)^1691
        have hw : |(-489355837/2500000000 : ℝ)|=(489355837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081464923/2000000000 : ℝ)|^2203 ≤ (44888492505927/100000000000000 : ℝ)^1691
        have hw : |(1081464923/2000000000 : ℝ)|=(1081464923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65591121/125000000 : ℝ)|^2203 ≤ (69064856987/160000000000 : ℝ)^1691
        have hw : |(65591121/125000000 : ℝ)|=(65591121/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s7_1 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5346960727/10000000000 : ℝ)*x 0 + (-509721741/2500000000 : ℝ)*x 1 + (5247288423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346960727/10000000000 : ℝ)^2203 ≤ (11059191955477/25000000000000 : ℝ)^1691 := by
    have hnat : (5346960727 : ℕ)^2203*25000000000000^1691 ≤ 11059191955477^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346960727 10000000000 11059191955477 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (509721741/2500000000 : ℝ)^2203 ≤ (6298855006099/50000000000000 : ℝ)^1691 := by
    have hnat : (509721741 : ℕ)^2203*50000000000000^1691 ≤ 6298855006099^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509721741 2500000000 6298855006099 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247288423/10000000000 : ℝ)^2203 ≤ (8633104429123/20000000000000 : ℝ)^1691 := by
    have hnat : (5247288423 : ℕ)^2203*20000000000000^1691 ≤ 8633104429123^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247288423 10000000000 8633104429123 20000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346960727/10000000000 : ℝ), (-509721741/2500000000 : ℝ), (5247288423/10000000000 : ℝ)] ![(11059191955477/25000000000000 : ℝ), (6298855006099/50000000000000 : ℝ), (8633104429123/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346960727/10000000000 : ℝ)|^2203 ≤ (11059191955477/25000000000000 : ℝ)^1691
        have hw : |(5346960727/10000000000 : ℝ)|=(5346960727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-509721741/2500000000 : ℝ)|^2203 ≤ (6298855006099/50000000000000 : ℝ)^1691
        have hw : |(-509721741/2500000000 : ℝ)|=(509721741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247288423/10000000000 : ℝ)|^2203 ≤ (8633104429123/20000000000000 : ℝ)^1691
        have hw : |(5247288423/10000000000 : ℝ)|=(5247288423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s7_2 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1044328/1953125 : ℝ)*x 0 + (41978327/80000000 : ℝ)*x 1 + (-2038885531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044328/1953125 : ℝ)^2203 ≤ (44236753088073/100000000000000 : ℝ)^1691 := by
    have hnat : (1044328 : ℕ)^2203*100000000000000^1691 ≤ 44236753088073^1691*1953125^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044328 1953125 44236753088073 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41978327/80000000 : ℝ)^2203 ≤ (10791387105921/25000000000000 : ℝ)^1691 := by
    have hnat : (41978327 : ℕ)^2203*25000000000000^1691 ≤ 10791387105921^1691*80000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41978327 80000000 10791387105921 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2038885531/10000000000 : ℝ)^2203 ≤ (6298849238627/50000000000000 : ℝ)^1691 := by
    have hnat : (2038885531 : ℕ)^2203*50000000000000^1691 ≤ 6298849238627^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038885531 10000000000 6298849238627 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044328/1953125 : ℝ), (41978327/80000000 : ℝ), (-2038885531/10000000000 : ℝ)] ![(44236753088073/100000000000000 : ℝ), (10791387105921/25000000000000 : ℝ), (6298849238627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044328/1953125 : ℝ)|^2203 ≤ (44236753088073/100000000000000 : ℝ)^1691
        have hw : |(1044328/1953125 : ℝ)|=(1044328/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41978327/80000000 : ℝ)|^2203 ≤ (10791387105921/25000000000000 : ℝ)^1691
        have hw : |(41978327/80000000 : ℝ)|=(41978327/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2038885531/10000000000 : ℝ)|^2203 ≤ (6298849238627/50000000000000 : ℝ)^1691
        have hw : |(-2038885531/10000000000 : ℝ)|=(2038885531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s7_3 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4199356/9765625 : ℝ)*x 0 + (4129110877/10000000000 : ℝ)*x 1 + (179098961/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4199356/9765625 : ℝ)^2203 ≤ (16652473210363/50000000000000 : ℝ)^1691 := by
    have hnat : (4199356 : ℕ)^2203*50000000000000^1691 ≤ 16652473210363^1691*9765625^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4199356 9765625 16652473210363 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4129110877/10000000000 : ℝ)^2203 ≤ (31589722599499/100000000000000 : ℝ)^1691 := by
    have hnat : (4129110877 : ℕ)^2203*100000000000000^1691 ≤ 31589722599499^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129110877 10000000000 31589722599499 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179098961/400000000 : ℝ)^2203 ≤ (35105330962081/100000000000000 : ℝ)^1691 := by
    have hnat : (179098961 : ℕ)^2203*100000000000000^1691 ≤ 35105330962081^1691*400000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179098961 400000000 35105330962081 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4199356/9765625 : ℝ), (4129110877/10000000000 : ℝ), (179098961/400000000 : ℝ)] ![(16652473210363/50000000000000 : ℝ), (31589722599499/100000000000000 : ℝ), (35105330962081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4199356/9765625 : ℝ)|^2203 ≤ (16652473210363/50000000000000 : ℝ)^1691
        have hw : |(4199356/9765625 : ℝ)|=(4199356/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4129110877/10000000000 : ℝ)|^2203 ≤ (31589722599499/100000000000000 : ℝ)^1691
        have hw : |(4129110877/10000000000 : ℝ)|=(4129110877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(179098961/400000000 : ℝ)|^2203 ≤ (35105330962081/100000000000000 : ℝ)^1691
        have hw : |(179098961/400000000 : ℝ)|=(179098961/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s7_4 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-978716383/5000000000 : ℝ)*x 0 + (327991781/625000000 : ℝ)*x 1 + (5406744097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (978716383/5000000000 : ℝ)^2203 ≤ (5973023373847/50000000000000 : ℝ)^1691 := by
    have hnat : (978716383 : ℕ)^2203*50000000000000^1691 ≤ 5973023373847^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978716383 5000000000 5973023373847 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327991781/625000000 : ℝ)^2203 ≤ (21585869444001/50000000000000 : ℝ)^1691 := by
    have hnat : (327991781 : ℕ)^2203*50000000000000^1691 ≤ 21585869444001^1691*625000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327991781 625000000 21585869444001 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406744097/10000000000 : ℝ)^2203 ≤ (11220553587493/25000000000000 : ℝ)^1691 := by
    have hnat : (5406744097 : ℕ)^2203*25000000000000^1691 ≤ 11220553587493^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406744097 10000000000 11220553587493 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-978716383/5000000000 : ℝ), (327991781/625000000 : ℝ), (5406744097/10000000000 : ℝ)] ![(5973023373847/50000000000000 : ℝ), (21585869444001/50000000000000 : ℝ), (11220553587493/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-978716383/5000000000 : ℝ)|^2203 ≤ (5973023373847/50000000000000 : ℝ)^1691
        have hw : |(-978716383/5000000000 : ℝ)|=(978716383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327991781/625000000 : ℝ)|^2203 ≤ (21585869444001/50000000000000 : ℝ)^1691
        have hw : |(327991781/625000000 : ℝ)|=(327991781/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406744097/10000000000 : ℝ)|^2203 ≤ (11220553587493/25000000000000 : ℝ)^1691
        have hw : |(5406744097/10000000000 : ℝ)|=(5406744097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s7_5 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326321623/2500000000 : ℝ)*x 0 + (-117464521/625000000 : ℝ)*x 1 + (5406744107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326321623/2500000000 : ℝ)^2203 ≤ (43788124460073/100000000000000 : ℝ)^1691 := by
    have hnat : (1326321623 : ℕ)^2203*100000000000000^1691 ≤ 43788124460073^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326321623 2500000000 43788124460073 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (117464521/625000000 : ℝ)^2203 ≤ (11329661071077/100000000000000 : ℝ)^1691 := by
    have hnat : (117464521 : ℕ)^2203*100000000000000^1691 ≤ 11329661071077^1691*625000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117464521 625000000 11329661071077 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406744107/10000000000 : ℝ)^2203 ≤ (22441107229059/50000000000000 : ℝ)^1691 := by
    have hnat : (5406744107 : ℕ)^2203*50000000000000^1691 ≤ 22441107229059^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406744107 10000000000 22441107229059 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326321623/2500000000 : ℝ), (-117464521/625000000 : ℝ), (5406744107/10000000000 : ℝ)] ![(43788124460073/100000000000000 : ℝ), (11329661071077/100000000000000 : ℝ), (22441107229059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326321623/2500000000 : ℝ)|^2203 ≤ (43788124460073/100000000000000 : ℝ)^1691
        have hw : |(1326321623/2500000000 : ℝ)|=(1326321623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-117464521/625000000 : ℝ)|^2203 ≤ (11329661071077/100000000000000 : ℝ)^1691
        have hw : |(-117464521/625000000 : ℝ)|=(117464521/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406744107/10000000000 : ℝ)|^2203 ≤ (22441107229059/50000000000000 : ℝ)^1691
        have hw : |(5406744107/10000000000 : ℝ)|=(5406744107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s7_6 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652643257/5000000000 : ℝ)*x 0 + (5406744111/10000000000 : ℝ)*x 1 + (-18794323/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652643257/5000000000 : ℝ)^2203 ≤ (43788124696633/100000000000000 : ℝ)^1691 := by
    have hnat : (2652643257 : ℕ)^2203*100000000000000^1691 ≤ 43788124696633^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652643257 5000000000 43788124696633 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406744111/10000000000 : ℝ)^2203 ≤ (43830287599/97656250000 : ℝ)^1691 := by
    have hnat : (5406744111 : ℕ)^2203*97656250000^1691 ≤ 43830287599^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406744111 10000000000 43830287599 97656250000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18794323/100000000 : ℝ)^2203 ≤ (88512974909/781250000000 : ℝ)^1691 := by
    have hnat : (18794323 : ℕ)^2203*781250000000^1691 ≤ 88512974909^1691*100000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18794323 100000000 88512974909 781250000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652643257/5000000000 : ℝ), (5406744111/10000000000 : ℝ), (-18794323/100000000 : ℝ)] ![(43788124696633/100000000000000 : ℝ), (43830287599/97656250000 : ℝ), (88512974909/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652643257/5000000000 : ℝ)|^2203 ≤ (43788124696633/100000000000000 : ℝ)^1691
        have hw : |(2652643257/5000000000 : ℝ)|=(2652643257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406744111/10000000000 : ℝ)|^2203 ≤ (43830287599/97656250000 : ℝ)^1691
        have hw : |(5406744111/10000000000 : ℝ)|=(5406744111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18794323/100000000 : ℝ)|^2203 ≤ (88512974909/781250000000 : ℝ)^1691
        have hw : |(-18794323/100000000 : ℝ)|=(18794323/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s7_7 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4300166153/10000000000 : ℝ)*x 0 + (4476216567/10000000000 : ℝ)*x 1 + (1032593379/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300166153/10000000000 : ℝ)^2203 ≤ (33305204819227/100000000000000 : ℝ)^1691 := by
    have hnat : (4300166153 : ℕ)^2203*100000000000000^1691 ≤ 33305204819227^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300166153 10000000000 33305204819227 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4476216567/10000000000 : ℝ)^2203 ≤ (3509248738761/10000000000000 : ℝ)^1691 := by
    have hnat : (4476216567 : ℕ)^2203*10000000000000^1691 ≤ 3509248738761^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476216567 10000000000 3509248738761 10000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032593379/2500000000 : ℝ)^2203 ≤ (31602307780311/100000000000000 : ℝ)^1691 := by
    have hnat : (1032593379 : ℕ)^2203*100000000000000^1691 ≤ 31602307780311^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032593379 2500000000 31602307780311 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300166153/10000000000 : ℝ), (4476216567/10000000000 : ℝ), (1032593379/2500000000 : ℝ)] ![(33305204819227/100000000000000 : ℝ), (3509248738761/10000000000000 : ℝ), (31602307780311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300166153/10000000000 : ℝ)|^2203 ≤ (33305204819227/100000000000000 : ℝ)^1691
        have hw : |(4300166153/10000000000 : ℝ)|=(4300166153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4476216567/10000000000 : ℝ)|^2203 ≤ (3509248738761/10000000000000 : ℝ)^1691
        have hw : |(4476216567/10000000000 : ℝ)|=(4476216567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032593379/2500000000 : ℝ)|^2203 ≤ (31602307780311/100000000000000 : ℝ)^1691
        have hw : |(1032593379/2500000000 : ℝ)|=(1032593379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s7_8 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-12829559/5000000000 : ℝ)*x 0 + (1174417357/2000000000 : ℝ)*x 1 + (2936036353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12829559/5000000000 : ℝ)^2203 ≤ (42151538881/100000000000000 : ℝ)^1691 := by
    have hnat : (12829559 : ℕ)^2203*100000000000000^1691 ≤ 42151538881^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12829559 5000000000 42151538881 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1174417357/2000000000 : ℝ)^2203 ≤ (49979002285369/100000000000000 : ℝ)^1691 := by
    have hnat : (1174417357 : ℕ)^2203*100000000000000^1691 ≤ 49979002285369^1691*2000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174417357 2000000000 49979002285369 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2936036353/5000000000 : ℝ)^2203 ≤ (12494711543219/25000000000000 : ℝ)^1691 := by
    have hnat : (2936036353 : ℕ)^2203*25000000000000^1691 ≤ 12494711543219^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2936036353 5000000000 12494711543219 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-12829559/5000000000 : ℝ), (1174417357/2000000000 : ℝ), (2936036353/5000000000 : ℝ)] ![(42151538881/100000000000000 : ℝ), (49979002285369/100000000000000 : ℝ), (12494711543219/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-12829559/5000000000 : ℝ)|^2203 ≤ (42151538881/100000000000000 : ℝ)^1691
        have hw : |(-12829559/5000000000 : ℝ)|=(12829559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1174417357/2000000000 : ℝ)|^2203 ≤ (49979002285369/100000000000000 : ℝ)^1691
        have hw : |(1174417357/2000000000 : ℝ)|=(1174417357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2936036353/5000000000 : ℝ)|^2203 ≤ (12494711543219/25000000000000 : ℝ)^1691
        have hw : |(2936036353/5000000000 : ℝ)|=(2936036353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s7_9 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (44686383/312500000 : ℝ)*x 0 + (110243783/200000000 : ℝ)*x 1 + (68916921/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44686383/312500000 : ℝ)^2203 ≤ (396775670473/5000000000000 : ℝ)^1691 := by
    have hnat : (44686383 : ℕ)^2203*5000000000000^1691 ≤ 396775670473^1691*312500000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44686383 312500000 396775670473 5000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110243783/200000000 : ℝ)^2203 ≤ (1841036368309/4000000000000 : ℝ)^1691 := by
    have hnat : (110243783 : ℕ)^2203*4000000000000^1691 ≤ 1841036368309^1691*200000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110243783 200000000 1841036368309 4000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68916921/125000000 : ℝ)^2203 ≤ (46038577373107/100000000000000 : ℝ)^1691 := by
    have hnat : (68916921 : ℕ)^2203*100000000000000^1691 ≤ 46038577373107^1691*125000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68916921 125000000 46038577373107 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(44686383/312500000 : ℝ), (110243783/200000000 : ℝ), (68916921/125000000 : ℝ)] ![(396775670473/5000000000000 : ℝ), (1841036368309/4000000000000 : ℝ), (46038577373107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(44686383/312500000 : ℝ)|^2203 ≤ (396775670473/5000000000000 : ℝ)^1691
        have hw : |(44686383/312500000 : ℝ)|=(44686383/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(110243783/200000000 : ℝ)|^2203 ≤ (1841036368309/4000000000000 : ℝ)^1691
        have hw : |(110243783/200000000 : ℝ)|=(110243783/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68916921/125000000 : ℝ)|^2203 ≤ (46038577373107/100000000000000 : ℝ)^1691
        have hw : |(68916921/125000000 : ℝ)|=(68916921/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1446_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (91/800 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2953/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7383/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5687/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5687/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5687/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5687/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5687/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5687/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5687/50000 : ℝ) ^ (4405/1024 : ℝ) ≤ (347398010225709/4000000000000000000 : ℝ) := by
    have hpowers : (5687/50000 : ℝ)^4405 ≤ (347398010225709/4000000000000000000 : ℝ)^1024 := by
      have hnat : (5687 : ℕ)^4405*4000000000000000000^1024 ≤ 347398010225709^1024*50000^4405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5687 50000 347398010225709 4000000000000000000 4405 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5687/50000 : ℝ)) (X := (347398010225709/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7383/50000 : ℝ) ^ (4405/1024 : ℝ) ≤ (13345659490218397/50000000000000000000 : ℝ) := by
    have hpowers : (7383/50000 : ℝ)^4405 ≤ (13345659490218397/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7383 : ℕ)^4405*50000000000000000000^1024 ≤ 13345659490218397^1024*50000^4405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7383 50000 13345659490218397 50000000000000000000 4405 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7383/50000 : ℝ)) (X := (13345659490218397/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000347398010225709/2000000000000000000 : ℝ) ≤ (2000080751839159/2000000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (2000347398010225709/2000000000000000000 : ℝ)^1024 ≤ (2000080751839159/2000000000000000 : ℝ)^4405 := by
      have hnat : (2000347398010225709 : ℕ)^1024*2000000000000000^4405 ≤ 2000080751839159^4405*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000347398010225709 2000000000000000000 2000080751839159 2000000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000080751839159/2000000000000000 : ℝ)) (X := (2000347398010225709/2000000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035376269236079519/100000000000000000000 : ℝ) ≤ (10000822256133229/10000000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (100035376269236079519/100000000000000000000 : ℝ)^1024 ≤ (10000822256133229/10000000000000000 : ℝ)^4405 := by
      have hnat : (100035376269236079519 : ℕ)^1024*10000000000000000^4405 ≤ 10000822256133229^4405*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035376269236079519 100000000000000000000 10000822256133229 10000000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000822256133229/10000000000000000 : ℝ)) (X := (100035376269236079519/100000000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013345659490218397/25000000000000000000 : ℝ) ≤ (10001240753070663/10000000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (25013345659490218397/25000000000000000000 : ℝ)^1024 ≤ (10001240753070663/10000000000000000 : ℝ)^4405 := by
      have hnat : (25013345659490218397 : ℕ)^1024*10000000000000000^4405 ≤ 10001240753070663^4405*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013345659490218397 25000000000000000000 10001240753070663 10000000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001240753070663/10000000000000000 : ℝ)) (X := (25013345659490218397/25000000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(347398010225709/4000000000000000000 : ℝ) ≤ ((4238981197857423501/4240000000000000000 : ℝ)+2*(209248468717/169600000000000 : ℝ)*(5687/50000 : ℝ))^(4405/1024 : ℝ) := by
    rw [show (4238981197857423501/4240000000000000000 : ℝ)+2*(209248468717/169600000000000 : ℝ)*(5687/50000 : ℝ)=(2000080751839159/2000000000000000 : ℝ) by norm_num, show 1+2*(347398010225709/4000000000000000000 : ℝ)=(2000347398010225709/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13345659490218397/50000000000000000000 : ℝ)+(347398010225709/4000000000000000000 : ℝ) ≤ ((4238981197857423501/4240000000000000000 : ℝ)+(209248468717/169600000000000 : ℝ)*((7383/50000 : ℝ)+(5687/50000 : ℝ)))^(4405/1024 : ℝ) := by
    rw [show (4238981197857423501/4240000000000000000 : ℝ)+(209248468717/169600000000000 : ℝ)*((7383/50000 : ℝ)+(5687/50000 : ℝ))=(10000822256133229/10000000000000000 : ℝ) by norm_num, show 1+(13345659490218397/50000000000000000000 : ℝ)+(347398010225709/4000000000000000000 : ℝ)=(100035376269236079519/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13345659490218397/50000000000000000000 : ℝ) ≤ ((4238981197857423501/4240000000000000000 : ℝ)+2*(209248468717/169600000000000 : ℝ)*(7383/50000 : ℝ))^(4405/1024 : ℝ) := by
    rw [show (4238981197857423501/4240000000000000000 : ℝ)+2*(209248468717/169600000000000 : ℝ)*(7383/50000 : ℝ)=(10001240753070663/10000000000000000 : ℝ) by norm_num, show 1+2*(13345659490218397/50000000000000000000 : ℝ)=(25013345659490218397/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4238981197857423501/4240000000000000000 : ℝ)*(X 1 0+X 2 0)+(209248468717/169600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (5687/50000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (4238981197857423501/4240000000000000000 : ℝ)) (alpha := (209248468717/169600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4238981197857423501/4240000000000000000 : ℝ)*(X 0 1+X 2 1)+(209248468717/169600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (5687/50000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (4238981197857423501/4240000000000000000 : ℝ)) (alpha := (209248468717/169600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4238981197857423501/4240000000000000000 : ℝ)*(X 0 2+X 1 2)+(209248468717/169600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (5687/50000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (4238981197857423501/4240000000000000000 : ℝ)) (alpha := (209248468717/169600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-489355837/2500000000 : ℝ)*X 0 0+(1081464923/2000000000 : ℝ)*X 0 1+(65591121/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346960727/10000000000 : ℝ)*X 1 0+(-509721741/2500000000 : ℝ)*X 1 1+(5247288423/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1044328/1953125 : ℝ)*X 2 0+(41978327/80000000 : ℝ)*X 2 1+(-2038885531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4199356/9765625 : ℝ)*X 0 0+(4129110877/10000000000 : ℝ)*X 0 1+(179098961/400000000 : ℝ)*X 0 2+(4199356/9765625 : ℝ)*X 1 0+(4129110877/10000000000 : ℝ)*X 1 1+(179098961/400000000 : ℝ)*X 1 2+(4199356/9765625 : ℝ)*X 2 0+(4129110877/10000000000 : ℝ)*X 2 1+(179098961/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-978716383/5000000000 : ℝ)*X 0 0+(327991781/625000000 : ℝ)*X 0 1+(5406744097/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326321623/2500000000 : ℝ)*X 1 0+(-117464521/625000000 : ℝ)*X 1 1+(5406744107/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652643257/5000000000 : ℝ)*X 2 0+(5406744111/10000000000 : ℝ)*X 2 1+(-18794323/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4300166153/10000000000 : ℝ)*X 0 0+(4476216567/10000000000 : ℝ)*X 0 1+(1032593379/2500000000 : ℝ)*X 0 2+(4300166153/10000000000 : ℝ)*X 1 0+(4476216567/10000000000 : ℝ)*X 1 1+(1032593379/2500000000 : ℝ)*X 1 2+(4300166153/10000000000 : ℝ)*X 2 0+(4476216567/10000000000 : ℝ)*X 2 1+(1032593379/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-12829559/5000000000 : ℝ)*X 0 0+(1174417357/2000000000 : ℝ)*X 0 1+(2936036353/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s7_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((44686383/312500000 : ℝ)*X 0 0+(110243783/200000000 : ℝ)*X 0 1+(68916921/125000000 : ℝ)*X 0 2+(44686383/312500000 : ℝ)*X 1 0+(110243783/200000000 : ℝ)*X 1 1+(68916921/125000000 : ℝ)*X 1 2+(44686383/312500000 : ℝ)*X 2 0+(110243783/200000000 : ℝ)*X 2 1+(68916921/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s7_9 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (729423369834061079574462783/212000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15559971/100000000000000 : ℝ)*(lower2) + (11751913/20000000000000 : ℝ)*(lower3) + (246910343/50000000000000 : ℝ)*(lower4) + (62700567/10000000000000 : ℝ)*(lower5) + (4559631860326413/100000000000000 : ℝ)*(major0) + (4559631860326413/100000000000000 : ℝ)*(major1) + (4559631860326413/100000000000000 : ℝ)*(major2) + (97635651798863/1562500000000 : ℝ)*(sp0) + (3124303212305759/50000000000000 : ℝ)*(sp1) + (6248696632891151/100000000000000 : ℝ)*(sp2) + (1435283486536219/50000000000000 : ℝ)*(sp3) + (73978593/1562500000000 : ℝ)*(sp4) + (90208279633/100000000000000 : ℝ)*(sp5) + (10183133967/100000000000000 : ℝ)*(sp8) + (1435283486536219/50000000000000 : ℝ)*(f.failure) + (6248696632891151/100000000000000 : ℝ)*(f.sum) + (646042984043081/8480000000000000000000000000 : ℝ)*base65 + (313737312658256913/424000000000000000000000000000000 : ℝ)*base67 + (5187471175546256913/424000000000000000000000000000000 : ℝ)*base69 + (4126109907434256913/424000000000000000000000000000000 : ℝ)*base71 + (46817361472841/8480000000000000000000000000 : ℝ)*base73 + (4752207599010256913/424000000000000000000000000000000 : ℝ)*base75 + (47709429316122256913/424000000000000000000000000000000 : ℝ)*base77 + (637667733666256913/424000000000000000000000000000000 : ℝ)*base79 + (53035383521001/8480000000000000000000000000 : ℝ)*base81 + (43166391/5000000000000000000000 : ℝ)*base90 + (43166391/5000000000000000000000 : ℝ)*base92 + (43166391/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (759961918085107338298943013/106000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (64396261/100000000000000 : ℝ)*(lower1) + (18324299/100000000000000 : ℝ)*(lower2) + (18457277/12500000000000 : ℝ)*(lower3) + (77778051/50000000000000 : ℝ)*(lower5) + (2296429026620829/50000000000000 : ℝ)*(major0) + (2296429026620829/50000000000000 : ℝ)*(major1) + (4592858053241659/100000000000000 : ℝ)*(major2) + (537159261/50000000000000 : ℝ)*(sp2) + (6294229050389291/100000000000000 : ℝ)*(sp4) + (3147115487484361/50000000000000 : ℝ)*(sp5) + (31471149503251/500000000000 : ℝ)*(sp6) + (722870886794049/25000000000000 : ℝ)*(sp7) + (1924579431/100000000000000 : ℝ)*(sp8) + (672678327/50000000000000 : ℝ)*(sp9) + (57829697850657/2000000000000 : ℝ)*(f.failure) + (3147115487484361/50000000000000 : ℝ)*(f.sum) + (17339289584209/16960000000000000000000000000 : ℝ)*base65 + (2012257197516510171/212000000000000000000000000000000 : ℝ)*base68 + (3910623358477521841/424000000000000000000000000000000 : ℝ)*base70 + (1525425443087489829/212000000000000000000000000000000 : ℝ)*base71 + (39782092040111/16960000000000000000000000000 : ℝ)*base74 + (239299647338478159/424000000000000000000000000000000 : ℝ)*base75 + (1147237952076527329/212000000000000000000000000000000 : ℝ)*base77 + (2008364981476527329/212000000000000000000000000000000 : ℝ)*base79 + (7946277208633/4240000000000000000000000000 : ℝ)*base81 + (1237173/200000000000000000000 : ℝ)*base90 + (1237173/200000000000000000000 : ℝ)*base92 + (3237173/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1446_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1446_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1446_box_0 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-898991061/5000000000 : ℝ)*x 0 + (673190737/1250000000 : ℝ)*x 1 + (1346381361/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (898991061/5000000000 : ℝ)^2203 ≤ (5347117398317/50000000000000 : ℝ)^1691 := by
    have hnat : (898991061 : ℕ)^2203*50000000000000^1691 ≤ 5347117398317^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898991061 5000000000 5347117398317 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673190737/1250000000 : ℝ)^2203 ≤ (44652885033339/100000000000000 : ℝ)^1691 := by
    have hnat : (673190737 : ℕ)^2203*100000000000000^1691 ≤ 44652885033339^1691*1250000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673190737 1250000000 44652885033339 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346381361/2500000000 : ℝ)^2203 ≤ (5581610018871/12500000000000 : ℝ)^1691 := by
    have hnat : (1346381361 : ℕ)^2203*12500000000000^1691 ≤ 5581610018871^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346381361 2500000000 5581610018871 12500000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-898991061/5000000000 : ℝ), (673190737/1250000000 : ℝ), (1346381361/2500000000 : ℝ)] ![(5347117398317/50000000000000 : ℝ), (44652885033339/100000000000000 : ℝ), (5581610018871/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-898991061/5000000000 : ℝ)|^2203 ≤ (5347117398317/50000000000000 : ℝ)^1691
        have hw : |(-898991061/5000000000 : ℝ)|=(898991061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673190737/1250000000 : ℝ)|^2203 ≤ (44652885033339/100000000000000 : ℝ)^1691
        have hw : |(673190737/1250000000 : ℝ)|=(673190737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346381361/2500000000 : ℝ)|^2203 ≤ (5581610018871/12500000000000 : ℝ)^1691
        have hw : |(1346381361/2500000000 : ℝ)|=(1346381361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_box_1 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (660772089/1250000000 : ℝ)*x 0 + (-1934541519/10000000000 : ℝ)*x 1 + (5385525273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660772089/1250000000 : ℝ)^2203 ≤ (43582754465741/100000000000000 : ℝ)^1691 := by
    have hnat : (660772089 : ℕ)^2203*100000000000000^1691 ≤ 43582754465741^1691*1250000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660772089 1250000000 43582754465741 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1934541519/10000000000 : ℝ)^2203 ≤ (5882183603459/50000000000000 : ℝ)^1691 := by
    have hnat : (1934541519 : ℕ)^2203*50000000000000^1691 ≤ 5882183603459^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934541519 10000000000 5882183603459 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385525273/10000000000 : ℝ)^2203 ≤ (44652878303877/100000000000000 : ℝ)^1691 := by
    have hnat : (5385525273 : ℕ)^2203*100000000000000^1691 ≤ 44652878303877^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385525273 10000000000 44652878303877 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660772089/1250000000 : ℝ), (-1934541519/10000000000 : ℝ), (5385525273/10000000000 : ℝ)] ![(43582754465741/100000000000000 : ℝ), (5882183603459/50000000000000 : ℝ), (44652878303877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660772089/1250000000 : ℝ)|^2203 ≤ (43582754465741/100000000000000 : ℝ)^1691
        have hw : |(660772089/1250000000 : ℝ)|=(660772089/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1934541519/10000000000 : ℝ)|^2203 ≤ (5882183603459/50000000000000 : ℝ)^1691
        have hw : |(-1934541519/10000000000 : ℝ)|=(1934541519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385525273/10000000000 : ℝ)|^2203 ≤ (44652878303877/100000000000000 : ℝ)^1691
        have hw : |(5385525273/10000000000 : ℝ)|=(5385525273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_box_2 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5286176301/10000000000 : ℝ)*x 0 + (5385525799/10000000000 : ℝ)*x 1 + (-1934541359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286176301/10000000000 : ℝ)^2203 ≤ (43582750051199/100000000000000 : ℝ)^1691 := by
    have hnat : (5286176301 : ℕ)^2203*100000000000000^1691 ≤ 43582750051199^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286176301 10000000000 43582750051199 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385525799/10000000000 : ℝ)^2203 ≤ (44652883985573/100000000000000 : ℝ)^1691 := by
    have hnat : (5385525799 : ℕ)^2203*100000000000000^1691 ≤ 44652883985573^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385525799 10000000000 44652883985573 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1934541359/10000000000 : ℝ)^2203 ≤ (294109148483/2500000000000 : ℝ)^1691 := by
    have hnat : (1934541359 : ℕ)^2203*2500000000000^1691 ≤ 294109148483^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934541359 10000000000 294109148483 2500000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286176301/10000000000 : ℝ), (5385525799/10000000000 : ℝ), (-1934541359/10000000000 : ℝ)] ![(43582750051199/100000000000000 : ℝ), (44652883985573/100000000000000 : ℝ), (294109148483/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286176301/10000000000 : ℝ)|^2203 ≤ (43582750051199/100000000000000 : ℝ)^1691
        have hw : |(5286176301/10000000000 : ℝ)|=(5286176301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385525799/10000000000 : ℝ)|^2203 ≤ (44652883985573/100000000000000 : ℝ)^1691
        have hw : |(5385525799/10000000000 : ℝ)|=(5385525799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1934541359/10000000000 : ℝ)|^2203 ≤ (294109148483/2500000000000 : ℝ)^1691
        have hw : |(-1934541359/10000000000 : ℝ)|=(1934541359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_box_3 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4446101839/10000000000 : ℝ)*x 0 + (528854781/1250000000 : ℝ)*x 1 + (4230837879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4446101839/10000000000 : ℝ)^2203 ≤ (34785224827471/100000000000000 : ℝ)^1691 := by
    have hnat : (4446101839 : ℕ)^2203*100000000000000^1691 ≤ 34785224827471^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4446101839 10000000000 34785224827471 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528854781/1250000000 : ℝ)^2203 ≤ (32607389435293/100000000000000 : ℝ)^1691 := by
    have hnat : (528854781 : ℕ)^2203*100000000000000^1691 ≤ 32607389435293^1691*1250000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528854781 1250000000 32607389435293 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230837879/10000000000 : ℝ)^2203 ≤ (6521477146061/20000000000000 : ℝ)^1691 := by
    have hnat : (4230837879 : ℕ)^2203*20000000000000^1691 ≤ 6521477146061^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230837879 10000000000 6521477146061 20000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4446101839/10000000000 : ℝ), (528854781/1250000000 : ℝ), (4230837879/10000000000 : ℝ)] ![(34785224827471/100000000000000 : ℝ), (32607389435293/100000000000000 : ℝ), (6521477146061/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4446101839/10000000000 : ℝ)|^2203 ≤ (34785224827471/100000000000000 : ℝ)^1691
        have hw : |(4446101839/10000000000 : ℝ)|=(4446101839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528854781/1250000000 : ℝ)|^2203 ≤ (32607389435293/100000000000000 : ℝ)^1691
        have hw : |(528854781/1250000000 : ℝ)|=(528854781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230837879/10000000000 : ℝ)|^2203 ≤ (6521477146061/20000000000000 : ℝ)^1691
        have hw : |(4230837879/10000000000 : ℝ)|=(4230837879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_box_4 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-105979679/500000000 : ℝ)*x 0 + (5266766599/10000000000 : ℝ)*x 1 + (5266767523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105979679/500000000 : ℝ)^2203 ≤ (13251216412369/100000000000000 : ℝ)^1691 := by
    have hnat : (105979679 : ℕ)^2203*100000000000000^1691 ≤ 13251216412369^1691*500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105979679 500000000 13251216412369 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266766599/10000000000 : ℝ)^2203 ≤ (10843596707909/25000000000000 : ℝ)^1691 := by
    have hnat : (5266766599 : ℕ)^2203*25000000000000^1691 ≤ 10843596707909^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266766599 10000000000 10843596707909 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266767523/10000000000 : ℝ)^2203 ≤ (21687198372627/50000000000000 : ℝ)^1691 := by
    have hnat : (5266767523 : ℕ)^2203*50000000000000^1691 ≤ 21687198372627^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266767523 10000000000 21687198372627 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-105979679/500000000 : ℝ), (5266766599/10000000000 : ℝ), (5266767523/10000000000 : ℝ)] ![(13251216412369/100000000000000 : ℝ), (10843596707909/25000000000000 : ℝ), (21687198372627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-105979679/500000000 : ℝ)|^2203 ≤ (13251216412369/100000000000000 : ℝ)^1691
        have hw : |(-105979679/500000000 : ℝ)|=(105979679/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266766599/10000000000 : ℝ)|^2203 ≤ (10843596707909/25000000000000 : ℝ)^1691
        have hw : |(5266766599/10000000000 : ℝ)|=(5266766599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266767523/10000000000 : ℝ)|^2203 ≤ (21687198372627/50000000000000 : ℝ)^1691
        have hw : |(5266767523/10000000000 : ℝ)|=(5266767523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_box_5 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2684616313/5000000000 : ℝ)*x 0 + (-991431757/5000000000 : ℝ)*x 1 + (5266767131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684616313/5000000000 : ℝ)^2203 ≤ (8895394121771/20000000000000 : ℝ)^1691 := by
    have hnat : (2684616313 : ℕ)^2203*20000000000000^1691 ≤ 8895394121771^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684616313 5000000000 8895394121771 20000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (991431757/5000000000 : ℝ)^2203 ≤ (3037159206007/25000000000000 : ℝ)^1691 := by
    have hnat : (991431757 : ℕ)^2203*25000000000000^1691 ≤ 3037159206007^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991431757 5000000000 3037159206007 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266767131/10000000000 : ℝ)^2203 ≤ (10843598134869/25000000000000 : ℝ)^1691 := by
    have hnat : (5266767131 : ℕ)^2203*25000000000000^1691 ≤ 10843598134869^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266767131 10000000000 10843598134869 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684616313/5000000000 : ℝ), (-991431757/5000000000 : ℝ), (5266767131/10000000000 : ℝ)] ![(8895394121771/20000000000000 : ℝ), (3037159206007/25000000000000 : ℝ), (10843598134869/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684616313/5000000000 : ℝ)|^2203 ≤ (8895394121771/20000000000000 : ℝ)^1691
        have hw : |(2684616313/5000000000 : ℝ)|=(2684616313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-991431757/5000000000 : ℝ)|^2203 ≤ (3037159206007/25000000000000 : ℝ)^1691
        have hw : |(-991431757/5000000000 : ℝ)|=(991431757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266767131/10000000000 : ℝ)|^2203 ≤ (10843598134869/25000000000000 : ℝ)^1691
        have hw : |(5266767131/10000000000 : ℝ)|=(5266767131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_box_6 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (536923217/1000000000 : ℝ)*x 0 + (2633383829/5000000000 : ℝ)*x 1 + (-30982241/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536923217/1000000000 : ℝ)^2203 ≤ (8895393137559/20000000000000 : ℝ)^1691 := by
    have hnat : (536923217 : ℕ)^2203*20000000000000^1691 ≤ 8895393137559^1691*1000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536923217 1000000000 8895393137559 20000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633383829/5000000000 : ℝ)^2203 ≤ (5421799774209/12500000000000 : ℝ)^1691 := by
    have hnat : (2633383829 : ℕ)^2203*12500000000000^1691 ≤ 5421799774209^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633383829 5000000000 5421799774209 12500000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (30982241/156250000 : ℝ)^2203 ≤ (6074318052829/50000000000000 : ℝ)^1691 := by
    have hnat : (30982241 : ℕ)^2203*50000000000000^1691 ≤ 6074318052829^1691*156250000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30982241 156250000 6074318052829 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536923217/1000000000 : ℝ), (2633383829/5000000000 : ℝ), (-30982241/156250000 : ℝ)] ![(8895393137559/20000000000000 : ℝ), (5421799774209/12500000000000 : ℝ), (6074318052829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536923217/1000000000 : ℝ)|^2203 ≤ (8895393137559/20000000000000 : ℝ)^1691
        have hw : |(536923217/1000000000 : ℝ)|=(536923217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633383829/5000000000 : ℝ)|^2203 ≤ (5421799774209/12500000000000 : ℝ)^1691
        have hw : |(2633383829/5000000000 : ℝ)|=(2633383829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-30982241/156250000 : ℝ)|^2203 ≤ (6074318052829/50000000000000 : ℝ)^1691
        have hw : |(-30982241/156250000 : ℝ)|=(30982241/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_box_7 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4153111409/10000000000 : ℝ)*x 0 + (4377283013/10000000000 : ℝ)*x 1 + (547160341/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4153111409/10000000000 : ℝ)^2203 ≤ (3182914374401/10000000000000 : ℝ)^1691 := by
    have hnat : (4153111409 : ℕ)^2203*10000000000000^1691 ≤ 3182914374401^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153111409 10000000000 3182914374401 10000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4377283013/10000000000 : ℝ)^2203 ≤ (8521357392033/25000000000000 : ℝ)^1691 := by
    have hnat : (4377283013 : ℕ)^2203*25000000000000^1691 ≤ 8521357392033^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377283013 10000000000 8521357392033 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547160341/1250000000 : ℝ)^2203 ≤ (852135666923/2500000000000 : ℝ)^1691 := by
    have hnat : (547160341 : ℕ)^2203*2500000000000^1691 ≤ 852135666923^1691*1250000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547160341 1250000000 852135666923 2500000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4153111409/10000000000 : ℝ), (4377283013/10000000000 : ℝ), (547160341/1250000000 : ℝ)] ![(3182914374401/10000000000000 : ℝ), (8521357392033/25000000000000 : ℝ), (852135666923/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4153111409/10000000000 : ℝ)|^2203 ≤ (3182914374401/10000000000000 : ℝ)^1691
        have hw : |(4153111409/10000000000 : ℝ)|=(4153111409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4377283013/10000000000 : ℝ)|^2203 ≤ (8521357392033/25000000000000 : ℝ)^1691
        have hw : |(4377283013/10000000000 : ℝ)|=(4377283013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(547160341/1250000000 : ℝ)|^2203 ≤ (852135666923/2500000000000 : ℝ)^1691
        have hw : |(547160341/1250000000 : ℝ)|=(547160341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_box_8 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2051816207/10000000000 : ℝ)*x 0 + (1296136869/2500000000 : ℝ)*x 1 + (5399488839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2051816207/10000000000 : ℝ)^2203 ≤ (12701883825231/100000000000000 : ℝ)^1691 := by
    have hnat : (2051816207 : ℕ)^2203*100000000000000^1691 ≤ 12701883825231^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051816207 10000000000 12701883825231 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296136869/2500000000 : ℝ)^2203 ≤ (21247174188263/50000000000000 : ℝ)^1691 := by
    have hnat : (1296136869 : ℕ)^2203*50000000000000^1691 ≤ 21247174188263^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296136869 2500000000 21247174188263 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399488839/10000000000 : ℝ)^2203 ≤ (44803767781941/100000000000000 : ℝ)^1691 := by
    have hnat : (5399488839 : ℕ)^2203*100000000000000^1691 ≤ 44803767781941^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399488839 10000000000 44803767781941 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2051816207/10000000000 : ℝ), (1296136869/2500000000 : ℝ), (5399488839/10000000000 : ℝ)] ![(12701883825231/100000000000000 : ℝ), (21247174188263/50000000000000 : ℝ), (44803767781941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2051816207/10000000000 : ℝ)|^2203 ≤ (12701883825231/100000000000000 : ℝ)^1691
        have hw : |(-2051816207/10000000000 : ℝ)|=(2051816207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296136869/2500000000 : ℝ)|^2203 ≤ (21247174188263/50000000000000 : ℝ)^1691
        have hw : |(1296136869/2500000000 : ℝ)|=(1296136869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399488839/10000000000 : ℝ)|^2203 ≤ (44803767781941/100000000000000 : ℝ)^1691
        have hw : |(5399488839/10000000000 : ℝ)|=(5399488839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_box_9 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1319101909/2500000000 : ℝ)*x 0 + (-241091813/1250000000 : ℝ)*x 1 + (5399488439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319101909/2500000000 : ℝ)^2203 ≤ (8695570878013/20000000000000 : ℝ)^1691 := by
    have hnat : (1319101909 : ℕ)^2203*20000000000000^1691 ≤ 8695570878013^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319101909 2500000000 8695570878013 20000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (241091813/1250000000 : ℝ)^2203 ≤ (11718382141019/100000000000000 : ℝ)^1691 := by
    have hnat : (241091813 : ℕ)^2203*100000000000000^1691 ≤ 11718382141019^1691*1250000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241091813 1250000000 11718382141019 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399488439/10000000000 : ℝ)^2203 ≤ (44803763457871/100000000000000 : ℝ)^1691 := by
    have hnat : (5399488439 : ℕ)^2203*100000000000000^1691 ≤ 44803763457871^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399488439 10000000000 44803763457871 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319101909/2500000000 : ℝ), (-241091813/1250000000 : ℝ), (5399488439/10000000000 : ℝ)] ![(8695570878013/20000000000000 : ℝ), (11718382141019/100000000000000 : ℝ), (44803763457871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319101909/2500000000 : ℝ)|^2203 ≤ (8695570878013/20000000000000 : ℝ)^1691
        have hw : |(1319101909/2500000000 : ℝ)|=(1319101909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-241091813/1250000000 : ℝ)|^2203 ≤ (11718382141019/100000000000000 : ℝ)^1691
        have hw : |(-241091813/1250000000 : ℝ)|=(241091813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399488439/10000000000 : ℝ)|^2203 ≤ (44803763457871/100000000000000 : ℝ)^1691
        have hw : |(5399488439/10000000000 : ℝ)|=(5399488439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_box_10 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5276407163/10000000000 : ℝ)*x 0 + (2699744297/5000000000 : ℝ)*x 1 + (-964367467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276407163/10000000000 : ℝ)^2203 ≤ (43477849312427/100000000000000 : ℝ)^1691 := by
    have hnat : (5276407163 : ℕ)^2203*100000000000000^1691 ≤ 43477849312427^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276407163 10000000000 43477849312427 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699744297/5000000000 : ℝ)^2203 ≤ (5600470641681/12500000000000 : ℝ)^1691 := by
    have hnat : (2699744297 : ℕ)^2203*12500000000000^1691 ≤ 5600470641681^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699744297 5000000000 5600470641681 12500000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (964367467/5000000000 : ℝ)^2203 ≤ (2929596386147/25000000000000 : ℝ)^1691 := by
    have hnat : (964367467 : ℕ)^2203*25000000000000^1691 ≤ 2929596386147^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964367467 5000000000 2929596386147 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276407163/10000000000 : ℝ), (2699744297/5000000000 : ℝ), (-964367467/5000000000 : ℝ)] ![(43477849312427/100000000000000 : ℝ), (5600470641681/12500000000000 : ℝ), (2929596386147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276407163/10000000000 : ℝ)|^2203 ≤ (43477849312427/100000000000000 : ℝ)^1691
        have hw : |(5276407163/10000000000 : ℝ)|=(5276407163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699744297/5000000000 : ℝ)|^2203 ≤ (5600470641681/12500000000000 : ℝ)^1691
        have hw : |(2699744297/5000000000 : ℝ)|=(2699744297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-964367467/5000000000 : ℝ)|^2203 ≤ (2929596386147/25000000000000 : ℝ)^1691
        have hw : |(-964367467/5000000000 : ℝ)|=(964367467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_box_11 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4479993737/10000000000 : ℝ)*x 0 + (1053401331/2500000000 : ℝ)*x 1 + (842720977/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4479993737/10000000000 : ℝ)^2203 ≤ (35131070383703/100000000000000 : ℝ)^1691 := by
    have hnat : (4479993737 : ℕ)^2203*100000000000000^1691 ≤ 35131070383703^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479993737 10000000000 35131070383703 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053401331/2500000000 : ℝ)^2203 ≤ (6486893400853/20000000000000 : ℝ)^1691 := by
    have hnat : (1053401331 : ℕ)^2203*20000000000000^1691 ≤ 6486893400853^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053401331 2500000000 6486893400853 20000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (842720977/2000000000 : ℝ)^2203 ≤ (16217231300939/50000000000000 : ℝ)^1691 := by
    have hnat : (842720977 : ℕ)^2203*50000000000000^1691 ≤ 16217231300939^1691*2000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842720977 2000000000 16217231300939 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4479993737/10000000000 : ℝ), (1053401331/2500000000 : ℝ), (842720977/2000000000 : ℝ)] ![(35131070383703/100000000000000 : ℝ), (6486893400853/20000000000000 : ℝ), (16217231300939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4479993737/10000000000 : ℝ)|^2203 ≤ (35131070383703/100000000000000 : ℝ)^1691
        have hw : |(4479993737/10000000000 : ℝ)|=(4479993737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053401331/2500000000 : ℝ)|^2203 ≤ (6486893400853/20000000000000 : ℝ)^1691
        have hw : |(1053401331/2500000000 : ℝ)|=(1053401331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(842720977/2000000000 : ℝ)|^2203 ≤ (16217231300939/50000000000000 : ℝ)^1691
        have hw : |(842720977/2000000000 : ℝ)|=(842720977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_box_12 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1865911339/10000000000 : ℝ)*x 0 + (1093150807/2000000000 : ℝ)*x 1 + (5255633363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1865911339/10000000000 : ℝ)^2203 ≤ (5611795143919/50000000000000 : ℝ)^1691 := by
    have hnat : (1865911339 : ℕ)^2203*50000000000000^1691 ≤ 5611795143919^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865911339 10000000000 5611795143919 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093150807/2000000000 : ℝ)^2203 ≤ (45521433367357/100000000000000 : ℝ)^1691 := by
    have hnat : (1093150807 : ℕ)^2203*100000000000000^1691 ≤ 45521433367357^1691*2000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093150807 2000000000 45521433367357 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255633363/10000000000 : ℝ)^2203 ≤ (43254976334047/100000000000000 : ℝ)^1691 := by
    have hnat : (5255633363 : ℕ)^2203*100000000000000^1691 ≤ 43254976334047^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255633363 10000000000 43254976334047 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1865911339/10000000000 : ℝ), (1093150807/2000000000 : ℝ), (5255633363/10000000000 : ℝ)] ![(5611795143919/50000000000000 : ℝ), (45521433367357/100000000000000 : ℝ), (43254976334047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1865911339/10000000000 : ℝ)|^2203 ≤ (5611795143919/50000000000000 : ℝ)^1691
        have hw : |(-1865911339/10000000000 : ℝ)|=(1865911339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093150807/2000000000 : ℝ)|^2203 ≤ (45521433367357/100000000000000 : ℝ)^1691
        have hw : |(1093150807/2000000000 : ℝ)|=(1093150807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255633363/10000000000 : ℝ)|^2203 ≤ (43254976334047/100000000000000 : ℝ)^1691
        have hw : |(5255633363/10000000000 : ℝ)|=(5255633363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_box_13 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1344254339/2500000000 : ℝ)*x 0 + (-993647677/5000000000 : ℝ)*x 1 + (42045067/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344254339/2500000000 : ℝ)^2203 ≤ (22280500144091/50000000000000 : ℝ)^1691 := by
    have hnat : (1344254339 : ℕ)^2203*50000000000000^1691 ≤ 22280500144091^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344254339 2500000000 22280500144091 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (993647677/5000000000 : ℝ)^2203 ≤ (12184023236867/100000000000000 : ℝ)^1691 := by
    have hnat : (993647677 : ℕ)^2203*100000000000000^1691 ≤ 12184023236867^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993647677 5000000000 12184023236867 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42045067/80000000 : ℝ)^2203 ≤ (43254976462713/100000000000000 : ℝ)^1691 := by
    have hnat : (42045067 : ℕ)^2203*100000000000000^1691 ≤ 43254976462713^1691*80000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42045067 80000000 43254976462713 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344254339/2500000000 : ℝ), (-993647677/5000000000 : ℝ), (42045067/80000000 : ℝ)] ![(22280500144091/50000000000000 : ℝ), (12184023236867/100000000000000 : ℝ), (43254976462713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344254339/2500000000 : ℝ)|^2203 ≤ (22280500144091/50000000000000 : ℝ)^1691
        have hw : |(1344254339/2500000000 : ℝ)|=(1344254339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-993647677/5000000000 : ℝ)|^2203 ≤ (12184023236867/100000000000000 : ℝ)^1691
        have hw : |(-993647677/5000000000 : ℝ)|=(993647677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42045067/80000000 : ℝ)|^2203 ≤ (43254976462713/100000000000000 : ℝ)^1691
        have hw : |(42045067/80000000 : ℝ)|=(42045067/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_box_14 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5377017377/10000000000 : ℝ)*x 0 + (5255633359/10000000000 : ℝ)*x 1 + (-993647673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377017377/10000000000 : ℝ)^2203 ≤ (44561000514909/100000000000000 : ℝ)^1691 := by
    have hnat : (5377017377 : ℕ)^2203*100000000000000^1691 ≤ 44561000514909^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377017377 10000000000 44561000514909 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255633359/10000000000 : ℝ)^2203 ≤ (21627488145579/50000000000000 : ℝ)^1691 := by
    have hnat : (5255633359 : ℕ)^2203*50000000000000^1691 ≤ 21627488145579^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255633359 10000000000 21627488145579 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (993647673/5000000000 : ℝ)^2203 ≤ (1523002896621/12500000000000 : ℝ)^1691 := by
    have hnat : (993647673 : ℕ)^2203*12500000000000^1691 ≤ 1523002896621^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993647673 5000000000 1523002896621 12500000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377017377/10000000000 : ℝ), (5255633359/10000000000 : ℝ), (-993647673/5000000000 : ℝ)] ![(44561000514909/100000000000000 : ℝ), (21627488145579/50000000000000 : ℝ), (1523002896621/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377017377/10000000000 : ℝ)|^2203 ≤ (44561000514909/100000000000000 : ℝ)^1691
        have hw : |(5377017377/10000000000 : ℝ)|=(5377017377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255633359/10000000000 : ℝ)|^2203 ≤ (21627488145579/50000000000000 : ℝ)^1691
        have hw : |(5255633359/10000000000 : ℝ)|=(5255633359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-993647673/5000000000 : ℝ)|^2203 ≤ (1523002896621/12500000000000 : ℝ)^1691
        have hw : |(-993647673/5000000000 : ℝ)|=(993647673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_box_15 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (412519281/1000000000 : ℝ)*x 0 + (4391001219/10000000000 : ℝ)*x 1 + (1097750309/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412519281/1000000000 : ℝ)^2203 ≤ (7887669305869/25000000000000 : ℝ)^1691 := by
    have hnat : (412519281 : ℕ)^2203*25000000000000^1691 ≤ 7887669305869^1691*1000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412519281 1000000000 7887669305869 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4391001219/10000000000 : ℝ)^2203 ≤ (8556165323477/25000000000000 : ℝ)^1691 := by
    have hnat : (4391001219 : ℕ)^2203*25000000000000^1691 ≤ 8556165323477^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4391001219 10000000000 8556165323477 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097750309/2500000000 : ℝ)^2203 ≤ (34224661466529/100000000000000 : ℝ)^1691 := by
    have hnat : (1097750309 : ℕ)^2203*100000000000000^1691 ≤ 34224661466529^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097750309 2500000000 34224661466529 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(412519281/1000000000 : ℝ), (4391001219/10000000000 : ℝ), (1097750309/2500000000 : ℝ)] ![(7887669305869/25000000000000 : ℝ), (8556165323477/25000000000000 : ℝ), (34224661466529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(412519281/1000000000 : ℝ)|^2203 ≤ (7887669305869/25000000000000 : ℝ)^1691
        have hw : |(412519281/1000000000 : ℝ)|=(412519281/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4391001219/10000000000 : ℝ)|^2203 ≤ (8556165323477/25000000000000 : ℝ)^1691
        have hw : |(4391001219/10000000000 : ℝ)|=(4391001219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1097750309/2500000000 : ℝ)|^2203 ≤ (34224661466529/100000000000000 : ℝ)^1691
        have hw : |(1097750309/2500000000 : ℝ)|=(1097750309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1446_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h) :
    -(6291/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59147/100000 : ℝ) ∧ (40271/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21187/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2953/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (91/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2953/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (91/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2953/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (91/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2953/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (91/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2953/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (91/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2953/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (91/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (91/800 : ℝ) ^ (4405/1024 : ℝ) ≤ (8688235465390883/100000000000000000000 : ℝ) := by
    have hpowers : (91/800 : ℝ)^4405 ≤ (8688235465390883/100000000000000000000 : ℝ)^1024 := by
      have hnat : (91 : ℕ)^4405*100000000000000000000^1024 ≤ 8688235465390883^1024*800^4405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91 800 8688235465390883 100000000000000000000 4405 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (91/800 : ℝ)) (X := (8688235465390883/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2953/20000 : ℝ) ^ (4405/1024 : ℝ) ≤ (26683543905705993/100000000000000000000 : ℝ) := by
    have hpowers : (2953/20000 : ℝ)^4405 ≤ (26683543905705993/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2953 : ℕ)^4405*100000000000000000000^1024 ≤ 26683543905705993^1024*20000^4405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2953 20000 26683543905705993 100000000000000000000 4405 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2953/20000 : ℝ)) (X := (26683543905705993/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008688235465390883/50000000000000000000 : ℝ) ≤ (5000201955956723/5000000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (50008688235465390883/50000000000000000000 : ℝ)^1024 ≤ (5000201955956723/5000000000000000 : ℝ)^4405 := by
      have hnat : (50008688235465390883 : ℕ)^1024*5000000000000000^4405 ≤ 5000201955956723^4405*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008688235465390883 50000000000000000000 5000201955956723 5000000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000201955956723/5000000000000000 : ℝ)) (X := (50008688235465390883/50000000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008842944842774219/25000000000000000000 : ℝ) ≤ (250020553794719/250000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (25008842944842774219/25000000000000000000 : ℝ)^1024 ≤ (250020553794719/250000000000000 : ℝ)^4405 := by
      have hnat : (25008842944842774219 : ℕ)^1024*250000000000000^4405 ≤ 250020553794719^4405*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008842944842774219 25000000000000000000 250020553794719 250000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250020553794719/250000000000000 : ℝ)) (X := (25008842944842774219/25000000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026683543905705993/50000000000000000000 : ℝ) ≤ (5000620195832037/5000000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (50026683543905705993/50000000000000000000 : ℝ)^1024 ≤ (5000620195832037/5000000000000000 : ℝ)^4405 := by
      have hnat : (50026683543905705993 : ℕ)^1024*5000000000000000^4405 ≤ 5000620195832037^4405*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026683543905705993 50000000000000000000 5000620195832037 5000000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000620195832037/5000000000000000 : ℝ)) (X := (50026683543905705993/50000000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8688235465390883/100000000000000000000 : ℝ) ≤ ((847296357605579711/847500000000000000 : ℝ)+2*(209119937657/169500000000000 : ℝ)*(91/800 : ℝ))^(4405/1024 : ℝ) := by
    rw [show (847296357605579711/847500000000000000 : ℝ)+2*(209119937657/169500000000000 : ℝ)*(91/800 : ℝ)=(5000201955956723/5000000000000000 : ℝ) by norm_num, show 1+2*(8688235465390883/100000000000000000000 : ℝ)=(50008688235465390883/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26683543905705993/100000000000000000000 : ℝ)+(8688235465390883/100000000000000000000 : ℝ) ≤ ((847296357605579711/847500000000000000 : ℝ)+(209119937657/169500000000000 : ℝ)*((2953/20000 : ℝ)+(91/800 : ℝ)))^(4405/1024 : ℝ) := by
    rw [show (847296357605579711/847500000000000000 : ℝ)+(209119937657/169500000000000 : ℝ)*((2953/20000 : ℝ)+(91/800 : ℝ))=(250020553794719/250000000000000 : ℝ) by norm_num, show 1+(26683543905705993/100000000000000000000 : ℝ)+(8688235465390883/100000000000000000000 : ℝ)=(25008842944842774219/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26683543905705993/100000000000000000000 : ℝ) ≤ ((847296357605579711/847500000000000000 : ℝ)+2*(209119937657/169500000000000 : ℝ)*(2953/20000 : ℝ))^(4405/1024 : ℝ) := by
    rw [show (847296357605579711/847500000000000000 : ℝ)+2*(209119937657/169500000000000 : ℝ)*(2953/20000 : ℝ)=(5000620195832037/5000000000000000 : ℝ) by norm_num, show 1+2*(26683543905705993/100000000000000000000 : ℝ)=(50026683543905705993/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (847296357605579711/847500000000000000 : ℝ)*(X 1 0+X 2 0)+(209119937657/169500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (91/800 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (847296357605579711/847500000000000000 : ℝ)) (alpha := (209119937657/169500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (847296357605579711/847500000000000000 : ℝ)*(X 0 1+X 2 1)+(209119937657/169500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (91/800 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (847296357605579711/847500000000000000 : ℝ)) (alpha := (209119937657/169500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (847296357605579711/847500000000000000 : ℝ)*(X 0 2+X 1 2)+(209119937657/169500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (91/800 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (847296357605579711/847500000000000000 : ℝ)) (alpha := (209119937657/169500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-898991061/5000000000 : ℝ)*X 0 0+(673190737/1250000000 : ℝ)*X 0 1+(1346381361/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((660772089/1250000000 : ℝ)*X 1 0+(-1934541519/10000000000 : ℝ)*X 1 1+(5385525273/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5286176301/10000000000 : ℝ)*X 2 0+(5385525799/10000000000 : ℝ)*X 2 1+(-1934541359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4446101839/10000000000 : ℝ)*X 0 0+(528854781/1250000000 : ℝ)*X 0 1+(4230837879/10000000000 : ℝ)*X 0 2+(4446101839/10000000000 : ℝ)*X 1 0+(528854781/1250000000 : ℝ)*X 1 1+(4230837879/10000000000 : ℝ)*X 1 2+(4446101839/10000000000 : ℝ)*X 2 0+(528854781/1250000000 : ℝ)*X 2 1+(4230837879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-105979679/500000000 : ℝ)*X 0 0+(5266766599/10000000000 : ℝ)*X 0 1+(5266767523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2684616313/5000000000 : ℝ)*X 1 0+(-991431757/5000000000 : ℝ)*X 1 1+(5266767131/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((536923217/1000000000 : ℝ)*X 2 0+(2633383829/5000000000 : ℝ)*X 2 1+(-30982241/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4153111409/10000000000 : ℝ)*X 0 0+(4377283013/10000000000 : ℝ)*X 0 1+(547160341/1250000000 : ℝ)*X 0 2+(4153111409/10000000000 : ℝ)*X 1 0+(4377283013/10000000000 : ℝ)*X 1 1+(547160341/1250000000 : ℝ)*X 1 2+(4153111409/10000000000 : ℝ)*X 2 0+(4377283013/10000000000 : ℝ)*X 2 1+(547160341/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2051816207/10000000000 : ℝ)*X 0 0+(1296136869/2500000000 : ℝ)*X 0 1+(5399488839/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1319101909/2500000000 : ℝ)*X 1 0+(-241091813/1250000000 : ℝ)*X 1 1+(5399488439/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276407163/10000000000 : ℝ)*X 2 0+(2699744297/5000000000 : ℝ)*X 2 1+(-964367467/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4479993737/10000000000 : ℝ)*X 0 0+(1053401331/2500000000 : ℝ)*X 0 1+(842720977/2000000000 : ℝ)*X 0 2+(4479993737/10000000000 : ℝ)*X 1 0+(1053401331/2500000000 : ℝ)*X 1 1+(842720977/2000000000 : ℝ)*X 1 2+(4479993737/10000000000 : ℝ)*X 2 0+(1053401331/2500000000 : ℝ)*X 2 1+(842720977/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1865911339/10000000000 : ℝ)*X 0 0+(1093150807/2000000000 : ℝ)*X 0 1+(5255633363/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1344254339/2500000000 : ℝ)*X 1 0+(-993647677/5000000000 : ℝ)*X 1 1+(42045067/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5377017377/10000000000 : ℝ)*X 2 0+(5255633359/10000000000 : ℝ)*X 2 1+(-993647673/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((412519281/1000000000 : ℝ)*X 0 0+(4391001219/10000000000 : ℝ)*X 0 1+(1097750309/2500000000 : ℝ)*X 0 2+(412519281/1000000000 : ℝ)*X 1 0+(4391001219/10000000000 : ℝ)*X 1 1+(1097750309/2500000000 : ℝ)*X 1 2+(412519281/1000000000 : ℝ)*X 2 0+(4391001219/10000000000 : ℝ)*X 2 1+(1097750309/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-6291/10000 : ℝ) ≤ (-555357298783899467712868728561/882812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (250340867/100000000000000 : ℝ)*(lower0) + (221425061/100000000000000 : ℝ)*(lower3) + (84706427/50000000000000 : ℝ)*(lower4) + (758829904201327/25000000000000 : ℝ)*(major0) + (758829904201327/25000000000000 : ℝ)*(major1) + (758829904201327/25000000000000 : ℝ)*(major2) + (2090342132333971/50000000000000 : ℝ)*(sp4) + (418063258198027/10000000000000 : ℝ)*(sp5) + (4180605320184099/100000000000000 : ℝ)*(sp6) + (955428689863999/50000000000000 : ℝ)*(sp7) + (4973068309/100000000000000 : ℝ)*(sp12) + (28327877991/50000000000000 : ℝ)*(sp13) + (10489694019/12500000000000 : ℝ)*(sp14) + (1546482157/2500000000000 : ℝ)*(sp15) + (955459619507139/50000000000000 : ℝ)*(f.failure) + (4180689237736251/100000000000000 : ℝ)*(f.sum) + (14725887523369/8475000000000000000000000000 : ℝ)*base66 + (110716486435452999/7062500000000000000000000000000 : ℝ)*base67 + (50776469174827999/7062500000000000000000000000000 : ℝ)*base69 + (55237941269765499/7062500000000000000000000000000 : ℝ)*base71 + (36178744712747/4237500000000000000000000000 : ℝ)*base74 + (14328225070859501/7062500000000000000000000000000 : ℝ)*base76 + (101893540020640499/7062500000000000000000000000000 : ℝ)*base77 + (83218906561640499/7062500000000000000000000000000 : ℝ)*base79 + (688468816561/2118750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (20950271/5000000000000000000000 : ℝ)*base90 + (20950271/5000000000000000000000 : ℝ)*base92 + (20950271/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59147/100000 : ℝ) ≤ (2088732735140493406213432501587/3531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (86380207/100000000000000 : ℝ)*(upper3) + (11490499/50000000000000 : ℝ)*(upper4) + (534327/1562500000000 : ℝ)*(lower5) + (776878320653661/25000000000000 : ℝ)*(major0) + (776878320653661/25000000000000 : ℝ)*(major1) + (776878320653661/25000000000000 : ℝ)*(major2) + (2119467151511383/50000000000000 : ℝ)*(sp0) + (264926282987793/6250000000000 : ℝ)*(sp1) + (2119465349833121/50000000000000 : ℝ)*(sp2) + (391273632095617/20000000000000 : ℝ)*(sp3) + (9649746379/100000000000000 : ℝ)*(sp6) + (7020757/500000000000 : ℝ)*(sp7) + (188949683/3125000000000 : ℝ)*(sp8) + (59910803967/50000000000000 : ℝ)*(sp9) + (391273912925897/20000000000000 : ℝ)*(f.failure) + (2119470174706311/50000000000000 : ℝ)*(f.sum) + (9918514557539/2825000000000000000000000000 : ℝ)*base66 + (121888516194285657/7062500000000000000000000000000 : ℝ)*base67 + (63971346956598157/7062500000000000000000000000000 : ℝ)*base69 + (67994467650598157/7062500000000000000000000000000 : ℝ)*base71 + (5270524243659/706250000000000000000000000 : ℝ)*base73 + (47469960049973157/7062500000000000000000000000000 : ℝ)*base75 + (92062525569598157/7062500000000000000000000000000 : ℝ)*base77 + (124764112311535657/7062500000000000000000000000000 : ℝ)*base79 + (7406866580289/2825000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (17617533/2000000000000000000000 : ℝ)*base90 + (17617533/2000000000000000000000 : ℝ)*base92 + (17617533/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40271/50000 : ℝ) ≤ (227537398627279322694451799231/282500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (227287/200000000000 : ℝ)*(upper1) + (220222389/100000000000000 : ℝ)*(upper2) + (90340721/50000000000000 : ℝ)*(lower5) + (68288762997679/2000000000000 : ℝ)*(major0) + (68288762997679/2000000000000 : ℝ)*(major1) + (68288762997679/2000000000000 : ℝ)*(major2) + (178928251/25000000000000 : ℝ)*(sp1) + (549453481/100000000000000 : ℝ)*(sp2) + (47318579849/100000000000000 : ℝ)*(sp3) + (5534385343/100000000000000 : ℝ)*(sp4) + (465242516475059/10000000000000 : ℝ)*(sp8) + (4652429983422929/100000000000000 : ℝ)*(sp9) + (1163107537420613/25000000000000 : ℝ)*(sp10) + (107477510570881/5000000000000 : ℝ)*(sp11) + (214959752999747/10000000000000 : ℝ)*(f.failure) + (4652430699135933/100000000000000 : ℝ)*(f.sum) + (794193792847/339000000000000000000000000 : ℝ)*base65 + (8182623169116923/565000000000000000000000000000 : ℝ)*base67 + (2782281908048077/565000000000000000000000000000 : ℝ)*base70 + (4030780438206923/565000000000000000000000000000 : ℝ)*base71 + (1881503323373/169500000000000000000000000 : ℝ)*base73 + (6644897359108077/565000000000000000000000000000 : ℝ)*base76 + (3206496985981923/565000000000000000000000000000 : ℝ)*base77 + (6199337845966923/565000000000000000000000000000 : ℝ)*base79 + (21168597083/33900000000000000000000000 : ℝ)*base82 + (3725183/1000000000000000000000 : ℝ)*base90 + (3725183/1000000000000000000000 : ℝ)*base92 + (3725183/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-21187/25000 : ℝ) ≤ (-5985168675591930263535232577757/7062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2198313/100000000000000 : ℝ)*(lower1) + (1214907/25000000000000 : ℝ)*(lower2) + (8226597/100000000000000 : ℝ)*(upper5) + (138084862046681/4000000000000 : ℝ)*(major0) + (138084862046681/4000000000000 : ℝ)*(major1) + (1726060775583513/50000000000000 : ℝ)*(major2) + (59925483/100000000000000 : ℝ)*(sp0) + (6595365689/100000000000000 : ℝ)*(sp6) + (2892292327/100000000000000 : ℝ)*(sp7) + (47518283/25000000000000 : ℝ)*(sp8) + (4759169901473459/100000000000000 : ℝ)*(sp12) + (4759170151472073/100000000000000 : ℝ)*(sp13) + (297447722256649/6250000000000 : ℝ)*(sp14) + (543329660572313/25000000000000 : ℝ)*(sp15) + (2173321534581579/100000000000000 : ℝ)*(f.failure) + (4759170151472073/100000000000000 : ℝ)*(f.sum) + (129375490944893/16950000000000000000000000000 : ℝ)*base66 + (40217786994454409/3390000000000000000000000000000 : ℝ)*base68 + (48887806184407757/42375000000000000000000000000000 : ℝ)*base70 + (10571475233215591/3390000000000000000000000000000 : ℝ)*base71 + (116382817360643/16950000000000000000000000000 : ℝ)*base74 + (48530184829657757/42375000000000000000000000000000 : ℝ)*base76 + (3328142779738603/1130000000000000000000000000000 : ℝ)*base78 + (3367555947781397/1130000000000000000000000000000 : ℝ)*base79 + (94934716703/13560000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (54020569/10000000000000000000000 : ℝ)*base89 + (54020569/10000000000000000000000 : ℝ)*base91 + (45979431/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1446_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6291/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(59147/100000 : ℝ) else (40271/50000 : ℝ) ≤ X j i ∧ X j i ≤ (21187/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1446_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1446_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6291/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(59147/100000 : ℝ) else (40271/50000 : ℝ) ≤ X j i ∧ X j i ≤ (21187/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1446_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1446_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1446_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6291/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(59147/100000 : ℝ) else (40271/50000 : ℝ) ≤ X j i ∧ X j i ≤ (21187/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1446_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

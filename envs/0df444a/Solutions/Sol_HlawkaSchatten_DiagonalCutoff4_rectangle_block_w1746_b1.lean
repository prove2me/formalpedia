-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1746_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:17:59.236027+00:00
-- url     : https://prove2.me/submissions/ab4ad796-ee2c-4237-a391-b00baca3aa70

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
theorem support_rectangle_w1746_s3_0 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-24896623/200000000 : ℝ)*x 0 + (5502467843/10000000000 : ℝ)*x 1 + (5079903603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24896623/200000000 : ℝ)^5711 ≤ (246753454963/3125000000000 : ℝ)^4687 := by
    have hnat : (24896623 : ℕ)^5711*3125000000000^4687 ≤ 246753454963^4687*200000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24896623 200000000 246753454963 3125000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5502467843/10000000000 : ℝ)^5711 ≤ (754562845857/1562500000000 : ℝ)^4687 := by
    have hnat : (5502467843 : ℕ)^5711*1562500000000^4687 ≤ 754562845857^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502467843 10000000000 754562845857 1562500000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5079903603/10000000000 : ℝ)^5711 ≤ (21905933646667/50000000000000 : ℝ)^4687 := by
    have hnat : (5079903603 : ℕ)^5711*50000000000000^4687 ≤ 21905933646667^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5079903603 10000000000 21905933646667 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-24896623/200000000 : ℝ), (5502467843/10000000000 : ℝ), (5079903603/10000000000 : ℝ)] ![(246753454963/3125000000000 : ℝ), (754562845857/1562500000000 : ℝ), (21905933646667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-24896623/200000000 : ℝ)|^5711 ≤ (246753454963/3125000000000 : ℝ)^4687
        have hw : |(-24896623/200000000 : ℝ)|=(24896623/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5502467843/10000000000 : ℝ)|^5711 ≤ (754562845857/1562500000000 : ℝ)^4687
        have hw : |(5502467843/10000000000 : ℝ)|=(5502467843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5079903603/10000000000 : ℝ)|^5711 ≤ (21905933646667/50000000000000 : ℝ)^4687
        have hw : |(5079903603/10000000000 : ℝ)|=(5079903603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s3_1 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5339088867/10000000000 : ℝ)*x 0 + (-733018231/5000000000 : ℝ)*x 1 + (1269975857/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5339088867/10000000000 : ℝ)^5711 ≤ (23275289589123/50000000000000 : ℝ)^4687 := by
    have hnat : (5339088867 : ℕ)^5711*50000000000000^4687 ≤ 23275289589123^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5339088867 10000000000 23275289589123 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (733018231/5000000000 : ℝ)^5711 ≤ (2409388838243/25000000000000 : ℝ)^4687 := by
    have hnat : (733018231 : ℕ)^5711*25000000000000^4687 ≤ 2409388838243^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733018231 5000000000 2409388838243 25000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1269975857/2500000000 : ℝ)^5711 ≤ (10952966363573/25000000000000 : ℝ)^4687 := by
    have hnat : (1269975857 : ℕ)^5711*25000000000000^4687 ≤ 10952966363573^4687*2500000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269975857 2500000000 10952966363573 25000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5339088867/10000000000 : ℝ), (-733018231/5000000000 : ℝ), (1269975857/2500000000 : ℝ)] ![(23275289589123/50000000000000 : ℝ), (2409388838243/25000000000000 : ℝ), (10952966363573/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5339088867/10000000000 : ℝ)|^5711 ≤ (23275289589123/50000000000000 : ℝ)^4687
        have hw : |(5339088867/10000000000 : ℝ)|=(5339088867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-733018231/5000000000 : ℝ)|^5711 ≤ (2409388838243/25000000000000 : ℝ)^4687
        have hw : |(-733018231/5000000000 : ℝ)|=(733018231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1269975857/2500000000 : ℝ)|^5711 ≤ (10952966363573/25000000000000 : ℝ)^4687
        have hw : |(1269975857/2500000000 : ℝ)|=(1269975857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s3_2 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5339088717/10000000000 : ℝ)*x 0 + (5079903681/10000000000 : ℝ)*x 1 + (-1466036329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5339088717/10000000000 : ℝ)^5711 ≤ (23275288792347/50000000000000 : ℝ)^4687 := by
    have hnat : (5339088717 : ℕ)^5711*50000000000000^4687 ≤ 23275288792347^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5339088717 10000000000 23275288792347 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5079903681/10000000000 : ℝ)^5711 ≤ (43811868113021/100000000000000 : ℝ)^4687 := by
    have hnat : (5079903681 : ℕ)^5711*100000000000000^4687 ≤ 43811868113021^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5079903681 10000000000 43811868113021 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1466036329/10000000000 : ℝ)^5711 ≤ (77100434301/800000000000 : ℝ)^4687 := by
    have hnat : (1466036329 : ℕ)^5711*800000000000^4687 ≤ 77100434301^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1466036329 10000000000 77100434301 800000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5339088717/10000000000 : ℝ), (5079903681/10000000000 : ℝ), (-1466036329/10000000000 : ℝ)] ![(23275288792347/50000000000000 : ℝ), (43811868113021/100000000000000 : ℝ), (77100434301/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5339088717/10000000000 : ℝ)|^5711 ≤ (23275288792347/50000000000000 : ℝ)^4687
        have hw : |(5339088717/10000000000 : ℝ)|=(5339088717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5079903681/10000000000 : ℝ)|^5711 ≤ (43811868113021/100000000000000 : ℝ)^4687
        have hw : |(5079903681/10000000000 : ℝ)|=(5079903681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1466036329/10000000000 : ℝ)|^5711 ≤ (77100434301/800000000000 : ℝ)^4687
        have hw : |(-1466036329/10000000000 : ℝ)|=(1466036329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s3_3 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2014652709/5000000000 : ℝ)*x 0 + (3378516203/10000000000 : ℝ)*x 1 + (1186059197/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2014652709/5000000000 : ℝ)^5711 ≤ (33035600583187/100000000000000 : ℝ)^4687 := by
    have hnat : (2014652709 : ℕ)^5711*100000000000000^4687 ≤ 33035600583187^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014652709 5000000000 33035600583187 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3378516203/10000000000 : ℝ)^5711 ≤ (13327038517151/50000000000000 : ℝ)^4687 := by
    have hnat : (3378516203 : ℕ)^5711*50000000000000^4687 ≤ 13327038517151^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3378516203 10000000000 13327038517151 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1186059197/2500000000 : ℝ)^5711 ≤ (322482578989/800000000000 : ℝ)^4687 := by
    have hnat : (1186059197 : ℕ)^5711*800000000000^4687 ≤ 322482578989^4687*2500000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1186059197 2500000000 322482578989 800000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2014652709/5000000000 : ℝ), (3378516203/10000000000 : ℝ), (1186059197/2500000000 : ℝ)] ![(33035600583187/100000000000000 : ℝ), (13327038517151/50000000000000 : ℝ), (322482578989/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2014652709/5000000000 : ℝ)|^5711 ≤ (33035600583187/100000000000000 : ℝ)^4687
        have hw : |(2014652709/5000000000 : ℝ)|=(2014652709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3378516203/10000000000 : ℝ)|^5711 ≤ (13327038517151/50000000000000 : ℝ)^4687
        have hw : |(3378516203/10000000000 : ℝ)|=(3378516203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1186059197/2500000000 : ℝ)|^5711 ≤ (322482578989/800000000000 : ℝ)^4687
        have hw : |(1186059197/2500000000 : ℝ)|=(1186059197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s3_4 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-38912201/312500000 : ℝ)*x 0 + (508673163/1000000000 : ℝ)*x 1 + (171734261/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38912201/312500000 : ℝ)^5711 ≤ (3949443757831/50000000000000 : ℝ)^4687 := by
    have hnat : (38912201 : ℕ)^5711*50000000000000^4687 ≤ 3949443757831^4687*312500000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38912201 312500000 3949443757831 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508673163/1000000000 : ℝ)^5711 ≤ (43883632256993/100000000000000 : ℝ)^4687 := by
    have hnat : (508673163 : ℕ)^5711*100000000000000^4687 ≤ 43883632256993^4687*1000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508673163 1000000000 43883632256993 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171734261/312500000 : ℝ)^5711 ≤ (385739841651/800000000000 : ℝ)^4687 := by
    have hnat : (171734261 : ℕ)^5711*800000000000^4687 ≤ 385739841651^4687*312500000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171734261 312500000 385739841651 800000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38912201/312500000 : ℝ), (508673163/1000000000 : ℝ), (171734261/312500000 : ℝ)] ![(3949443757831/50000000000000 : ℝ), (43883632256993/100000000000000 : ℝ), (385739841651/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38912201/312500000 : ℝ)|^5711 ≤ (3949443757831/50000000000000 : ℝ)^4687
        have hw : |(-38912201/312500000 : ℝ)|=(38912201/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(508673163/1000000000 : ℝ)|^5711 ≤ (43883632256993/100000000000000 : ℝ)^4687
        have hw : |(508673163/1000000000 : ℝ)|=(508673163/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(171734261/312500000 : ℝ)|^5711 ≤ (385739841651/800000000000 : ℝ)^4687
        have hw : |(171734261/312500000 : ℝ)|=(171734261/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s3_5 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (81671197/156250000 : ℝ)*x 0 + (-1050443483/10000000000 : ℝ)*x 1 + (2747748171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81671197/156250000 : ℝ)^5711 ≤ (2835129350671/6250000000000 : ℝ)^4687 := by
    have hnat : (81671197 : ℕ)^5711*6250000000000^4687 ≤ 2835129350671^4687*156250000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81671197 156250000 2835129350671 6250000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050443483/10000000000 : ℝ)^5711 ≤ (25079883909/390625000000 : ℝ)^4687 := by
    have hnat : (1050443483 : ℕ)^5711*390625000000^4687 ≤ 25079883909^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050443483 10000000000 25079883909 390625000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2747748171/5000000000 : ℝ)^5711 ≤ (24108740049733/50000000000000 : ℝ)^4687 := by
    have hnat : (2747748171 : ℕ)^5711*50000000000000^4687 ≤ 24108740049733^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747748171 5000000000 24108740049733 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(81671197/156250000 : ℝ), (-1050443483/10000000000 : ℝ), (2747748171/5000000000 : ℝ)] ![(2835129350671/6250000000000 : ℝ), (25079883909/390625000000 : ℝ), (24108740049733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(81671197/156250000 : ℝ)|^5711 ≤ (2835129350671/6250000000000 : ℝ)^4687
        have hw : |(81671197/156250000 : ℝ)|=(81671197/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1050443483/10000000000 : ℝ)|^5711 ≤ (25079883909/390625000000 : ℝ)^4687
        have hw : |(-1050443483/10000000000 : ℝ)|=(1050443483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2747748171/5000000000 : ℝ)|^5711 ≤ (24108740049733/50000000000000 : ℝ)^4687
        have hw : |(2747748171/5000000000 : ℝ)|=(2747748171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s3_6 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (522695657/1000000000 : ℝ)*x 0 + (2747748199/5000000000 : ℝ)*x 1 + (-16413179/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522695657/1000000000 : ℝ)^5711 ≤ (45362069208903/100000000000000 : ℝ)^4687 := by
    have hnat : (522695657 : ℕ)^5711*100000000000000^4687 ≤ 45362069208903^4687*1000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522695657 1000000000 45362069208903 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2747748199/5000000000 : ℝ)^5711 ≤ (48217480698157/100000000000000 : ℝ)^4687 := by
    have hnat : (2747748199 : ℕ)^5711*100000000000000^4687 ≤ 48217480698157^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747748199 5000000000 48217480698157 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16413179/156250000 : ℝ)^5711 ≤ (6420450079621/100000000000000 : ℝ)^4687 := by
    have hnat : (16413179 : ℕ)^5711*100000000000000^4687 ≤ 6420450079621^4687*156250000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16413179 156250000 6420450079621 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522695657/1000000000 : ℝ), (2747748199/5000000000 : ℝ), (-16413179/156250000 : ℝ)] ![(45362069208903/100000000000000 : ℝ), (48217480698157/100000000000000 : ℝ), (6420450079621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522695657/1000000000 : ℝ)|^5711 ≤ (45362069208903/100000000000000 : ℝ)^4687
        have hw : |(522695657/1000000000 : ℝ)|=(522695657/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2747748199/5000000000 : ℝ)|^5711 ≤ (48217480698157/100000000000000 : ℝ)^4687
        have hw : |(2747748199/5000000000 : ℝ)|=(2747748199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16413179/156250000 : ℝ)|^5711 ≤ (6420450079621/100000000000000 : ℝ)^4687
        have hw : |(-16413179/156250000 : ℝ)|=(16413179/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s3_7 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4030466819/10000000000 : ℝ)*x 0 + (4722169073/10000000000 : ℝ)*x 1 + (3401047459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4030466819/10000000000 : ℝ)^5711 ≤ (33047203444317/100000000000000 : ℝ)^4687 := by
    have hnat : (4030466819 : ℕ)^5711*100000000000000^4687 ≤ 33047203444317^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030466819 10000000000 33047203444317 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4722169073/10000000000 : ℝ)^5711 ≤ (2505123192051/6250000000000 : ℝ)^4687 := by
    have hnat : (4722169073 : ℕ)^5711*6250000000000^4687 ≤ 2505123192051^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4722169073 10000000000 2505123192051 6250000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3401047459/10000000000 : ℝ)^5711 ≤ (13435412735897/50000000000000 : ℝ)^4687 := by
    have hnat : (3401047459 : ℕ)^5711*50000000000000^4687 ≤ 13435412735897^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3401047459 10000000000 13435412735897 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4030466819/10000000000 : ℝ), (4722169073/10000000000 : ℝ), (3401047459/10000000000 : ℝ)] ![(33047203444317/100000000000000 : ℝ), (2505123192051/6250000000000 : ℝ), (13435412735897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4030466819/10000000000 : ℝ)|^5711 ≤ (33047203444317/100000000000000 : ℝ)^4687
        have hw : |(4030466819/10000000000 : ℝ)|=(4030466819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4722169073/10000000000 : ℝ)|^5711 ≤ (2505123192051/6250000000000 : ℝ)^4687
        have hw : |(4722169073/10000000000 : ℝ)|=(4722169073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3401047459/10000000000 : ℝ)|^5711 ≤ (13435412735897/50000000000000 : ℝ)^4687
        have hw : |(3401047459/10000000000 : ℝ)|=(3401047459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1746_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (211599271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3611/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4493/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (8987/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18053/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3611/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4493/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3611/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4493/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3611/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4493/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3611/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4493/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3611/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4493/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3611/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4493/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4493/50000 : ℝ) ^ (5695/1024 : ℝ) ≤ (151438077312593/100000000000000000000 : ℝ) := by
    have hpowers : (4493/50000 : ℝ)^5695 ≤ (151438077312593/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4493 : ℕ)^5695*100000000000000000000^1024 ≤ 151438077312593^1024*50000^5695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4493 50000 151438077312593 100000000000000000000 5695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4493/50000 : ℝ)) (X := (151438077312593/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3611/20000 : ℝ) ^ (5695/1024 : ℝ) ≤ (7337523961659087/100000000000000000000 : ℝ) := by
    have hpowers : (3611/20000 : ℝ)^5695 ≤ (7337523961659087/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3611 : ℕ)^5695*100000000000000000000^1024 ≤ 7337523961659087^1024*20000^5695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3611 20000 7337523961659087 100000000000000000000 5695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3611/20000 : ℝ)) (X := (7337523961659087/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000151438077312593/50000000000000000000 : ℝ) ≤ (10000005445913909/10000000000000000 : ℝ) ^ (5695/1024 : ℝ) := by
    have hpowers : (50000151438077312593/50000000000000000000 : ℝ)^1024 ≤ (10000005445913909/10000000000000000 : ℝ)^5695 := by
      have hnat : (50000151438077312593 : ℕ)^1024*10000000000000000^5695 ≤ 10000005445913909^5695*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000151438077312593 50000000000000000000 10000005445913909 10000000000000000 1024 5695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000005445913909/10000000000000000 : ℝ)) (X := (50000151438077312593/50000000000000000000 : ℝ)) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (625046806012743573/625000000000000000 : ℝ) ≤ (5000067326265301/5000000000000000 : ℝ) ^ (5695/1024 : ℝ) := by
    have hpowers : (625046806012743573/625000000000000000 : ℝ)^1024 ≤ (5000067326265301/5000000000000000 : ℝ)^5695 := by
      have hnat : (625046806012743573 : ℕ)^1024*5000000000000000^5695 ≤ 5000067326265301^5695*625000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625046806012743573 625000000000000000 5000067326265301 5000000000000000 1024 5695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000067326265301/5000000000000000 : ℝ)) (X := (625046806012743573/625000000000000000 : ℝ)) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50007337523961659087/50000000000000000000 : ℝ) ≤ (2000052771829459/2000000000000000 : ℝ) ^ (5695/1024 : ℝ) := by
    have hpowers : (50007337523961659087/50000000000000000000 : ℝ)^1024 ≤ (2000052771829459/2000000000000000 : ℝ)^5695 := by
      have hnat : (50007337523961659087 : ℕ)^1024*2000000000000000^5695 ≤ 2000052771829459^5695*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50007337523961659087 50000000000000000000 2000052771829459 2000000000000000 1024 5695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000052771829459/2000000000000000 : ℝ)) (X := (50007337523961659087/50000000000000000000 : ℝ)) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(151438077312593/100000000000000000000 : ℝ) ≤ ((241833939433808091/241840000000000000 : ℝ)+2*(43068872231/302300000000000 : ℝ)*(4493/50000 : ℝ))^(5695/1024 : ℝ) := by
    rw [show (241833939433808091/241840000000000000 : ℝ)+2*(43068872231/302300000000000 : ℝ)*(4493/50000 : ℝ)=(10000005445913909/10000000000000000 : ℝ) by norm_num, show 1+2*(151438077312593/100000000000000000000 : ℝ)=(50000151438077312593/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7337523961659087/100000000000000000000 : ℝ)+(151438077312593/100000000000000000000 : ℝ) ≤ ((241833939433808091/241840000000000000 : ℝ)+(43068872231/302300000000000 : ℝ)*((3611/20000 : ℝ)+(4493/50000 : ℝ)))^(5695/1024 : ℝ) := by
    rw [show (241833939433808091/241840000000000000 : ℝ)+(43068872231/302300000000000 : ℝ)*((3611/20000 : ℝ)+(4493/50000 : ℝ))=(5000067326265301/5000000000000000 : ℝ) by norm_num, show 1+(7337523961659087/100000000000000000000 : ℝ)+(151438077312593/100000000000000000000 : ℝ)=(625046806012743573/625000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7337523961659087/100000000000000000000 : ℝ) ≤ ((241833939433808091/241840000000000000 : ℝ)+2*(43068872231/302300000000000 : ℝ)*(3611/20000 : ℝ))^(5695/1024 : ℝ) := by
    rw [show (241833939433808091/241840000000000000 : ℝ)+2*(43068872231/302300000000000 : ℝ)*(3611/20000 : ℝ)=(2000052771829459/2000000000000000 : ℝ) by norm_num, show 1+2*(7337523961659087/100000000000000000000 : ℝ)=(50007337523961659087/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (241833939433808091/241840000000000000 : ℝ)*(X 1 0+X 2 0)+(43068872231/302300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5695/1024 : ℝ)) (lo := (4493/50000 : ℝ)) (hi := (3611/20000 : ℝ)) (c := (241833939433808091/241840000000000000 : ℝ)) (alpha := (43068872231/302300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (241833939433808091/241840000000000000 : ℝ)*(X 0 1+X 2 1)+(43068872231/302300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5695/1024 : ℝ)) (lo := (4493/50000 : ℝ)) (hi := (3611/20000 : ℝ)) (c := (241833939433808091/241840000000000000 : ℝ)) (alpha := (43068872231/302300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (241833939433808091/241840000000000000 : ℝ)*(X 0 2+X 1 2)+(43068872231/302300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5695/1024 : ℝ)) (lo := (4493/50000 : ℝ)) (hi := (3611/20000 : ℝ)) (c := (241833939433808091/241840000000000000 : ℝ)) (alpha := (43068872231/302300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-24896623/200000000 : ℝ)*X 0 0+(5502467843/10000000000 : ℝ)*X 0 1+(5079903603/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5339088867/10000000000 : ℝ)*X 1 0+(-733018231/5000000000 : ℝ)*X 1 1+(1269975857/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5339088717/10000000000 : ℝ)*X 2 0+(5079903681/10000000000 : ℝ)*X 2 1+(-1466036329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2014652709/5000000000 : ℝ)*X 0 0+(3378516203/10000000000 : ℝ)*X 0 1+(1186059197/2500000000 : ℝ)*X 0 2+(2014652709/5000000000 : ℝ)*X 1 0+(3378516203/10000000000 : ℝ)*X 1 1+(1186059197/2500000000 : ℝ)*X 1 2+(2014652709/5000000000 : ℝ)*X 2 0+(3378516203/10000000000 : ℝ)*X 2 1+(1186059197/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-38912201/312500000 : ℝ)*X 0 0+(508673163/1000000000 : ℝ)*X 0 1+(171734261/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((81671197/156250000 : ℝ)*X 1 0+(-1050443483/10000000000 : ℝ)*X 1 1+(2747748171/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((522695657/1000000000 : ℝ)*X 2 0+(2747748199/5000000000 : ℝ)*X 2 1+(-16413179/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4030466819/10000000000 : ℝ)*X 0 0+(4722169073/10000000000 : ℝ)*X 0 1+(3401047459/10000000000 : ℝ)*X 0 2+(4030466819/10000000000 : ℝ)*X 1 0+(4722169073/10000000000 : ℝ)*X 1 1+(3401047459/10000000000 : ℝ)*X 1 2+(4030466819/10000000000 : ℝ)*X 2 0+(4722169073/10000000000 : ℝ)*X 2 1+(3401047459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (75473260364315281874537253/6046000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1668453613/100000000000000 : ℝ)*(base19) + (302246803/20000000000000 : ℝ)*(base23) + (12110759/25000000000000 : ℝ)*(lower2) + (258960007/100000000000000 : ℝ)*(upper3) + (253222627/100000000000000 : ℝ)*(upper5) + (774687563882661/50000000000000 : ℝ)*(major0) + (774687563882661/50000000000000 : ℝ)*(major1) + (774687563882661/50000000000000 : ℝ)*(major2) + (59162898063753/2500000000000 : ℝ)*(sp0) + (94661071155311/4000000000000 : ℝ)*(sp1) + (1183263468051187/50000000000000 : ℝ)*(sp2) + (91527210195917/12500000000000 : ℝ)*(sp3) + (12524786269/100000000000000 : ℝ)*(sp4) + (1855260583/50000000000000 : ℝ)*(sp7) + (366110696044251/50000000000000 : ℝ)*(f.failure) + (591632111834097/25000000000000 : ℝ)*(f.sum) + (7498704934241/1889375000000000000000000000 : ℝ)*base66 + (118220174730189049/12092000000000000000000000000000 : ℝ)*base68 + (18303063300842951/12092000000000000000000000000000 : ℝ)*base69 + (1530674244321049/12092000000000000000000000000000 : ℝ)*base72 + (26322638664179/7557500000000000000000000000 : ℝ)*base74 + (111080388548858951/12092000000000000000000000000000 : ℝ)*base75 + (125833389877757049/12092000000000000000000000000000 : ℝ)*base78 + (46969988132077049/12092000000000000000000000000000 : ℝ)*base80 + (33696557754021/7557500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (4658979/5000000000000000000000 : ℝ)*base90 + (4658979/5000000000000000000000 : ℝ)*base92 + (4658979/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5632458636830838929904477/1209200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4745549/800000000000 : ℝ)*(base19) + (324373523/50000000000000 : ℝ)*(base23) + (42285549/25000000000000 : ℝ)*(lower1) + (95615697/100000000000000 : ℝ)*(upper3) + (31539467/100000000000000 : ℝ)*(lower4) + (18626981/20000000000000 : ℝ)*(upper5) + (160166096098749/10000000000000 : ℝ)*(major0) + (160166096098749/10000000000000 : ℝ)*(major1) + (160166096098749/10000000000000 : ℝ)*(major2) + (12118453/2000000000000 : ℝ)*(sp2) + (1223195269219833/50000000000000 : ℝ)*(sp4) + (61159748631151/2500000000000 : ℝ)*(sp5) + (244638928376997/10000000000000 : ℝ)*(sp6) + (756931228268499/100000000000000 : ℝ)*(sp7) + (756931228268499/100000000000000 : ℝ)*(f.failure) + (1223195269219833/50000000000000 : ℝ)*(f.sum) + (2302813914751/3023000000000000000000000000 : ℝ)*base65 + (40354872664559/2418400000000000000000000000000 : ℝ)*base67 + (15604632005690159/2418400000000000000000000000000 : ℝ)*base69 + (135531763352825041/2418400000000000000000000000000 : ℝ)*base72 + (2186684952577/3023000000000000000000000000 : ℝ)*base73 + (15435259314873041/2418400000000000000000000000000 : ℝ)*base76 + (5146413300417041/2418400000000000000000000000000 : ℝ)*base78 + (547333570527441/2418400000000000000000000000000 : ℝ)*base80 + (1485984394001/604600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (19335771/10000000000000000000000 : ℝ)*base90 + (19335771/10000000000000000000000 : ℝ)*base92 + (19335771/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1746_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (211599271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3611/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4493/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8987/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18053/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1746_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1746_box_0 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-851393827/10000000000 : ℝ)*x 0 + (2714842173/5000000000 : ℝ)*x 1 + (2714842197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (851393827/10000000000 : ℝ)^5711 ≤ (994074654911/20000000000000 : ℝ)^4687 := by
    have hnat : (851393827 : ℕ)^5711*20000000000000^4687 ≤ 994074654911^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851393827 10000000000 994074654911 20000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714842173/5000000000 : ℝ)^5711 ≤ (47514813100709/100000000000000 : ℝ)^4687 := by
    have hnat : (2714842173 : ℕ)^5711*100000000000000^4687 ≤ 47514813100709^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714842173 5000000000 47514813100709 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714842197/5000000000 : ℝ)^5711 ≤ (11878703403131/25000000000000 : ℝ)^4687 := by
    have hnat : (2714842197 : ℕ)^5711*25000000000000^4687 ≤ 11878703403131^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714842197 5000000000 11878703403131 25000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-851393827/10000000000 : ℝ), (2714842173/5000000000 : ℝ), (2714842197/5000000000 : ℝ)] ![(994074654911/20000000000000 : ℝ), (47514813100709/100000000000000 : ℝ), (11878703403131/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-851393827/10000000000 : ℝ)|^5711 ≤ (994074654911/20000000000000 : ℝ)^4687
        have hw : |(-851393827/10000000000 : ℝ)|=(851393827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714842173/5000000000 : ℝ)|^5711 ≤ (47514813100709/100000000000000 : ℝ)^4687
        have hw : |(2714842173/5000000000 : ℝ)|=(2714842173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714842197/5000000000 : ℝ)|^5711 ≤ (11878703403131/25000000000000 : ℝ)^4687
        have hw : |(2714842197/5000000000 : ℝ)|=(2714842197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_box_1 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5194766387/10000000000 : ℝ)*x 0 + (-594274519/5000000000 : ℝ)*x 1 + (5429684413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5194766387/10000000000 : ℝ)^5711 ≤ (45021902443787/100000000000000 : ℝ)^4687 := by
    have hnat : (5194766387 : ℕ)^5711*100000000000000^4687 ≤ 45021902443787^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194766387 10000000000 45021902443787 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (594274519/5000000000 : ℝ)^5711 ≤ (3731641863033/50000000000000 : ℝ)^4687 := by
    have hnat : (594274519 : ℕ)^5711*50000000000000^4687 ≤ 3731641863033^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594274519 5000000000 3731641863033 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429684413/10000000000 : ℝ)^5711 ≤ (23757406907559/50000000000000 : ℝ)^4687 := by
    have hnat : (5429684413 : ℕ)^5711*50000000000000^4687 ≤ 23757406907559^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429684413 10000000000 23757406907559 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5194766387/10000000000 : ℝ), (-594274519/5000000000 : ℝ), (5429684413/10000000000 : ℝ)] ![(45021902443787/100000000000000 : ℝ), (3731641863033/50000000000000 : ℝ), (23757406907559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5194766387/10000000000 : ℝ)|^5711 ≤ (45021902443787/100000000000000 : ℝ)^4687
        have hw : |(5194766387/10000000000 : ℝ)|=(5194766387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-594274519/5000000000 : ℝ)|^5711 ≤ (3731641863033/50000000000000 : ℝ)^4687
        have hw : |(-594274519/5000000000 : ℝ)|=(594274519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429684413/10000000000 : ℝ)|^5711 ≤ (23757406907559/50000000000000 : ℝ)^4687
        have hw : |(5429684413/10000000000 : ℝ)|=(5429684413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_box_2 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5194766447/10000000000 : ℝ)*x 0 + (5429684379/10000000000 : ℝ)*x 1 + (-594274501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5194766447/10000000000 : ℝ)^5711 ≤ (45021903077403/100000000000000 : ℝ)^4687 := by
    have hnat : (5194766447 : ℕ)^5711*100000000000000^4687 ≤ 45021903077403^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194766447 10000000000 45021903077403 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429684379/10000000000 : ℝ)^5711 ≤ (23757406726291/50000000000000 : ℝ)^4687 := by
    have hnat : (5429684379 : ℕ)^5711*50000000000000^4687 ≤ 23757406726291^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429684379 10000000000 23757406726291 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (594274501/5000000000 : ℝ)^5711 ≤ (7463283450623/100000000000000 : ℝ)^4687 := by
    have hnat : (594274501 : ℕ)^5711*100000000000000^4687 ≤ 7463283450623^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594274501 5000000000 7463283450623 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5194766447/10000000000 : ℝ), (5429684379/10000000000 : ℝ), (-594274501/5000000000 : ℝ)] ![(45021903077403/100000000000000 : ℝ), (23757406726291/50000000000000 : ℝ), (7463283450623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5194766447/10000000000 : ℝ)|^5711 ≤ (45021903077403/100000000000000 : ℝ)^4687
        have hw : |(5194766447/10000000000 : ℝ)|=(5194766447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429684379/10000000000 : ℝ)|^5711 ≤ (23757406726291/50000000000000 : ℝ)^4687
        have hw : |(5429684379/10000000000 : ℝ)|=(5429684379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-594274501/5000000000 : ℝ)|^5711 ≤ (7463283450623/100000000000000 : ℝ)^4687
        have hw : |(-594274501/5000000000 : ℝ)|=(594274501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_box_3 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (911279549/2000000000 : ℝ)*x 0 + (3805439877/10000000000 : ℝ)*x 1 + (761087997/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (911279549/2000000000 : ℝ)^5711 ≤ (7674824002977/20000000000000 : ℝ)^4687 := by
    have hnat : (911279549 : ℕ)^5711*20000000000000^4687 ≤ 7674824002977^4687*2000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911279549 2000000000 7674824002977 20000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3805439877/10000000000 : ℝ)^5711 ≤ (6162587890719/20000000000000 : ℝ)^4687 := by
    have hnat : (3805439877 : ℕ)^5711*20000000000000^4687 ≤ 6162587890719^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3805439877 10000000000 6162587890719 20000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (761087997/2000000000 : ℝ)^5711 ≤ (30812940519133/100000000000000 : ℝ)^4687 := by
    have hnat : (761087997 : ℕ)^5711*100000000000000^4687 ≤ 30812940519133^4687*2000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      761087997 2000000000 30812940519133 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(911279549/2000000000 : ℝ), (3805439877/10000000000 : ℝ), (761087997/2000000000 : ℝ)] ![(7674824002977/20000000000000 : ℝ), (6162587890719/20000000000000 : ℝ), (30812940519133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(911279549/2000000000 : ℝ)|^5711 ≤ (7674824002977/20000000000000 : ℝ)^4687
        have hw : |(911279549/2000000000 : ℝ)|=(911279549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3805439877/10000000000 : ℝ)|^5711 ≤ (6162587890719/20000000000000 : ℝ)^4687
        have hw : |(3805439877/10000000000 : ℝ)|=(3805439877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(761087997/2000000000 : ℝ)|^5711 ≤ (30812940519133/100000000000000 : ℝ)^4687
        have hw : |(761087997/2000000000 : ℝ)|=(761087997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_box_4 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-419573401/2500000000 : ℝ)*x 0 + (5128030933/10000000000 : ℝ)*x 1 + (512803103/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419573401/2500000000 : ℝ)^5711 ≤ (2272739651333/20000000000000 : ℝ)^4687 := by
    have hnat : (419573401 : ℕ)^5711*20000000000000^4687 ≤ 2272739651333^4687*2500000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419573401 2500000000 2272739651333 20000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5128030933/10000000000 : ℝ)^5711 ≤ (44318150353477/100000000000000 : ℝ)^4687 := by
    have hnat : (5128030933 : ℕ)^5711*100000000000000^4687 ≤ 44318150353477^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128030933 10000000000 44318150353477 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512803103/1000000000 : ℝ)^5711 ≤ (44318151374933/100000000000000 : ℝ)^4687 := by
    have hnat : (512803103 : ℕ)^5711*100000000000000^4687 ≤ 44318151374933^4687*1000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512803103 1000000000 44318151374933 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-419573401/2500000000 : ℝ), (5128030933/10000000000 : ℝ), (512803103/1000000000 : ℝ)] ![(2272739651333/20000000000000 : ℝ), (44318150353477/100000000000000 : ℝ), (44318151374933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-419573401/2500000000 : ℝ)|^5711 ≤ (2272739651333/20000000000000 : ℝ)^4687
        have hw : |(-419573401/2500000000 : ℝ)|=(419573401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5128030933/10000000000 : ℝ)|^5711 ≤ (44318150353477/100000000000000 : ℝ)^4687
        have hw : |(5128030933/10000000000 : ℝ)|=(5128030933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(512803103/1000000000 : ℝ)|^5711 ≤ (44318151374933/100000000000000 : ℝ)^4687
        have hw : |(512803103/1000000000 : ℝ)|=(512803103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_box_5 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2698521423/5000000000 : ℝ)*x 0 + (-662170407/5000000000 : ℝ)*x 1 + (164097/320000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698521423/5000000000 : ℝ)^5711 ≤ (2947936995653/6250000000000 : ℝ)^4687 := by
    have hnat : (2698521423 : ℕ)^5711*6250000000000^4687 ≤ 2947936995653^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698521423 5000000000 2947936995653 6250000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (662170407/5000000000 : ℝ)^5711 ≤ (8514854360071/100000000000000 : ℝ)^4687 := by
    have hnat : (662170407 : ℕ)^5711*100000000000000^4687 ≤ 8514854360071^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662170407 5000000000 8514854360071 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164097/320000 : ℝ)^5711 ≤ (44318153691639/100000000000000 : ℝ)^4687 := by
    have hnat : (164097 : ℕ)^5711*100000000000000^4687 ≤ 44318153691639^4687*320000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164097 320000 44318153691639 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698521423/5000000000 : ℝ), (-662170407/5000000000 : ℝ), (164097/320000 : ℝ)] ![(2947936995653/6250000000000 : ℝ), (8514854360071/100000000000000 : ℝ), (44318153691639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698521423/5000000000 : ℝ)|^5711 ≤ (2947936995653/6250000000000 : ℝ)^4687
        have hw : |(2698521423/5000000000 : ℝ)|=(2698521423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-662170407/5000000000 : ℝ)|^5711 ≤ (8514854360071/100000000000000 : ℝ)^4687
        have hw : |(-662170407/5000000000 : ℝ)|=(662170407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164097/320000 : ℝ)|^5711 ≤ (44318153691639/100000000000000 : ℝ)^4687
        have hw : |(164097/320000 : ℝ)|=(164097/320000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_box_6 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (337315181/625000000 : ℝ)*x 0 + (128200781/250000000 : ℝ)*x 1 + (-33108519/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337315181/625000000 : ℝ)^5711 ≤ (47166992462887/100000000000000 : ℝ)^4687 := by
    have hnat : (337315181 : ℕ)^5711*100000000000000^4687 ≤ 47166992462887^4687*625000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337315181 625000000 47166992462887 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128200781/250000000 : ℝ)^5711 ≤ (22159076793167/50000000000000 : ℝ)^4687 := by
    have hnat : (128200781 : ℕ)^5711*50000000000000^4687 ≤ 22159076793167^4687*250000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128200781 250000000 22159076793167 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33108519/250000000 : ℝ)^5711 ≤ (66522296383/781250000000 : ℝ)^4687 := by
    have hnat : (33108519 : ℕ)^5711*781250000000^4687 ≤ 66522296383^4687*250000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33108519 250000000 66522296383 781250000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(337315181/625000000 : ℝ), (128200781/250000000 : ℝ), (-33108519/250000000 : ℝ)] ![(47166992462887/100000000000000 : ℝ), (22159076793167/50000000000000 : ℝ), (66522296383/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(337315181/625000000 : ℝ)|^5711 ≤ (47166992462887/100000000000000 : ℝ)^4687
        have hw : |(337315181/625000000 : ℝ)|=(337315181/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(128200781/250000000 : ℝ)|^5711 ≤ (22159076793167/50000000000000 : ℝ)^4687
        have hw : |(128200781/250000000 : ℝ)|=(128200781/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-33108519/250000000 : ℝ)|^5711 ≤ (66522296383/781250000000 : ℝ)^4687
        have hw : |(-33108519/250000000 : ℝ)|=(33108519/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_box_7 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (693258813/2000000000 : ℝ)*x 0 + (2174173411/5000000000 : ℝ)*x 1 + (1087086773/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (693258813/2000000000 : ℝ)^5711 ≤ (27500256470247/100000000000000 : ℝ)^4687 := by
    have hnat : (693258813 : ℕ)^5711*100000000000000^4687 ≤ 27500256470247^4687*2000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693258813 2000000000 27500256470247 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2174173411/5000000000 : ℝ)^5711 ≤ (18124935190311/50000000000000 : ℝ)^4687 := by
    have hnat : (2174173411 : ℕ)^5711*50000000000000^4687 ≤ 18124935190311^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174173411 5000000000 18124935190311 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087086773/2500000000 : ℝ)^5711 ≤ (36249873123227/100000000000000 : ℝ)^4687 := by
    have hnat : (1087086773 : ℕ)^5711*100000000000000^4687 ≤ 36249873123227^4687*2500000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087086773 2500000000 36249873123227 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(693258813/2000000000 : ℝ), (2174173411/5000000000 : ℝ), (1087086773/2500000000 : ℝ)] ![(27500256470247/100000000000000 : ℝ), (18124935190311/50000000000000 : ℝ), (36249873123227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(693258813/2000000000 : ℝ)|^5711 ≤ (27500256470247/100000000000000 : ℝ)^4687
        have hw : |(693258813/2000000000 : ℝ)|=(693258813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2174173411/5000000000 : ℝ)|^5711 ≤ (18124935190311/50000000000000 : ℝ)^4687
        have hw : |(2174173411/5000000000 : ℝ)|=(2174173411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087086773/2500000000 : ℝ)|^5711 ≤ (36249873123227/100000000000000 : ℝ)^4687
        have hw : |(1087086773/2500000000 : ℝ)|=(1087086773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_box_8 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1498584489/10000000000 : ℝ)*x 0 + (4898771149/10000000000 : ℝ)*x 1 + (549248023/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1498584489/10000000000 : ℝ)^5711 ≤ (4949448903181/50000000000000 : ℝ)^4687 := by
    have hnat : (1498584489 : ℕ)^5711*50000000000000^4687 ≤ 4949448903181^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1498584489 10000000000 4949448903181 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4898771149/10000000000 : ℝ)^5711 ≤ (20957932568197/50000000000000 : ℝ)^4687 := by
    have hnat : (4898771149 : ℕ)^5711*50000000000000^4687 ≤ 20957932568197^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4898771149 10000000000 20957932568197 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549248023/1000000000 : ℝ)^5711 ≤ (48185237042101/100000000000000 : ℝ)^4687 := by
    have hnat : (549248023 : ℕ)^5711*100000000000000^4687 ≤ 48185237042101^4687*1000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549248023 1000000000 48185237042101 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1498584489/10000000000 : ℝ), (4898771149/10000000000 : ℝ), (549248023/1000000000 : ℝ)] ![(4949448903181/50000000000000 : ℝ), (20957932568197/50000000000000 : ℝ), (48185237042101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1498584489/10000000000 : ℝ)|^5711 ≤ (4949448903181/50000000000000 : ℝ)^4687
        have hw : |(-1498584489/10000000000 : ℝ)|=(1498584489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4898771149/10000000000 : ℝ)|^5711 ≤ (20957932568197/50000000000000 : ℝ)^4687
        have hw : |(4898771149/10000000000 : ℝ)|=(4898771149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(549248023/1000000000 : ℝ)|^5711 ≤ (48185237042101/100000000000000 : ℝ)^4687
        have hw : |(549248023/1000000000 : ℝ)|=(549248023/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_box_9 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152719517/10000000000 : ℝ)*x 0 + (-579411583/5000000000 : ℝ)*x 1 + (343280149/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152719517/10000000000 : ℝ)^5711 ≤ (11144567392573/25000000000000 : ℝ)^4687 := by
    have hnat : (5152719517 : ℕ)^5711*25000000000000^4687 ≤ 11144567392573^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152719517 10000000000 11144567392573 25000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (579411583/5000000000 : ℝ)^5711 ≤ (7236470346711/100000000000000 : ℝ)^4687 := by
    have hnat : (579411583 : ℕ)^5711*100000000000000^4687 ≤ 7236470346711^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579411583 5000000000 7236470346711 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (343280149/625000000 : ℝ)^5711 ≤ (48185260067567/100000000000000 : ℝ)^4687 := by
    have hnat : (343280149 : ℕ)^5711*100000000000000^4687 ≤ 48185260067567^4687*625000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343280149 625000000 48185260067567 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152719517/10000000000 : ℝ), (-579411583/5000000000 : ℝ), (343280149/625000000 : ℝ)] ![(11144567392573/25000000000000 : ℝ), (7236470346711/100000000000000 : ℝ), (48185260067567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152719517/10000000000 : ℝ)|^5711 ≤ (11144567392573/25000000000000 : ℝ)^4687
        have hw : |(5152719517/10000000000 : ℝ)|=(5152719517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-579411583/5000000000 : ℝ)|^5711 ≤ (7236470346711/100000000000000 : ℝ)^4687
        have hw : |(-579411583/5000000000 : ℝ)|=(579411583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(343280149/625000000 : ℝ)|^5711 ≤ (48185260067567/100000000000000 : ℝ)^4687
        have hw : |(343280149/625000000 : ℝ)|=(343280149/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_box_10 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1288180081/2500000000 : ℝ)*x 0 + (2746240869/5000000000 : ℝ)*x 1 + (-289705739/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1288180081/2500000000 : ℝ)^5711 ≤ (348267797479/781250000000 : ℝ)^4687 := by
    have hnat : (1288180081 : ℕ)^5711*781250000000^4687 ≤ 348267797479^4687*2500000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288180081 2500000000 348267797479 781250000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2746240869/5000000000 : ℝ)^5711 ≤ (9637050632413/20000000000000 : ℝ)^4687 := by
    have hnat : (2746240869 : ℕ)^5711*20000000000000^4687 ≤ 9637050632413^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746240869 5000000000 9637050632413 20000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (289705739/2500000000 : ℝ)^5711 ≤ (904558593603/12500000000000 : ℝ)^4687 := by
    have hnat : (289705739 : ℕ)^5711*12500000000000^4687 ≤ 904558593603^4687*2500000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289705739 2500000000 904558593603 12500000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1288180081/2500000000 : ℝ), (2746240869/5000000000 : ℝ), (-289705739/2500000000 : ℝ)] ![(348267797479/781250000000 : ℝ), (9637050632413/20000000000000 : ℝ), (904558593603/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1288180081/2500000000 : ℝ)|^5711 ≤ (348267797479/781250000000 : ℝ)^4687
        have hw : |(1288180081/2500000000 : ℝ)|=(1288180081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2746240869/5000000000 : ℝ)|^5711 ≤ (9637050632413/20000000000000 : ℝ)^4687
        have hw : |(2746240869/5000000000 : ℝ)|=(2746240869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-289705739/2500000000 : ℝ)|^5711 ≤ (904558593603/12500000000000 : ℝ)^4687
        have hw : |(-289705739/2500000000 : ℝ)|=(289705739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_box_11 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (954540971/2000000000 : ℝ)*x 0 + (3691997527/10000000000 : ℝ)*x 1 + (28843727/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (954540971/2000000000 : ℝ)^5711 ≤ (5075655722359/12500000000000 : ℝ)^4687 := by
    have hnat : (954540971 : ℕ)^5711*12500000000000^4687 ≤ 5075655722359^4687*2000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954540971 2000000000 5075655722359 12500000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3691997527/10000000000 : ℝ)^5711 ≤ (29697379411481/100000000000000 : ℝ)^4687 := by
    have hnat : (3691997527 : ℕ)^5711*100000000000000^4687 ≤ 29697379411481^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3691997527 10000000000 29697379411481 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28843727/78125000 : ℝ)^5711 ≤ (7424343698793/25000000000000 : ℝ)^4687 := by
    have hnat : (28843727 : ℕ)^5711*25000000000000^4687 ≤ 7424343698793^4687*78125000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28843727 78125000 7424343698793 25000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(954540971/2000000000 : ℝ), (3691997527/10000000000 : ℝ), (28843727/78125000 : ℝ)] ![(5075655722359/12500000000000 : ℝ), (29697379411481/100000000000000 : ℝ), (7424343698793/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(954540971/2000000000 : ℝ)|^5711 ≤ (5075655722359/12500000000000 : ℝ)^4687
        have hw : |(954540971/2000000000 : ℝ)|=(954540971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3691997527/10000000000 : ℝ)|^5711 ≤ (29697379411481/100000000000000 : ℝ)^4687
        have hw : |(3691997527/10000000000 : ℝ)|=(3691997527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28843727/78125000 : ℝ)|^5711 ≤ (7424343698793/25000000000000 : ℝ)^4687
        have hw : |(28843727/78125000 : ℝ)|=(28843727/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_box_12 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1017637617/10000000000 : ℝ)*x 0 + (5645269429/10000000000 : ℝ)*x 1 + (5097761637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1017637617/10000000000 : ℝ)^5711 ≤ (6176969276059/100000000000000 : ℝ)^4687 := by
    have hnat : (1017637617 : ℕ)^5711*100000000000000^4687 ≤ 6176969276059^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017637617 10000000000 6176969276059 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5645269429/10000000000 : ℝ)^5711 ≤ (2491171237631/5000000000000 : ℝ)^4687 := by
    have hnat : (5645269429 : ℕ)^5711*5000000000000^4687 ≤ 2491171237631^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5645269429 10000000000 2491171237631 5000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5097761637/10000000000 : ℝ)^5711 ≤ (8799921192729/20000000000000 : ℝ)^4687 := by
    have hnat : (5097761637 : ℕ)^5711*20000000000000^4687 ≤ 8799921192729^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5097761637 10000000000 8799921192729 20000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1017637617/10000000000 : ℝ), (5645269429/10000000000 : ℝ), (5097761637/10000000000 : ℝ)] ![(6176969276059/100000000000000 : ℝ), (2491171237631/5000000000000 : ℝ), (8799921192729/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1017637617/10000000000 : ℝ)|^5711 ≤ (6176969276059/100000000000000 : ℝ)^4687
        have hw : |(-1017637617/10000000000 : ℝ)|=(1017637617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5645269429/10000000000 : ℝ)|^5711 ≤ (2491171237631/5000000000000 : ℝ)^4687
        have hw : |(5645269429/10000000000 : ℝ)|=(5645269429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5097761637/10000000000 : ℝ)|^5711 ≤ (8799921192729/20000000000000 : ℝ)^4687
        have hw : |(5097761637/10000000000 : ℝ)|=(5097761637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_box_13 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083482577/2000000000 : ℝ)*x 0 + (-668644659/5000000000 : ℝ)*x 1 + (1019552199/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083482577/2000000000 : ℝ)^5711 ≤ (23691998586863/50000000000000 : ℝ)^4687 := by
    have hnat : (1083482577 : ℕ)^5711*50000000000000^4687 ≤ 23691998586863^4687*2000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083482577 2000000000 23691998586863 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (668644659/5000000000 : ℝ)^5711 ≤ (4308201801687/50000000000000 : ℝ)^4687 := by
    have hnat : (668644659 : ℕ)^5711*50000000000000^4687 ≤ 4308201801687^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668644659 5000000000 4308201801687 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1019552199/2000000000 : ℝ)^5711 ≤ (8799919842363/20000000000000 : ℝ)^4687 := by
    have hnat : (1019552199 : ℕ)^5711*20000000000000^4687 ≤ 8799919842363^4687*2000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019552199 2000000000 8799919842363 20000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083482577/2000000000 : ℝ), (-668644659/5000000000 : ℝ), (1019552199/2000000000 : ℝ)] ![(23691998586863/50000000000000 : ℝ), (4308201801687/50000000000000 : ℝ), (8799919842363/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083482577/2000000000 : ℝ)|^5711 ≤ (23691998586863/50000000000000 : ℝ)^4687
        have hw : |(1083482577/2000000000 : ℝ)|=(1083482577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-668644659/5000000000 : ℝ)|^5711 ≤ (4308201801687/50000000000000 : ℝ)^4687
        have hw : |(-668644659/5000000000 : ℝ)|=(668644659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1019552199/2000000000 : ℝ)|^5711 ≤ (8799919842363/20000000000000 : ℝ)^4687
        have hw : |(1019552199/2000000000 : ℝ)|=(1019552199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_box_14 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5417412649/10000000000 : ℝ)*x 0 + (509776171/1000000000 : ℝ)*x 1 + (-33432217/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5417412649/10000000000 : ℝ)^5711 ≤ (47383994658547/100000000000000 : ℝ)^4687 := by
    have hnat : (5417412649 : ℕ)^5711*100000000000000^4687 ≤ 47383994658547^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417412649 10000000000 47383994658547 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (509776171/1000000000 : ℝ)^5711 ≤ (2749975420711/6250000000000 : ℝ)^4687 := by
    have hnat : (509776171 : ℕ)^5711*6250000000000^4687 ≤ 2749975420711^4687*1000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509776171 1000000000 2749975420711 6250000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33432217/250000000 : ℝ)^5711 ≤ (8616398594519/100000000000000 : ℝ)^4687 := by
    have hnat : (33432217 : ℕ)^5711*100000000000000^4687 ≤ 8616398594519^4687*250000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33432217 250000000 8616398594519 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5417412649/10000000000 : ℝ), (509776171/1000000000 : ℝ), (-33432217/250000000 : ℝ)] ![(47383994658547/100000000000000 : ℝ), (2749975420711/6250000000000 : ℝ), (8616398594519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5417412649/10000000000 : ℝ)|^5711 ≤ (47383994658547/100000000000000 : ℝ)^4687
        have hw : |(5417412649/10000000000 : ℝ)|=(5417412649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(509776171/1000000000 : ℝ)|^5711 ≤ (2749975420711/6250000000000 : ℝ)^4687
        have hw : |(509776171/1000000000 : ℝ)|=(509776171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-33432217/250000000 : ℝ)|^5711 ≤ (8616398594519/100000000000000 : ℝ)^4687
        have hw : |(-33432217/250000000 : ℝ)|=(33432217/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_box_15 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3351693907/10000000000 : ℝ)*x 0 + (880521023/2000000000 : ℝ)*x 1 + (4402606237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3351693907/10000000000 : ℝ)^5711 ≤ (6599115202361/25000000000000 : ℝ)^4687 := by
    have hnat : (3351693907 : ℕ)^5711*25000000000000^4687 ≤ 6599115202361^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3351693907 10000000000 6599115202361 25000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (880521023/2000000000 : ℝ)^5711 ≤ (36801763873097/100000000000000 : ℝ)^4687 := by
    have hnat : (880521023 : ℕ)^5711*100000000000000^4687 ≤ 36801763873097^4687*2000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880521023 2000000000 36801763873097 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4402606237/10000000000 : ℝ)^5711 ≤ (4600221912633/12500000000000 : ℝ)^4687 := by
    have hnat : (4402606237 : ℕ)^5711*12500000000000^4687 ≤ 4600221912633^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4402606237 10000000000 4600221912633 12500000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3351693907/10000000000 : ℝ), (880521023/2000000000 : ℝ), (4402606237/10000000000 : ℝ)] ![(6599115202361/25000000000000 : ℝ), (36801763873097/100000000000000 : ℝ), (4600221912633/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3351693907/10000000000 : ℝ)|^5711 ≤ (6599115202361/25000000000000 : ℝ)^4687
        have hw : |(3351693907/10000000000 : ℝ)|=(3351693907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(880521023/2000000000 : ℝ)|^5711 ≤ (36801763873097/100000000000000 : ℝ)^4687
        have hw : |(880521023/2000000000 : ℝ)|=(880521023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4402606237/10000000000 : ℝ)|^5711 ≤ (4600221912633/12500000000000 : ℝ)^4687
        have hw : |(4402606237/10000000000 : ℝ)|=(4402606237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1746_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (211599271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(34419/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(57913/100000 : ℝ) ∧ (81331/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (11603/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8987/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8987/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8987/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8987/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8987/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8987/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8987/100000 : ℝ) ^ (5695/1024 : ℝ) ≤ (75765913807219/50000000000000000000 : ℝ) := by
    have hpowers : (8987/100000 : ℝ)^5695 ≤ (75765913807219/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8987 : ℕ)^5695*50000000000000000000^1024 ≤ 75765913807219^1024*100000^5695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8987 100000 75765913807219 50000000000000000000 5695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8987/100000 : ℝ)) (X := (75765913807219/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18053/100000 : ℝ) ^ (5695/1024 : ℝ) ≤ (733300471459051/10000000000000000000 : ℝ) := by
    have hpowers : (18053/100000 : ℝ)^5695 ≤ (733300471459051/10000000000000000000 : ℝ)^1024 := by
      have hnat : (18053 : ℕ)^5695*10000000000000000000^1024 ≤ 733300471459051^1024*100000^5695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18053 100000 733300471459051 10000000000000000000 5695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18053/100000 : ℝ)) (X := (733300471459051/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000075765913807219/25000000000000000000 : ℝ) ≤ (1000000544928529/1000000000000000 : ℝ) ^ (5695/1024 : ℝ) := by
    have hpowers : (25000075765913807219/25000000000000000000 : ℝ)^1024 ≤ (1000000544928529/1000000000000000 : ℝ)^5695 := by
      have hnat : (25000075765913807219 : ℕ)^1024*1000000000000000^5695 ≤ 1000000544928529^5695*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000075765913807219 25000000000000000000 1000000544928529 1000000000000000 1024 5695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000544928529/1000000000000000 : ℝ)) (X := (25000075765913807219/25000000000000000000 : ℝ)) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25001871134135551237/25000000000000000000 : ℝ) ≤ (5000067286481013/5000000000000000 : ℝ) ^ (5695/1024 : ℝ) := by
    have hpowers : (25001871134135551237/25000000000000000000 : ℝ)^1024 ≤ (5000067286481013/5000000000000000 : ℝ)^5695 := by
      have hnat : (25001871134135551237 : ℕ)^1024*5000000000000000^5695 ≤ 5000067286481013^5695*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001871134135551237 25000000000000000000 5000067286481013 5000000000000000 1024 5695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000067286481013/5000000000000000 : ℝ)) (X := (25001871134135551237/25000000000000000000 : ℝ)) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5000733300471459051/5000000000000000000 : ℝ) ≤ (5000131848319381/5000000000000000 : ℝ) ^ (5695/1024 : ℝ) := by
    have hpowers : (5000733300471459051/5000000000000000000 : ℝ)^1024 ≤ (5000131848319381/5000000000000000 : ℝ)^5695 := by
      have hnat : (5000733300471459051 : ℕ)^1024*5000000000000000^5695 ≤ 5000131848319381^5695*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000733300471459051 5000000000000000000 5000131848319381 5000000000000000 1024 5695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000131848319381/5000000000000000 : ℝ)) (X := (5000733300471459051/5000000000000000000 : ℝ)) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(75765913807219/50000000000000000000 : ℝ) ≤ ((22664432133563696569/22665000000000000000 : ℝ)+2*(2017557449/14165625000000 : ℝ)*(8987/100000 : ℝ))^(5695/1024 : ℝ) := by
    rw [show (22664432133563696569/22665000000000000000 : ℝ)+2*(2017557449/14165625000000 : ℝ)*(8987/100000 : ℝ)=(1000000544928529/1000000000000000 : ℝ) by norm_num, show 1+2*(75765913807219/50000000000000000000 : ℝ)=(25000075765913807219/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(733300471459051/10000000000000000000 : ℝ)+(75765913807219/50000000000000000000 : ℝ) ≤ ((22664432133563696569/22665000000000000000 : ℝ)+(2017557449/14165625000000 : ℝ)*((18053/100000 : ℝ)+(8987/100000 : ℝ)))^(5695/1024 : ℝ) := by
    rw [show (22664432133563696569/22665000000000000000 : ℝ)+(2017557449/14165625000000 : ℝ)*((18053/100000 : ℝ)+(8987/100000 : ℝ))=(5000067286481013/5000000000000000 : ℝ) by norm_num, show 1+(733300471459051/10000000000000000000 : ℝ)+(75765913807219/50000000000000000000 : ℝ)=(25001871134135551237/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(733300471459051/10000000000000000000 : ℝ) ≤ ((22664432133563696569/22665000000000000000 : ℝ)+2*(2017557449/14165625000000 : ℝ)*(18053/100000 : ℝ))^(5695/1024 : ℝ) := by
    rw [show (22664432133563696569/22665000000000000000 : ℝ)+2*(2017557449/14165625000000 : ℝ)*(18053/100000 : ℝ)=(5000131848319381/5000000000000000 : ℝ) by norm_num, show 1+2*(733300471459051/10000000000000000000 : ℝ)=(5000733300471459051/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22664432133563696569/22665000000000000000 : ℝ)*(X 1 0+X 2 0)+(2017557449/14165625000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5695/1024 : ℝ)) (lo := (8987/100000 : ℝ)) (hi := (18053/100000 : ℝ)) (c := (22664432133563696569/22665000000000000000 : ℝ)) (alpha := (2017557449/14165625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22664432133563696569/22665000000000000000 : ℝ)*(X 0 1+X 2 1)+(2017557449/14165625000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5695/1024 : ℝ)) (lo := (8987/100000 : ℝ)) (hi := (18053/100000 : ℝ)) (c := (22664432133563696569/22665000000000000000 : ℝ)) (alpha := (2017557449/14165625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22664432133563696569/22665000000000000000 : ℝ)*(X 0 2+X 1 2)+(2017557449/14165625000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5695/1024 : ℝ)) (lo := (8987/100000 : ℝ)) (hi := (18053/100000 : ℝ)) (c := (22664432133563696569/22665000000000000000 : ℝ)) (alpha := (2017557449/14165625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-851393827/10000000000 : ℝ)*X 0 0+(2714842173/5000000000 : ℝ)*X 0 1+(2714842197/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5194766387/10000000000 : ℝ)*X 1 0+(-594274519/5000000000 : ℝ)*X 1 1+(5429684413/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5194766447/10000000000 : ℝ)*X 2 0+(5429684379/10000000000 : ℝ)*X 2 1+(-594274501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((911279549/2000000000 : ℝ)*X 0 0+(3805439877/10000000000 : ℝ)*X 0 1+(761087997/2000000000 : ℝ)*X 0 2+(911279549/2000000000 : ℝ)*X 1 0+(3805439877/10000000000 : ℝ)*X 1 1+(761087997/2000000000 : ℝ)*X 1 2+(911279549/2000000000 : ℝ)*X 2 0+(3805439877/10000000000 : ℝ)*X 2 1+(761087997/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-419573401/2500000000 : ℝ)*X 0 0+(5128030933/10000000000 : ℝ)*X 0 1+(512803103/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2698521423/5000000000 : ℝ)*X 1 0+(-662170407/5000000000 : ℝ)*X 1 1+(164097/320000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((337315181/625000000 : ℝ)*X 2 0+(128200781/250000000 : ℝ)*X 2 1+(-33108519/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((693258813/2000000000 : ℝ)*X 0 0+(2174173411/5000000000 : ℝ)*X 0 1+(1087086773/2500000000 : ℝ)*X 0 2+(693258813/2000000000 : ℝ)*X 1 0+(2174173411/5000000000 : ℝ)*X 1 1+(1087086773/2500000000 : ℝ)*X 1 2+(693258813/2000000000 : ℝ)*X 2 0+(2174173411/5000000000 : ℝ)*X 2 1+(1087086773/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1498584489/10000000000 : ℝ)*X 0 0+(4898771149/10000000000 : ℝ)*X 0 1+(549248023/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5152719517/10000000000 : ℝ)*X 1 0+(-579411583/5000000000 : ℝ)*X 1 1+(343280149/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1288180081/2500000000 : ℝ)*X 2 0+(2746240869/5000000000 : ℝ)*X 2 1+(-289705739/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((954540971/2000000000 : ℝ)*X 0 0+(3691997527/10000000000 : ℝ)*X 0 1+(28843727/78125000 : ℝ)*X 0 2+(954540971/2000000000 : ℝ)*X 1 0+(3691997527/10000000000 : ℝ)*X 1 1+(28843727/78125000 : ℝ)*X 1 2+(954540971/2000000000 : ℝ)*X 2 0+(3691997527/10000000000 : ℝ)*X 2 1+(28843727/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1017637617/10000000000 : ℝ)*X 0 0+(5645269429/10000000000 : ℝ)*X 0 1+(5097761637/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1083482577/2000000000 : ℝ)*X 1 0+(-668644659/5000000000 : ℝ)*X 1 1+(1019552199/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5417412649/10000000000 : ℝ)*X 2 0+(509776171/1000000000 : ℝ)*X 2 1+(-33432217/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3351693907/10000000000 : ℝ)*X 0 0+(880521023/2000000000 : ℝ)*X 0 1+(4402606237/10000000000 : ℝ)*X 0 2+(3351693907/10000000000 : ℝ)*X 1 0+(880521023/2000000000 : ℝ)*X 1 1+(4402606237/10000000000 : ℝ)*X 1 2+(3351693907/10000000000 : ℝ)*X 2 0+(880521023/2000000000 : ℝ)*X 2 1+(4402606237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-34419/50000 : ℝ) ≤ (-130013993233121335250894657434479/188875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2525553/100000000000000 : ℝ)*(upper1) + (48740141/100000000000000 : ℝ)*(upper3) + (7854037/10000000000000 : ℝ)*(upper5) + (517962901690203/50000000000000 : ℝ)*(major0) + (517962901690203/50000000000000 : ℝ)*(major1) + (517962901690203/50000000000000 : ℝ)*(major2) + (491382567/100000000000000 : ℝ)*(sp1) + (177634611/20000000000000 : ℝ)*(sp2) + (43315137/4000000000000 : ℝ)*(sp3) + (802613592736017/50000000000000 : ℝ)*(sp4) + (401306700433687/25000000000000 : ℝ)*(sp5) + (80261320247213/5000000000000 : ℝ)*(sp6) + (48956856378657/10000000000000 : ℝ)*(sp7) + (107645281/100000000000000 : ℝ)*(sp8) + (122392411666249/25000000000000 : ℝ)*(f.failure) + (802613646558657/50000000000000 : ℝ)*(f.sum) + (13798855484493/3777500000000000000000000000 : ℝ)*base65 + (1539052575214928831/377750000000000000000000000000000 : ℝ)*base68 + (2901531798952178831/377750000000000000000000000000000 : ℝ)*base70 + (2851615610618928831/377750000000000000000000000000000 : ℝ)*base72 + (59220167400051/7555000000000000000000000000 : ℝ)*base73 + (453784901509928831/377750000000000000000000000000000 : ℝ)*base76 + (2345458680465928831/377750000000000000000000000000000 : ℝ)*base78 + (2624579398263428831/377750000000000000000000000000000 : ℝ)*base80 + (32043405387889/7555000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (33704479/2500000000000000000000 : ℝ)*base89 + (33704479/2500000000000000000000 : ℝ)*base91 + (33704479/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (57913/100000 : ℝ) ≤ (1093880019410293859486067911/1888750000000000000000000000 : ℝ) := by norm_num
    linear_combination (7256029/100000000000000 : ℝ)*(lower1) + (437333/100000000000000 : ℝ)*(lower3) + (9206153/100000000000000 : ℝ)*(upper4) + (5411627/100000000000000 : ℝ)*(upper5) + (1157079612355073/100000000000000 : ℝ)*(major0) + (1157079612355073/100000000000000 : ℝ)*(major1) + (1157079612355073/100000000000000 : ℝ)*(major2) + (874014018739981/50000000000000 : ℝ)*(sp0) + (13984225142793/800000000000 : ℝ)*(sp1) + (874013918971059/50000000000000 : ℝ)*(sp2) + (109365176060633/20000000000000 : ℝ)*(sp3) + (1701057/10000000000000 : ℝ)*(sp7) + (304907007/100000000000000 : ℝ)*(sp10) + (105369163/100000000000000 : ℝ)*(sp12) + (68353237164217/12500000000000 : ℝ)*(f.failure) + (13984225142793/800000000000 : ℝ)*(f.sum) + (56430186039457/11332500000000000000000000000 : ℝ)*base65 + (3636951498897651821/755500000000000000000000000000000 : ℝ)*base68 + (2340903185797651821/755500000000000000000000000000000 : ℝ)*base70 + (1447805770309348179/755500000000000000000000000000000 : ℝ)*base71 + (30162501833311/22665000000000000000000000000 : ℝ)*base74 + (678709327010651821/755500000000000000000000000000000 : ℝ)*base76 + (653727191044848179/755500000000000000000000000000000 : ℝ)*base77 + (1090045708752848179/755500000000000000000000000000000 : ℝ)*base79 + (87368248837741/22665000000000000000000000000 : ℝ)*base82 + (11985807/1250000000000000000000 : ℝ)*base89 + (11985807/1250000000000000000000 : ℝ)*base91 + (11985807/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (81331/100000 : ℝ) ≤ (307236324401021727887198165052567/377750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11663423/100000000000000 : ℝ)*(upper0) + (7939913/50000000000000 : ℝ)*(lower1) + (11171487/10000000000000 : ℝ)*(upper4) + (1120487624200981/100000000000000 : ℝ)*(major0) + (1120487624200981/100000000000000 : ℝ)*(major1) + (1120487624200981/100000000000000 : ℝ)*(major2) + (3966340477/100000000000000 : ℝ)*(sp0) + (59210847553/100000000000000 : ℝ)*(sp1) + (53453778041/100000000000000 : ℝ)*(sp2) + (7133708479/50000000000000 : ℝ)*(sp3) + (1684327363489277/100000000000000 : ℝ)*(sp8) + (8421360594911/500000000000 : ℝ)*(sp9) + (6579210453327/390625000000 : ℝ)*(sp10) + (26475928512313/5000000000000 : ℝ)*(sp11) + (529532837663217/100000000000000 : ℝ)*(f.failure) + (842165664914877/50000000000000 : ℝ)*(f.sum) + (35321404454431/11332500000000000000000000000 : ℝ)*base66 + (4753121397903321937/755500000000000000000000000000000 : ℝ)*base68 + (5863260907506821937/755500000000000000000000000000000 : ℝ)*base70 + (1645957599963321937/755500000000000000000000000000000 : ℝ)*base72 + (55909543671593/5666250000000000000000000000 : ℝ)*base74 + (4016778519232321937/755500000000000000000000000000000 : ℝ)*base76 + (1531413679285321937/755500000000000000000000000000000 : ℝ)*base78 + (11131818988643321937/755500000000000000000000000000000 : ℝ)*base80 + (21972822498233/5666250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (39285193/10000000000000000000000 : ℝ)*base90 + (39285193/10000000000000000000000 : ℝ)*base92 + (39285193/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-11603/12500 : ℝ) ≤ (-35063422330897514594842359177367/37775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25478603/50000000000000 : ℝ)*(lower1) + (46249303/100000000000000 : ℝ)*(lower2) + (37820237/100000000000000 : ℝ)*(lower3) + (33283307/100000000000000 : ℝ)*(upper5) + (235106420022143/20000000000000 : ℝ)*(major0) + (235106420022143/20000000000000 : ℝ)*(major1) + (235106420022143/20000000000000 : ℝ)*(major2) + (157630207/20000000000000 : ℝ)*(sp4) + (43865267539/100000000000000 : ℝ)*(sp5) + (7524064143/100000000000000 : ℝ)*(sp7) + (1826457616226249/100000000000000 : ℝ)*(sp12) + (913207269554873/50000000000000 : ℝ)*(sp13) + (456614601094321/25000000000000 : ℝ)*(sp14) + (22221554425787/4000000000000 : ℝ)*(sp15) + (277773192354409/50000000000000 : ℝ)*(f.failure) + (456614601094321/25000000000000 : ℝ)*(f.sum) + (22182752535473/4533000000000000000000000000 : ℝ)*base65 + (508250797953075789/151100000000000000000000000000000 : ℝ)*base67 + (69492337541375789/151100000000000000000000000000000 : ℝ)*base69 + (44115813281624211/151100000000000000000000000000000 : ℝ)*base72 + (6602561048377/4533000000000000000000000000 : ℝ)*base74 + (52187556098675789/151100000000000000000000000000000 : ℝ)*base75 + (1215391516595175789/151100000000000000000000000000000 : ℝ)*base77 + (570807986372675789/151100000000000000000000000000000 : ℝ)*base79 + (26007558062239/4533000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (31964161/5000000000000000000000 : ℝ)*base90 + (31964161/5000000000000000000000 : ℝ)*base92 + (31964161/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1746_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (211599271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(34419/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(57913/100000 : ℝ) else (81331/100000 : ℝ) ≤ X j i ∧ X j i ≤ (11603/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1746_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1746_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (211599271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3611/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4493/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(34419/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(57913/100000 : ℝ) else (81331/100000 : ℝ) ≤ X j i ∧ X j i ≤ (11603/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1746_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1746_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (211599271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3611/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4493/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(34419/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(57913/100000 : ℝ) else (81331/100000 : ℝ) ≤ X j i ∧ X j i ≤ (11603/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1746_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

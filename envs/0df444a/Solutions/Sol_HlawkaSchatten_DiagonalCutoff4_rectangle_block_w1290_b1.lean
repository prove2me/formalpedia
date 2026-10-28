-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1290_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:25:14.390764+00:00
-- url     : https://prove2.me/submissions/e4f6856b-6c5c-489f-af01-e13d77f00db0

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
theorem support_rectangle_w1290_s3_0 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-260922781/1250000000 : ℝ)*x 0 + (339648191/625000000 : ℝ)*x 1 + (1306360753/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (260922781/1250000000 : ℝ)^2125 ≤ (12694903338577/100000000000000 : ℝ)^1613 := by
    have hnat : (260922781 : ℕ)^2125*100000000000000^1613 ≤ 12694903338577^1613*1250000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260922781 1250000000 12694903338577 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339648191/625000000 : ℝ)^2125 ≤ (44779591021079/100000000000000 : ℝ)^1613 := by
    have hnat : (339648191 : ℕ)^2125*100000000000000^1613 ≤ 44779591021079^1613*625000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339648191 625000000 44779591021079 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306360753/2500000000 : ℝ)^2125 ≤ (2126275281141/5000000000000 : ℝ)^1613 := by
    have hnat : (1306360753 : ℕ)^2125*5000000000000^1613 ≤ 2126275281141^1613*2500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306360753 2500000000 2126275281141 5000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-260922781/1250000000 : ℝ), (339648191/625000000 : ℝ), (1306360753/2500000000 : ℝ)] ![(12694903338577/100000000000000 : ℝ), (44779591021079/100000000000000 : ℝ), (2126275281141/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-260922781/1250000000 : ℝ)|^2125 ≤ (12694903338577/100000000000000 : ℝ)^1613
        have hw : |(-260922781/1250000000 : ℝ)|=(260922781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339648191/625000000 : ℝ)|^2125 ≤ (44779591021079/100000000000000 : ℝ)^1613
        have hw : |(339648191/625000000 : ℝ)|=(339648191/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1306360753/2500000000 : ℝ)|^2125 ≤ (2126275281141/5000000000000 : ℝ)^1613
        have hw : |(1306360753/2500000000 : ℝ)|=(1306360753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s3_1 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1338656587/2500000000 : ℝ)*x 0 + (-438863069/2000000000 : ℝ)*x 1 + (1306360769/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338656587/2500000000 : ℝ)^2125 ≤ (43915934130463/100000000000000 : ℝ)^1613 := by
    have hnat : (1338656587 : ℕ)^2125*100000000000000^1613 ≤ 43915934130463^1613*2500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338656587 2500000000 43915934130463 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438863069/2000000000 : ℝ)^2125 ≤ (6779279770531/50000000000000 : ℝ)^1613 := by
    have hnat : (438863069 : ℕ)^2125*50000000000000^1613 ≤ 6779279770531^1613*2000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438863069 2000000000 6779279770531 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306360769/2500000000 : ℝ)^2125 ≤ (42525506308989/100000000000000 : ℝ)^1613 := by
    have hnat : (1306360769 : ℕ)^2125*100000000000000^1613 ≤ 42525506308989^1613*2500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306360769 2500000000 42525506308989 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338656587/2500000000 : ℝ), (-438863069/2000000000 : ℝ), (1306360769/2500000000 : ℝ)] ![(43915934130463/100000000000000 : ℝ), (6779279770531/50000000000000 : ℝ), (42525506308989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338656587/2500000000 : ℝ)|^2125 ≤ (43915934130463/100000000000000 : ℝ)^1613
        have hw : |(1338656587/2500000000 : ℝ)|=(1338656587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-438863069/2000000000 : ℝ)|^2125 ≤ (6779279770531/50000000000000 : ℝ)^1613
        have hw : |(-438863069/2000000000 : ℝ)|=(438863069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1306360769/2500000000 : ℝ)|^2125 ≤ (42525506308989/100000000000000 : ℝ)^1613
        have hw : |(1306360769/2500000000 : ℝ)|=(1306360769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s3_2 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1070925281/2000000000 : ℝ)*x 0 + (1306360697/2500000000 : ℝ)*x 1 + (-2194315649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070925281/2000000000 : ℝ)^2125 ≤ (43915934746337/100000000000000 : ℝ)^1613 := by
    have hnat : (1070925281 : ℕ)^2125*100000000000000^1613 ≤ 43915934746337^1613*2000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070925281 2000000000 43915934746337 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1306360697/2500000000 : ℝ)^2125 ≤ (4252550322123/10000000000000 : ℝ)^1613 := by
    have hnat : (1306360697 : ℕ)^2125*10000000000000^1613 ≤ 4252550322123^1613*2500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306360697 2500000000 4252550322123 10000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2194315649/10000000000 : ℝ)^2125 ≤ (2711712403141/20000000000000 : ℝ)^1613 := by
    have hnat : (2194315649 : ℕ)^2125*20000000000000^1613 ≤ 2711712403141^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194315649 10000000000 2711712403141 20000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070925281/2000000000 : ℝ), (1306360697/2500000000 : ℝ), (-2194315649/10000000000 : ℝ)] ![(43915934746337/100000000000000 : ℝ), (4252550322123/10000000000000 : ℝ), (2711712403141/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070925281/2000000000 : ℝ)|^2125 ≤ (43915934746337/100000000000000 : ℝ)^1613
        have hw : |(1070925281/2000000000 : ℝ)|=(1070925281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1306360697/2500000000 : ℝ)|^2125 ≤ (4252550322123/10000000000000 : ℝ)^1613
        have hw : |(1306360697/2500000000 : ℝ)|=(1306360697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2194315649/10000000000 : ℝ)|^2125 ≤ (2711712403141/20000000000000 : ℝ)^1613
        have hw : |(-2194315649/10000000000 : ℝ)|=(2194315649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s3_3 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4338968897/10000000000 : ℝ)*x 0 + (4129504827/10000000000 : ℝ)*x 1 + (2279286889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4338968897/10000000000 : ℝ)^2125 ≤ (4160978179913/12500000000000 : ℝ)^1613 := by
    have hnat : (4338968897 : ℕ)^2125*12500000000000^1613 ≤ 4160978179913^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338968897 10000000000 4160978179913 12500000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4129504827/10000000000 : ℝ)^2125 ≤ (15593584281353/50000000000000 : ℝ)^1613 := by
    have hnat : (4129504827 : ℕ)^2125*50000000000000^1613 ≤ 15593584281353^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129504827 10000000000 15593584281353 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2279286889/5000000000 : ℝ)^2125 ≤ (17762502987831/50000000000000 : ℝ)^1613 := by
    have hnat : (2279286889 : ℕ)^2125*50000000000000^1613 ≤ 17762502987831^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279286889 5000000000 17762502987831 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4338968897/10000000000 : ℝ), (4129504827/10000000000 : ℝ), (2279286889/5000000000 : ℝ)] ![(4160978179913/12500000000000 : ℝ), (15593584281353/50000000000000 : ℝ), (17762502987831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4338968897/10000000000 : ℝ)|^2125 ≤ (4160978179913/12500000000000 : ℝ)^1613
        have hw : |(4338968897/10000000000 : ℝ)|=(4338968897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4129504827/10000000000 : ℝ)|^2125 ≤ (15593584281353/50000000000000 : ℝ)^1613
        have hw : |(4129504827/10000000000 : ℝ)|=(4129504827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2279286889/5000000000 : ℝ)|^2125 ≤ (17762502987831/50000000000000 : ℝ)^1613
        have hw : |(2279286889/5000000000 : ℝ)|=(2279286889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s3_4 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2087404679/10000000000 : ℝ)*x 0 + (5226344193/10000000000 : ℝ)*x 1 + (169795763/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087404679/10000000000 : ℝ)^2125 ≤ (793442691289/6250000000000 : ℝ)^1613 := by
    have hnat : (2087404679 : ℕ)^2125*6250000000000^1613 ≤ 793442691289^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087404679 10000000000 793442691289 6250000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5226344193/10000000000 : ℝ)^2125 ≤ (2126758389837/5000000000000 : ℝ)^1613 := by
    have hnat : (5226344193 : ℕ)^2125*5000000000000^1613 ≤ 2126758389837^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226344193 10000000000 2126758389837 5000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169795763/312500000 : ℝ)^2125 ≤ (44769749124953/100000000000000 : ℝ)^1613 := by
    have hnat : (169795763 : ℕ)^2125*100000000000000^1613 ≤ 44769749124953^1613*312500000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169795763 312500000 44769749124953 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2087404679/10000000000 : ℝ), (5226344193/10000000000 : ℝ), (169795763/312500000 : ℝ)] ![(793442691289/6250000000000 : ℝ), (2126758389837/5000000000000 : ℝ), (44769749124953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2087404679/10000000000 : ℝ)|^2125 ≤ (793442691289/6250000000000 : ℝ)^1613
        have hw : |(-2087404679/10000000000 : ℝ)|=(2087404679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5226344193/10000000000 : ℝ)|^2125 ≤ (2126758389837/5000000000000 : ℝ)^1613
        have hw : |(5226344193/10000000000 : ℝ)|=(5226344193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169795763/312500000 : ℝ)|^2125 ≤ (44769749124953/100000000000000 : ℝ)^1613
        have hw : |(169795763/312500000 : ℝ)|=(169795763/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s3_5 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2650571801/5000000000 : ℝ)*x 0 + (-496573651/2500000000 : ℝ)*x 1 + (169795781/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650571801/5000000000 : ℝ)^2125 ≤ (2708686303239/6250000000000 : ℝ)^1613 := by
    have hnat : (2650571801 : ℕ)^2125*6250000000000^1613 ≤ 2708686303239^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650571801 5000000000 2708686303239 6250000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (496573651/2500000000 : ℝ)^2125 ≤ (2972815938267/25000000000000 : ℝ)^1613 := by
    have hnat : (496573651 : ℕ)^2125*25000000000000^1613 ≤ 2972815938267^1613*2500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496573651 2500000000 2972815938267 25000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169795781/312500000 : ℝ)^2125 ≤ (4476975537747/10000000000000 : ℝ)^1613 := by
    have hnat : (169795781 : ℕ)^2125*10000000000000^1613 ≤ 4476975537747^1613*312500000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169795781 312500000 4476975537747 10000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650571801/5000000000 : ℝ), (-496573651/2500000000 : ℝ), (169795781/312500000 : ℝ)] ![(2708686303239/6250000000000 : ℝ), (2972815938267/25000000000000 : ℝ), (4476975537747/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650571801/5000000000 : ℝ)|^2125 ≤ (2708686303239/6250000000000 : ℝ)^1613
        have hw : |(2650571801/5000000000 : ℝ)|=(2650571801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-496573651/2500000000 : ℝ)|^2125 ≤ (2972815938267/25000000000000 : ℝ)^1613
        have hw : |(-496573651/2500000000 : ℝ)|=(496573651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169795781/312500000 : ℝ)|^2125 ≤ (4476975537747/10000000000000 : ℝ)^1613
        have hw : |(169795781/312500000 : ℝ)|=(169795781/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s3_6 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5301145183/10000000000 : ℝ)*x 0 + (1086692847/2000000000 : ℝ)*x 1 + (-1986293487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301145183/10000000000 : ℝ)^2125 ≤ (433389978799/1000000000000 : ℝ)^1613 := by
    have hnat : (5301145183 : ℕ)^2125*1000000000000^1613 ≤ 433389978799^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301145183 10000000000 433389978799 1000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086692847/2000000000 : ℝ)^2125 ≤ (22384873580093/50000000000000 : ℝ)^1613 := by
    have hnat : (1086692847 : ℕ)^2125*50000000000000^1613 ≤ 22384873580093^1613*2000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086692847 2000000000 22384873580093 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1986293487/10000000000 : ℝ)^2125 ≤ (11891254943349/100000000000000 : ℝ)^1613 := by
    have hnat : (1986293487 : ℕ)^2125*100000000000000^1613 ≤ 11891254943349^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986293487 10000000000 11891254943349 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301145183/10000000000 : ℝ), (1086692847/2000000000 : ℝ), (-1986293487/10000000000 : ℝ)] ![(433389978799/1000000000000 : ℝ), (22384873580093/50000000000000 : ℝ), (11891254943349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301145183/10000000000 : ℝ)|^2125 ≤ (433389978799/1000000000000 : ℝ)^1613
        have hw : |(5301145183/10000000000 : ℝ)|=(5301145183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086692847/2000000000 : ℝ)|^2125 ≤ (22384873580093/50000000000000 : ℝ)^1613
        have hw : |(1086692847/2000000000 : ℝ)|=(1086692847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1986293487/10000000000 : ℝ)|^2125 ≤ (11891254943349/100000000000000 : ℝ)^1613
        have hw : |(-1986293487/10000000000 : ℝ)|=(1986293487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s3_7 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2169507859/5000000000 : ℝ)*x 0 + (4556723227/10000000000 : ℝ)*x 1 + (4131366547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169507859/5000000000 : ℝ)^2125 ≤ (16644149330629/50000000000000 : ℝ)^1613 := by
    have hnat : (2169507859 : ℕ)^2125*50000000000000^1613 ≤ 16644149330629^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169507859 5000000000 16644149330629 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4556723227/10000000000 : ℝ)^2125 ≤ (35506008197473/100000000000000 : ℝ)^1613 := by
    have hnat : (4556723227 : ℕ)^2125*100000000000000^1613 ≤ 35506008197473^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4556723227 10000000000 35506008197473 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4131366547/10000000000 : ℝ)^2125 ≤ (6241138625137/20000000000000 : ℝ)^1613 := by
    have hnat : (4131366547 : ℕ)^2125*20000000000000^1613 ≤ 6241138625137^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131366547 10000000000 6241138625137 20000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169507859/5000000000 : ℝ), (4556723227/10000000000 : ℝ), (4131366547/10000000000 : ℝ)] ![(16644149330629/50000000000000 : ℝ), (35506008197473/100000000000000 : ℝ), (6241138625137/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169507859/5000000000 : ℝ)|^2125 ≤ (16644149330629/50000000000000 : ℝ)^1613
        have hw : |(2169507859/5000000000 : ℝ)|=(2169507859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4556723227/10000000000 : ℝ)|^2125 ≤ (35506008197473/100000000000000 : ℝ)^1613
        have hw : |(4556723227/10000000000 : ℝ)|=(4556723227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4131366547/10000000000 : ℝ)|^2125 ≤ (6241138625137/20000000000000 : ℝ)^1613
        have hw : |(4131366547/10000000000 : ℝ)|=(4131366547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1290_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8163/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (949/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10649/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15069/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8163/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (949/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8163/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (949/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8163/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (949/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8163/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (949/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8163/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (949/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8163/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (949/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (949/10000 : ℝ) ^ (4249/1024 : ℝ) ≤ (570497886247219/10000000000000000000 : ℝ) := by
    have hpowers : (949/10000 : ℝ)^4249 ≤ (570497886247219/10000000000000000000 : ℝ)^1024 := by
      have hnat : (949 : ℕ)^4249*10000000000000000000^1024 ≤ 570497886247219^1024*10000^4249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        949 10000 570497886247219 10000000000000000000 4249 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (949/10000 : ℝ)) (X := (570497886247219/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8163/50000 : ℝ) ^ (4249/1024 : ℝ) ≤ (54189150238832803/100000000000000000000 : ℝ) := by
    have hpowers : (8163/50000 : ℝ)^4249 ≤ (54189150238832803/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8163 : ℕ)^4249*100000000000000000000^1024 ≤ 54189150238832803^1024*50000^4249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8163 50000 54189150238832803 100000000000000000000 4249 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8163/50000 : ℝ)) (X := (54189150238832803/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000570497886247219/5000000000000000000 : ℝ) ≤ (5000137482829197/5000000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (5000570497886247219/5000000000000000000 : ℝ)^1024 ≤ (5000137482829197/5000000000000000 : ℝ)^4249 := by
      have hnat : (5000570497886247219 : ℕ)^1024*5000000000000000^4249 ≤ 5000137482829197^4249*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000570497886247219 5000000000000000000 5000137482829197 5000000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000137482829197/5000000000000000 : ℝ)) (X := (5000570497886247219/5000000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100059894129101304993/100000000000000000000 : ℝ) ≤ (2500360776962189/2500000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (100059894129101304993/100000000000000000000 : ℝ)^1024 ≤ (2500360776962189/2500000000000000 : ℝ)^4249 := by
      have hnat : (100059894129101304993 : ℕ)^1024*2500000000000000^4249 ≤ 2500360776962189^4249*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100059894129101304993 100000000000000000000 2500360776962189 2500000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500360776962189/2500000000000000 : ℝ)) (X := (100059894129101304993/100000000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50054189150238832803/50000000000000000000 : ℝ) ≤ (5001305625019559/5000000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (50054189150238832803/50000000000000000000 : ℝ)^1024 ≤ (5001305625019559/5000000000000000 : ℝ)^4249 := by
      have hnat : (50054189150238832803 : ℕ)^1024*5000000000000000^4249 ≤ 5001305625019559^4249*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50054189150238832803 50000000000000000000 5001305625019559 5000000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001305625019559/5000000000000000 : ℝ)) (X := (50054189150238832803/50000000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(570497886247219/10000000000000000000 : ℝ) ≤ ((2135615885202115957/2136250000000000000 : ℝ)+2*(584071095181/341800000000000 : ℝ)*(949/10000 : ℝ))^(4249/1024 : ℝ) := by
    rw [show (2135615885202115957/2136250000000000000 : ℝ)+2*(584071095181/341800000000000 : ℝ)*(949/10000 : ℝ)=(5000137482829197/5000000000000000 : ℝ) by norm_num, show 1+2*(570497886247219/10000000000000000000 : ℝ)=(5000570497886247219/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(54189150238832803/100000000000000000000 : ℝ)+(570497886247219/10000000000000000000 : ℝ) ≤ ((2135615885202115957/2136250000000000000 : ℝ)+(584071095181/341800000000000 : ℝ)*((8163/50000 : ℝ)+(949/10000 : ℝ)))^(4249/1024 : ℝ) := by
    rw [show (2135615885202115957/2136250000000000000 : ℝ)+(584071095181/341800000000000 : ℝ)*((8163/50000 : ℝ)+(949/10000 : ℝ))=(2500360776962189/2500000000000000 : ℝ) by norm_num, show 1+(54189150238832803/100000000000000000000 : ℝ)+(570497886247219/10000000000000000000 : ℝ)=(100059894129101304993/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(54189150238832803/100000000000000000000 : ℝ) ≤ ((2135615885202115957/2136250000000000000 : ℝ)+2*(584071095181/341800000000000 : ℝ)*(8163/50000 : ℝ))^(4249/1024 : ℝ) := by
    rw [show (2135615885202115957/2136250000000000000 : ℝ)+2*(584071095181/341800000000000 : ℝ)*(8163/50000 : ℝ)=(5001305625019559/5000000000000000 : ℝ) by norm_num, show 1+2*(54189150238832803/100000000000000000000 : ℝ)=(50054189150238832803/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2135615885202115957/2136250000000000000 : ℝ)*(X 1 0+X 2 0)+(584071095181/341800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (949/10000 : ℝ)) (hi := (8163/50000 : ℝ)) (c := (2135615885202115957/2136250000000000000 : ℝ)) (alpha := (584071095181/341800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2135615885202115957/2136250000000000000 : ℝ)*(X 0 1+X 2 1)+(584071095181/341800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (949/10000 : ℝ)) (hi := (8163/50000 : ℝ)) (c := (2135615885202115957/2136250000000000000 : ℝ)) (alpha := (584071095181/341800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2135615885202115957/2136250000000000000 : ℝ)*(X 0 2+X 1 2)+(584071095181/341800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (949/10000 : ℝ)) (hi := (8163/50000 : ℝ)) (c := (2135615885202115957/2136250000000000000 : ℝ)) (alpha := (584071095181/341800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-260922781/1250000000 : ℝ)*X 0 0+(339648191/625000000 : ℝ)*X 0 1+(1306360753/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338656587/2500000000 : ℝ)*X 1 0+(-438863069/2000000000 : ℝ)*X 1 1+(1306360769/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070925281/2000000000 : ℝ)*X 2 0+(1306360697/2500000000 : ℝ)*X 2 1+(-2194315649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4338968897/10000000000 : ℝ)*X 0 0+(4129504827/10000000000 : ℝ)*X 0 1+(2279286889/5000000000 : ℝ)*X 0 2+(4338968897/10000000000 : ℝ)*X 1 0+(4129504827/10000000000 : ℝ)*X 1 1+(2279286889/5000000000 : ℝ)*X 1 2+(4338968897/10000000000 : ℝ)*X 2 0+(4129504827/10000000000 : ℝ)*X 2 1+(2279286889/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2087404679/10000000000 : ℝ)*X 0 0+(5226344193/10000000000 : ℝ)*X 0 1+(169795763/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2650571801/5000000000 : ℝ)*X 1 0+(-496573651/2500000000 : ℝ)*X 1 1+(169795781/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301145183/10000000000 : ℝ)*X 2 0+(1086692847/2000000000 : ℝ)*X 2 1+(-1986293487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2169507859/5000000000 : ℝ)*X 0 0+(4556723227/10000000000 : ℝ)*X 0 1+(4131366547/10000000000 : ℝ)*X 0 2+(2169507859/5000000000 : ℝ)*X 1 0+(4556723227/10000000000 : ℝ)*X 1 1+(4131366547/10000000000 : ℝ)*X 1 2+(2169507859/5000000000 : ℝ)*X 2 0+(4556723227/10000000000 : ℝ)*X 2 1+(4131366547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (86485197017804635457687343/13351562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (158888623/12500000000000 : ℝ)*(base19) + (128342631/10000000000000 : ℝ)*(base23) + (29316933/50000000000000 : ℝ)*(lower2) + (326034863/100000000000000 : ℝ)*(upper3) + (37946997/100000000000000 : ℝ)*(lower4) + (1779256303699391/50000000000000 : ℝ)*(major0) + (1779256303699391/50000000000000 : ℝ)*(major1) + (1779256303699391/50000000000000 : ℝ)*(major2) + (191454440103719/4000000000000 : ℝ)*(sp0) + (598296838215021/12500000000000 : ℝ)*(sp1) + (4786374693402843/100000000000000 : ℝ)*(sp2) + (291329523848559/12500000000000 : ℝ)*(sp3) + (7487118089/50000000000000 : ℝ)*(sp4) + (6415631071/50000000000000 : ℝ)*(sp7) + (1165324511025307/50000000000000 : ℝ)*(f.failure) + (149574249275911/3125000000000 : ℝ)*(f.sum) + (50632133368739/8545000000000000000000000000 : ℝ)*base66 + (665344085179649063/106812500000000000000000000000000 : ℝ)*base68 + (292895424564274063/106812500000000000000000000000000 : ℝ)*base70 + (685768480045149063/106812500000000000000000000000000 : ℝ)*base72 + (6890534206039/8545000000000000000000000000 : ℝ)*base74 + (301807306674475937/106812500000000000000000000000000 : ℝ)*base75 + (102794715248836563/106812500000000000000000000000000 : ℝ)*base78 + (595200351677774063/106812500000000000000000000000000 : ℝ)*base80 + (252303586009/2136250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (20108231/5000000000000000000000 : ℝ)*base89 + (20108231/5000000000000000000000 : ℝ)*base91 + (20108231/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (139461542969452034089322601/13351562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (155675201/50000000000000 : ℝ)*(base19) + (2776554641/100000000000000 : ℝ)*(base23) + (155857779/50000000000000 : ℝ)*(upper3) + (302158113/100000000000000 : ℝ)*(lower4) + (85918549/50000000000000 : ℝ)*(upper5) + (897386190349121/25000000000000 : ℝ)*(major0) + (897386190349121/25000000000000 : ℝ)*(major1) + (897386190349121/25000000000000 : ℝ)*(major2) + (5218832493/100000000000000 : ℝ)*(sp1) + (25174178167/50000000000000 : ℝ)*(sp2) + (4828115632927719/100000000000000 : ℝ)*(sp4) + (603513762843103/12500000000000 : ℝ)*(sp5) + (603507813502093/12500000000000 : ℝ)*(sp6) + (2350973541687411/100000000000000 : ℝ)*(sp7) + (2350973541687411/100000000000000 : ℝ)*(f.failure) + (4828115632927719/100000000000000 : ℝ)*(f.sum) + (14395179053063/8545000000000000000000000000 : ℝ)*base66 + (70369247342655047/53406250000000000000000000000000 : ℝ)*base67 + (92030509542248797/53406250000000000000000000000000 : ℝ)*base69 + (524136163654717547/53406250000000000000000000000000 : ℝ)*base71 + (3524229118709/4272500000000000000000000000 : ℝ)*base74 + (61197865250123797/53406250000000000000000000000000 : ℝ)*base75 + (175831185739405047/53406250000000000000000000000000 : ℝ)*base77 + (141122687689998797/53406250000000000000000000000000 : ℝ)*base79 + (42213373796233/8545000000000000000000000000 : ℝ)*base82 + (44379137/10000000000000000000000 : ℝ)*base90 + (44379137/10000000000000000000000 : ℝ)*base92 + (44379137/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1290_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8163/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (949/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10649/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15069/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1290_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1290_s4_0 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-417864379/2000000000 : ℝ)*x 0 + (5419086371/10000000000 : ℝ)*x 1 + (2619728243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417864379/2000000000 : ℝ)^2125 ≤ (3177611619201/25000000000000 : ℝ)^1613 := by
    have hnat : (417864379 : ℕ)^2125*25000000000000^1613 ≤ 3177611619201^1613*2000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417864379 2000000000 3177611619201 25000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419086371/10000000000 : ℝ)^2125 ≤ (2788358756851/6250000000000 : ℝ)^1613 := by
    have hnat : (5419086371 : ℕ)^2125*6250000000000^1613 ≤ 2788358756851^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419086371 10000000000 2788358756851 6250000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619728243/5000000000 : ℝ)^2125 ≤ (42675813397303/100000000000000 : ℝ)^1613 := by
    have hnat : (2619728243 : ℕ)^2125*100000000000000^1613 ≤ 42675813397303^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619728243 5000000000 42675813397303 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-417864379/2000000000 : ℝ), (5419086371/10000000000 : ℝ), (2619728243/5000000000 : ℝ)] ![(3177611619201/25000000000000 : ℝ), (2788358756851/6250000000000 : ℝ), (42675813397303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-417864379/2000000000 : ℝ)|^2125 ≤ (3177611619201/25000000000000 : ℝ)^1613
        have hw : |(-417864379/2000000000 : ℝ)|=(417864379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419086371/10000000000 : ℝ)|^2125 ≤ (2788358756851/6250000000000 : ℝ)^1613
        have hw : |(5419086371/10000000000 : ℝ)|=(5419086371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619728243/5000000000 : ℝ)|^2125 ≤ (42675813397303/100000000000000 : ℝ)^1613
        have hw : |(2619728243/5000000000 : ℝ)|=(2619728243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s4_1 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5350765047/10000000000 : ℝ)*x 0 + (-436192503/2000000000 : ℝ)*x 1 + (5239456429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350765047/10000000000 : ℝ)^2125 ≤ (1754968729811/4000000000000 : ℝ)^1613 := by
    have hnat : (5350765047 : ℕ)^2125*4000000000000^1613 ≤ 1754968729811^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350765047 10000000000 1754968729811 4000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (436192503/2000000000 : ℝ)^2125 ≤ (1681246119303/12500000000000 : ℝ)^1613 := by
    have hnat : (436192503 : ℕ)^2125*12500000000000^1613 ≤ 1681246119303^1613*2000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436192503 2000000000 1681246119303 12500000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239456429/10000000000 : ℝ)^2125 ≤ (83351196847/195312500000 : ℝ)^1613 := by
    have hnat : (5239456429 : ℕ)^2125*195312500000^1613 ≤ 83351196847^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239456429 10000000000 83351196847 195312500000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350765047/10000000000 : ℝ), (-436192503/2000000000 : ℝ), (5239456429/10000000000 : ℝ)] ![(1754968729811/4000000000000 : ℝ), (1681246119303/12500000000000 : ℝ), (83351196847/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350765047/10000000000 : ℝ)|^2125 ≤ (1754968729811/4000000000000 : ℝ)^1613
        have hw : |(5350765047/10000000000 : ℝ)|=(5350765047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-436192503/2000000000 : ℝ)|^2125 ≤ (1681246119303/12500000000000 : ℝ)^1613
        have hw : |(-436192503/2000000000 : ℝ)|=(436192503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239456429/10000000000 : ℝ)|^2125 ≤ (83351196847/195312500000 : ℝ)^1613
        have hw : |(5239456429/10000000000 : ℝ)|=(5239456429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s4_2 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2675382521/5000000000 : ℝ)*x 0 + (1309864113/2500000000 : ℝ)*x 1 + (-2180962491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675382521/5000000000 : ℝ)^2125 ≤ (43874218191263/100000000000000 : ℝ)^1613 := by
    have hnat : (2675382521 : ℕ)^2125*100000000000000^1613 ≤ 43874218191263^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675382521 5000000000 43874218191263 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309864113/2500000000 : ℝ)^2125 ≤ (21337906516233/50000000000000 : ℝ)^1613 := by
    have hnat : (1309864113 : ℕ)^2125*50000000000000^1613 ≤ 21337906516233^1613*2500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309864113 2500000000 21337906516233 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2180962491/10000000000 : ℝ)^2125 ≤ (3362492189859/25000000000000 : ℝ)^1613 := by
    have hnat : (2180962491 : ℕ)^2125*25000000000000^1613 ≤ 3362492189859^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180962491 10000000000 3362492189859 25000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675382521/5000000000 : ℝ), (1309864113/2500000000 : ℝ), (-2180962491/10000000000 : ℝ)] ![(43874218191263/100000000000000 : ℝ), (21337906516233/50000000000000 : ℝ), (3362492189859/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675382521/5000000000 : ℝ)|^2125 ≤ (43874218191263/100000000000000 : ℝ)^1613
        have hw : |(2675382521/5000000000 : ℝ)|=(2675382521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309864113/2500000000 : ℝ)|^2125 ≤ (21337906516233/50000000000000 : ℝ)^1613
        have hw : |(1309864113/2500000000 : ℝ)|=(1309864113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2180962491/10000000000 : ℝ)|^2125 ≤ (3362492189859/25000000000000 : ℝ)^1613
        have hw : |(-2180962491/10000000000 : ℝ)|=(2180962491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s4_3 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2170071083/5000000000 : ℝ)*x 0 + (4159441433/10000000000 : ℝ)*x 1 + (141510677/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170071083/5000000000 : ℝ)^2125 ≤ (16649842105223/50000000000000 : ℝ)^1613 := by
    have hnat : (2170071083 : ℕ)^2125*50000000000000^1613 ≤ 16649842105223^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170071083 5000000000 16649842105223 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4159441433/10000000000 : ℝ)^2125 ≤ (7871341459861/25000000000000 : ℝ)^1613 := by
    have hnat : (4159441433 : ℕ)^2125*25000000000000^1613 ≤ 7871341459861^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4159441433 10000000000 7871341459861 25000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141510677/312500000 : ℝ)^2125 ≤ (4401868741343/12500000000000 : ℝ)^1613 := by
    have hnat : (141510677 : ℕ)^2125*12500000000000^1613 ≤ 4401868741343^1613*312500000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141510677 312500000 4401868741343 12500000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170071083/5000000000 : ℝ), (4159441433/10000000000 : ℝ), (141510677/312500000 : ℝ)] ![(16649842105223/50000000000000 : ℝ), (7871341459861/25000000000000 : ℝ), (4401868741343/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170071083/5000000000 : ℝ)|^2125 ≤ (16649842105223/50000000000000 : ℝ)^1613
        have hw : |(2170071083/5000000000 : ℝ)|=(2170071083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4159441433/10000000000 : ℝ)|^2125 ≤ (7871341459861/25000000000000 : ℝ)^1613
        have hw : |(4159441433/10000000000 : ℝ)|=(4159441433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(141510677/312500000 : ℝ)|^2125 ≤ (4401868741343/12500000000000 : ℝ)^1613
        have hw : |(141510677/312500000 : ℝ)|=(141510677/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s4_4 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1044668091/5000000000 : ℝ)*x 0 + (524012337/1000000000 : ℝ)*x 1 + (5418416001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044668091/5000000000 : ℝ)^2125 ≤ (2542112196207/20000000000000 : ℝ)^1613 := by
    have hnat : (1044668091 : ℕ)^2125*20000000000000^1613 ≤ 2542112196207^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044668091 5000000000 2542112196207 20000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524012337/1000000000 : ℝ)^2125 ≤ (21341484771773/50000000000000 : ℝ)^1613 := by
    have hnat : (524012337 : ℕ)^2125*50000000000000^1613 ≤ 21341484771773^1613*1000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524012337 1000000000 21341484771773 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418416001/10000000000 : ℝ)^2125 ≤ (44606469460753/100000000000000 : ℝ)^1613 := by
    have hnat : (5418416001 : ℕ)^2125*100000000000000^1613 ≤ 44606469460753^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418416001 10000000000 44606469460753 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1044668091/5000000000 : ℝ), (524012337/1000000000 : ℝ), (5418416001/10000000000 : ℝ)] ![(2542112196207/20000000000000 : ℝ), (21341484771773/50000000000000 : ℝ), (44606469460753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1044668091/5000000000 : ℝ)|^2125 ≤ (2542112196207/20000000000000 : ℝ)^1613
        have hw : |(-1044668091/5000000000 : ℝ)|=(1044668091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524012337/1000000000 : ℝ)|^2125 ≤ (21341484771773/50000000000000 : ℝ)^1613
        have hw : |(524012337/1000000000 : ℝ)|=(524012337/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418416001/10000000000 : ℝ)|^2125 ≤ (44606469460753/100000000000000 : ℝ)^1613
        have hw : |(5418416001/10000000000 : ℝ)|=(5418416001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s4_5 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652393399/5000000000 : ℝ)*x 0 + (-1001001381/5000000000 : ℝ)*x 1 + (677301979/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652393399/5000000000 : ℝ)^2125 ≤ (43378223977283/100000000000000 : ℝ)^1613 := by
    have hnat : (2652393399 : ℕ)^2125*100000000000000^1613 ≤ 43378223977283^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652393399 5000000000 43378223977283 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1001001381/5000000000 : ℝ)^2125 ≤ (3003827094709/25000000000000 : ℝ)^1613 := by
    have hnat : (1001001381 : ℕ)^2125*25000000000000^1613 ≤ 3003827094709^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001001381 5000000000 3003827094709 25000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677301979/1250000000 : ℝ)^2125 ≤ (44606467627861/100000000000000 : ℝ)^1613 := by
    have hnat : (677301979 : ℕ)^2125*100000000000000^1613 ≤ 44606467627861^1613*1250000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677301979 1250000000 44606467627861 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652393399/5000000000 : ℝ), (-1001001381/5000000000 : ℝ), (677301979/1250000000 : ℝ)] ![(43378223977283/100000000000000 : ℝ), (3003827094709/25000000000000 : ℝ), (44606467627861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652393399/5000000000 : ℝ)|^2125 ≤ (43378223977283/100000000000000 : ℝ)^1613
        have hw : |(2652393399/5000000000 : ℝ)|=(2652393399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1001001381/5000000000 : ℝ)|^2125 ≤ (3003827094709/25000000000000 : ℝ)^1613
        have hw : |(-1001001381/5000000000 : ℝ)|=(1001001381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677301979/1250000000 : ℝ)|^2125 ≤ (44606467627861/100000000000000 : ℝ)^1613
        have hw : |(677301979/1250000000 : ℝ)|=(677301979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s4_6 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5304786353/10000000000 : ℝ)*x 0 + (5418416311/10000000000 : ℝ)*x 1 + (-250250339/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304786353/10000000000 : ℝ)^2125 ≤ (43378219183389/100000000000000 : ℝ)^1613 := by
    have hnat : (5304786353 : ℕ)^2125*100000000000000^1613 ≤ 43378219183389^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304786353 10000000000 43378219183389 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418416311/10000000000 : ℝ)^2125 ≤ (44606472822861/100000000000000 : ℝ)^1613 := by
    have hnat : (5418416311 : ℕ)^2125*100000000000000^1613 ≤ 44606472822861^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418416311 10000000000 44606472822861 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250250339/1250000000 : ℝ)^2125 ≤ (12015307983501/100000000000000 : ℝ)^1613 := by
    have hnat : (250250339 : ℕ)^2125*100000000000000^1613 ≤ 12015307983501^1613*1250000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250250339 1250000000 12015307983501 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304786353/10000000000 : ℝ), (5418416311/10000000000 : ℝ), (-250250339/1250000000 : ℝ)] ![(43378219183389/100000000000000 : ℝ), (44606472822861/100000000000000 : ℝ), (12015307983501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304786353/10000000000 : ℝ)|^2125 ≤ (43378219183389/100000000000000 : ℝ)^1613
        have hw : |(5304786353/10000000000 : ℝ)|=(5304786353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418416311/10000000000 : ℝ)|^2125 ≤ (44606472822861/100000000000000 : ℝ)^1613
        have hw : |(5418416311/10000000000 : ℝ)|=(5418416311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-250250339/1250000000 : ℝ)|^2125 ≤ (12015307983501/100000000000000 : ℝ)^1613
        have hw : |(-250250339/1250000000 : ℝ)|=(250250339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s4_7 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1085042903/2500000000 : ℝ)*x 0 + (1131743107/2500000000 : ℝ)*x 1 + (2080409059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085042903/2500000000 : ℝ)^2125 ≤ (6659996369569/20000000000000 : ℝ)^1613 := by
    have hnat : (1085042903 : ℕ)^2125*20000000000000^1613 ≤ 6659996369569^1613*2500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085042903 2500000000 6659996369569 20000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1131743107/2500000000 : ℝ)^2125 ≤ (35200922765249/100000000000000 : ℝ)^1613 := by
    have hnat : (1131743107 : ℕ)^2125*100000000000000^1613 ≤ 35200922765249^1613*2500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131743107 2500000000 35200922765249 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2080409059/5000000000 : ℝ)^2125 ≤ (31499095370027/100000000000000 : ℝ)^1613 := by
    have hnat : (2080409059 : ℕ)^2125*100000000000000^1613 ≤ 31499095370027^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080409059 5000000000 31499095370027 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085042903/2500000000 : ℝ), (1131743107/2500000000 : ℝ), (2080409059/5000000000 : ℝ)] ![(6659996369569/20000000000000 : ℝ), (35200922765249/100000000000000 : ℝ), (31499095370027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085042903/2500000000 : ℝ)|^2125 ≤ (6659996369569/20000000000000 : ℝ)^1613
        have hw : |(1085042903/2500000000 : ℝ)|=(1085042903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1131743107/2500000000 : ℝ)|^2125 ≤ (35200922765249/100000000000000 : ℝ)^1613
        have hw : |(1131743107/2500000000 : ℝ)|=(1131743107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2080409059/5000000000 : ℝ)|^2125 ≤ (31499095370027/100000000000000 : ℝ)^1613
        have hw : |(2080409059/5000000000 : ℝ)|=(2080409059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1290_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10649/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2737/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (59/400 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10649/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10649/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10649/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10649/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10649/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10649/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10649/100000 : ℝ) ^ (4249/1024 : ℝ) ≤ (57515061137597/625000000000000000 : ℝ) := by
    have hpowers : (10649/100000 : ℝ)^4249 ≤ (57515061137597/625000000000000000 : ℝ)^1024 := by
      have hnat : (10649 : ℕ)^4249*625000000000000000^1024 ≤ 57515061137597^1024*100000^4249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10649 100000 57515061137597 625000000000000000 4249 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10649/100000 : ℝ)) (X := (57515061137597/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15069/100000 : ℝ) ^ (4249/1024 : ℝ) ≤ (38862612083620931/100000000000000000000 : ℝ) := by
    have hpowers : (15069/100000 : ℝ)^4249 ≤ (38862612083620931/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15069 : ℕ)^4249*100000000000000000000^1024 ≤ 38862612083620931^1024*100000^4249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15069 100000 38862612083620931 100000000000000000000 4249 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15069/100000 : ℝ)) (X := (38862612083620931/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (312557515061137597/312500000000000000 : ℝ) ≤ (5000221760637931/5000000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (312557515061137597/312500000000000000 : ℝ)^1024 ≤ (5000221760637931/5000000000000000 : ℝ)^4249 := by
      have hnat : (312557515061137597 : ℕ)^1024*5000000000000000^4249 ≤ 5000221760637931^4249*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312557515061137597 312500000000000000 5000221760637931 5000000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000221760637931/5000000000000000 : ℝ)) (X := (312557515061137597/312500000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048065021865636451/100000000000000000000 : ℝ) ≤ (625072384100807/625000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (100048065021865636451/100000000000000000000 : ℝ)^1024 ≤ (625072384100807/625000000000000 : ℝ)^4249 := by
      have hnat : (100048065021865636451 : ℕ)^1024*625000000000000^4249 ≤ 625072384100807^4249*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048065021865636451 100000000000000000000 625072384100807 625000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625072384100807/625000000000000 : ℝ)) (X := (100048065021865636451/100000000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038862612083620931/50000000000000000000 : ℝ) ≤ (5000936384974981/5000000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (50038862612083620931/50000000000000000000 : ℝ)^1024 ≤ (5000936384974981/5000000000000000 : ℝ)^4249 := by
      have hnat : (50038862612083620931 : ℕ)^1024*5000000000000000^4249 ≤ 5000936384974981^4249*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038862612083620931 50000000000000000000 5000936384974981 5000000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000936384974981/5000000000000000 : ℝ)) (X := (50038862612083620931/50000000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(57515061137597/625000000000000000 : ℝ) ≤ ((169949001134264689/170000000000000000 : ℝ)+2*(1099422057/680000000000 : ℝ)*(10649/100000 : ℝ))^(4249/1024 : ℝ) := by
    rw [show (169949001134264689/170000000000000000 : ℝ)+2*(1099422057/680000000000 : ℝ)*(10649/100000 : ℝ)=(5000221760637931/5000000000000000 : ℝ) by norm_num, show 1+2*(57515061137597/625000000000000000 : ℝ)=(312557515061137597/312500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38862612083620931/100000000000000000000 : ℝ)+(57515061137597/625000000000000000 : ℝ) ≤ ((169949001134264689/170000000000000000 : ℝ)+(1099422057/680000000000 : ℝ)*((15069/100000 : ℝ)+(10649/100000 : ℝ)))^(4249/1024 : ℝ) := by
    rw [show (169949001134264689/170000000000000000 : ℝ)+(1099422057/680000000000 : ℝ)*((15069/100000 : ℝ)+(10649/100000 : ℝ))=(625072384100807/625000000000000 : ℝ) by norm_num, show 1+(38862612083620931/100000000000000000000 : ℝ)+(57515061137597/625000000000000000 : ℝ)=(100048065021865636451/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38862612083620931/100000000000000000000 : ℝ) ≤ ((169949001134264689/170000000000000000 : ℝ)+2*(1099422057/680000000000 : ℝ)*(15069/100000 : ℝ))^(4249/1024 : ℝ) := by
    rw [show (169949001134264689/170000000000000000 : ℝ)+2*(1099422057/680000000000 : ℝ)*(15069/100000 : ℝ)=(5000936384974981/5000000000000000 : ℝ) by norm_num, show 1+2*(38862612083620931/100000000000000000000 : ℝ)=(50038862612083620931/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (169949001134264689/170000000000000000 : ℝ)*(X 1 0+X 2 0)+(1099422057/680000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (10649/100000 : ℝ)) (hi := (15069/100000 : ℝ)) (c := (169949001134264689/170000000000000000 : ℝ)) (alpha := (1099422057/680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (169949001134264689/170000000000000000 : ℝ)*(X 0 1+X 2 1)+(1099422057/680000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (10649/100000 : ℝ)) (hi := (15069/100000 : ℝ)) (c := (169949001134264689/170000000000000000 : ℝ)) (alpha := (1099422057/680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (169949001134264689/170000000000000000 : ℝ)*(X 0 2+X 1 2)+(1099422057/680000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (10649/100000 : ℝ)) (hi := (15069/100000 : ℝ)) (c := (169949001134264689/170000000000000000 : ℝ)) (alpha := (1099422057/680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-417864379/2000000000 : ℝ)*X 0 0+(5419086371/10000000000 : ℝ)*X 0 1+(2619728243/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350765047/10000000000 : ℝ)*X 1 0+(-436192503/2000000000 : ℝ)*X 1 1+(5239456429/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675382521/5000000000 : ℝ)*X 2 0+(1309864113/2500000000 : ℝ)*X 2 1+(-2180962491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2170071083/5000000000 : ℝ)*X 0 0+(4159441433/10000000000 : ℝ)*X 0 1+(141510677/312500000 : ℝ)*X 0 2+(2170071083/5000000000 : ℝ)*X 1 0+(4159441433/10000000000 : ℝ)*X 1 1+(141510677/312500000 : ℝ)*X 1 2+(2170071083/5000000000 : ℝ)*X 2 0+(4159441433/10000000000 : ℝ)*X 2 1+(141510677/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1044668091/5000000000 : ℝ)*X 0 0+(524012337/1000000000 : ℝ)*X 0 1+(5418416001/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652393399/5000000000 : ℝ)*X 1 0+(-1001001381/5000000000 : ℝ)*X 1 1+(677301979/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304786353/10000000000 : ℝ)*X 2 0+(5418416311/10000000000 : ℝ)*X 2 1+(-250250339/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1085042903/2500000000 : ℝ)*X 0 0+(1131743107/2500000000 : ℝ)*X 0 1+(2080409059/5000000000 : ℝ)*X 0 2+(1085042903/2500000000 : ℝ)*X 1 0+(1131743107/2500000000 : ℝ)*X 1 1+(2080409059/5000000000 : ℝ)*X 1 2+(1085042903/2500000000 : ℝ)*X 2 0+(1131743107/2500000000 : ℝ)*X 2 1+(2080409059/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39914931196528189408043649/4250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1025272031/50000000000000 : ℝ)*(base19) + (499401069/25000000000000 : ℝ)*(base23) + (199557/781250000000 : ℝ)*(lower2) + (230180879/100000000000000 : ℝ)*(upper3) + (1725961/781250000000 : ℝ)*(upper5) + (2069470816444151/50000000000000 : ℝ)*(major0) + (2069470816444151/50000000000000 : ℝ)*(major1) + (2069470816444151/50000000000000 : ℝ)*(major2) + (2783520917343063/50000000000000 : ℝ)*(sp0) + (2783539847902653/50000000000000 : ℝ)*(sp1) + (5567079748745091/100000000000000 : ℝ)*(sp2) + (108431215557173/4000000000000 : ℝ)*(sp3) + (19955831621/50000000000000 : ℝ)*(sp4) + (5204359903/25000000000000 : ℝ)*(sp7) + (2710801206368937/100000000000000 : ℝ)*(f.failure) + (695885218293671/12500000000000 : ℝ)*(f.sum) + (41362490047/17000000000000000000000000 : ℝ)*base65 + (47643553622134039/8500000000000000000000000000000 : ℝ)*base67 + (134225908972634039/8500000000000000000000000000000 : ℝ)*base69 + (118759169725634039/8500000000000000000000000000000 : ℝ)*base71 + (314243873/85000000000000000000000 : ℝ)*base74 + (89747416706634039/8500000000000000000000000000000 : ℝ)*base75 + (183104429485634039/8500000000000000000000000000000 : ℝ)*base77 + (255895909431134039/8500000000000000000000000000000 : ℝ)*base79 + (3753506511/2125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (71172979/10000000000000000000000 : ℝ)*base90 + (71172979/10000000000000000000000 : ℝ)*base92 + (71172979/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31065783129810666651/3400000000000000000000000 : ℝ) := by norm_num
    linear_combination (138135017/6250000000000 : ℝ)*(base19) + (236343497/12500000000000 : ℝ)*(base23) + (12628509/5000000000000 : ℝ)*(upper3) + (10443103/20000000000000 : ℝ)*(lower4) + (91766367/100000000000000 : ℝ)*(upper5) + (521239794082091/12500000000000 : ℝ)*(major0) + (521239794082091/12500000000000 : ℝ)*(major1) + (521239794082091/12500000000000 : ℝ)*(major2) + (1858649267/5000000000000 : ℝ)*(sp1) + (10811916983/25000000000000 : ℝ)*(sp2) + (5608746981408213/100000000000000 : ℝ)*(sp4) + (28043537991313/500000000000 : ℝ)*(sp5) + (1121740368598461/20000000000000 : ℝ)*(sp6) + (170693088708671/6250000000000 : ℝ)*(sp7) + (170693088708671/6250000000000 : ℝ)*(f.failure) + (5608746981408213/100000000000000 : ℝ)*(f.sum) + (29764615213/8500000000000000000000000 : ℝ)*base65 + (3110048547084699/2125000000000000000000000000000 : ℝ)*base67 + (1882592780709699/2125000000000000000000000000000 : ℝ)*base69 + (28911544834834699/2125000000000000000000000000000 : ℝ)*base71 + (11167428143/1062500000000000000000000 : ℝ)*base74 + (1277745144165301/2125000000000000000000000000000 : ℝ)*base76 + (10795102351790301/2125000000000000000000000000000 : ℝ)*base78 + (5983137359540301/2125000000000000000000000000000 : ℝ)*base80 + (4166423807/2125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (4280443/625000000000000000000 : ℝ)*base89 + (4280443/625000000000000000000 : ℝ)*base91 + (4280443/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1290_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10649/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2737/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (59/400 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1290_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1290_s5_0 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2040709/9765625 : ℝ)*x 0 + (2708003121/5000000000 : ℝ)*x 1 + (655287157/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2040709/9765625 : ℝ)^2125 ≤ (12713364829359/100000000000000 : ℝ)^1613 := by
    have hnat : (2040709 : ℕ)^2125*100000000000000^1613 ≤ 12713364829359^1613*9765625^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040709 9765625 12713364829359 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708003121/5000000000 : ℝ)^2125 ≤ (5572542029337/12500000000000 : ℝ)^1613 := by
    have hnat : (2708003121 : ℕ)^2125*12500000000000^1613 ≤ 5572542029337^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708003121 5000000000 5572542029337 12500000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655287157/1250000000 : ℝ)^2125 ≤ (42706298915019/100000000000000 : ℝ)^1613 := by
    have hnat : (655287157 : ℕ)^2125*100000000000000^1613 ≤ 42706298915019^1613*1250000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655287157 1250000000 42706298915019 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2040709/9765625 : ℝ), (2708003121/5000000000 : ℝ), (655287157/1250000000 : ℝ)] ![(12713364829359/100000000000000 : ℝ), (5572542029337/12500000000000 : ℝ), (42706298915019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2040709/9765625 : ℝ)|^2125 ≤ (12713364829359/100000000000000 : ℝ)^1613
        have hw : |(-2040709/9765625 : ℝ)|=(2040709/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708003121/5000000000 : ℝ)|^2125 ≤ (5572542029337/12500000000000 : ℝ)^1613
        have hw : |(2708003121/5000000000 : ℝ)|=(2708003121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655287157/1250000000 : ℝ)|^2125 ≤ (42706298915019/100000000000000 : ℝ)^1613
        have hw : |(655287157/1250000000 : ℝ)|=(655287157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s5_1 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337496017/2500000000 : ℝ)*x 0 + (-2178247981/10000000000 : ℝ)*x 1 + (5242297257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337496017/2500000000 : ℝ)^2125 ≤ (21932891017733/50000000000000 : ℝ)^1613 := by
    have hnat : (1337496017 : ℕ)^2125*50000000000000^1613 ≤ 21932891017733^1613*2500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337496017 2500000000 21932891017733 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2178247981/10000000000 : ℝ)^2125 ≤ (13427919029739/100000000000000 : ℝ)^1613 := by
    have hnat : (2178247981 : ℕ)^2125*100000000000000^1613 ≤ 13427919029739^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178247981 10000000000 13427919029739 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242297257/10000000000 : ℝ)^2125 ≤ (42706298925751/100000000000000 : ℝ)^1613 := by
    have hnat : (5242297257 : ℕ)^2125*100000000000000^1613 ≤ 42706298925751^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242297257 10000000000 42706298925751 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337496017/2500000000 : ℝ), (-2178247981/10000000000 : ℝ), (5242297257/10000000000 : ℝ)] ![(21932891017733/50000000000000 : ℝ), (13427919029739/100000000000000 : ℝ), (42706298925751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337496017/2500000000 : ℝ)|^2125 ≤ (21932891017733/50000000000000 : ℝ)^1613
        have hw : |(1337496017/2500000000 : ℝ)|=(1337496017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2178247981/10000000000 : ℝ)|^2125 ≤ (13427919029739/100000000000000 : ℝ)^1613
        have hw : |(-2178247981/10000000000 : ℝ)|=(2178247981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242297257/10000000000 : ℝ)|^2125 ≤ (42706298925751/100000000000000 : ℝ)^1613
        have hw : |(5242297257/10000000000 : ℝ)|=(5242297257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s5_2 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668748009/1250000000 : ℝ)*x 0 + (2621148627/5000000000 : ℝ)*x 1 + (-108912399/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668748009/1250000000 : ℝ)^2125 ≤ (43865782078673/100000000000000 : ℝ)^1613 := by
    have hnat : (668748009 : ℕ)^2125*100000000000000^1613 ≤ 43865782078673^1613*1250000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668748009 1250000000 43865782078673 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621148627/5000000000 : ℝ)^2125 ≤ (21353149446777/50000000000000 : ℝ)^1613 := by
    have hnat : (2621148627 : ℕ)^2125*50000000000000^1613 ≤ 21353149446777^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621148627 5000000000 21353149446777 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108912399/500000000 : ℝ)^2125 ≤ (6713959510809/50000000000000 : ℝ)^1613 := by
    have hnat : (108912399 : ℕ)^2125*50000000000000^1613 ≤ 6713959510809^1613*500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108912399 500000000 6713959510809 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668748009/1250000000 : ℝ), (2621148627/5000000000 : ℝ), (-108912399/500000000 : ℝ)] ![(43865782078673/100000000000000 : ℝ), (21353149446777/50000000000000 : ℝ), (6713959510809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668748009/1250000000 : ℝ)|^2125 ≤ (43865782078673/100000000000000 : ℝ)^1613
        have hw : |(668748009/1250000000 : ℝ)|=(668748009/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621148627/5000000000 : ℝ)|^2125 ≤ (21353149446777/50000000000000 : ℝ)^1613
        have hw : |(2621148627/5000000000 : ℝ)|=(2621148627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-108912399/500000000 : ℝ)|^2125 ≤ (6713959510809/50000000000000 : ℝ)^1613
        have hw : |(-108912399/500000000 : ℝ)|=(108912399/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s5_3 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (434035781/1000000000 : ℝ)*x 0 + (833098839/2000000000 : ℝ)*x 1 + (4522234553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434035781/1000000000 : ℝ)^2125 ≤ (16650931967283/50000000000000 : ℝ)^1613 := by
    have hnat : (434035781 : ℕ)^2125*50000000000000^1613 ≤ 16650931967283^1613*1000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434035781 1000000000 16650931967283 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833098839/2000000000 : ℝ)^2125 ≤ (1971608759091/6250000000000 : ℝ)^1613 := by
    have hnat : (833098839 : ℕ)^2125*6250000000000^1613 ≤ 1971608759091^1613*2000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833098839 2000000000 1971608759091 6250000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4522234553/10000000000 : ℝ)^2125 ≤ (35152395903863/100000000000000 : ℝ)^1613 := by
    have hnat : (4522234553 : ℕ)^2125*100000000000000^1613 ≤ 35152395903863^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522234553 10000000000 35152395903863 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434035781/1000000000 : ℝ), (833098839/2000000000 : ℝ), (4522234553/10000000000 : ℝ)] ![(16650931967283/50000000000000 : ℝ), (1971608759091/6250000000000 : ℝ), (35152395903863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434035781/1000000000 : ℝ)|^2125 ≤ (16650931967283/50000000000000 : ℝ)^1613
        have hw : |(434035781/1000000000 : ℝ)|=(434035781/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(833098839/2000000000 : ℝ)|^2125 ≤ (1971608759091/6250000000000 : ℝ)^1613
        have hw : |(833098839/2000000000 : ℝ)|=(833098839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4522234553/10000000000 : ℝ)|^2125 ≤ (35152395903863/100000000000000 : ℝ)^1613
        have hw : |(4522234553/10000000000 : ℝ)|=(4522234553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s5_4 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-208969903/1000000000 : ℝ)*x 0 + (5242920907/10000000000 : ℝ)*x 1 + (5415379369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208969903/1000000000 : ℝ)^2125 ≤ (3178367284199/25000000000000 : ℝ)^1613 := by
    have hnat : (208969903 : ℕ)^2125*25000000000000^1613 ≤ 3178367284199^1613*1000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208969903 1000000000 3178367284199 25000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242920907/10000000000 : ℝ)^2125 ≤ (42712992282693/100000000000000 : ℝ)^1613 := by
    have hnat : (5242920907 : ℕ)^2125*100000000000000^1613 ≤ 42712992282693^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242920907 10000000000 42712992282693 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415379369/10000000000 : ℝ)^2125 ≤ (22286769280317/50000000000000 : ℝ)^1613 := by
    have hnat : (5415379369 : ℕ)^2125*50000000000000^1613 ≤ 22286769280317^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415379369 10000000000 22286769280317 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208969903/1000000000 : ℝ), (5242920907/10000000000 : ℝ), (5415379369/10000000000 : ℝ)] ![(3178367284199/25000000000000 : ℝ), (42712992282693/100000000000000 : ℝ), (22286769280317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208969903/1000000000 : ℝ)|^2125 ≤ (3178367284199/25000000000000 : ℝ)^1613
        have hw : |(-208969903/1000000000 : ℝ)|=(208969903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242920907/10000000000 : ℝ)|^2125 ≤ (42712992282693/100000000000000 : ℝ)^1613
        have hw : |(5242920907/10000000000 : ℝ)|=(5242920907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415379369/10000000000 : ℝ)|^2125 ≤ (22286769280317/50000000000000 : ℝ)^1613
        have hw : |(5415379369/10000000000 : ℝ)|=(5415379369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s5_5 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (212220853/400000000 : ℝ)*x 0 + (-501291467/2500000000 : ℝ)*x 1 + (541537937/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212220853/400000000 : ℝ)^2125 ≤ (1084653426501/2500000000000 : ℝ)^1613 := by
    have hnat : (212220853 : ℕ)^2125*2500000000000^1613 ≤ 1084653426501^1613*400000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212220853 400000000 1084653426501 2500000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501291467/2500000000 : ℝ)^2125 ≤ (188130068009/1562500000000 : ℝ)^1613 := by
    have hnat : (501291467 : ℕ)^2125*1562500000000^1613 ≤ 188130068009^1613*2500000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501291467 2500000000 188130068009 1562500000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541537937/1000000000 : ℝ)^2125 ≤ (44573538571477/100000000000000 : ℝ)^1613 := by
    have hnat : (541537937 : ℕ)^2125*100000000000000^1613 ≤ 44573538571477^1613*1000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541537937 1000000000 44573538571477 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212220853/400000000 : ℝ), (-501291467/2500000000 : ℝ), (541537937/1000000000 : ℝ)] ![(1084653426501/2500000000000 : ℝ), (188130068009/1562500000000 : ℝ), (44573538571477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212220853/400000000 : ℝ)|^2125 ≤ (1084653426501/2500000000000 : ℝ)^1613
        have hw : |(212220853/400000000 : ℝ)|=(212220853/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-501291467/2500000000 : ℝ)|^2125 ≤ (188130068009/1562500000000 : ℝ)^1613
        have hw : |(-501291467/2500000000 : ℝ)|=(501291467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541537937/1000000000 : ℝ)|^2125 ≤ (44573538571477/100000000000000 : ℝ)^1613
        have hw : |(541537937/1000000000 : ℝ)|=(541537937/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s5_6 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652760661/5000000000 : ℝ)*x 0 + (2707689687/5000000000 : ℝ)*x 1 + (-2005165867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652760661/5000000000 : ℝ)^2125 ≤ (1084653425693/2500000000000 : ℝ)^1613 := by
    have hnat : (2652760661 : ℕ)^2125*2500000000000^1613 ≤ 1084653425693^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652760661 5000000000 1084653425693 2500000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707689687/5000000000 : ℝ)^2125 ≤ (44573538614851/100000000000000 : ℝ)^1613 := by
    have hnat : (2707689687 : ℕ)^2125*100000000000000^1613 ≤ 44573538614851^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707689687 5000000000 44573538614851 100000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2005165867/10000000000 : ℝ)^2125 ≤ (2408064868933/20000000000000 : ℝ)^1613 := by
    have hnat : (2005165867 : ℕ)^2125*20000000000000^1613 ≤ 2408064868933^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005165867 10000000000 2408064868933 20000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652760661/5000000000 : ℝ), (2707689687/5000000000 : ℝ), (-2005165867/10000000000 : ℝ)] ![(1084653425693/2500000000000 : ℝ), (44573538614851/100000000000000 : ℝ), (2408064868933/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652760661/5000000000 : ℝ)|^2125 ≤ (1084653425693/2500000000000 : ℝ)^1613
        have hw : |(2652760661/5000000000 : ℝ)|=(2652760661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707689687/5000000000 : ℝ)|^2125 ≤ (44573538614851/100000000000000 : ℝ)^1613
        have hw : |(2707689687/5000000000 : ℝ)|=(2707689687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2005165867/10000000000 : ℝ)|^2125 ≤ (2408064868933/20000000000000 : ℝ)^1613
        have hw : |(-2005165867/10000000000 : ℝ)|=(2005165867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1290_s5_7 (p : ℝ) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4340384543/10000000000 : ℝ)*x 0 + (4520953793/10000000000 : ℝ)*x 1 + (2083390797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4340384543/10000000000 : ℝ)^2125 ≤ (8325533538363/25000000000000 : ℝ)^1613 := by
    have hnat : (4340384543 : ℕ)^2125*25000000000000^1613 ≤ 8325533538363^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340384543 10000000000 8325533538363 25000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4520953793/10000000000 : ℝ)^2125 ≤ (17569640356027/50000000000000 : ℝ)^1613 := by
    have hnat : (4520953793 : ℕ)^2125*50000000000000^1613 ≤ 17569640356027^1613*10000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520953793 10000000000 17569640356027 50000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2083390797/5000000000 : ℝ)^2125 ≤ (7889646279817/25000000000000 : ℝ)^1613 := by
    have hnat : (2083390797 : ℕ)^2125*25000000000000^1613 ≤ 7889646279817^1613*5000000000^2125 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083390797 5000000000 7889646279817 25000000000000 2125 1613 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2125/512 : ℝ)) 2125 1613 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4340384543/10000000000 : ℝ), (4520953793/10000000000 : ℝ), (2083390797/5000000000 : ℝ)] ![(8325533538363/25000000000000 : ℝ), (17569640356027/50000000000000 : ℝ), (7889646279817/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4340384543/10000000000 : ℝ)|^2125 ≤ (8325533538363/25000000000000 : ℝ)^1613
        have hw : |(4340384543/10000000000 : ℝ)|=(4340384543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4520953793/10000000000 : ℝ)|^2125 ≤ (17569640356027/50000000000000 : ℝ)^1613
        have hw : |(4520953793/10000000000 : ℝ)|=(4520953793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2083390797/5000000000 : ℝ)|^2125 ≤ (7889646279817/25000000000000 : ℝ)^1613
        have hw : |(2083390797/5000000000 : ℝ)|=(2083390797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1290_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2737/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11009/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2937/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2737/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2737/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2737/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2737/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2737/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2737/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2737/25000 : ℝ) ^ (4249/1024 : ℝ) ≤ (10322912901347517/100000000000000000000 : ℝ) := by
    have hpowers : (2737/25000 : ℝ)^4249 ≤ (10322912901347517/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2737 : ℕ)^4249*100000000000000000000^1024 ≤ 10322912901347517^1024*25000^4249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2737 25000 10322912901347517 100000000000000000000 4249 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2737/25000 : ℝ)) (X := (10322912901347517/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (59/400 : ℝ) ^ (4249/1024 : ℝ) ≤ (17780498161634279/50000000000000000000 : ℝ) := by
    have hpowers : (59/400 : ℝ)^4249 ≤ (17780498161634279/50000000000000000000 : ℝ)^1024 := by
      have hnat : (59 : ℕ)^4249*50000000000000000000^1024 ≤ 17780498161634279^1024*400^4249 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59 400 17780498161634279 50000000000000000000 4249 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59/400 : ℝ)) (X := (17780498161634279/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010322912901347517/50000000000000000000 : ℝ) ≤ (19532221720799/19531250000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (50010322912901347517/50000000000000000000 : ℝ)^1024 ≤ (19532221720799/19531250000000 : ℝ)^4249 := by
      have hnat : (50010322912901347517 : ℕ)^1024*19531250000000^4249 ≤ 19532221720799^4249*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010322912901347517 50000000000000000000 19532221720799 19531250000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (19532221720799/19531250000000 : ℝ)) (X := (50010322912901347517/50000000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001835356368984643/4000000000000000000 : ℝ) ≤ (10001105599993661/10000000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (4001835356368984643/4000000000000000000 : ℝ)^1024 ≤ (10001105599993661/10000000000000000 : ℝ)^4249 := by
      have hnat : (4001835356368984643 : ℕ)^1024*10000000000000000^4249 ≤ 10001105599993661^4249*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001835356368984643 4000000000000000000 10001105599993661 10000000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001105599993661/10000000000000000 : ℝ)) (X := (4001835356368984643/4000000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017780498161634279/25000000000000000000 : ℝ) ≤ (5000856839469117/5000000000000000 : ℝ) ^ (4249/1024 : ℝ) := by
    have hpowers : (25017780498161634279/25000000000000000000 : ℝ)^1024 ≤ (5000856839469117/5000000000000000 : ℝ)^4249 := by
      have hnat : (25017780498161634279 : ℕ)^1024*5000000000000000^4249 ≤ 5000856839469117^4249*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017780498161634279 25000000000000000000 5000856839469117 5000000000000000 1024 4249 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000856839469117/5000000000000000 : ℝ)) (X := (25017780498161634279/25000000000000000000 : ℝ)) (by norm_num) 4249 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10322912901347517/100000000000000000000 : ℝ) ≤ ((4751072134807282771/4752500000000000000 : ℝ)+2*(608078944573/380200000000000 : ℝ)*(2737/25000 : ℝ))^(4249/1024 : ℝ) := by
    rw [show (4751072134807282771/4752500000000000000 : ℝ)+2*(608078944573/380200000000000 : ℝ)*(2737/25000 : ℝ)=(19532221720799/19531250000000 : ℝ) by norm_num, show 1+2*(10322912901347517/100000000000000000000 : ℝ)=(50010322912901347517/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17780498161634279/50000000000000000000 : ℝ)+(10322912901347517/100000000000000000000 : ℝ) ≤ ((4751072134807282771/4752500000000000000 : ℝ)+(608078944573/380200000000000 : ℝ)*((59/400 : ℝ)+(2737/25000 : ℝ)))^(4249/1024 : ℝ) := by
    rw [show (4751072134807282771/4752500000000000000 : ℝ)+(608078944573/380200000000000 : ℝ)*((59/400 : ℝ)+(2737/25000 : ℝ))=(10001105599993661/10000000000000000 : ℝ) by norm_num, show 1+(17780498161634279/50000000000000000000 : ℝ)+(10322912901347517/100000000000000000000 : ℝ)=(4001835356368984643/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17780498161634279/50000000000000000000 : ℝ) ≤ ((4751072134807282771/4752500000000000000 : ℝ)+2*(608078944573/380200000000000 : ℝ)*(59/400 : ℝ))^(4249/1024 : ℝ) := by
    rw [show (4751072134807282771/4752500000000000000 : ℝ)+2*(608078944573/380200000000000 : ℝ)*(59/400 : ℝ)=(5000856839469117/5000000000000000 : ℝ) by norm_num, show 1+2*(17780498161634279/50000000000000000000 : ℝ)=(25017780498161634279/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4751072134807282771/4752500000000000000 : ℝ)*(X 1 0+X 2 0)+(608078944573/380200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (2737/25000 : ℝ)) (hi := (59/400 : ℝ)) (c := (4751072134807282771/4752500000000000000 : ℝ)) (alpha := (608078944573/380200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4751072134807282771/4752500000000000000 : ℝ)*(X 0 1+X 2 1)+(608078944573/380200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (2737/25000 : ℝ)) (hi := (59/400 : ℝ)) (c := (4751072134807282771/4752500000000000000 : ℝ)) (alpha := (608078944573/380200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4751072134807282771/4752500000000000000 : ℝ)*(X 0 2+X 1 2)+(608078944573/380200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4249/1024 : ℝ)) (lo := (2737/25000 : ℝ)) (hi := (59/400 : ℝ)) (c := (4751072134807282771/4752500000000000000 : ℝ)) (alpha := (608078944573/380200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2040709/9765625 : ℝ)*X 0 0+(2708003121/5000000000 : ℝ)*X 0 1+(655287157/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337496017/2500000000 : ℝ)*X 1 0+(-2178247981/10000000000 : ℝ)*X 1 1+(5242297257/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668748009/1250000000 : ℝ)*X 2 0+(2621148627/5000000000 : ℝ)*X 2 1+(-108912399/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((434035781/1000000000 : ℝ)*X 0 0+(833098839/2000000000 : ℝ)*X 0 1+(4522234553/10000000000 : ℝ)*X 0 2+(434035781/1000000000 : ℝ)*X 1 0+(833098839/2000000000 : ℝ)*X 1 1+(4522234553/10000000000 : ℝ)*X 1 2+(434035781/1000000000 : ℝ)*X 2 0+(833098839/2000000000 : ℝ)*X 2 1+(4522234553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-208969903/1000000000 : ℝ)*X 0 0+(5242920907/10000000000 : ℝ)*X 0 1+(5415379369/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212220853/400000000 : ℝ)*X 1 0+(-501291467/2500000000 : ℝ)*X 1 1+(541537937/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652760661/5000000000 : ℝ)*X 2 0+(2707689687/5000000000 : ℝ)*X 2 1+(-2005165867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4340384543/10000000000 : ℝ)*X 0 0+(4520953793/10000000000 : ℝ)*X 0 1+(2083390797/5000000000 : ℝ)*X 0 2+(4340384543/10000000000 : ℝ)*X 1 0+(4520953793/10000000000 : ℝ)*X 1 1+(2083390797/5000000000 : ℝ)*X 1 2+(4340384543/10000000000 : ℝ)*X 2 0+(4520953793/10000000000 : ℝ)*X 2 1+(2083390797/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1290_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (98510462375435022319695129/14851562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (643087317/50000000000000 : ℝ)*(base19) + (1202303919/100000000000000 : ℝ)*(base23) + (47173421/100000000000000 : ℝ)*(lower2) + (21294073/12500000000000 : ℝ)*(upper3) + (26705703/25000000000000 : ℝ)*(upper5) + (133749869792957/3125000000000 : ℝ)*(major0) + (133749869792957/3125000000000 : ℝ)*(major1) + (133749869792957/3125000000000 : ℝ)*(major2) + (5756781198017343/100000000000000 : ℝ)*(sp0) + (2878402728666867/50000000000000 : ℝ)*(sp1) + (5756805541204449/100000000000000 : ℝ)*(sp2) + (2803171236989479/100000000000000 : ℝ)*(sp3) + (1021819641/4000000000000 : ℝ)*(sp4) + (13465151273/100000000000000 : ℝ)*(sp7) + (175199043883797/6250000000000 : ℝ)*(f.failure) + (359800421469273/6250000000000 : ℝ)*(f.sum) + (61420686421679/9505000000000000000000000000 : ℝ)*base66 + (513625851135590819/29703125000000000000000000000000 : ℝ)*base67 + (120333201624495361/7425781250000000000000000000000 : ℝ)*base69 + (394953354854872069/29703125000000000000000000000000 : ℝ)*base71 + (1408359863661/594062500000000000000000000 : ℝ)*base73 + (877192483949465819/29703125000000000000000000000000 : ℝ)*base75 + (359708030217122069/29703125000000000000000000000000 : ℝ)*base77 + (337313319615725097/14851562500000000000000000000000 : ℝ)*base79 + (8662243287869/9505000000000000000000000000 : ℝ)*base82 + (9344599/625000000000000000000 : ℝ)*base90 + (9344599/625000000000000000000 : ℝ)*base92 + (9344599/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34907548288435114751859/9505000000000000000000000000 : ℝ) := by norm_num
    linear_combination (641314599/100000000000000 : ℝ)*(base19) + (701185491/100000000000000 : ℝ)*(base23) + (74695027/100000000000000 : ℝ)*(upper3) + (3551857/12500000000000 : ℝ)*(lower4) + (74248379/100000000000000 : ℝ)*(upper5) + (1077747795277907/25000000000000 : ℝ)*(major0) + (1077747795277907/25000000000000 : ℝ)*(major1) + (1077747795277907/25000000000000 : ℝ)*(major2) + (79407121/625000000000 : ℝ)*(sp1) + (6924881687/50000000000000 : ℝ)*(sp2) + (5798497124300257/100000000000000 : ℝ)*(sp4) + (5798483777846297/100000000000000 : ℝ)*(sp5) + (181202580417231/3125000000000 : ℝ)*(sp6) + (3529356394381/125000000000 : ℝ)*(sp7) + (3529356394381/125000000000 : ℝ)*(f.failure) + (5798497124300257/100000000000000 : ℝ)*(f.sum) + (3105484140993/2376250000000000000000000000 : ℝ)*base65 + (588525275111990297/118812500000000000000000000000000 : ℝ)*base67 + (752412742646384703/118812500000000000000000000000000 : ℝ)*base70 + (164088184592865297/118812500000000000000000000000000 : ℝ)*base71 + (8288090618899/4752500000000000000000000000 : ℝ)*base74 + (302853638076197203/118812500000000000000000000000000 : ℝ)*base76 + (85163705310072203/118812500000000000000000000000000 : ℝ)*base78 + (684740765736677797/118812500000000000000000000000000 : ℝ)*base79 + (7878268248171/4752500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (51873/12500000000000000000 : ℝ)*base89 + (51873/12500000000000000000 : ℝ)*base91 + (51873/12500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1290_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2737/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11009/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1290_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1290_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8163/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (949/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11009/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1290_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1290_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1290_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4249/1024 : ℝ) ≤ p) (hpb : p ≤ (2125/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152683333/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8163/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (949/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11009/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1290_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

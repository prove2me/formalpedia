-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1504_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:53:40.223257+00:00
-- url     : https://prove2.me/submissions/90a66f96-36b9-4410-ab80-7c05169ea442

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
theorem support_rectangle_w1504_s6_0 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1879899747/10000000000 : ℝ)*x 0 + (5434276211/10000000000 : ℝ)*x 1 + (260861137/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1879899747/10000000000 : ℝ)^4505 ≤ (5748811895779/50000000000000 : ℝ)^3481 := by
    have hnat : (1879899747 : ℕ)^4505*50000000000000^3481 ≤ 5748811895779^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1879899747 10000000000 5748811895779 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434276211/10000000000 : ℝ)^4505 ≤ (45418081392771/100000000000000 : ℝ)^3481 := by
    have hnat : (5434276211 : ℕ)^4505*100000000000000^3481 ≤ 45418081392771^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434276211 10000000000 45418081392771 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260861137/500000000 : ℝ)^4505 ≤ (43084294804957/100000000000000 : ℝ)^3481 := by
    have hnat : (260861137 : ℕ)^4505*100000000000000^3481 ≤ 43084294804957^3481*500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260861137 500000000 43084294804957 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1879899747/10000000000 : ℝ), (5434276211/10000000000 : ℝ), (260861137/500000000 : ℝ)] ![(5748811895779/50000000000000 : ℝ), (45418081392771/100000000000000 : ℝ), (43084294804957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1879899747/10000000000 : ℝ)|^4505 ≤ (5748811895779/50000000000000 : ℝ)^3481
        have hw : |(-1879899747/10000000000 : ℝ)|=(1879899747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434276211/10000000000 : ℝ)|^4505 ≤ (45418081392771/100000000000000 : ℝ)^3481
        have hw : |(5434276211/10000000000 : ℝ)|=(5434276211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260861137/500000000 : ℝ)|^4505 ≤ (43084294804957/100000000000000 : ℝ)^3481
        have hw : |(260861137/500000000 : ℝ)|=(260861137/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s6_1 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676016073/5000000000 : ℝ)*x 0 + (-1991082189/10000000000 : ℝ)*x 1 + (260861137/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676016073/5000000000 : ℝ)^4505 ≤ (8906098803049/20000000000000 : ℝ)^3481 := by
    have hnat : (2676016073 : ℕ)^4505*20000000000000^3481 ≤ 8906098803049^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676016073 5000000000 8906098803049 20000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1991082189/10000000000 : ℝ)^4505 ≤ (1548151395343/12500000000000 : ℝ)^3481 := by
    have hnat : (1991082189 : ℕ)^4505*12500000000000^3481 ≤ 1548151395343^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991082189 10000000000 1548151395343 12500000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260861137/500000000 : ℝ)^4505 ≤ (43084294804957/100000000000000 : ℝ)^3481 := by
    have hnat : (260861137 : ℕ)^4505*100000000000000^3481 ≤ 43084294804957^3481*500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260861137 500000000 43084294804957 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676016073/5000000000 : ℝ), (-1991082189/10000000000 : ℝ), (260861137/500000000 : ℝ)] ![(8906098803049/20000000000000 : ℝ), (1548151395343/12500000000000 : ℝ), (43084294804957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676016073/5000000000 : ℝ)|^4505 ≤ (8906098803049/20000000000000 : ℝ)^3481
        have hw : |(2676016073/5000000000 : ℝ)|=(2676016073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1991082189/10000000000 : ℝ)|^4505 ≤ (1548151395343/12500000000000 : ℝ)^3481
        have hw : |(-1991082189/10000000000 : ℝ)|=(1991082189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260861137/500000000 : ℝ)|^4505 ≤ (43084294804957/100000000000000 : ℝ)^3481
        have hw : |(260861137/500000000 : ℝ)|=(260861137/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s6_2 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676016073/5000000000 : ℝ)*x 0 + (5217222739/10000000000 : ℝ)*x 1 + (-199108219/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676016073/5000000000 : ℝ)^4505 ≤ (8906098803049/20000000000000 : ℝ)^3481 := by
    have hnat : (2676016073 : ℕ)^4505*20000000000000^3481 ≤ 8906098803049^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676016073 5000000000 8906098803049 20000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217222739/10000000000 : ℝ)^4505 ≤ (43084294794269/100000000000000 : ℝ)^3481 := by
    have hnat : (5217222739 : ℕ)^4505*100000000000000^3481 ≤ 43084294794269^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217222739 10000000000 43084294794269 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199108219/1000000000 : ℝ)^4505 ≤ (6192605585397/50000000000000 : ℝ)^3481 := by
    have hnat : (199108219 : ℕ)^4505*50000000000000^3481 ≤ 6192605585397^3481*1000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199108219 1000000000 6192605585397 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676016073/5000000000 : ℝ), (5217222739/10000000000 : ℝ), (-199108219/1000000000 : ℝ)] ![(8906098803049/20000000000000 : ℝ), (43084294794269/100000000000000 : ℝ), (6192605585397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676016073/5000000000 : ℝ)|^4505 ≤ (8906098803049/20000000000000 : ℝ)^3481
        have hw : |(2676016073/5000000000 : ℝ)|=(2676016073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217222739/10000000000 : ℝ)|^4505 ≤ (43084294794269/100000000000000 : ℝ)^3481
        have hw : |(5217222739/10000000000 : ℝ)|=(5217222739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-199108219/1000000000 : ℝ)|^4505 ≤ (6192605585397/50000000000000 : ℝ)^3481
        have hw : |(-199108219/1000000000 : ℝ)|=(199108219/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s6_3 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068378087/2500000000 : ℝ)*x 0 + (4034793487/10000000000 : ℝ)*x 1 + (180968297/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068378087/2500000000 : ℝ)^4505 ≤ (33279254409821/100000000000000 : ℝ)^3481 := by
    have hnat : (1068378087 : ℕ)^4505*100000000000000^3481 ≤ 33279254409821^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068378087 2500000000 33279254409821 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4034793487/10000000000 : ℝ)^4505 ≤ (30893450647603/100000000000000 : ℝ)^3481 := by
    have hnat : (4034793487 : ℕ)^4505*100000000000000^3481 ≤ 30893450647603^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4034793487 10000000000 30893450647603 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180968297/400000000 : ℝ)^4505 ≤ (35827294921913/100000000000000 : ℝ)^3481 := by
    have hnat : (180968297 : ℕ)^4505*100000000000000^3481 ≤ 35827294921913^3481*400000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180968297 400000000 35827294921913 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068378087/2500000000 : ℝ), (4034793487/10000000000 : ℝ), (180968297/400000000 : ℝ)] ![(33279254409821/100000000000000 : ℝ), (30893450647603/100000000000000 : ℝ), (35827294921913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068378087/2500000000 : ℝ)|^4505 ≤ (33279254409821/100000000000000 : ℝ)^3481
        have hw : |(1068378087/2500000000 : ℝ)|=(1068378087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4034793487/10000000000 : ℝ)|^4505 ≤ (30893450647603/100000000000000 : ℝ)^3481
        have hw : |(4034793487/10000000000 : ℝ)|=(4034793487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(180968297/400000000 : ℝ)|^4505 ≤ (35827294921913/100000000000000 : ℝ)^3481
        have hw : |(180968297/400000000 : ℝ)|=(180968297/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s6_4 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-375985811/2000000000 : ℝ)*x 0 + (5218338247/10000000000 : ℝ)*x 1 + (1358288121/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (375985811/2000000000 : ℝ)^4505 ≤ (1437231971499/12500000000000 : ℝ)^3481 := by
    have hnat : (375985811 : ℕ)^4505*12500000000000^3481 ≤ 1437231971499^3481*2000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375985811 2000000000 1437231971499 12500000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218338247/10000000000 : ℝ)^4505 ≤ (21548108501603/50000000000000 : ℝ)^3481 := by
    have hnat : (5218338247 : ℕ)^4505*50000000000000^3481 ≤ 21548108501603^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218338247 10000000000 21548108501603 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358288121/2500000000 : ℝ)^4505 ≤ (1418935225583/3125000000000 : ℝ)^3481 := by
    have hnat : (1358288121 : ℕ)^4505*3125000000000^3481 ≤ 1418935225583^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358288121 2500000000 1418935225583 3125000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-375985811/2000000000 : ℝ), (5218338247/10000000000 : ℝ), (1358288121/2500000000 : ℝ)] ![(1437231971499/12500000000000 : ℝ), (21548108501603/50000000000000 : ℝ), (1418935225583/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-375985811/2000000000 : ℝ)|^4505 ≤ (1437231971499/12500000000000 : ℝ)^3481
        have hw : |(-375985811/2000000000 : ℝ)|=(375985811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218338247/10000000000 : ℝ)|^4505 ≤ (21548108501603/50000000000000 : ℝ)^3481
        have hw : |(5218338247/10000000000 : ℝ)|=(5218338247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358288121/2500000000 : ℝ)|^4505 ≤ (1418935225583/3125000000000 : ℝ)^3481
        have hw : |(1358288121/2500000000 : ℝ)|=(1358288121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s6_5 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295122839/10000000000 : ℝ)*x 0 + (-887576203/5000000000 : ℝ)*x 1 + (1086630501/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295122839/10000000000 : ℝ)^4505 ≤ (43918663123783/100000000000000 : ℝ)^3481 := by
    have hnat : (5295122839 : ℕ)^4505*100000000000000^3481 ≤ 43918663123783^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295122839 10000000000 43918663123783 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (887576203/5000000000 : ℝ)^4505 ≤ (1334426176663/12500000000000 : ℝ)^3481 := by
    have hnat : (887576203 : ℕ)^4505*12500000000000^3481 ≤ 1334426176663^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887576203 5000000000 1334426176663 12500000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086630501/2000000000 : ℝ)^4505 ≤ (5675740930723/12500000000000 : ℝ)^3481 := by
    have hnat : (1086630501 : ℕ)^4505*12500000000000^3481 ≤ 5675740930723^3481*2000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086630501 2000000000 5675740930723 12500000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295122839/10000000000 : ℝ), (-887576203/5000000000 : ℝ), (1086630501/2000000000 : ℝ)] ![(43918663123783/100000000000000 : ℝ), (1334426176663/12500000000000 : ℝ), (5675740930723/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295122839/10000000000 : ℝ)|^4505 ≤ (43918663123783/100000000000000 : ℝ)^3481
        have hw : |(5295122839/10000000000 : ℝ)|=(5295122839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-887576203/5000000000 : ℝ)|^4505 ≤ (1334426176663/12500000000000 : ℝ)^3481
        have hw : |(-887576203/5000000000 : ℝ)|=(887576203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086630501/2000000000 : ℝ)|^4505 ≤ (5675740930723/12500000000000 : ℝ)^3481
        have hw : |(1086630501/2000000000 : ℝ)|=(1086630501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s6_6 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295122817/10000000000 : ℝ)*x 0 + (2716576257/5000000000 : ℝ)*x 1 + (-221894053/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295122817/10000000000 : ℝ)^4505 ≤ (21959331443817/50000000000000 : ℝ)^3481 := by
    have hnat : (5295122817 : ℕ)^4505*50000000000000^3481 ≤ 21959331443817^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295122817 10000000000 21959331443817 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716576257/5000000000 : ℝ)^4505 ≤ (11351481885781/25000000000000 : ℝ)^3481 := by
    have hnat : (2716576257 : ℕ)^4505*25000000000000^3481 ≤ 11351481885781^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716576257 5000000000 11351481885781 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221894053/1250000000 : ℝ)^4505 ≤ (2668852388349/25000000000000 : ℝ)^3481 := by
    have hnat : (221894053 : ℕ)^4505*25000000000000^3481 ≤ 2668852388349^3481*1250000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221894053 1250000000 2668852388349 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295122817/10000000000 : ℝ), (2716576257/5000000000 : ℝ), (-221894053/1250000000 : ℝ)] ![(21959331443817/50000000000000 : ℝ), (11351481885781/25000000000000 : ℝ), (2668852388349/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295122817/10000000000 : ℝ)|^4505 ≤ (21959331443817/50000000000000 : ℝ)^3481
        have hw : |(5295122817/10000000000 : ℝ)|=(5295122817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716576257/5000000000 : ℝ)|^4505 ≤ (11351481885781/25000000000000 : ℝ)^3481
        have hw : |(2716576257/5000000000 : ℝ)|=(2716576257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-221894053/1250000000 : ℝ)|^4505 ≤ (2668852388349/25000000000000 : ℝ)^3481
        have hw : |(-221894053/1250000000 : ℝ)|=(221894053/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s6_7 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (427357841/1000000000 : ℝ)*x 0 + (1130423041/2500000000 : ℝ)*x 1 + (2018663633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427357841/1000000000 : ℝ)^4505 ≤ (33279920191901/100000000000000 : ℝ)^3481 := by
    have hnat : (427357841 : ℕ)^4505*100000000000000^3481 ≤ 33279920191901^3481*1000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427357841 1000000000 33279920191901 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130423041/2500000000 : ℝ)^4505 ≤ (35801519260383/100000000000000 : ℝ)^3481 := by
    have hnat : (1130423041 : ℕ)^4505*100000000000000^3481 ≤ 35801519260383^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130423041 2500000000 35801519260383 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2018663633/5000000000 : ℝ)^4505 ≤ (15459280266173/50000000000000 : ℝ)^3481 := by
    have hnat : (2018663633 : ℕ)^4505*50000000000000^3481 ≤ 15459280266173^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018663633 5000000000 15459280266173 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(427357841/1000000000 : ℝ), (1130423041/2500000000 : ℝ), (2018663633/5000000000 : ℝ)] ![(33279920191901/100000000000000 : ℝ), (35801519260383/100000000000000 : ℝ), (15459280266173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(427357841/1000000000 : ℝ)|^4505 ≤ (33279920191901/100000000000000 : ℝ)^3481
        have hw : |(427357841/1000000000 : ℝ)|=(427357841/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1130423041/2500000000 : ℝ)|^4505 ≤ (35801519260383/100000000000000 : ℝ)^3481
        have hw : |(1130423041/2500000000 : ℝ)|=(1130423041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2018663633/5000000000 : ℝ)|^4505 ≤ (15459280266173/50000000000000 : ℝ)^3481
        have hw : |(2018663633/5000000000 : ℝ)|=(2018663633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1504_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2721/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2177/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15481/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2721/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2721/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2721/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2721/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2721/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2721/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2721/25000 : ℝ) ^ (4503/1024 : ℝ) ≤ (5811860744260387/100000000000000000000 : ℝ) := by
    have hpowers : (2721/25000 : ℝ)^4503 ≤ (5811860744260387/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2721 : ℕ)^4503*100000000000000000000^1024 ≤ 5811860744260387^1024*25000^4503 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2721 25000 5811860744260387 100000000000000000000 4503 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2721/25000 : ℝ)) (X := (5811860744260387/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7741/50000 : ℝ) ^ (4503/1024 : ℝ) ≤ (13685673090250437/50000000000000000000 : ℝ) := by
    have hpowers : (7741/50000 : ℝ)^4503 ≤ (13685673090250437/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7741 : ℕ)^4503*50000000000000000000^1024 ≤ 13685673090250437^1024*50000^4503 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7741 50000 13685673090250437 50000000000000000000 4503 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7741/50000 : ℝ)) (X := (13685673090250437/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005811860744260387/50000000000000000000 : ℝ) ≤ (5000132158076659/5000000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (50005811860744260387/50000000000000000000 : ℝ)^1024 ≤ (5000132158076659/5000000000000000 : ℝ)^4503 := by
      have hnat : (50005811860744260387 : ℕ)^1024*5000000000000000^4503 ≤ 5000132158076659^4503*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005811860744260387 50000000000000000000 5000132158076659 5000000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000132158076659/5000000000000000 : ℝ)) (X := (50005811860744260387/50000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100033183206924761261/100000000000000000000 : ℝ) ≤ (80006036020259/80000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (100033183206924761261/100000000000000000000 : ℝ)^1024 ≤ (80006036020259/80000000000000 : ℝ)^4503 := by
      have hnat : (100033183206924761261 : ℕ)^1024*80000000000000^4503 ≤ 80006036020259^4503*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100033183206924761261 100000000000000000000 80006036020259 80000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80006036020259/80000000000000 : ℝ)) (X := (100033183206924761261/100000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013685673090250437/25000000000000000000 : ℝ) ≤ (1250155586113929/1250000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (25013685673090250437/25000000000000000000 : ℝ)^1024 ≤ (1250155586113929/1250000000000000 : ℝ)^4503 := by
      have hnat : (25013685673090250437 : ℕ)^1024*1250000000000000^4503 ≤ 1250155586113929^4503*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013685673090250437 25000000000000000000 1250155586113929 1250000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250155586113929/1250000000000000 : ℝ)) (X := (25013685673090250437/25000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5811860744260387/100000000000000000000 : ℝ) ≤ ((11492636237143410847/11495000000000000000 : ℝ)+2*(490186379057/459800000000000 : ℝ)*(2721/25000 : ℝ))^(4503/1024 : ℝ) := by
    rw [show (11492636237143410847/11495000000000000000 : ℝ)+2*(490186379057/459800000000000 : ℝ)*(2721/25000 : ℝ)=(5000132158076659/5000000000000000 : ℝ) by norm_num, show 1+2*(5811860744260387/100000000000000000000 : ℝ)=(50005811860744260387/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13685673090250437/50000000000000000000 : ℝ)+(5811860744260387/100000000000000000000 : ℝ) ≤ ((11492636237143410847/11495000000000000000 : ℝ)+(490186379057/459800000000000 : ℝ)*((7741/50000 : ℝ)+(2721/25000 : ℝ)))^(4503/1024 : ℝ) := by
    rw [show (11492636237143410847/11495000000000000000 : ℝ)+(490186379057/459800000000000 : ℝ)*((7741/50000 : ℝ)+(2721/25000 : ℝ))=(80006036020259/80000000000000 : ℝ) by norm_num, show 1+(13685673090250437/50000000000000000000 : ℝ)+(5811860744260387/100000000000000000000 : ℝ)=(100033183206924761261/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13685673090250437/50000000000000000000 : ℝ) ≤ ((11492636237143410847/11495000000000000000 : ℝ)+2*(490186379057/459800000000000 : ℝ)*(7741/50000 : ℝ))^(4503/1024 : ℝ) := by
    rw [show (11492636237143410847/11495000000000000000 : ℝ)+2*(490186379057/459800000000000 : ℝ)*(7741/50000 : ℝ)=(1250155586113929/1250000000000000 : ℝ) by norm_num, show 1+2*(13685673090250437/50000000000000000000 : ℝ)=(25013685673090250437/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11492636237143410847/11495000000000000000 : ℝ)*(X 1 0+X 2 0)+(490186379057/459800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (2721/25000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (11492636237143410847/11495000000000000000 : ℝ)) (alpha := (490186379057/459800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11492636237143410847/11495000000000000000 : ℝ)*(X 0 1+X 2 1)+(490186379057/459800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (2721/25000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (11492636237143410847/11495000000000000000 : ℝ)) (alpha := (490186379057/459800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11492636237143410847/11495000000000000000 : ℝ)*(X 0 2+X 1 2)+(490186379057/459800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (2721/25000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (11492636237143410847/11495000000000000000 : ℝ)) (alpha := (490186379057/459800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1879899747/10000000000 : ℝ)*X 0 0+(5434276211/10000000000 : ℝ)*X 0 1+(260861137/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676016073/5000000000 : ℝ)*X 1 0+(-1991082189/10000000000 : ℝ)*X 1 1+(260861137/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676016073/5000000000 : ℝ)*X 2 0+(5217222739/10000000000 : ℝ)*X 2 1+(-199108219/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1068378087/2500000000 : ℝ)*X 0 0+(4034793487/10000000000 : ℝ)*X 0 1+(180968297/400000000 : ℝ)*X 0 2+(1068378087/2500000000 : ℝ)*X 1 0+(4034793487/10000000000 : ℝ)*X 1 1+(180968297/400000000 : ℝ)*X 1 2+(1068378087/2500000000 : ℝ)*X 2 0+(4034793487/10000000000 : ℝ)*X 2 1+(180968297/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-375985811/2000000000 : ℝ)*X 0 0+(5218338247/10000000000 : ℝ)*X 0 1+(1358288121/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295122839/10000000000 : ℝ)*X 1 0+(-887576203/5000000000 : ℝ)*X 1 1+(1086630501/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295122817/10000000000 : ℝ)*X 2 0+(2716576257/5000000000 : ℝ)*X 2 1+(-221894053/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((427357841/1000000000 : ℝ)*X 0 0+(1130423041/2500000000 : ℝ)*X 0 1+(2018663633/5000000000 : ℝ)*X 0 2+(427357841/1000000000 : ℝ)*X 1 0+(1130423041/2500000000 : ℝ)*X 1 1+(2018663633/5000000000 : ℝ)*X 1 2+(427357841/1000000000 : ℝ)*X 2 0+(1130423041/2500000000 : ℝ)*X 2 1+(2018663633/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (231875414944780470238546257/71843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (285011263/50000000000000 : ℝ)*(base19) + (66443033/12500000000000 : ℝ)*(base23) + (20593691/100000000000000 : ℝ)*(lower2) + (10159959/12500000000000 : ℝ)*(upper3) + (52002297/100000000000000 : ℝ)*(upper5) + (831305767329573/25000000000000 : ℝ)*(major0) + (831305767329573/25000000000000 : ℝ)*(major1) + (831305767329573/25000000000000 : ℝ)*(major2) + (4607168930011903/100000000000000 : ℝ)*(sp0) + (4607177221640489/100000000000000 : ℝ)*(sp1) + (737148361619/16000000000 : ℝ)*(sp2) + (2043263960201491/100000000000000 : ℝ)*(sp3) + (8861651111/100000000000000 : ℝ)*(sp4) + (4279188871/100000000000000 : ℝ)*(sp7) + (1021634119695181/50000000000000 : ℝ)*(f.failure) + (921435558332603/20000000000000 : ℝ)*(f.sum) + (1301001211991/5747500000000000000000000000 : ℝ)*base65 + (107249500375907121/26125000000000000000000000000000 : ℝ)*base67 + (185573990457657121/26125000000000000000000000000000 : ℝ)*base69 + (174149862042717879/26125000000000000000000000000000 : ℝ)*base72 + (9426367211511/5747500000000000000000000000 : ℝ)*base73 + (69520577152157121/26125000000000000000000000000000 : ℝ)*base75 + (353727234938032121/26125000000000000000000000000000 : ℝ)*base77 + (164223571788407121/26125000000000000000000000000000 : ℝ)*base79 + (35426003328127/11495000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (1053269/625000000000000000000 : ℝ)*base90 + (1053269/625000000000000000000 : ℝ)*base92 + (1053269/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (85533089450049225672078549/7562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (376304187/20000000000000 : ℝ)*(base19) + (1002563299/50000000000000 : ℝ)*(base23) + (316448729/50000000000000 : ℝ)*(lower1) + (118070141/50000000000000 : ℝ)*(upper3) + (13344001/20000000000000 : ℝ)*(lower4) + (2347849/1000000000000 : ℝ)*(upper5) + (839962534284209/25000000000000 : ℝ)*(major0) + (839962534284209/25000000000000 : ℝ)*(major1) + (839962534284209/25000000000000 : ℝ)*(major2) + (78827493/5000000000000 : ℝ)*(sp2) + (4655154171699741/100000000000000 : ℝ)*(sp4) + (931030458035761/20000000000000 : ℝ)*(sp5) + (4655150590023283/100000000000000 : ℝ)*(sp6) + (25806821569607/1250000000000 : ℝ)*(sp7) + (25806821569607/1250000000000 : ℝ)*(f.failure) + (4655154171699741/100000000000000 : ℝ)*(f.sum) + (2668700562029/605000000000000000000000000 : ℝ)*base65 + (27692145795717153/1375000000000000000000000000000 : ℝ)*base68 + (11971096315907847/1375000000000000000000000000000 : ℝ)*base69 + (84015664596717153/1375000000000000000000000000000 : ℝ)*base72 + (116586351949/151250000000000000000000000 : ℝ)*base74 + (10640990229532847/1375000000000000000000000000000 : ℝ)*base75 + (7948294886282847/1375000000000000000000000000000 : ℝ)*base77 + (1665539738657847/1375000000000000000000000000000 : ℝ)*base79 + (1163570662307/302500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (177543/15625000000000000000 : ℝ)*base90 + (177543/15625000000000000000 : ℝ)*base92 + (177543/15625000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1504_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2721/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2177/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1504_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1504_s7_0 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352030753/10000000000 : ℝ)*x 0 + (5217227869/10000000000 : ℝ)*x 1 + (-1991077243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352030753/10000000000 : ℝ)^4505 ≤ (44530479015611/100000000000000 : ℝ)^3481 := by
    have hnat : (5352030753 : ℕ)^4505*100000000000000^3481 ≤ 44530479015611^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352030753 10000000000 44530479015611 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217227869/10000000000 : ℝ)^4505 ≤ (43084349620427/100000000000000 : ℝ)^3481 := by
    have hnat : (5217227869 : ℕ)^4505*100000000000000^3481 ≤ 43084349620427^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217227869 10000000000 43084349620427 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1991077243/10000000000 : ℝ)^4505 ≤ (6192585673311/50000000000000 : ℝ)^3481 := by
    have hnat : (1991077243 : ℕ)^4505*50000000000000^3481 ≤ 6192585673311^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991077243 10000000000 6192585673311 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352030753/10000000000 : ℝ), (5217227869/10000000000 : ℝ), (-1991077243/10000000000 : ℝ)] ![(44530479015611/100000000000000 : ℝ), (43084349620427/100000000000000 : ℝ), (6192585673311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352030753/10000000000 : ℝ)|^4505 ≤ (44530479015611/100000000000000 : ℝ)^3481
        have hw : |(5352030753/10000000000 : ℝ)|=(5352030753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217227869/10000000000 : ℝ)|^4505 ≤ (43084349620427/100000000000000 : ℝ)^3481
        have hw : |(5217227869/10000000000 : ℝ)|=(5217227869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1991077243/10000000000 : ℝ)|^4505 ≤ (6192585673311/50000000000000 : ℝ)^3481
        have hw : |(-1991077243/10000000000 : ℝ)|=(1991077243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s7_1 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1879929489/10000000000 : ℝ)*x 0 + (2609172109/5000000000 : ℝ)*x 1 + (1086629253/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1879929489/10000000000 : ℝ)^4505 ≤ (5748929603611/50000000000000 : ℝ)^3481 := by
    have hnat : (1879929489 : ℕ)^4505*50000000000000^3481 ≤ 5748929603611^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1879929489 10000000000 5748929603611 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609172109/5000000000 : ℝ)^4505 ≤ (5387035102681/12500000000000 : ℝ)^3481 := by
    have hnat : (2609172109 : ℕ)^4505*12500000000000^3481 ≤ 5387035102681^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609172109 5000000000 5387035102681 12500000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086629253/2000000000 : ℝ)^4505 ≤ (1816234398253/4000000000000 : ℝ)^3481 := by
    have hnat : (1086629253 : ℕ)^4505*4000000000000^3481 ≤ 1816234398253^3481*2000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086629253 2000000000 1816234398253 4000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1879929489/10000000000 : ℝ), (2609172109/5000000000 : ℝ), (1086629253/2000000000 : ℝ)] ![(5748929603611/50000000000000 : ℝ), (5387035102681/12500000000000 : ℝ), (1816234398253/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1879929489/10000000000 : ℝ)|^4505 ≤ (5748929603611/50000000000000 : ℝ)^3481
        have hw : |(-1879929489/10000000000 : ℝ)|=(1879929489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609172109/5000000000 : ℝ)|^4505 ≤ (5387035102681/12500000000000 : ℝ)^3481
        have hw : |(2609172109/5000000000 : ℝ)|=(2609172109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086629253/2000000000 : ℝ)|^4505 ≤ (1816234398253/4000000000000 : ℝ)^3481
        have hw : |(1086629253/2000000000 : ℝ)|=(1086629253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s7_2 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059024693/2000000000 : ℝ)*x 0 + (-887579291/5000000000 : ℝ)*x 1 + (5433147439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059024693/2000000000 : ℝ)^4505 ≤ (21959334921651/50000000000000 : ℝ)^3481 := by
    have hnat : (1059024693 : ℕ)^4505*50000000000000^3481 ≤ 21959334921651^3481*2000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059024693 2000000000 21959334921651 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (887579291/5000000000 : ℝ)^4505 ≤ (5337728740161/50000000000000 : ℝ)^3481 := by
    have hnat : (887579291 : ℕ)^4505*50000000000000^3481 ≤ 5337728740161^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887579291 5000000000 5337728740161 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433147439/10000000000 : ℝ)^4505 ≤ (45405872653859/100000000000000 : ℝ)^3481 := by
    have hnat : (5433147439 : ℕ)^4505*100000000000000^3481 ≤ 45405872653859^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433147439 10000000000 45405872653859 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059024693/2000000000 : ℝ), (-887579291/5000000000 : ℝ), (5433147439/10000000000 : ℝ)] ![(21959334921651/50000000000000 : ℝ), (5337728740161/50000000000000 : ℝ), (45405872653859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059024693/2000000000 : ℝ)|^4505 ≤ (21959334921651/50000000000000 : ℝ)^3481
        have hw : |(1059024693/2000000000 : ℝ)|=(1059024693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-887579291/5000000000 : ℝ)|^4505 ≤ (5337728740161/50000000000000 : ℝ)^3481
        have hw : |(-887579291/5000000000 : ℝ)|=(887579291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433147439/10000000000 : ℝ)|^4505 ≤ (45405872653859/100000000000000 : ℝ)^3481
        have hw : |(5433147439/10000000000 : ℝ)|=(5433147439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s7_3 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295123993/10000000000 : ℝ)*x 0 + (5433147213/10000000000 : ℝ)*x 1 + (-1775158169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295123993/10000000000 : ℝ)^4505 ≤ (10979668877721/25000000000000 : ℝ)^3481 := by
    have hnat : (5295123993 : ℕ)^4505*25000000000000^3481 ≤ 10979668877721^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295123993 10000000000 10979668877721 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433147213/10000000000 : ℝ)^4505 ≤ (4540587020953/10000000000000 : ℝ)^3481 := by
    have hnat : (5433147213 : ℕ)^4505*10000000000000^3481 ≤ 4540587020953^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433147213 10000000000 4540587020953 10000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1775158169/10000000000 : ℝ)^4505 ≤ (5337727132997/50000000000000 : ℝ)^3481 := by
    have hnat : (1775158169 : ℕ)^4505*50000000000000^3481 ≤ 5337727132997^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1775158169 10000000000 5337727132997 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295123993/10000000000 : ℝ), (5433147213/10000000000 : ℝ), (-1775158169/10000000000 : ℝ)] ![(10979668877721/25000000000000 : ℝ), (4540587020953/10000000000000 : ℝ), (5337727132997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295123993/10000000000 : ℝ)|^4505 ≤ (10979668877721/25000000000000 : ℝ)^3481
        have hw : |(5295123993/10000000000 : ℝ)|=(5295123993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433147213/10000000000 : ℝ)|^4505 ≤ (4540587020953/10000000000000 : ℝ)^3481
        have hw : |(5433147213/10000000000 : ℝ)|=(5433147213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1775158169/10000000000 : ℝ)|^4505 ≤ (5337727132997/50000000000000 : ℝ)^3481
        have hw : |(-1775158169/10000000000 : ℝ)|=(1775158169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s7_4 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4273580549/10000000000 : ℝ)*x 0 + (4521677527/10000000000 : ℝ)*x 1 + (63083441/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4273580549/10000000000 : ℝ)^4505 ≤ (33279941749093/100000000000000 : ℝ)^3481 := by
    have hnat : (4273580549 : ℕ)^4505*100000000000000^3481 ≤ 33279941749093^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273580549 10000000000 33279941749093 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4521677527/10000000000 : ℝ)^4505 ≤ (7160273855403/20000000000000 : ℝ)^3481 := by
    have hnat : (4521677527 : ℕ)^4505*20000000000000^3481 ≤ 7160273855403^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521677527 10000000000 7160273855403 20000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63083441/156250000 : ℝ)^4505 ≤ (30918688958733/100000000000000 : ℝ)^3481 := by
    have hnat : (63083441 : ℕ)^4505*100000000000000^3481 ≤ 30918688958733^3481*156250000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63083441 156250000 30918688958733 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4273580549/10000000000 : ℝ), (4521677527/10000000000 : ℝ), (63083441/156250000 : ℝ)] ![(33279941749093/100000000000000 : ℝ), (7160273855403/20000000000000 : ℝ), (30918688958733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4273580549/10000000000 : ℝ)|^4505 ≤ (33279941749093/100000000000000 : ℝ)^3481
        have hw : |(4273580549/10000000000 : ℝ)|=(4273580549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4521677527/10000000000 : ℝ)|^4505 ≤ (7160273855403/20000000000000 : ℝ)^3481
        have hw : |(4521677527/10000000000 : ℝ)|=(4521677527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(63083441/156250000 : ℝ)|^4505 ≤ (30918688958733/100000000000000 : ℝ)^3481
        have hw : |(63083441/156250000 : ℝ)|=(63083441/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1504_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2177/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2177/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (387/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2177/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2177/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2177/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2177/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2177/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2177/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (2177/20000 : ℝ) ^ (4503/1024 : ℝ) ≤ (290710463801543/5000000000000000000 : ℝ) := by
    have hpowers : (2177/20000 : ℝ)^4503 ≤ (290710463801543/5000000000000000000 : ℝ)^1024 := by
      have hnat : (2177 : ℕ)^4503*5000000000000000000^1024 ≤ 290710463801543^1024*20000^4503 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2177 20000 290710463801543 5000000000000000000 4503 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2177/20000 : ℝ)) (X := (290710463801543/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15481/100000 : ℝ) ^ (4503/1024 : ℝ) ≤ (1094542902330281/4000000000000000000 : ℝ) := by
    have hpowers : (15481/100000 : ℝ)^4503 ≤ (1094542902330281/4000000000000000000 : ℝ)^1024 := by
      have hnat : (15481 : ℕ)^4503*4000000000000000000^1024 ≤ 1094542902330281^1024*100000^4503 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15481 100000 1094542902330281 4000000000000000000 4503 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15481/100000 : ℝ)) (X := (1094542902330281/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500290710463801543/2500000000000000000 : ℝ) ≤ (5000132211478403/5000000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (2500290710463801543/2500000000000000000 : ℝ)^1024 ≤ (5000132211478403/5000000000000000 : ℝ)^4503 := by
      have hnat : (2500290710463801543 : ℕ)^1024*5000000000000000^4503 ≤ 5000132211478403^4503*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500290710463801543 2500000000000000000 5000132211478403 5000000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000132211478403/5000000000000000 : ℝ)) (X := (2500290710463801543/2500000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20006635556366857577/20000000000000000000 : ℝ) ≤ (10000754379195289/10000000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (20006635556366857577/20000000000000000000 : ℝ)^1024 ≤ (10000754379195289/10000000000000000 : ℝ)^4503 := by
      have hnat : (20006635556366857577 : ℕ)^1024*10000000000000000^4503 ≤ 10000754379195289^4503*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20006635556366857577 20000000000000000000 10000754379195289 10000000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000754379195289/10000000000000000 : ℝ)) (X := (20006635556366857577/20000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001094542902330281/2000000000000000000 : ℝ) ≤ (2500311083858443/2500000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (2001094542902330281/2000000000000000000 : ℝ)^1024 ≤ (2500311083858443/2500000000000000 : ℝ)^4503 := by
      have hnat : (2001094542902330281 : ℕ)^1024*2500000000000000^4503 ≤ 2500311083858443^4503*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001094542902330281 2000000000000000000 2500311083858443 2500000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500311083858443/2500000000000000 : ℝ)) (X := (2001094542902330281/2000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(290710463801543/5000000000000000000 : ℝ) ≤ ((7658424823432950911/7660000000000000000 : ℝ)+2*(163318746161/153200000000000 : ℝ)*(2177/20000 : ℝ))^(4503/1024 : ℝ) := by
    rw [show (7658424823432950911/7660000000000000000 : ℝ)+2*(163318746161/153200000000000 : ℝ)*(2177/20000 : ℝ)=(5000132211478403/5000000000000000 : ℝ) by norm_num, show 1+2*(290710463801543/5000000000000000000 : ℝ)=(2500290710463801543/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1094542902330281/4000000000000000000 : ℝ)+(290710463801543/5000000000000000000 : ℝ) ≤ ((7658424823432950911/7660000000000000000 : ℝ)+(163318746161/153200000000000 : ℝ)*((15481/100000 : ℝ)+(2177/20000 : ℝ)))^(4503/1024 : ℝ) := by
    rw [show (7658424823432950911/7660000000000000000 : ℝ)+(163318746161/153200000000000 : ℝ)*((15481/100000 : ℝ)+(2177/20000 : ℝ))=(10000754379195289/10000000000000000 : ℝ) by norm_num, show 1+(1094542902330281/4000000000000000000 : ℝ)+(290710463801543/5000000000000000000 : ℝ)=(20006635556366857577/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1094542902330281/4000000000000000000 : ℝ) ≤ ((7658424823432950911/7660000000000000000 : ℝ)+2*(163318746161/153200000000000 : ℝ)*(15481/100000 : ℝ))^(4503/1024 : ℝ) := by
    rw [show (7658424823432950911/7660000000000000000 : ℝ)+2*(163318746161/153200000000000 : ℝ)*(15481/100000 : ℝ)=(2500311083858443/2500000000000000 : ℝ) by norm_num, show 1+2*(1094542902330281/4000000000000000000 : ℝ)=(2001094542902330281/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7658424823432950911/7660000000000000000 : ℝ)*(X 1 0+X 2 0)+(163318746161/153200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (2177/20000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (7658424823432950911/7660000000000000000 : ℝ)) (alpha := (163318746161/153200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7658424823432950911/7660000000000000000 : ℝ)*(X 0 1+X 2 1)+(163318746161/153200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (2177/20000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (7658424823432950911/7660000000000000000 : ℝ)) (alpha := (163318746161/153200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7658424823432950911/7660000000000000000 : ℝ)*(X 0 2+X 1 2)+(163318746161/153200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (2177/20000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (7658424823432950911/7660000000000000000 : ℝ)) (alpha := (163318746161/153200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5352030753/10000000000 : ℝ)*X 2 0+(5217227869/10000000000 : ℝ)*X 2 1+(-1991077243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s7_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1879929489/10000000000 : ℝ)*X 0 0+(2609172109/5000000000 : ℝ)*X 0 1+(1086629253/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s7_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1059024693/2000000000 : ℝ)*X 1 0+(-887579291/5000000000 : ℝ)*X 1 1+(5433147439/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s7_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5295123993/10000000000 : ℝ)*X 2 0+(5433147213/10000000000 : ℝ)*X 2 1+(-1775158169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s7_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4273580549/10000000000 : ℝ)*X 0 0+(4521677527/10000000000 : ℝ)*X 0 1+(63083441/156250000 : ℝ)*X 0 2+(4273580549/10000000000 : ℝ)*X 1 0+(4521677527/10000000000 : ℝ)*X 1 1+(63083441/156250000 : ℝ)*X 1 2+(4273580549/10000000000 : ℝ)*X 2 0+(4521677527/10000000000 : ℝ)*X 2 1+(63083441/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s7_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1138496083132456692532861767/383000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15691273/20000000000000 : ℝ)*(base15) + (176391717/50000000000000 : ℝ)*(lower1) + (22794539/6250000000000 : ℝ)*(lower2) + (151138577/100000000000000 : ℝ)*(upper3) + (136794917/100000000000000 : ℝ)*(lower4) + (146649717/100000000000000 : ℝ)*(upper5) + (3360055336356499/100000000000000 : ℝ)*(major0) + (3360055336356499/100000000000000 : ℝ)*(major1) + (3360055336356499/100000000000000 : ℝ)*(major2) + (52232621/1562500000000 : ℝ)*(sp0) + (2327719379078703/50000000000000 : ℝ)*(sp1) + (2327719339850521/50000000000000 : ℝ)*(sp2) + (4655435415269663/100000000000000 : ℝ)*(sp3) + (2064671815469763/100000000000000 : ℝ)*(sp4) + (2064671815469763/100000000000000 : ℝ)*(f.failure) + (2327719379078703/50000000000000 : ℝ)*(f.sum) + (42887731093641/7660000000000000000000000000 : ℝ)*base66 + (7116996453314229411/766000000000000000000000000000000 : ℝ)*base68 + (417348222647770589/766000000000000000000000000000000 : ℝ)*base69 + (9134024442242229411/766000000000000000000000000000000 : ℝ)*base72 + (3003484562281/7660000000000000000000000000 : ℝ)*base74 + (1231650001079770589/766000000000000000000000000000000 : ℝ)*base75 + (4654429678968229411/766000000000000000000000000000000 : ℝ)*base78 + (5717712270516229411/766000000000000000000000000000000 : ℝ)*base80 + (99648451508841/7660000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (5285413/1250000000000000000000 : ℝ)*base89 + (5285413/1250000000000000000000 : ℝ)*base91 + (5285413/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1504_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2177/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2177/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (387/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1504_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1504_box_0 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1664839001/10000000000 : ℝ)*x 0 + (2701847991/5000000000 : ℝ)*x 1 + (42216373/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1664839001/10000000000 : ℝ)^4505 ≤ (1964964007371/20000000000000 : ℝ)^3481 := by
    have hnat : (1664839001 : ℕ)^4505*20000000000000^3481 ≤ 1964964007371^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1664839001 10000000000 1964964007371 20000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701847991/5000000000 : ℝ)^4505 ≤ (45087591261497/100000000000000 : ℝ)^3481 := by
    have hnat : (2701847991 : ℕ)^4505*100000000000000^3481 ≤ 45087591261497^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701847991 5000000000 45087591261497 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42216373/78125000 : ℝ)^4505 ≤ (11271897172873/25000000000000 : ℝ)^3481 := by
    have hnat : (42216373 : ℕ)^4505*25000000000000^3481 ≤ 11271897172873^3481*78125000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42216373 78125000 11271897172873 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1664839001/10000000000 : ℝ), (2701847991/5000000000 : ℝ), (42216373/78125000 : ℝ)] ![(1964964007371/20000000000000 : ℝ), (45087591261497/100000000000000 : ℝ), (11271897172873/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1664839001/10000000000 : ℝ)|^4505 ≤ (1964964007371/20000000000000 : ℝ)^3481
        have hw : |(-1664839001/10000000000 : ℝ)|=(1664839001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701847991/5000000000 : ℝ)|^4505 ≤ (45087591261497/100000000000000 : ℝ)^3481
        have hw : |(2701847991/5000000000 : ℝ)|=(2701847991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42216373/78125000 : ℝ)|^4505 ≤ (11271897172873/25000000000000 : ℝ)^3481
        have hw : |(42216373/78125000 : ℝ)|=(42216373/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_box_1 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1317666747/2500000000 : ℝ)*x 0 + (-1849309309/10000000000 : ℝ)*x 1 + (5403696233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317666747/2500000000 : ℝ)^4505 ≤ (21828165589593/50000000000000 : ℝ)^3481 := by
    have hnat : (1317666747 : ℕ)^4505*50000000000000^3481 ≤ 21828165589593^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317666747 2500000000 21828165589593 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1849309309/10000000000 : ℝ)^4505 ≤ (11256074835517/100000000000000 : ℝ)^3481 := by
    have hnat : (1849309309 : ℕ)^4505*100000000000000^3481 ≤ 11256074835517^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1849309309 10000000000 11256074835517 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403696233/10000000000 : ℝ)^4505 ≤ (45087593971879/100000000000000 : ℝ)^3481 := by
    have hnat : (5403696233 : ℕ)^4505*100000000000000^3481 ≤ 45087593971879^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403696233 10000000000 45087593971879 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317666747/2500000000 : ℝ), (-1849309309/10000000000 : ℝ), (5403696233/10000000000 : ℝ)] ![(21828165589593/50000000000000 : ℝ), (11256074835517/100000000000000 : ℝ), (45087593971879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317666747/2500000000 : ℝ)|^4505 ≤ (21828165589593/50000000000000 : ℝ)^3481
        have hw : |(1317666747/2500000000 : ℝ)|=(1317666747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1849309309/10000000000 : ℝ)|^4505 ≤ (11256074835517/100000000000000 : ℝ)^3481
        have hw : |(-1849309309/10000000000 : ℝ)|=(1849309309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403696233/10000000000 : ℝ)|^4505 ≤ (45087593971879/100000000000000 : ℝ)^3481
        have hw : |(5403696233/10000000000 : ℝ)|=(5403696233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_box_2 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635333109/5000000000 : ℝ)*x 0 + (1350924131/2500000000 : ℝ)*x 1 + (-924654979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635333109/5000000000 : ℝ)^4505 ≤ (43656322925211/100000000000000 : ℝ)^3481 := by
    have hnat : (2635333109 : ℕ)^4505*100000000000000^3481 ≤ 43656322925211^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635333109 5000000000 43656322925211 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350924131/2500000000 : ℝ)^4505 ≤ (11271899278549/25000000000000 : ℝ)^3481 := by
    have hnat : (1350924131 : ℕ)^4505*25000000000000^3481 ≤ 11271899278549^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350924131 2500000000 11271899278549 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (924654979/5000000000 : ℝ)^4505 ≤ (5496132787/48828125000 : ℝ)^3481 := by
    have hnat : (924654979 : ℕ)^4505*48828125000^3481 ≤ 5496132787^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924654979 5000000000 5496132787 48828125000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635333109/5000000000 : ℝ), (1350924131/2500000000 : ℝ), (-924654979/5000000000 : ℝ)] ![(43656322925211/100000000000000 : ℝ), (11271899278549/25000000000000 : ℝ), (5496132787/48828125000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635333109/5000000000 : ℝ)|^4505 ≤ (43656322925211/100000000000000 : ℝ)^3481
        have hw : |(2635333109/5000000000 : ℝ)|=(2635333109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350924131/2500000000 : ℝ)|^4505 ≤ (11271899278549/25000000000000 : ℝ)^3481
        have hw : |(1350924131/2500000000 : ℝ)|=(1350924131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-924654979/5000000000 : ℝ)|^4505 ≤ (5496132787/48828125000 : ℝ)^3481
        have hw : |(-924654979/5000000000 : ℝ)|=(924654979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_box_3 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2238469221/5000000000 : ℝ)*x 0 + (4178834453/10000000000 : ℝ)*x 1 + (4178833143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2238469221/5000000000 : ℝ)^4505 ≤ (8835900709253/25000000000000 : ℝ)^3481 := by
    have hnat : (2238469221 : ℕ)^4505*25000000000000^3481 ≤ 8835900709253^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238469221 5000000000 8835900709253 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4178834453/10000000000 : ℝ)^4505 ≤ (32328205130723/100000000000000 : ℝ)^3481 := by
    have hnat : (4178834453 : ℕ)^4505*100000000000000^3481 ≤ 32328205130723^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4178834453 10000000000 32328205130723 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4178833143/10000000000 : ℝ)^4505 ≤ (16164096007557/50000000000000 : ℝ)^3481 := by
    have hnat : (4178833143 : ℕ)^4505*50000000000000^3481 ≤ 16164096007557^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4178833143 10000000000 16164096007557 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2238469221/5000000000 : ℝ), (4178834453/10000000000 : ℝ), (4178833143/10000000000 : ℝ)] ![(8835900709253/25000000000000 : ℝ), (32328205130723/100000000000000 : ℝ), (16164096007557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2238469221/5000000000 : ℝ)|^4505 ≤ (8835900709253/25000000000000 : ℝ)^3481
        have hw : |(2238469221/5000000000 : ℝ)|=(2238469221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4178834453/10000000000 : ℝ)|^4505 ≤ (32328205130723/100000000000000 : ℝ)^3481
        have hw : |(4178834453/10000000000 : ℝ)|=(4178834453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4178833143/10000000000 : ℝ)|^4505 ≤ (16164096007557/50000000000000 : ℝ)^3481
        have hw : |(4178833143/10000000000 : ℝ)|=(4178833143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_box_4 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2100411131/10000000000 : ℝ)*x 0 + (262167943/500000000 : ℝ)*x 1 + (2621679481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100411131/10000000000 : ℝ)^4505 ≤ (3318086490691/25000000000000 : ℝ)^3481 := by
    have hnat : (2100411131 : ℕ)^4505*25000000000000^3481 ≤ 3318086490691^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100411131 10000000000 3318086490691 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262167943/500000000 : ℝ)^4505 ≤ (10840956616533/25000000000000 : ℝ)^3481 := by
    have hnat : (262167943 : ℕ)^4505*25000000000000^3481 ≤ 10840956616533^3481*500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262167943 500000000 10840956616533 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621679481/5000000000 : ℝ)^4505 ≤ (21681913778923/50000000000000 : ℝ)^3481 := by
    have hnat : (2621679481 : ℕ)^4505*50000000000000^3481 ≤ 21681913778923^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621679481 5000000000 21681913778923 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2100411131/10000000000 : ℝ), (262167943/500000000 : ℝ), (2621679481/5000000000 : ℝ)] ![(3318086490691/25000000000000 : ℝ), (10840956616533/25000000000000 : ℝ), (21681913778923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2100411131/10000000000 : ℝ)|^4505 ≤ (3318086490691/25000000000000 : ℝ)^3481
        have hw : |(-2100411131/10000000000 : ℝ)|=(2100411131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262167943/500000000 : ℝ)|^4505 ≤ (10840956616533/25000000000000 : ℝ)^3481
        have hw : |(262167943/500000000 : ℝ)|=(262167943/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621679481/5000000000 : ℝ)|^4505 ≤ (21681913778923/50000000000000 : ℝ)^3481
        have hw : |(2621679481/5000000000 : ℝ)|=(2621679481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_box_5 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336397871/625000000 : ℝ)*x 0 + (-957660971/5000000000 : ℝ)*x 1 + (1310839827/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336397871/625000000 : ℝ)^4505 ≤ (44857396075067/100000000000000 : ℝ)^3481 := by
    have hnat : (336397871 : ℕ)^4505*100000000000000^3481 ≤ 44857396075067^3481*625000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336397871 625000000 44857396075067 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (957660971/5000000000 : ℝ)^4505 ≤ (11778772651719/100000000000000 : ℝ)^3481 := by
    have hnat : (957660971 : ℕ)^4505*100000000000000^3481 ≤ 11778772651719^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957660971 5000000000 11778772651719 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310839827/2500000000 : ℝ)^4505 ≤ (5420478907639/12500000000000 : ℝ)^3481 := by
    have hnat : (1310839827 : ℕ)^4505*12500000000000^3481 ≤ 5420478907639^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310839827 2500000000 5420478907639 12500000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336397871/625000000 : ℝ), (-957660971/5000000000 : ℝ), (1310839827/2500000000 : ℝ)] ![(44857396075067/100000000000000 : ℝ), (11778772651719/100000000000000 : ℝ), (5420478907639/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336397871/625000000 : ℝ)|^4505 ≤ (44857396075067/100000000000000 : ℝ)^3481
        have hw : |(336397871/625000000 : ℝ)|=(336397871/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-957660971/5000000000 : ℝ)|^4505 ≤ (11778772651719/100000000000000 : ℝ)^3481
        have hw : |(-957660971/5000000000 : ℝ)|=(957660971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310839827/2500000000 : ℝ)|^4505 ≤ (5420478907639/12500000000000 : ℝ)^3481
        have hw : |(1310839827/2500000000 : ℝ)|=(1310839827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_box_6 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345591681/2500000000 : ℝ)*x 0 + (5243358537/10000000000 : ℝ)*x 1 + (-1915321911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345591681/2500000000 : ℝ)^4505 ≤ (22428702287131/50000000000000 : ℝ)^3481 := by
    have hnat : (1345591681 : ℕ)^4505*50000000000000^3481 ≤ 22428702287131^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345591681 2500000000 22428702287131 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243358537/10000000000 : ℝ)^4505 ≤ (43363823009037/100000000000000 : ℝ)^3481 := by
    have hnat : (5243358537 : ℕ)^4505*100000000000000^3481 ≤ 43363823009037^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243358537 10000000000 43363823009037 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1915321911/10000000000 : ℝ)^4505 ≤ (2944693101249/25000000000000 : ℝ)^3481 := by
    have hnat : (1915321911 : ℕ)^4505*25000000000000^3481 ≤ 2944693101249^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915321911 10000000000 2944693101249 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345591681/2500000000 : ℝ), (5243358537/10000000000 : ℝ), (-1915321911/10000000000 : ℝ)] ![(22428702287131/50000000000000 : ℝ), (43363823009037/100000000000000 : ℝ), (2944693101249/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345591681/2500000000 : ℝ)|^4505 ≤ (22428702287131/50000000000000 : ℝ)^3481
        have hw : |(1345591681/2500000000 : ℝ)|=(1345591681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243358537/10000000000 : ℝ)|^4505 ≤ (43363823009037/100000000000000 : ℝ)^3481
        have hw : |(5243358537/10000000000 : ℝ)|=(5243358537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1915321911/10000000000 : ℝ)|^4505 ≤ (2944693101249/25000000000000 : ℝ)^3481
        have hw : |(-1915321911/10000000000 : ℝ)|=(1915321911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_box_7 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1016926657/2500000000 : ℝ)*x 0 + (438331433/1000000000 : ℝ)*x 1 + (4383314401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1016926657/2500000000 : ℝ)^4505 ≤ (15609991033323/50000000000000 : ℝ)^3481 := by
    have hnat : (1016926657 : ℕ)^4505*50000000000000^3481 ≤ 15609991033323^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016926657 2500000000 15609991033323 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438331433/1000000000 : ℝ)^4505 ≤ (17195004297031/50000000000000 : ℝ)^3481 := by
    have hnat : (438331433 : ℕ)^4505*50000000000000^3481 ≤ 17195004297031^3481*1000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438331433 1000000000 17195004297031 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4383314401/10000000000 : ℝ)^4505 ≤ (4298751164371/12500000000000 : ℝ)^3481 := by
    have hnat : (4383314401 : ℕ)^4505*12500000000000^3481 ≤ 4298751164371^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4383314401 10000000000 4298751164371 12500000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1016926657/2500000000 : ℝ), (438331433/1000000000 : ℝ), (4383314401/10000000000 : ℝ)] ![(15609991033323/50000000000000 : ℝ), (17195004297031/50000000000000 : ℝ), (4298751164371/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1016926657/2500000000 : ℝ)|^4505 ≤ (15609991033323/50000000000000 : ℝ)^3481
        have hw : |(1016926657/2500000000 : ℝ)|=(1016926657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(438331433/1000000000 : ℝ)|^4505 ≤ (17195004297031/50000000000000 : ℝ)^3481
        have hw : |(438331433/1000000000 : ℝ)|=(438331433/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4383314401/10000000000 : ℝ)|^4505 ≤ (4298751164371/12500000000000 : ℝ)^3481
        have hw : |(4383314401/10000000000 : ℝ)|=(4383314401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_box_8 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-251050889/1250000000 : ℝ)*x 0 + (5131119519/10000000000 : ℝ)*x 1 + (2712085977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (251050889/1250000000 : ℝ)^4505 ≤ (6262428925903/50000000000000 : ℝ)^3481 := by
    have hnat : (251050889 : ℕ)^4505*50000000000000^3481 ≤ 6262428925903^3481*1250000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251050889 1250000000 6262428925903 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5131119519/10000000000 : ℝ)^4505 ≤ (42166321295443/100000000000000 : ℝ)^3481 := by
    have hnat : (5131119519 : ℕ)^4505*100000000000000^3481 ≤ 42166321295443^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131119519 10000000000 42166321295443 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712085977/5000000000 : ℝ)^4505 ≤ (45308820840477/100000000000000 : ℝ)^3481 := by
    have hnat : (2712085977 : ℕ)^4505*100000000000000^3481 ≤ 45308820840477^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712085977 5000000000 45308820840477 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-251050889/1250000000 : ℝ), (5131119519/10000000000 : ℝ), (2712085977/5000000000 : ℝ)] ![(6262428925903/50000000000000 : ℝ), (42166321295443/100000000000000 : ℝ), (45308820840477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-251050889/1250000000 : ℝ)|^4505 ≤ (6262428925903/50000000000000 : ℝ)^3481
        have hw : |(-251050889/1250000000 : ℝ)|=(251050889/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5131119519/10000000000 : ℝ)|^4505 ≤ (42166321295443/100000000000000 : ℝ)^3481
        have hw : |(5131119519/10000000000 : ℝ)|=(5131119519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712085977/5000000000 : ℝ)|^4505 ≤ (45308820840477/100000000000000 : ℝ)^3481
        have hw : |(2712085977/5000000000 : ℝ)|=(2712085977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_box_9 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051279169/2000000000 : ℝ)*x 0 + (-115039479/625000000 : ℝ)*x 1 + (678021479/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051279169/2000000000 : ℝ)^4505 ≤ (43503413364161/100000000000000 : ℝ)^3481 := by
    have hnat : (1051279169 : ℕ)^4505*100000000000000^3481 ≤ 43503413364161^3481*2000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051279169 2000000000 43503413364161 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (115039479/625000000 : ℝ)^4505 ≤ (5593883549581/50000000000000 : ℝ)^3481 := by
    have hnat : (115039479 : ℕ)^4505*50000000000000^3481 ≤ 5593883549581^3481*625000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115039479 625000000 5593883549581 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678021479/1250000000 : ℝ)^4505 ≤ (22654409760807/50000000000000 : ℝ)^3481 := by
    have hnat : (678021479 : ℕ)^4505*50000000000000^3481 ≤ 22654409760807^3481*1250000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678021479 1250000000 22654409760807 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051279169/2000000000 : ℝ), (-115039479/625000000 : ℝ), (678021479/1250000000 : ℝ)] ![(43503413364161/100000000000000 : ℝ), (5593883549581/50000000000000 : ℝ), (22654409760807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051279169/2000000000 : ℝ)|^4505 ≤ (43503413364161/100000000000000 : ℝ)^3481
        have hw : |(1051279169/2000000000 : ℝ)|=(1051279169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-115039479/625000000 : ℝ)|^4505 ≤ (5593883549581/50000000000000 : ℝ)^3481
        have hw : |(-115039479/625000000 : ℝ)|=(115039479/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678021479/1250000000 : ℝ)|^4505 ≤ (22654409760807/50000000000000 : ℝ)^3481
        have hw : |(678021479/1250000000 : ℝ)|=(678021479/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_box_10 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628197887/5000000000 : ℝ)*x 0 + (5424172639/10000000000 : ℝ)*x 1 + (-460157663/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628197887/5000000000 : ℝ)^4505 ≤ (43503412603687/100000000000000 : ℝ)^3481 := by
    have hnat : (2628197887 : ℕ)^4505*100000000000000^3481 ≤ 43503412603687^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628197887 5000000000 43503412603687 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424172639/10000000000 : ℝ)^4505 ≤ (45308828245573/100000000000000 : ℝ)^3481 := by
    have hnat : (5424172639 : ℕ)^4505*100000000000000^3481 ≤ 45308828245573^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424172639 10000000000 45308828245573 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (460157663/2500000000 : ℝ)^4505 ≤ (5593879569263/50000000000000 : ℝ)^3481 := by
    have hnat : (460157663 : ℕ)^4505*50000000000000^3481 ≤ 5593879569263^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460157663 2500000000 5593879569263 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628197887/5000000000 : ℝ), (5424172639/10000000000 : ℝ), (-460157663/2500000000 : ℝ)] ![(43503412603687/100000000000000 : ℝ), (45308828245573/100000000000000 : ℝ), (5593879569263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628197887/5000000000 : ℝ)|^4505 ≤ (43503412603687/100000000000000 : ℝ)^3481
        have hw : |(2628197887/5000000000 : ℝ)|=(2628197887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424172639/10000000000 : ℝ)|^4505 ≤ (45308828245573/100000000000000 : ℝ)^3481
        have hw : |(5424172639/10000000000 : ℝ)|=(5424172639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-460157663/2500000000 : ℝ)|^4505 ≤ (5593879569263/50000000000000 : ℝ)^3481
        have hw : |(-460157663/2500000000 : ℝ)|=(460157663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_box_11 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4528048997/10000000000 : ℝ)*x 0 + (4152687779/10000000000 : ℝ)*x 1 + (4152687121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4528048997/10000000000 : ℝ)^4505 ≤ (717333407357/2000000000000 : ℝ)^3481 := by
    have hnat : (4528048997 : ℕ)^4505*2000000000000^3481 ≤ 717333407357^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4528048997 10000000000 717333407357 2000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4152687779/10000000000 : ℝ)^4505 ≤ (400833351189/1250000000000 : ℝ)^3481 := by
    have hnat : (4152687779 : ℕ)^4505*1250000000000^3481 ≤ 400833351189^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152687779 10000000000 400833351189 1250000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4152687121/10000000000 : ℝ)^4505 ≤ (4008332689929/12500000000000 : ℝ)^3481 := by
    have hnat : (4152687121 : ℕ)^4505*12500000000000^3481 ≤ 4008332689929^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152687121 10000000000 4008332689929 12500000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4528048997/10000000000 : ℝ), (4152687779/10000000000 : ℝ), (4152687121/10000000000 : ℝ)] ![(717333407357/2000000000000 : ℝ), (400833351189/1250000000000 : ℝ), (4008332689929/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4528048997/10000000000 : ℝ)|^4505 ≤ (717333407357/2000000000000 : ℝ)^3481
        have hw : |(4528048997/10000000000 : ℝ)|=(4528048997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4152687779/10000000000 : ℝ)|^4505 ≤ (400833351189/1250000000000 : ℝ)^3481
        have hw : |(4152687779/10000000000 : ℝ)|=(4152687779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4152687121/10000000000 : ℝ)|^4505 ≤ (4008332689929/12500000000000 : ℝ)^3481
        have hw : |(4152687121/10000000000 : ℝ)|=(4152687121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_box_12 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1756835693/10000000000 : ℝ)*x 0 + (1102459869/2000000000 : ℝ)*x 1 + (653542577/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1756835693/10000000000 : ℝ)^4505 ≤ (526653486747/5000000000000 : ℝ)^3481 := by
    have hnat : (1756835693 : ℕ)^4505*5000000000000^3481 ≤ 526653486747^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1756835693 10000000000 526653486747 5000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102459869/2000000000 : ℝ)^4505 ≤ (46263777498533/100000000000000 : ℝ)^3481 := by
    have hnat : (1102459869 : ℕ)^4505*100000000000000^3481 ≤ 46263777498533^3481*2000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102459869 2000000000 46263777498533 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (653542577/1250000000 : ℝ)^4505 ≤ (43203152756793/100000000000000 : ℝ)^3481 := by
    have hnat : (653542577 : ℕ)^4505*100000000000000^3481 ≤ 43203152756793^3481*1250000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653542577 1250000000 43203152756793 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1756835693/10000000000 : ℝ), (1102459869/2000000000 : ℝ), (653542577/1250000000 : ℝ)] ![(526653486747/5000000000000 : ℝ), (46263777498533/100000000000000 : ℝ), (43203152756793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1756835693/10000000000 : ℝ)|^4505 ≤ (526653486747/5000000000000 : ℝ)^3481
        have hw : |(-1756835693/10000000000 : ℝ)|=(1756835693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1102459869/2000000000 : ℝ)|^4505 ≤ (46263777498533/100000000000000 : ℝ)^3481
        have hw : |(1102459869/2000000000 : ℝ)|=(1102459869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(653542577/1250000000 : ℝ)|^4505 ≤ (43203152756793/100000000000000 : ℝ)^3481
        have hw : |(653542577/1250000000 : ℝ)|=(653542577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_box_13 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348207251/2500000000 : ℝ)*x 0 + (-960662793/5000000000 : ℝ)*x 1 + (5228339673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348207251/2500000000 : ℝ)^4505 ≤ (44970280690901/100000000000000 : ℝ)^3481 := by
    have hnat : (1348207251 : ℕ)^4505*100000000000000^3481 ≤ 44970280690901^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348207251 2500000000 44970280690901 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (960662793/5000000000 : ℝ)^4505 ≤ (5913288312391/50000000000000 : ℝ)^3481 := by
    have hnat : (960662793 : ℕ)^4505*50000000000000^3481 ≤ 5913288312391^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960662793 5000000000 5913288312391 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228339673/10000000000 : ℝ)^4505 ≤ (43203142672301/100000000000000 : ℝ)^3481 := by
    have hnat : (5228339673 : ℕ)^4505*100000000000000^3481 ≤ 43203142672301^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228339673 10000000000 43203142672301 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348207251/2500000000 : ℝ), (-960662793/5000000000 : ℝ), (5228339673/10000000000 : ℝ)] ![(44970280690901/100000000000000 : ℝ), (5913288312391/50000000000000 : ℝ), (43203142672301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348207251/2500000000 : ℝ)|^4505 ≤ (44970280690901/100000000000000 : ℝ)^3481
        have hw : |(1348207251/2500000000 : ℝ)|=(1348207251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-960662793/5000000000 : ℝ)|^4505 ≤ (5913288312391/50000000000000 : ℝ)^3481
        have hw : |(-960662793/5000000000 : ℝ)|=(960662793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228339673/10000000000 : ℝ)|^4505 ≤ (43203142672301/100000000000000 : ℝ)^3481
        have hw : |(5228339673/10000000000 : ℝ)|=(5228339673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_box_14 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392828499/10000000000 : ℝ)*x 0 + (5228340637/10000000000 : ℝ)*x 1 + (-1921324977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392828499/10000000000 : ℝ)^4505 ≤ (44970275240969/100000000000000 : ℝ)^3481 := by
    have hnat : (5392828499 : ℕ)^4505*100000000000000^3481 ≤ 44970275240969^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392828499 10000000000 44970275240969 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228340637/10000000000 : ℝ)^4505 ≤ (5400394122671/12500000000000 : ℝ)^3481 := by
    have hnat : (5228340637 : ℕ)^4505*12500000000000^3481 ≤ 5400394122671^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228340637 10000000000 5400394122671 12500000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1921324977/10000000000 : ℝ)^4505 ≤ (11826571773393/100000000000000 : ℝ)^3481 := by
    have hnat : (1921324977 : ℕ)^4505*100000000000000^3481 ≤ 11826571773393^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921324977 10000000000 11826571773393 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392828499/10000000000 : ℝ), (5228340637/10000000000 : ℝ), (-1921324977/10000000000 : ℝ)] ![(44970275240969/100000000000000 : ℝ), (5400394122671/12500000000000 : ℝ), (11826571773393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392828499/10000000000 : ℝ)|^4505 ≤ (44970275240969/100000000000000 : ℝ)^3481
        have hw : |(5392828499/10000000000 : ℝ)|=(5392828499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228340637/10000000000 : ℝ)|^4505 ≤ (5400394122671/12500000000000 : ℝ)^3481
        have hw : |(5228340637/10000000000 : ℝ)|=(5228340637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1921324977/10000000000 : ℝ)|^4505 ≤ (11826571773393/100000000000000 : ℝ)^3481
        have hw : |(-1921324977/10000000000 : ℝ)|=(1921324977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_box_15 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2014255393/5000000000 : ℝ)*x 0 + (4402446357/10000000000 : ℝ)*x 1 + (137576469/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2014255393/5000000000 : ℝ)^4505 ≤ (15415604379771/50000000000000 : ℝ)^3481 := by
    have hnat : (2014255393 : ℕ)^4505*50000000000000^3481 ≤ 15415604379771^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014255393 5000000000 15415604379771 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4402446357/10000000000 : ℝ)^4505 ≤ (34584392301609/100000000000000 : ℝ)^3481 := by
    have hnat : (4402446357 : ℕ)^4505*100000000000000^3481 ≤ 34584392301609^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4402446357 10000000000 34584392301609 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137576469/312500000 : ℝ)^4505 ≤ (34584398920083/100000000000000 : ℝ)^3481 := by
    have hnat : (137576469 : ℕ)^4505*100000000000000^3481 ≤ 34584398920083^3481*312500000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137576469 312500000 34584398920083 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2014255393/5000000000 : ℝ), (4402446357/10000000000 : ℝ), (137576469/312500000 : ℝ)] ![(15415604379771/50000000000000 : ℝ), (34584392301609/100000000000000 : ℝ), (34584398920083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2014255393/5000000000 : ℝ)|^4505 ≤ (15415604379771/50000000000000 : ℝ)^3481
        have hw : |(2014255393/5000000000 : ℝ)|=(2014255393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4402446357/10000000000 : ℝ)|^4505 ≤ (34584392301609/100000000000000 : ℝ)^3481
        have hw : |(4402446357/10000000000 : ℝ)|=(4402446357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(137576469/312500000 : ℝ)|^4505 ≤ (34584398920083/100000000000000 : ℝ)^3481
        have hw : |(137576469/312500000 : ℝ)|=(137576469/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1504_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2177/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63729/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5859/10000 : ℝ) ∧ (80233/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (1719/2000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2177/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2177/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2177/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2177/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2177/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2177/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2177/20000 : ℝ) ^ (4503/1024 : ℝ) ≤ (290710463801543/5000000000000000000 : ℝ) := by
    have hpowers : (2177/20000 : ℝ)^4503 ≤ (290710463801543/5000000000000000000 : ℝ)^1024 := by
      have hnat : (2177 : ℕ)^4503*5000000000000000000^1024 ≤ 290710463801543^1024*20000^4503 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2177 20000 290710463801543 5000000000000000000 4503 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2177/20000 : ℝ)) (X := (290710463801543/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (387/2500 : ℝ) ^ (4503/1024 : ℝ) ≤ (27355800641825467/100000000000000000000 : ℝ) := by
    have hpowers : (387/2500 : ℝ)^4503 ≤ (27355800641825467/100000000000000000000 : ℝ)^1024 := by
      have hnat : (387 : ℕ)^4503*100000000000000000000^1024 ≤ 27355800641825467^1024*2500^4503 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        387 2500 27355800641825467 100000000000000000000 4503 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (387/2500 : ℝ)) (X := (27355800641825467/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500290710463801543/2500000000000000000 : ℝ) ≤ (5000132211478403/5000000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (2500290710463801543/2500000000000000000 : ℝ)^1024 ≤ (5000132211478403/5000000000000000 : ℝ)^4503 := by
      have hnat : (2500290710463801543 : ℕ)^1024*5000000000000000^4503 ≤ 5000132211478403^4503*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500290710463801543 2500000000000000000 5000132211478403 5000000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000132211478403/5000000000000000 : ℝ)) (X := (2500290710463801543/2500000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100033170009917856327/100000000000000000000 : ℝ) ≤ (5000377101252061/5000000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (100033170009917856327/100000000000000000000 : ℝ)^1024 ≤ (5000377101252061/5000000000000000 : ℝ)^4503 := by
      have hnat : (100033170009917856327 : ℕ)^1024*5000000000000000^4503 ≤ 5000377101252061^4503*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100033170009917856327 100000000000000000000 5000377101252061 5000000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000377101252061/5000000000000000 : ℝ)) (X := (100033170009917856327/100000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027355800641825467/50000000000000000000 : ℝ) ≤ (5000621991025719/5000000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (50027355800641825467/50000000000000000000 : ℝ)^1024 ≤ (5000621991025719/5000000000000000 : ℝ)^4503 := by
      have hnat : (50027355800641825467 : ℕ)^1024*5000000000000000^4503 ≤ 5000621991025719^4503*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027355800641825467 50000000000000000000 5000621991025719 5000000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000621991025719/5000000000000000 : ℝ)) (X := (50027355800641825467/50000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(290710463801543/5000000000000000000 : ℝ) ≤ ((183762210090965817/183800000000000000 : ℝ)+2*(122444886829/114875000000000 : ℝ)*(2177/20000 : ℝ))^(4503/1024 : ℝ) := by
    rw [show (183762210090965817/183800000000000000 : ℝ)+2*(122444886829/114875000000000 : ℝ)*(2177/20000 : ℝ)=(5000132211478403/5000000000000000 : ℝ) by norm_num, show 1+2*(290710463801543/5000000000000000000 : ℝ)=(2500290710463801543/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27355800641825467/100000000000000000000 : ℝ)+(290710463801543/5000000000000000000 : ℝ) ≤ ((183762210090965817/183800000000000000 : ℝ)+(122444886829/114875000000000 : ℝ)*((387/2500 : ℝ)+(2177/20000 : ℝ)))^(4503/1024 : ℝ) := by
    rw [show (183762210090965817/183800000000000000 : ℝ)+(122444886829/114875000000000 : ℝ)*((387/2500 : ℝ)+(2177/20000 : ℝ))=(5000377101252061/5000000000000000 : ℝ) by norm_num, show 1+(27355800641825467/100000000000000000000 : ℝ)+(290710463801543/5000000000000000000 : ℝ)=(100033170009917856327/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27355800641825467/100000000000000000000 : ℝ) ≤ ((183762210090965817/183800000000000000 : ℝ)+2*(122444886829/114875000000000 : ℝ)*(387/2500 : ℝ))^(4503/1024 : ℝ) := by
    rw [show (183762210090965817/183800000000000000 : ℝ)+2*(122444886829/114875000000000 : ℝ)*(387/2500 : ℝ)=(5000621991025719/5000000000000000 : ℝ) by norm_num, show 1+2*(27355800641825467/100000000000000000000 : ℝ)=(50027355800641825467/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (183762210090965817/183800000000000000 : ℝ)*(X 1 0+X 2 0)+(122444886829/114875000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (2177/20000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (183762210090965817/183800000000000000 : ℝ)) (alpha := (122444886829/114875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (183762210090965817/183800000000000000 : ℝ)*(X 0 1+X 2 1)+(122444886829/114875000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (2177/20000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (183762210090965817/183800000000000000 : ℝ)) (alpha := (122444886829/114875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (183762210090965817/183800000000000000 : ℝ)*(X 0 2+X 1 2)+(122444886829/114875000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (2177/20000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (183762210090965817/183800000000000000 : ℝ)) (alpha := (122444886829/114875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1664839001/10000000000 : ℝ)*X 0 0+(2701847991/5000000000 : ℝ)*X 0 1+(42216373/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1317666747/2500000000 : ℝ)*X 1 0+(-1849309309/10000000000 : ℝ)*X 1 1+(5403696233/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2635333109/5000000000 : ℝ)*X 2 0+(1350924131/2500000000 : ℝ)*X 2 1+(-924654979/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2238469221/5000000000 : ℝ)*X 0 0+(4178834453/10000000000 : ℝ)*X 0 1+(4178833143/10000000000 : ℝ)*X 0 2+(2238469221/5000000000 : ℝ)*X 1 0+(4178834453/10000000000 : ℝ)*X 1 1+(4178833143/10000000000 : ℝ)*X 1 2+(2238469221/5000000000 : ℝ)*X 2 0+(4178834453/10000000000 : ℝ)*X 2 1+(4178833143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2100411131/10000000000 : ℝ)*X 0 0+(262167943/500000000 : ℝ)*X 0 1+(2621679481/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((336397871/625000000 : ℝ)*X 1 0+(-957660971/5000000000 : ℝ)*X 1 1+(1310839827/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1345591681/2500000000 : ℝ)*X 2 0+(5243358537/10000000000 : ℝ)*X 2 1+(-1915321911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1016926657/2500000000 : ℝ)*X 0 0+(438331433/1000000000 : ℝ)*X 0 1+(4383314401/10000000000 : ℝ)*X 0 2+(1016926657/2500000000 : ℝ)*X 1 0+(438331433/1000000000 : ℝ)*X 1 1+(4383314401/10000000000 : ℝ)*X 1 2+(1016926657/2500000000 : ℝ)*X 2 0+(438331433/1000000000 : ℝ)*X 2 1+(4383314401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-251050889/1250000000 : ℝ)*X 0 0+(5131119519/10000000000 : ℝ)*X 0 1+(2712085977/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1051279169/2000000000 : ℝ)*X 1 0+(-115039479/625000000 : ℝ)*X 1 1+(678021479/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2628197887/5000000000 : ℝ)*X 2 0+(5424172639/10000000000 : ℝ)*X 2 1+(-460157663/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4528048997/10000000000 : ℝ)*X 0 0+(4152687779/10000000000 : ℝ)*X 0 1+(4152687121/10000000000 : ℝ)*X 0 2+(4528048997/10000000000 : ℝ)*X 1 0+(4152687779/10000000000 : ℝ)*X 1 1+(4152687121/10000000000 : ℝ)*X 1 2+(4528048997/10000000000 : ℝ)*X 2 0+(4152687779/10000000000 : ℝ)*X 2 1+(4152687121/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1756835693/10000000000 : ℝ)*X 0 0+(1102459869/2000000000 : ℝ)*X 0 1+(653542577/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1348207251/2500000000 : ℝ)*X 1 0+(-960662793/5000000000 : ℝ)*X 1 1+(5228339673/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5392828499/10000000000 : ℝ)*X 2 0+(5228340637/10000000000 : ℝ)*X 2 1+(-1921324977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2014255393/5000000000 : ℝ)*X 0 0+(4402446357/10000000000 : ℝ)*X 0 1+(137576469/312500000 : ℝ)*X 0 2+(2014255393/5000000000 : ℝ)*X 1 0+(4402446357/10000000000 : ℝ)*X 1 1+(137576469/312500000 : ℝ)*X 1 2+(2014255393/5000000000 : ℝ)*X 2 0+(4402446357/10000000000 : ℝ)*X 2 1+(137576469/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63729/100000 : ℝ) ≤ (-2928234757960400424378097269627/4595000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (454783/2000000000000 : ℝ)*(upper0) + (51399957/50000000000000 : ℝ)*(lower2) + (78581487/100000000000000 : ℝ)*(upper5) + (1105811094780977/50000000000000 : ℝ)*(major0) + (1105811094780977/50000000000000 : ℝ)*(major1) + (1105811094780977/50000000000000 : ℝ)*(major2) + (206145381/2500000000000 : ℝ)*(sp2) + (1703343377/100000000000000 : ℝ)*(sp3) + (1542748373815227/50000000000000 : ℝ)*(sp4) + (1542726363112369/50000000000000 : ℝ)*(sp5) + (385686322130271/12500000000000 : ℝ)*(sp6) + (679493017350059/50000000000000 : ℝ)*(sp7) + (1037613477/50000000000000 : ℝ)*(sp8) + (4609663267/10000000000000 : ℝ)*(sp13) + (679493869021747/50000000000000 : ℝ)*(f.failure) + (3085498822857407/100000000000000 : ℝ)*(f.sum) + (484398830267/2871875000000000000000000000 : ℝ)*base66 + (357519782414426009/9190000000000000000000000000000 : ℝ)*base67 + (2034591362713991/9190000000000000000000000000000 : ℝ)*base70 + (22811069042616009/9190000000000000000000000000000 : ℝ)*base71 + (197490058673089/22975000000000000000000000000 : ℝ)*base73 + (7956639769213991/9190000000000000000000000000000 : ℝ)*base76 + (63946478550856009/9190000000000000000000000000000 : ℝ)*base77 + (56869149206526009/9190000000000000000000000000000 : ℝ)*base79 + (50903633581011/22975000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4043403/625000000000000000000 : ℝ)*base90 + (4043403/625000000000000000000 : ℝ)*base92 + (4043403/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (5859/10000 : ℝ) ≤ (336541259813895755182698728769/574375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43414369/25000000000000 : ℝ)*(lower0) + (25850443/100000000000000 : ℝ)*(upper1) + (117585809/50000000000000 : ℝ)*(upper2) + (179866023/100000000000000 : ℝ)*(upper3) + (13496237/100000000000000 : ℝ)*(lower5) + (285914629937119/12500000000000 : ℝ)*(major0) + (285914629937119/12500000000000 : ℝ)*(major1) + (285914629937119/12500000000000 : ℝ)*(major2) + (787400709936841/25000000000000 : ℝ)*(sp0) + (787400709936841/25000000000000 : ℝ)*(sp1) + (393700272741839/12500000000000 : ℝ)*(sp2) + (702735278240049/50000000000000 : ℝ)*(sp3) + (164453163/25000000000000 : ℝ)*(sp6) + (149076563/500000000000 : ℝ)*(sp11) + (702750185896349/50000000000000 : ℝ)*(f.failure) + (787400709936841/25000000000000 : ℝ)*(f.sum) + (6723837054829/2871875000000000000000000000 : ℝ)*base65 + (25028250120992177/2297500000000000000000000000000 : ℝ)*base68 + (22542373932922177/2297500000000000000000000000000 : ℝ)*base70 + (24298991240027177/2297500000000000000000000000000 : ℝ)*base72 + (32397008737391/11487500000000000000000000000 : ℝ)*base73 + (3565356928767823/2297500000000000000000000000000 : ℝ)*base75 + (23095403664547177/2297500000000000000000000000000 : ℝ)*base78 + (8252501928782177/2297500000000000000000000000000 : ℝ)*base80 + (13181727018241/11487500000000000000000000000 : ℝ)*base81 + (10246299/625000000000000000000 : ℝ)*base89 + (10246299/625000000000000000000 : ℝ)*base91 + (10246299/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80233/100000 : ℝ) ≤ (1843408528969986199870378360287/2297500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1935511/100000000000000 : ℝ)*(lower2) + (496507/390625000000 : ℝ)*(lower3) + (134943301/50000000000000 : ℝ)*(upper4) + (62206823/100000000000000 : ℝ)*(lower5) + (1241086375073463/50000000000000 : ℝ)*(major0) + (1241086375073463/50000000000000 : ℝ)*(major1) + (1241086375073463/50000000000000 : ℝ)*(major2) + (20872387473/50000000000000 : ℝ)*(sp1) + (249203512679/100000000000000 : ℝ)*(sp2) + (81535271411/100000000000000 : ℝ)*(sp3) + (3412365924142209/100000000000000 : ℝ)*(sp8) + (1706162089683631/50000000000000 : ℝ)*(sp9) + (341211672062953/10000000000000 : ℝ)*(sp10) + (11915257065957/781250000000 : ℝ)*(sp11) + (762617219856953/50000000000000 : ℝ)*(f.failure) + (3412365924142209/100000000000000 : ℝ)*(f.sum) + (78379851486617/11487500000000000000000000000 : ℝ)*base66 + (74075298607717471/9190000000000000000000000000000 : ℝ)*base67 + (111487621928687471/9190000000000000000000000000000 : ℝ)*base69 + (124100051108657471/9190000000000000000000000000000 : ℝ)*base71 + (11905388977741/22975000000000000000000000000 : ℝ)*base73 + (114327919941647471/9190000000000000000000000000000 : ℝ)*base75 + (6159700016102529/9190000000000000000000000000000 : ℝ)*base78 + (40513602453667471/9190000000000000000000000000000 : ℝ)*base79 + (107643719713291/22975000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (8392897/625000000000000000000 : ℝ)*base90 + (8392897/625000000000000000000 : ℝ)*base92 + (8392897/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-1719/2000 : ℝ) ≤ (-3949297312793044880452868483331/4595000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2477793/10000000000000 : ℝ)*(lower1) + (4681247/20000000000000 : ℝ)*(lower2) + (22736099/25000000000000 : ℝ)*(lower3) + (84111021/100000000000000 : ℝ)*(upper5) + (1260533888473973/50000000000000 : ℝ)*(major0) + (1260533888473973/50000000000000 : ℝ)*(major1) + (1260533888473973/50000000000000 : ℝ)*(major2) + (1911553909/12500000000000 : ℝ)*(sp4) + (192342797183/100000000000000 : ℝ)*(sp5) + (138677931599/100000000000000 : ℝ)*(sp7) + (110051094253711/3125000000000 : ℝ)*(sp12) + (88036449143821/2500000000000 : ℝ)*(sp13) + (440206288568753/12500000000000 : ℝ)*(sp14) + (387248951089679/25000000000000 : ℝ)*(sp15) + (309826896458063/20000000000000 : ℝ)*(f.failure) + (440206288568753/12500000000000 : ℝ)*(f.sum) + (14238887374391/5743750000000000000000000000 : ℝ)*base66 + (31377945480211859/9190000000000000000000000000000 : ℝ)*base68 + (94937558633601859/9190000000000000000000000000000 : ℝ)*base70 + (22563632257471859/9190000000000000000000000000000 : ℝ)*base72 + (929577365099/358984375000000000000000000 : ℝ)*base73 + (79797583085321859/9190000000000000000000000000000 : ℝ)*base76 + (167866762031791859/9190000000000000000000000000000 : ℝ)*base78 + (95270850038531859/9190000000000000000000000000000 : ℝ)*base80 + (47882033732911/22975000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (938713/250000000000000000000 : ℝ)*base89 + (938713/250000000000000000000 : ℝ)*base91 + (938713/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1504_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2177/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63729/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5859/10000 : ℝ) else (80233/100000 : ℝ) ≤ X j i ∧ X j i ≤ (1719/2000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1504_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1504_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2721/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63729/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5859/10000 : ℝ) else (80233/100000 : ℝ) ≤ X j i ∧ X j i ≤ (1719/2000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1504_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1504_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1504_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2721/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63729/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5859/10000 : ℝ) else (80233/100000 : ℝ) ≤ X j i ∧ X j i ≤ (1719/2000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1504_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

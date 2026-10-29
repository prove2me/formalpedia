-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1404_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:47:18.284344+00:00
-- url     : https://prove2.me/submissions/802a9053-53a8-410c-9965-7f81310214d2

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
theorem support_rectangle_w1404_s3_0 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-199037251/1000000000 : ℝ)*x 0 + (1083977453/2000000000 : ℝ)*x 1 + (5236746451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (199037251/1000000000 : ℝ)^1091 ≤ (2426760248107/20000000000000 : ℝ)^835 := by
    have hnat : (199037251 : ℕ)^1091*20000000000000^835 ≤ 2426760248107^835*1000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199037251 1000000000 2426760248107 20000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083977453/2000000000 : ℝ)^1091 ≤ (44919526444819/100000000000000 : ℝ)^835 := by
    have hnat : (1083977453 : ℕ)^1091*100000000000000^835 ≤ 44919526444819^835*2000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083977453 2000000000 44919526444819 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236746451/10000000000 : ℝ)^1091 ≤ (10736668074321/25000000000000 : ℝ)^835 := by
    have hnat : (5236746451 : ℕ)^1091*25000000000000^835 ≤ 10736668074321^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236746451 10000000000 10736668074321 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-199037251/1000000000 : ℝ), (1083977453/2000000000 : ℝ), (5236746451/10000000000 : ℝ)] ![(2426760248107/20000000000000 : ℝ), (44919526444819/100000000000000 : ℝ), (10736668074321/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-199037251/1000000000 : ℝ)|^1091 ≤ (2426760248107/20000000000000 : ℝ)^835
        have hw : |(-199037251/1000000000 : ℝ)|=(199037251/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083977453/2000000000 : ℝ)|^1091 ≤ (44919526444819/100000000000000 : ℝ)^835
        have hw : |(1083977453/2000000000 : ℝ)|=(1083977453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236746451/10000000000 : ℝ)|^1091 ≤ (10736668074321/25000000000000 : ℝ)^835
        have hw : |(5236746451/10000000000 : ℝ)|=(5236746451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s3_1 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (83601743/156250000 : ℝ)*x 0 + (-2083838281/10000000000 : ℝ)*x 1 + (5236746403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83601743/156250000 : ℝ)^1091 ≤ (2208487213973/5000000000000 : ℝ)^835 := by
    have hnat : (83601743 : ℕ)^1091*5000000000000^835 ≤ 2208487213973^835*156250000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83601743 156250000 2208487213973 5000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2083838281/10000000000 : ℝ)^1091 ≤ (6441791965589/50000000000000 : ℝ)^835 := by
    have hnat : (2083838281 : ℕ)^1091*50000000000000^835 ≤ 6441791965589^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083838281 10000000000 6441791965589 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236746403/10000000000 : ℝ)^1091 ≤ (42946671782947/100000000000000 : ℝ)^835 := by
    have hnat : (5236746403 : ℕ)^1091*100000000000000^835 ≤ 42946671782947^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236746403 10000000000 42946671782947 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83601743/156250000 : ℝ), (-2083838281/10000000000 : ℝ), (5236746403/10000000000 : ℝ)] ![(2208487213973/5000000000000 : ℝ), (6441791965589/50000000000000 : ℝ), (42946671782947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83601743/156250000 : ℝ)|^1091 ≤ (2208487213973/5000000000000 : ℝ)^835
        have hw : |(83601743/156250000 : ℝ)|=(83601743/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2083838281/10000000000 : ℝ)|^1091 ≤ (6441791965589/50000000000000 : ℝ)^835
        have hw : |(-2083838281/10000000000 : ℝ)|=(2083838281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236746403/10000000000 : ℝ)|^1091 ≤ (42946671782947/100000000000000 : ℝ)^835
        have hw : |(5236746403/10000000000 : ℝ)|=(5236746403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s3_2 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1337627889/2500000000 : ℝ)*x 0 + (1309186613/2500000000 : ℝ)*x 1 + (-2083838209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337627889/2500000000 : ℝ)^1091 ≤ (8833948864521/20000000000000 : ℝ)^835 := by
    have hnat : (1337627889 : ℕ)^1091*20000000000000^835 ≤ 8833948864521^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337627889 2500000000 8833948864521 20000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309186613/2500000000 : ℝ)^1091 ≤ (42946672307999/100000000000000 : ℝ)^835 := by
    have hnat : (1309186613 : ℕ)^1091*100000000000000^835 ≤ 42946672307999^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309186613 2500000000 42946672307999 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2083838209/10000000000 : ℝ)^1091 ≤ (805223959347/6250000000000 : ℝ)^835 := by
    have hnat : (2083838209 : ℕ)^1091*6250000000000^835 ≤ 805223959347^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083838209 10000000000 805223959347 6250000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337627889/2500000000 : ℝ), (1309186613/2500000000 : ℝ), (-2083838209/10000000000 : ℝ)] ![(8833948864521/20000000000000 : ℝ), (42946672307999/100000000000000 : ℝ), (805223959347/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337627889/2500000000 : ℝ)|^1091 ≤ (8833948864521/20000000000000 : ℝ)^835
        have hw : |(1337627889/2500000000 : ℝ)|=(1337627889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309186613/2500000000 : ℝ)|^1091 ≤ (42946672307999/100000000000000 : ℝ)^835
        have hw : |(1309186613/2500000000 : ℝ)|=(1309186613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2083838209/10000000000 : ℝ)|^1091 ≤ (805223959347/6250000000000 : ℝ)^835
        have hw : |(-2083838209/10000000000 : ℝ)|=(2083838209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s3_3 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2154959447/5000000000 : ℝ)*x 0 + (64339019/156250000 : ℝ)*x 1 + (451026589/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154959447/5000000000 : ℝ)^1091 ≤ (1664838622487/5000000000000 : ℝ)^835 := by
    have hnat : (2154959447 : ℕ)^1091*5000000000000^835 ≤ 1664838622487^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154959447 5000000000 1664838622487 5000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64339019/156250000 : ℝ)^1091 ≤ (31369856127973/100000000000000 : ℝ)^835 := by
    have hnat : (64339019 : ℕ)^1091*100000000000000^835 ≤ 31369856127973^835*156250000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64339019 156250000 31369856127973 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451026589/1000000000 : ℝ)^1091 ≤ (17666685698119/50000000000000 : ℝ)^835 := by
    have hnat : (451026589 : ℕ)^1091*50000000000000^835 ≤ 17666685698119^835*1000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451026589 1000000000 17666685698119 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154959447/5000000000 : ℝ), (64339019/156250000 : ℝ), (451026589/1000000000 : ℝ)] ![(1664838622487/5000000000000 : ℝ), (31369856127973/100000000000000 : ℝ), (17666685698119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154959447/5000000000 : ℝ)|^1091 ≤ (1664838622487/5000000000000 : ℝ)^835
        have hw : |(2154959447/5000000000 : ℝ)|=(2154959447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(64339019/156250000 : ℝ)|^1091 ≤ (31369856127973/100000000000000 : ℝ)^835
        have hw : |(64339019/156250000 : ℝ)|=(64339019/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(451026589/1000000000 : ℝ)|^1091 ≤ (17666685698119/50000000000000 : ℝ)^835
        have hw : |(451026589/1000000000 : ℝ)|=(451026589/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s3_4 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1990389171/10000000000 : ℝ)*x 0 + (1309371393/2500000000 : ℝ)*x 1 + (2709571803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1990389171/10000000000 : ℝ)^1091 ≤ (3033483487539/25000000000000 : ℝ)^835 := by
    have hnat : (1990389171 : ℕ)^1091*25000000000000^835 ≤ 3033483487539^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990389171 10000000000 3033483487539 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309371393/2500000000 : ℝ)^1091 ≤ (42954592406749/100000000000000 : ℝ)^835 := by
    have hnat : (1309371393 : ℕ)^1091*100000000000000^835 ≤ 42954592406749^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309371393 2500000000 42954592406749 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709571803/5000000000 : ℝ)^1091 ≤ (359291789013/800000000000 : ℝ)^835 := by
    have hnat : (2709571803 : ℕ)^1091*800000000000^835 ≤ 359291789013^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709571803 5000000000 359291789013 800000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1990389171/10000000000 : ℝ), (1309371393/2500000000 : ℝ), (2709571803/5000000000 : ℝ)] ![(3033483487539/25000000000000 : ℝ), (42954592406749/100000000000000 : ℝ), (359291789013/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1990389171/10000000000 : ℝ)|^1091 ≤ (3033483487539/25000000000000 : ℝ)^835
        have hw : |(-1990389171/10000000000 : ℝ)|=(1990389171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309371393/2500000000 : ℝ)|^1091 ≤ (42954592406749/100000000000000 : ℝ)^835
        have hw : |(1309371393/2500000000 : ℝ)|=(1309371393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709571803/5000000000 : ℝ)|^1091 ≤ (359291789013/800000000000 : ℝ)^835
        have hw : |(2709571803/5000000000 : ℝ)|=(2709571803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s3_5 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1060603917/2000000000 : ℝ)*x 0 + (-1901440523/10000000000 : ℝ)*x 1 + (541914401/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060603917/2000000000 : ℝ)^1091 ≤ (10914546397837/25000000000000 : ℝ)^835 := by
    have hnat : (1060603917 : ℕ)^1091*25000000000000^835 ≤ 10914546397837^835*2000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060603917 2000000000 10914546397837 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1901440523/10000000000 : ℝ)^1091 ≤ (5715168199731/50000000000000 : ℝ)^835 := by
    have hnat : (1901440523 : ℕ)^1091*50000000000000^835 ≤ 5715168199731^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901440523 10000000000 5715168199731 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541914401/1000000000 : ℝ)^1091 ≤ (8982295600261/20000000000000 : ℝ)^835 := by
    have hnat : (541914401 : ℕ)^1091*20000000000000^835 ≤ 8982295600261^835*1000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541914401 1000000000 8982295600261 20000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060603917/2000000000 : ℝ), (-1901440523/10000000000 : ℝ), (541914401/1000000000 : ℝ)] ![(10914546397837/25000000000000 : ℝ), (5715168199731/50000000000000 : ℝ), (8982295600261/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060603917/2000000000 : ℝ)|^1091 ≤ (10914546397837/25000000000000 : ℝ)^835
        have hw : |(1060603917/2000000000 : ℝ)|=(1060603917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1901440523/10000000000 : ℝ)|^1091 ≤ (5715168199731/50000000000000 : ℝ)^835
        have hw : |(-1901440523/10000000000 : ℝ)|=(1901440523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541914401/1000000000 : ℝ)|^1091 ≤ (8982295600261/20000000000000 : ℝ)^835
        have hw : |(541914401/1000000000 : ℝ)|=(541914401/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s3_6 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2651510241/5000000000 : ℝ)*x 0 + (5419143321/10000000000 : ℝ)*x 1 + (-1901440243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651510241/5000000000 : ℝ)^1091 ≤ (8731639048029/20000000000000 : ℝ)^835 := by
    have hnat : (2651510241 : ℕ)^1091*20000000000000^835 ≤ 8731639048029^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651510241 5000000000 8731639048029 20000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419143321/10000000000 : ℝ)^1091 ≤ (22455735270263/50000000000000 : ℝ)^835 := by
    have hnat : (5419143321 : ℕ)^1091*50000000000000^835 ≤ 22455735270263^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419143321 10000000000 22455735270263 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1901440243/10000000000 : ℝ)^1091 ≤ (11430334200223/100000000000000 : ℝ)^835 := by
    have hnat : (1901440243 : ℕ)^1091*100000000000000^835 ≤ 11430334200223^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901440243 10000000000 11430334200223 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651510241/5000000000 : ℝ), (5419143321/10000000000 : ℝ), (-1901440243/10000000000 : ℝ)] ![(8731639048029/20000000000000 : ℝ), (22455735270263/50000000000000 : ℝ), (11430334200223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651510241/5000000000 : ℝ)|^1091 ≤ (8731639048029/20000000000000 : ℝ)^835
        have hw : |(2651510241/5000000000 : ℝ)|=(2651510241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419143321/10000000000 : ℝ)|^1091 ≤ (22455735270263/50000000000000 : ℝ)^835
        have hw : |(5419143321/10000000000 : ℝ)|=(5419143321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1901440243/10000000000 : ℝ)|^1091 ≤ (11430334200223/100000000000000 : ℝ)^835
        have hw : |(-1901440243/10000000000 : ℝ)|=(1901440243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s3_7 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4309954891/10000000000 : ℝ)*x 0 + (2254340629/5000000000 : ℝ)*x 1 + (4119290027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4309954891/10000000000 : ℝ)^1091 ≤ (33297135810629/100000000000000 : ℝ)^835 := by
    have hnat : (4309954891 : ℕ)^1091*100000000000000^835 ≤ 33297135810629^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309954891 10000000000 33297135810629 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254340629/5000000000 : ℝ)^1091 ≤ (35317152315439/100000000000000 : ℝ)^835 := by
    have hnat : (2254340629 : ℕ)^1091*100000000000000^835 ≤ 35317152315439^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254340629 5000000000 35317152315439 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4119290027/10000000000 : ℝ)^1091 ≤ (15692855931671/50000000000000 : ℝ)^835 := by
    have hnat : (4119290027 : ℕ)^1091*50000000000000^835 ≤ 15692855931671^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4119290027 10000000000 15692855931671 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4309954891/10000000000 : ℝ), (2254340629/5000000000 : ℝ), (4119290027/10000000000 : ℝ)] ![(33297135810629/100000000000000 : ℝ), (35317152315439/100000000000000 : ℝ), (15692855931671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4309954891/10000000000 : ℝ)|^1091 ≤ (33297135810629/100000000000000 : ℝ)^835
        have hw : |(4309954891/10000000000 : ℝ)|=(4309954891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254340629/5000000000 : ℝ)|^1091 ≤ (35317152315439/100000000000000 : ℝ)^835
        have hw : |(2254340629/5000000000 : ℝ)|=(2254340629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4119290027/10000000000 : ℝ)|^1091 ≤ (15692855931671/50000000000000 : ℝ)^835
        have hw : |(4119290027/10000000000 : ℝ)|=(4119290027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1404_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15879/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1023/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11083/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14961/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15879/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1023/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15879/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1023/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15879/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1023/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15879/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1023/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15879/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1023/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15879/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1023/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1023/10000 : ℝ) ^ (4363/1024 : ℝ) ≤ (6044151500708489/100000000000000000000 : ℝ) := by
    have hpowers : (1023/10000 : ℝ)^4363 ≤ (6044151500708489/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1023 : ℕ)^4363*100000000000000000000^1024 ≤ 6044151500708489^1024*10000^4363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1023 10000 6044151500708489 100000000000000000000 4363 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1023/10000 : ℝ)) (X := (6044151500708489/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15879/100000 : ℝ) ^ (4363/1024 : ℝ) ≤ (39347167531379721/100000000000000000000 : ℝ) := by
    have hpowers : (15879/100000 : ℝ)^4363 ≤ (39347167531379721/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15879 : ℕ)^4363*100000000000000000000^1024 ≤ 39347167531379721^1024*100000^4363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15879 100000 39347167531379721 100000000000000000000 4363 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15879/100000 : ℝ)) (X := (39347167531379721/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006044151500708489/50000000000000000000 : ℝ) ≤ (10000283700429519/10000000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (50006044151500708489/50000000000000000000 : ℝ)^1024 ≤ (10000283700429519/10000000000000000 : ℝ)^4363 := by
      have hnat : (50006044151500708489 : ℕ)^1024*10000000000000000^4363 ≤ 10000283700429519^4363*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006044151500708489 50000000000000000000 10000283700429519 10000000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283700429519/10000000000000000 : ℝ)) (X := (50006044151500708489/50000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004539131903208821/10000000000000000000 : ℝ) ≤ (5000532576663131/5000000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (10004539131903208821/10000000000000000000 : ℝ)^1024 ≤ (5000532576663131/5000000000000000 : ℝ)^4363 := by
      have hnat : (10004539131903208821 : ℕ)^1024*5000000000000000^4363 ≤ 5000532576663131^4363*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004539131903208821 10000000000000000000 5000532576663131 5000000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000532576663131/5000000000000000 : ℝ)) (X := (10004539131903208821/10000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039347167531379721/50000000000000000000 : ℝ) ≤ (2000369321244601/2000000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (50039347167531379721/50000000000000000000 : ℝ)^1024 ≤ (2000369321244601/2000000000000000 : ℝ)^4363 := by
      have hnat : (50039347167531379721 : ℕ)^1024*2000000000000000^4363 ≤ 2000369321244601^4363*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039347167531379721 50000000000000000000 2000369321244601 2000000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000369321244601/2000000000000000 : ℝ)) (X := (50039347167531379721/50000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6044151500708489/100000000000000000000 : ℝ) ≤ ((18825204699152997017/18830000000000000000 : ℝ)+2*(781452896743/564900000000000 : ℝ)*(1023/10000 : ℝ))^(4363/1024 : ℝ) := by
    rw [show (18825204699152997017/18830000000000000000 : ℝ)+2*(781452896743/564900000000000 : ℝ)*(1023/10000 : ℝ)=(10000283700429519/10000000000000000 : ℝ) by norm_num, show 1+2*(6044151500708489/100000000000000000000 : ℝ)=(50006044151500708489/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39347167531379721/100000000000000000000 : ℝ)+(6044151500708489/100000000000000000000 : ℝ) ≤ ((18825204699152997017/18830000000000000000 : ℝ)+(781452896743/564900000000000 : ℝ)*((15879/100000 : ℝ)+(1023/10000 : ℝ)))^(4363/1024 : ℝ) := by
    rw [show (18825204699152997017/18830000000000000000 : ℝ)+(781452896743/564900000000000 : ℝ)*((15879/100000 : ℝ)+(1023/10000 : ℝ))=(5000532576663131/5000000000000000 : ℝ) by norm_num, show 1+(39347167531379721/100000000000000000000 : ℝ)+(6044151500708489/100000000000000000000 : ℝ)=(10004539131903208821/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39347167531379721/100000000000000000000 : ℝ) ≤ ((18825204699152997017/18830000000000000000 : ℝ)+2*(781452896743/564900000000000 : ℝ)*(15879/100000 : ℝ))^(4363/1024 : ℝ) := by
    rw [show (18825204699152997017/18830000000000000000 : ℝ)+2*(781452896743/564900000000000 : ℝ)*(15879/100000 : ℝ)=(2000369321244601/2000000000000000 : ℝ) by norm_num, show 1+2*(39347167531379721/100000000000000000000 : ℝ)=(50039347167531379721/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18825204699152997017/18830000000000000000 : ℝ)*(X 1 0+X 2 0)+(781452896743/564900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (1023/10000 : ℝ)) (hi := (15879/100000 : ℝ)) (c := (18825204699152997017/18830000000000000000 : ℝ)) (alpha := (781452896743/564900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18825204699152997017/18830000000000000000 : ℝ)*(X 0 1+X 2 1)+(781452896743/564900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (1023/10000 : ℝ)) (hi := (15879/100000 : ℝ)) (c := (18825204699152997017/18830000000000000000 : ℝ)) (alpha := (781452896743/564900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18825204699152997017/18830000000000000000 : ℝ)*(X 0 2+X 1 2)+(781452896743/564900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (1023/10000 : ℝ)) (hi := (15879/100000 : ℝ)) (c := (18825204699152997017/18830000000000000000 : ℝ)) (alpha := (781452896743/564900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-199037251/1000000000 : ℝ)*X 0 0+(1083977453/2000000000 : ℝ)*X 0 1+(5236746451/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83601743/156250000 : ℝ)*X 1 0+(-2083838281/10000000000 : ℝ)*X 1 1+(5236746403/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337627889/2500000000 : ℝ)*X 2 0+(1309186613/2500000000 : ℝ)*X 2 1+(-2083838209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2154959447/5000000000 : ℝ)*X 0 0+(64339019/156250000 : ℝ)*X 0 1+(451026589/1000000000 : ℝ)*X 0 2+(2154959447/5000000000 : ℝ)*X 1 0+(64339019/156250000 : ℝ)*X 1 1+(451026589/1000000000 : ℝ)*X 1 2+(2154959447/5000000000 : ℝ)*X 2 0+(64339019/156250000 : ℝ)*X 2 1+(451026589/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1990389171/10000000000 : ℝ)*X 0 0+(1309371393/2500000000 : ℝ)*X 0 1+(2709571803/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060603917/2000000000 : ℝ)*X 1 0+(-1901440523/10000000000 : ℝ)*X 1 1+(541914401/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651510241/5000000000 : ℝ)*X 2 0+(5419143321/10000000000 : ℝ)*X 2 1+(-1901440243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4309954891/10000000000 : ℝ)*X 0 0+(2254340629/5000000000 : ℝ)*X 0 1+(4119290027/10000000000 : ℝ)*X 0 2+(4309954891/10000000000 : ℝ)*X 1 0+(2254340629/5000000000 : ℝ)*X 1 1+(4119290027/10000000000 : ℝ)*X 1 2+(4309954891/10000000000 : ℝ)*X 2 0+(2254340629/5000000000 : ℝ)*X 2 1+(4119290027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (92252017476287236568643/9415000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1820261689/100000000000000 : ℝ)*(base19) + (892128731/50000000000000 : ℝ)*(base23) + (10724121/50000000000000 : ℝ)*(lower2) + (25476421/12500000000000 : ℝ)*(upper3) + (127827809/50000000000000 : ℝ)*(upper5) + (500481439745673/12500000000000 : ℝ)*(major0) + (500481439745673/12500000000000 : ℝ)*(major1) + (500481439745673/12500000000000 : ℝ)*(major2) + (5460311659209409/100000000000000 : ℝ)*(sp0) + (2730172381801363/50000000000000 : ℝ)*(sp1) + (5460344799606953/100000000000000 : ℝ)*(sp2) + (636835189717969/25000000000000 : ℝ)*(sp3) + (17462327503/50000000000000 : ℝ)*(sp4) + (15366580843/100000000000000 : ℝ)*(sp7) + (1273678062726359/50000000000000 : ℝ)*(f.failure) + (1092069316772883/20000000000000 : ℝ)*(f.sum) + (14078390648089/9415000000000000000000000000 : ℝ)*base65 + (995279453358667559/235375000000000000000000000000000 : ℝ)*base68 + (2771444567437957441/235375000000000000000000000000000 : ℝ)*base69 + (694842444684417559/235375000000000000000000000000000 : ℝ)*base72 + (647186238283/294218750000000000000000000 : ℝ)*base74 + (621495074376832441/235375000000000000000000000000000 : ℝ)*base75 + (1262828363762082441/235375000000000000000000000000000 : ℝ)*base77 + (2244516010625792559/235375000000000000000000000000000 : ℝ)*base80 + (492612131471/147109375000000000000000000 : ℝ)*base81 + (19624867/1250000000000000000000 : ℝ)*base90 + (19624867/1250000000000000000000 : ℝ)*base92 + (19624867/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3205313547939590688018175299/941500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (145331119/6250000000000 : ℝ)*(base19) + (3528321367/100000000000000 : ℝ)*(base23) + (426062159/100000000000000 : ℝ)*(upper3) + (51497843/100000000000000 : ℝ)*(lower4) + (58209491/25000000000000 : ℝ)*(upper5) + (4036482629041283/100000000000000 : ℝ)*(major0) + (4036482629041283/100000000000000 : ℝ)*(major1) + (4036482629041283/100000000000000 : ℝ)*(major2) + (47233031563/100000000000000 : ℝ)*(sp1) + (66749857521/100000000000000 : ℝ)*(sp2) + (1376212061025491/25000000000000 : ℝ)*(sp4) + (344049917860781/6250000000000 : ℝ)*(sp5) + (220191118636923/4000000000000 : ℝ)*(sp6) + (2568116900498083/100000000000000 : ℝ)*(sp7) + (2568116900498083/100000000000000 : ℝ)*(f.failure) + (1376212061025491/25000000000000 : ℝ)*(f.sum) + (19022987843141/7061250000000000000000000000 : ℝ)*base65 + (20511824325744541567/5649000000000000000000000000000000 : ℝ)*base68 + (45665514164091541567/5649000000000000000000000000000000 : ℝ)*base70 + (10109936872227541567/5649000000000000000000000000000000 : ℝ)*base72 + (7307398427767/14122500000000000000000000000 : ℝ)*base73 + (39023559296676541567/5649000000000000000000000000000000 : ℝ)*base76 + (17289730515837541567/5649000000000000000000000000000000 : ℝ)*base78 + (29219385889935541567/5649000000000000000000000000000000 : ℝ)*base80 + (34870545429577/14122500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (8456479/2500000000000000000000 : ℝ)*base90 + (8456479/2500000000000000000000 : ℝ)*base92 + (8456479/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1404_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15879/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1023/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11083/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14961/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1404_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1404_s4_0 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-12446303/62500000 : ℝ)*x 0 + (5411155677/10000000000 : ℝ)*x 1 + (2622398159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12446303/62500000 : ℝ)^1091 ≤ (3035513421257/25000000000000 : ℝ)^835 := by
    have hnat : (12446303 : ℕ)^1091*25000000000000^835 ≤ 3035513421257^835*62500000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12446303 62500000 3035513421257 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411155677/10000000000 : ℝ)^1091 ≤ (22412498280967/50000000000000 : ℝ)^835 := by
    have hnat : (5411155677 : ℕ)^1091*50000000000000^835 ≤ 22412498280967^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411155677 10000000000 22412498280967 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622398159/5000000000 : ℝ)^1091 ≤ (43032949735341/100000000000000 : ℝ)^835 := by
    have hnat : (2622398159 : ℕ)^1091*100000000000000^835 ≤ 43032949735341^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622398159 5000000000 43032949735341 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-12446303/62500000 : ℝ), (5411155677/10000000000 : ℝ), (2622398159/5000000000 : ℝ)] ![(3035513421257/25000000000000 : ℝ), (22412498280967/50000000000000 : ℝ), (43032949735341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-12446303/62500000 : ℝ)|^1091 ≤ (3035513421257/25000000000000 : ℝ)^835
        have hw : |(-12446303/62500000 : ℝ)|=(12446303/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411155677/10000000000 : ℝ)|^1091 ≤ (22412498280967/50000000000000 : ℝ)^835
        have hw : |(5411155677/10000000000 : ℝ)|=(5411155677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622398159/5000000000 : ℝ)|^1091 ≤ (43032949735341/100000000000000 : ℝ)^835
        have hw : |(2622398159/5000000000 : ℝ)|=(2622398159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s4_1 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5348265449/10000000000 : ℝ)*x 0 + (-2076152373/10000000000 : ℝ)*x 1 + (5244796319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348265449/10000000000 : ℝ)^1091 ≤ (8829103791353/20000000000000 : ℝ)^835 := by
    have hnat : (5348265449 : ℕ)^1091*20000000000000^835 ≤ 8829103791353^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348265449 10000000000 8829103791353 20000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2076152373/10000000000 : ℝ)^1091 ≤ (12821531284873/100000000000000 : ℝ)^835 := by
    have hnat : (2076152373 : ℕ)^1091*100000000000000^835 ≤ 12821531284873^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076152373 10000000000 12821531284873 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244796319/10000000000 : ℝ)^1091 ≤ (43032949746061/100000000000000 : ℝ)^835 := by
    have hnat : (5244796319 : ℕ)^1091*100000000000000^835 ≤ 43032949746061^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244796319 10000000000 43032949746061 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348265449/10000000000 : ℝ), (-2076152373/10000000000 : ℝ), (5244796319/10000000000 : ℝ)] ![(8829103791353/20000000000000 : ℝ), (12821531284873/100000000000000 : ℝ), (43032949746061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348265449/10000000000 : ℝ)|^1091 ≤ (8829103791353/20000000000000 : ℝ)^835
        have hw : |(5348265449/10000000000 : ℝ)|=(5348265449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2076152373/10000000000 : ℝ)|^1091 ≤ (12821531284873/100000000000000 : ℝ)^835
        have hw : |(-2076152373/10000000000 : ℝ)|=(2076152373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244796319/10000000000 : ℝ)|^1091 ≤ (43032949746061/100000000000000 : ℝ)^835
        have hw : |(5244796319/10000000000 : ℝ)|=(5244796319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s4_2 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5348265449/10000000000 : ℝ)*x 0 + (5244796319/10000000000 : ℝ)*x 1 + (-519038093/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348265449/10000000000 : ℝ)^1091 ≤ (8829103791353/20000000000000 : ℝ)^835 := by
    have hnat : (5348265449 : ℕ)^1091*20000000000000^835 ≤ 8829103791353^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348265449 10000000000 8829103791353 20000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244796319/10000000000 : ℝ)^1091 ≤ (43032949746061/100000000000000 : ℝ)^835 := by
    have hnat : (5244796319 : ℕ)^1091*100000000000000^835 ≤ 43032949746061^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244796319 10000000000 43032949746061 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519038093/2500000000 : ℝ)^1091 ≤ (3205382819201/25000000000000 : ℝ)^835 := by
    have hnat : (519038093 : ℕ)^1091*25000000000000^835 ≤ 3205382819201^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519038093 2500000000 3205382819201 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348265449/10000000000 : ℝ), (5244796319/10000000000 : ℝ), (-519038093/2500000000 : ℝ)] ![(8829103791353/20000000000000 : ℝ), (43032949746061/100000000000000 : ℝ), (3205382819201/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348265449/10000000000 : ℝ)|^1091 ≤ (8829103791353/20000000000000 : ℝ)^835
        have hw : |(5348265449/10000000000 : ℝ)|=(5348265449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244796319/10000000000 : ℝ)|^1091 ≤ (43032949746061/100000000000000 : ℝ)^835
        have hw : |(5244796319/10000000000 : ℝ)|=(5244796319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-519038093/2500000000 : ℝ)|^1091 ≤ (3205382819201/25000000000000 : ℝ)^835
        have hw : |(-519038093/2500000000 : ℝ)|=(519038093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s4_3 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4310551743/10000000000 : ℝ)*x 0 + (4135606137/10000000000 : ℝ)*x 1 + (4492203237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310551743/10000000000 : ℝ)^1091 ≤ (8325790172307/25000000000000 : ℝ)^835 := by
    have hnat : (4310551743 : ℕ)^1091*25000000000000^835 ≤ 8325790172307^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310551743 10000000000 8325790172307 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4135606137/10000000000 : ℝ)^1091 ≤ (31548239749469/100000000000000 : ℝ)^835 := by
    have hnat : (4135606137 : ℕ)^1091*100000000000000^835 ≤ 31548239749469^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135606137 10000000000 31548239749469 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4492203237/10000000000 : ℝ)^1091 ≤ (7029719909751/20000000000000 : ℝ)^835 := by
    have hnat : (4492203237 : ℕ)^1091*20000000000000^835 ≤ 7029719909751^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492203237 10000000000 7029719909751 20000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310551743/10000000000 : ℝ), (4135606137/10000000000 : ℝ), (4492203237/10000000000 : ℝ)] ![(8325790172307/25000000000000 : ℝ), (31548239749469/100000000000000 : ℝ), (7029719909751/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310551743/10000000000 : ℝ)|^1091 ≤ (8325790172307/25000000000000 : ℝ)^835
        have hw : |(4310551743/10000000000 : ℝ)|=(4310551743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4135606137/10000000000 : ℝ)|^1091 ≤ (31548239749469/100000000000000 : ℝ)^835
        have hw : |(4135606137/10000000000 : ℝ)|=(4135606137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4492203237/10000000000 : ℝ)|^1091 ≤ (7029719909751/20000000000000 : ℝ)^835
        have hw : |(4492203237/10000000000 : ℝ)|=(4492203237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s4_4 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-497855199/2500000000 : ℝ)*x 0 + (655675813/1250000000 : ℝ)*x 1 + (2705271109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (497855199/2500000000 : ℝ)^1091 ≤ (6071075900551/50000000000000 : ℝ)^835 := by
    have hnat : (497855199 : ℕ)^1091*50000000000000^835 ≤ 6071075900551^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497855199 2500000000 6071075900551 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655675813/1250000000 : ℝ)^1091 ≤ (21519745643297/50000000000000 : ℝ)^835 := by
    have hnat : (655675813 : ℕ)^1091*50000000000000^835 ≤ 21519745643297^835*1250000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655675813 1250000000 21519745643297 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705271109/5000000000 : ℝ)^1091 ≤ (8963671378353/20000000000000 : ℝ)^835 := by
    have hnat : (2705271109 : ℕ)^1091*20000000000000^835 ≤ 8963671378353^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705271109 5000000000 8963671378353 20000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-497855199/2500000000 : ℝ), (655675813/1250000000 : ℝ), (2705271109/5000000000 : ℝ)] ![(6071075900551/50000000000000 : ℝ), (21519745643297/50000000000000 : ℝ), (8963671378353/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-497855199/2500000000 : ℝ)|^1091 ≤ (6071075900551/50000000000000 : ℝ)^835
        have hw : |(-497855199/2500000000 : ℝ)|=(497855199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655675813/1250000000 : ℝ)|^1091 ≤ (21519745643297/50000000000000 : ℝ)^835
        have hw : |(655675813/1250000000 : ℝ)|=(655675813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705271109/5000000000 : ℝ)|^1091 ≤ (8963671378353/20000000000000 : ℝ)^835
        have hw : |(2705271109/5000000000 : ℝ)|=(2705271109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s4_5 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1061024967/2000000000 : ℝ)*x 0 + (-955203211/5000000000 : ℝ)*x 1 + (5410542333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061024967/2000000000 : ℝ)^1091 ≤ (8736166519823/20000000000000 : ℝ)^835 := by
    have hnat : (1061024967 : ℕ)^1091*20000000000000^835 ≤ 8736166519823^835*2000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061024967 2000000000 8736166519823 20000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (955203211/5000000000 : ℝ)^1091 ≤ (1437601156473/12500000000000 : ℝ)^835 := by
    have hnat : (955203211 : ℕ)^1091*12500000000000^835 ≤ 1437601156473^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955203211 5000000000 1437601156473 12500000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410542333/10000000000 : ℝ)^1091 ≤ (22409179068213/50000000000000 : ℝ)^835 := by
    have hnat : (5410542333 : ℕ)^1091*50000000000000^835 ≤ 22409179068213^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410542333 10000000000 22409179068213 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061024967/2000000000 : ℝ), (-955203211/5000000000 : ℝ), (5410542333/10000000000 : ℝ)] ![(8736166519823/20000000000000 : ℝ), (1437601156473/12500000000000 : ℝ), (22409179068213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061024967/2000000000 : ℝ)|^1091 ≤ (8736166519823/20000000000000 : ℝ)^835
        have hw : |(1061024967/2000000000 : ℝ)|=(1061024967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-955203211/5000000000 : ℝ)|^1091 ≤ (1437601156473/12500000000000 : ℝ)^835
        have hw : |(-955203211/5000000000 : ℝ)|=(955203211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410542333/10000000000 : ℝ)|^1091 ≤ (22409179068213/50000000000000 : ℝ)^835
        have hw : |(5410542333/10000000000 : ℝ)|=(5410542333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s4_6 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (331570301/625000000 : ℝ)*x 0 + (541054227/1000000000 : ℝ)*x 1 + (-382081307/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331570301/625000000 : ℝ)^1091 ≤ (5460104049339/12500000000000 : ℝ)^835 := by
    have hnat : (331570301 : ℕ)^1091*12500000000000^835 ≤ 5460104049339^835*625000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331570301 625000000 5460104049339 12500000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541054227/1000000000 : ℝ)^1091 ≤ (5602294681821/12500000000000 : ℝ)^835 := by
    have hnat : (541054227 : ℕ)^1091*12500000000000^835 ≤ 5602294681821^835*1000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541054227 1000000000 5602294681821 12500000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (382081307/2000000000 : ℝ)^1091 ≤ (1437601267577/12500000000000 : ℝ)^835 := by
    have hnat : (382081307 : ℕ)^1091*12500000000000^835 ≤ 1437601267577^835*2000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382081307 2000000000 1437601267577 12500000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331570301/625000000 : ℝ), (541054227/1000000000 : ℝ), (-382081307/2000000000 : ℝ)] ![(5460104049339/12500000000000 : ℝ), (5602294681821/12500000000000 : ℝ), (1437601267577/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331570301/625000000 : ℝ)|^1091 ≤ (5460104049339/12500000000000 : ℝ)^835
        have hw : |(331570301/625000000 : ℝ)|=(331570301/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541054227/1000000000 : ℝ)|^1091 ≤ (5602294681821/12500000000000 : ℝ)^835
        have hw : |(541054227/1000000000 : ℝ)|=(541054227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-382081307/2000000000 : ℝ)|^1091 ≤ (1437601267577/12500000000000 : ℝ)^835
        have hw : |(-382081307/2000000000 : ℝ)|=(382081307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s4_7 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4310577933/10000000000 : ℝ)*x 0 + (2245447577/5000000000 : ℝ)*x 1 + (827384233/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310577933/10000000000 : ℝ)^1091 ≤ (16651712534057/50000000000000 : ℝ)^835 := by
    have hnat : (4310577933 : ℕ)^1091*50000000000000^835 ≤ 16651712534057^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310577933 10000000000 16651712534057 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245447577/5000000000 : ℝ)^1091 ≤ (1756761367507/5000000000000 : ℝ)^835 := by
    have hnat : (2245447577 : ℕ)^1091*5000000000000^835 ≤ 1756761367507^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245447577 5000000000 1756761367507 5000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (827384233/2000000000 : ℝ)^1091 ≤ (31561347567501/100000000000000 : ℝ)^835 := by
    have hnat : (827384233 : ℕ)^1091*100000000000000^835 ≤ 31561347567501^835*2000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827384233 2000000000 31561347567501 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310577933/10000000000 : ℝ), (2245447577/5000000000 : ℝ), (827384233/2000000000 : ℝ)] ![(16651712534057/50000000000000 : ℝ), (1756761367507/5000000000000 : ℝ), (31561347567501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310577933/10000000000 : ℝ)|^1091 ≤ (16651712534057/50000000000000 : ℝ)^835
        have hw : |(4310577933/10000000000 : ℝ)|=(4310577933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245447577/5000000000 : ℝ)|^1091 ≤ (1756761367507/5000000000000 : ℝ)^835
        have hw : |(2245447577/5000000000 : ℝ)|=(2245447577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(827384233/2000000000 : ℝ)|^1091 ≤ (31561347567501/100000000000000 : ℝ)^835
        have hw : |(827384233/2000000000 : ℝ)|=(827384233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1404_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14961/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11083/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2251/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7389/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14961/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11083/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14961/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11083/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14961/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11083/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14961/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11083/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14961/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11083/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14961/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11083/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11083/100000 : ℝ) ^ (4363/1024 : ℝ) ≤ (4251098819448317/50000000000000000000 : ℝ) := by
    have hpowers : (11083/100000 : ℝ)^4363 ≤ (4251098819448317/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11083 : ℕ)^4363*50000000000000000000^1024 ≤ 4251098819448317^1024*100000^4363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11083 100000 4251098819448317 50000000000000000000 4363 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11083/100000 : ℝ)) (X := (4251098819448317/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14961/100000 : ℝ) ^ (4363/1024 : ℝ) ≤ (244236128304909/800000000000000000 : ℝ) := by
    have hpowers : (14961/100000 : ℝ)^4363 ≤ (244236128304909/800000000000000000 : ℝ)^1024 := by
      have hnat : (14961 : ℕ)^4363*800000000000000000^1024 ≤ 244236128304909^1024*100000^4363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14961 100000 244236128304909 800000000000000000 4363 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14961/100000 : ℝ)) (X := (244236128304909/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004251098819448317/25000000000000000000 : ℝ) ≤ (1250049883588971/1250000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (25004251098819448317/25000000000000000000 : ℝ)^1024 ≤ (1250049883588971/1250000000000000 : ℝ)^4363 := by
      have hnat : (25004251098819448317 : ℕ)^1024*1250000000000000^4363 ≤ 1250049883588971^4363*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004251098819448317 25000000000000000000 1250049883588971 1250000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250049883588971/1250000000000000 : ℝ)) (X := (25004251098819448317/25000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039031713677010259/100000000000000000000 : ℝ) ≤ (5000457970509939/5000000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (100039031713677010259/100000000000000000000 : ℝ)^1024 ≤ (5000457970509939/5000000000000000 : ℝ)^4363 := by
      have hnat : (100039031713677010259 : ℕ)^1024*5000000000000000^4363 ≤ 5000457970509939^4363*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039031713677010259 100000000000000000000 5000457970509939 5000000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000457970509939/5000000000000000 : ℝ)) (X := (100039031713677010259/100000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (400244236128304909/400000000000000000 : ℝ) ≤ (2500358203331997/2500000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (400244236128304909/400000000000000000 : ℝ)^1024 ≤ (2500358203331997/2500000000000000 : ℝ)^4363 := by
      have hnat : (400244236128304909 : ℕ)^1024*2500000000000000^4363 ≤ 2500358203331997^4363*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400244236128304909 400000000000000000 2500358203331997 2500000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500358203331997/2500000000000000 : ℝ)) (X := (400244236128304909/400000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4251098819448317/50000000000000000000 : ℝ) ≤ ((9692522649220667511/9695000000000000000 : ℝ)+2*(51687230811/38780000000000 : ℝ)*(11083/100000 : ℝ))^(4363/1024 : ℝ) := by
    rw [show (9692522649220667511/9695000000000000000 : ℝ)+2*(51687230811/38780000000000 : ℝ)*(11083/100000 : ℝ)=(1250049883588971/1250000000000000 : ℝ) by norm_num, show 1+2*(4251098819448317/50000000000000000000 : ℝ)=(25004251098819448317/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(244236128304909/800000000000000000 : ℝ)+(4251098819448317/50000000000000000000 : ℝ) ≤ ((9692522649220667511/9695000000000000000 : ℝ)+(51687230811/38780000000000 : ℝ)*((14961/100000 : ℝ)+(11083/100000 : ℝ)))^(4363/1024 : ℝ) := by
    rw [show (9692522649220667511/9695000000000000000 : ℝ)+(51687230811/38780000000000 : ℝ)*((14961/100000 : ℝ)+(11083/100000 : ℝ))=(5000457970509939/5000000000000000 : ℝ) by norm_num, show 1+(244236128304909/800000000000000000 : ℝ)+(4251098819448317/50000000000000000000 : ℝ)=(100039031713677010259/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(244236128304909/800000000000000000 : ℝ) ≤ ((9692522649220667511/9695000000000000000 : ℝ)+2*(51687230811/38780000000000 : ℝ)*(14961/100000 : ℝ))^(4363/1024 : ℝ) := by
    rw [show (9692522649220667511/9695000000000000000 : ℝ)+2*(51687230811/38780000000000 : ℝ)*(14961/100000 : ℝ)=(2500358203331997/2500000000000000 : ℝ) by norm_num, show 1+2*(244236128304909/800000000000000000 : ℝ)=(400244236128304909/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9692522649220667511/9695000000000000000 : ℝ)*(X 1 0+X 2 0)+(51687230811/38780000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (11083/100000 : ℝ)) (hi := (14961/100000 : ℝ)) (c := (9692522649220667511/9695000000000000000 : ℝ)) (alpha := (51687230811/38780000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9692522649220667511/9695000000000000000 : ℝ)*(X 0 1+X 2 1)+(51687230811/38780000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (11083/100000 : ℝ)) (hi := (14961/100000 : ℝ)) (c := (9692522649220667511/9695000000000000000 : ℝ)) (alpha := (51687230811/38780000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9692522649220667511/9695000000000000000 : ℝ)*(X 0 2+X 1 2)+(51687230811/38780000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (11083/100000 : ℝ)) (hi := (14961/100000 : ℝ)) (c := (9692522649220667511/9695000000000000000 : ℝ)) (alpha := (51687230811/38780000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-12446303/62500000 : ℝ)*X 0 0+(5411155677/10000000000 : ℝ)*X 0 1+(2622398159/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348265449/10000000000 : ℝ)*X 1 0+(-2076152373/10000000000 : ℝ)*X 1 1+(5244796319/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348265449/10000000000 : ℝ)*X 2 0+(5244796319/10000000000 : ℝ)*X 2 1+(-519038093/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4310551743/10000000000 : ℝ)*X 0 0+(4135606137/10000000000 : ℝ)*X 0 1+(4492203237/10000000000 : ℝ)*X 0 2+(4310551743/10000000000 : ℝ)*X 1 0+(4135606137/10000000000 : ℝ)*X 1 1+(4492203237/10000000000 : ℝ)*X 1 2+(4310551743/10000000000 : ℝ)*X 2 0+(4135606137/10000000000 : ℝ)*X 2 1+(4492203237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-497855199/2500000000 : ℝ)*X 0 0+(655675813/1250000000 : ℝ)*X 0 1+(2705271109/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061024967/2000000000 : ℝ)*X 1 0+(-955203211/5000000000 : ℝ)*X 1 1+(5410542333/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331570301/625000000 : ℝ)*X 2 0+(541054227/1000000000 : ℝ)*X 2 1+(-382081307/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4310577933/10000000000 : ℝ)*X 0 0+(2245447577/5000000000 : ℝ)*X 0 1+(827384233/2000000000 : ℝ)*X 0 2+(4310577933/10000000000 : ℝ)*X 1 0+(2245447577/5000000000 : ℝ)*X 1 1+(827384233/2000000000 : ℝ)*X 1 2+(4310577933/10000000000 : ℝ)*X 2 0+(2245447577/5000000000 : ℝ)*X 2 1+(827384233/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7716795506193165958287453/875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (811208321/50000000000000 : ℝ)*(base19) + (1511976583/100000000000000 : ℝ)*(base23) + (2362651/4000000000000 : ℝ)*(lower2) + (221007997/100000000000000 : ℝ)*(upper3) + (35173533/25000000000000 : ℝ)*(upper5) + (2203867206095243/50000000000000 : ℝ)*(major0) + (2203867206095243/50000000000000 : ℝ)*(major1) + (2203867206095243/50000000000000 : ℝ)*(major2) + (240444727498257/4000000000000 : ℝ)*(sp0) + (1502787453460701/25000000000000 : ℝ)*(sp1) + (375696870267679/6250000000000 : ℝ)*(sp2) + (87634384828999/3125000000000 : ℝ)*(sp3) + (33248803021/100000000000000 : ℝ)*(sp4) + (16779620389/100000000000000 : ℝ)*(sp7) + (2804317094148357/100000000000000 : ℝ)*(f.failure) + (3005575718129723/50000000000000 : ℝ)*(f.sum) + (11044383283709/1939000000000000000000000000 : ℝ)*base66 + (2569870892742750173/484750000000000000000000000000000 : ℝ)*base67 + (1156150114087250173/484750000000000000000000000000000 : ℝ)*base69 + (1971676879035749827/484750000000000000000000000000000 : ℝ)*base72 + (673976731411/121187500000000000000000000 : ℝ)*base73 + (6511690049994250173/484750000000000000000000000000000 : ℝ)*base75 + (5405397173200749827/484750000000000000000000000000000 : ℝ)*base78 + (1152047767424500173/484750000000000000000000000000000 : ℝ)*base79 + (44182321919/1939000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4299241/2500000000000000000000 : ℝ)*base90 + (4299241/2500000000000000000000 : ℝ)*base92 + (4299241/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3886195318102321976671527/875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (338339059/50000000000000 : ℝ)*(base19) + (672273811/100000000000000 : ℝ)*(base23) + (14628041/50000000000000 : ℝ)*(upper2) + (83777921/100000000000000 : ℝ)*(upper3) + (525751/400000000000 : ℝ)*(upper5) + (2220172814919863/50000000000000 : ℝ)*(major0) + (2220172814919863/50000000000000 : ℝ)*(major1) + (2220172814919863/50000000000000 : ℝ)*(major2) + (8942004957/50000000000000 : ℝ)*(sp1) + (6613925113/50000000000000 : ℝ)*(sp2) + (6055625899163851/100000000000000 : ℝ)*(sp4) + (6055607338475819/100000000000000 : ℝ)*(sp5) + (3027805999519907/50000000000000 : ℝ)*(sp6) + (2825065212470057/100000000000000 : ℝ)*(sp7) + (2825065212470057/100000000000000 : ℝ)*(f.failure) + (6055625899163851/100000000000000 : ℝ)*(f.sum) + (7536203558329/1939000000000000000000000000 : ℝ)*base66 + (2057095258456420993/484750000000000000000000000000000 : ℝ)*base67 + (7653332996618329007/484750000000000000000000000000000 : ℝ)*base70 + (5461759103356079007/484750000000000000000000000000000 : ℝ)*base72 + (365076630269/121187500000000000000000000 : ℝ)*base73 + (1626964999799579007/484750000000000000000000000000000 : ℝ)*base76 + (6742730100289329007/484750000000000000000000000000000 : ℝ)*base78 + (9584793050248920993/484750000000000000000000000000000 : ℝ)*base79 + (9351163901791/1939000000000000000000000000 : ℝ)*base82 + (1658659/2500000000000000000000 : ℝ)*base89 + (1658659/2500000000000000000000 : ℝ)*base91 + (1658659/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1404_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14961/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11083/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2251/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7389/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1404_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1404_s5_0 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1991570991/10000000000 : ℝ)*x 0 + (5409733491/10000000000 : ℝ)*x 1 + (524611131/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1991570991/10000000000 : ℝ)^1091 ≤ (12143348352591/100000000000000 : ℝ)^835 := by
    have hnat : (1991570991 : ℕ)^1091*100000000000000^835 ≤ 12143348352591^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991570991 10000000000 12143348352591 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409733491/10000000000 : ℝ)^1091 ≤ (22404802061989/50000000000000 : ℝ)^835 := by
    have hnat : (5409733491 : ℕ)^1091*50000000000000^835 ≤ 22404802061989^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409733491 10000000000 22404802061989 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524611131/1000000000 : ℝ)^1091 ≤ (8609409502007/20000000000000 : ℝ)^835 := by
    have hnat : (524611131 : ℕ)^1091*20000000000000^835 ≤ 8609409502007^835*1000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524611131 1000000000 8609409502007 20000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1991570991/10000000000 : ℝ), (5409733491/10000000000 : ℝ), (524611131/1000000000 : ℝ)] ![(12143348352591/100000000000000 : ℝ), (22404802061989/50000000000000 : ℝ), (8609409502007/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1991570991/10000000000 : ℝ)|^1091 ≤ (12143348352591/100000000000000 : ℝ)^835
        have hw : |(-1991570991/10000000000 : ℝ)|=(1991570991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409733491/10000000000 : ℝ)|^1091 ≤ (22404802061989/50000000000000 : ℝ)^835
        have hw : |(5409733491/10000000000 : ℝ)|=(5409733491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524611131/1000000000 : ℝ)|^1091 ≤ (8609409502007/20000000000000 : ℝ)^835
        have hw : |(524611131/1000000000 : ℝ)|=(524611131/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s5_1 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5347898663/10000000000 : ℝ)*x 0 + (-1037447613/5000000000 : ℝ)*x 1 + (5246111391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347898663/10000000000 : ℝ)^1091 ≤ (882831265721/2000000000000 : ℝ)^835 := by
    have hnat : (5347898663 : ℕ)^1091*2000000000000^835 ≤ 882831265721^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347898663 10000000000 882831265721 2000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037447613/5000000000 : ℝ)^1091 ≤ (12811388325377/100000000000000 : ℝ)^835 := by
    have hnat : (1037447613 : ℕ)^1091*100000000000000^835 ≤ 12811388325377^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037447613 5000000000 12811388325377 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246111391/10000000000 : ℝ)^1091 ≤ (21523524189227/50000000000000 : ℝ)^835 := by
    have hnat : (5246111391 : ℕ)^1091*50000000000000^835 ≤ 21523524189227^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246111391 10000000000 21523524189227 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347898663/10000000000 : ℝ), (-1037447613/5000000000 : ℝ), (5246111391/10000000000 : ℝ)] ![(882831265721/2000000000000 : ℝ), (12811388325377/100000000000000 : ℝ), (21523524189227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347898663/10000000000 : ℝ)|^1091 ≤ (882831265721/2000000000000 : ℝ)^835
        have hw : |(5347898663/10000000000 : ℝ)|=(5347898663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1037447613/5000000000 : ℝ)|^1091 ≤ (12811388325377/100000000000000 : ℝ)^835
        have hw : |(-1037447613/5000000000 : ℝ)|=(1037447613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246111391/10000000000 : ℝ)|^1091 ≤ (21523524189227/50000000000000 : ℝ)^835
        have hw : |(5246111391/10000000000 : ℝ)|=(5246111391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s5_2 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1336974671/2500000000 : ℝ)*x 0 + (2623055669/5000000000 : ℝ)*x 1 + (-2074895267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336974671/2500000000 : ℝ)^1091 ≤ (22070781756263/50000000000000 : ℝ)^835 := by
    have hnat : (1336974671 : ℕ)^1091*50000000000000^835 ≤ 22070781756263^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336974671 2500000000 22070781756263 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623055669/5000000000 : ℝ)^1091 ≤ (43047047810229/100000000000000 : ℝ)^835 := by
    have hnat : (2623055669 : ℕ)^1091*100000000000000^835 ≤ 43047047810229^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623055669 5000000000 43047047810229 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2074895267/10000000000 : ℝ)^1091 ≤ (800711791009/6250000000000 : ℝ)^835 := by
    have hnat : (2074895267 : ℕ)^1091*6250000000000^835 ≤ 800711791009^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074895267 10000000000 800711791009 6250000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336974671/2500000000 : ℝ), (2623055669/5000000000 : ℝ), (-2074895267/10000000000 : ℝ)] ![(22070781756263/50000000000000 : ℝ), (43047047810229/100000000000000 : ℝ), (800711791009/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336974671/2500000000 : ℝ)|^1091 ≤ (22070781756263/50000000000000 : ℝ)^835
        have hw : |(1336974671/2500000000 : ℝ)|=(1336974671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623055669/5000000000 : ℝ)|^1091 ≤ (43047047810229/100000000000000 : ℝ)^835
        have hw : |(2623055669/5000000000 : ℝ)|=(2623055669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2074895267/10000000000 : ℝ)|^1091 ≤ (800711791009/6250000000000 : ℝ)^835
        have hw : |(-2074895267/10000000000 : ℝ)|=(2074895267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s5_3 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (269415577/625000000 : ℝ)*x 0 + (827705603/2000000000 : ℝ)*x 1 + (1122314413/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269415577/625000000 : ℝ)^1091 ≤ (33304144809067/100000000000000 : ℝ)^835 := by
    have hnat : (269415577 : ℕ)^1091*100000000000000^835 ≤ 33304144809067^835*625000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269415577 625000000 33304144809067 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (827705603/2000000000 : ℝ)^1091 ≤ (789434147921/2500000000000 : ℝ)^835 := by
    have hnat : (827705603 : ℕ)^1091*2500000000000^835 ≤ 789434147921^835*2000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827705603 2000000000 789434147921 2500000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122314413/2500000000 : ℝ)^1091 ≤ (17559244634117/50000000000000 : ℝ)^835 := by
    have hnat : (1122314413 : ℕ)^1091*50000000000000^835 ≤ 17559244634117^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122314413 2500000000 17559244634117 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269415577/625000000 : ℝ), (827705603/2000000000 : ℝ), (1122314413/2500000000 : ℝ)] ![(33304144809067/100000000000000 : ℝ), (789434147921/2500000000000 : ℝ), (17559244634117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269415577/625000000 : ℝ)|^1091 ≤ (33304144809067/100000000000000 : ℝ)^835
        have hw : |(269415577/625000000 : ℝ)|=(269415577/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(827705603/2000000000 : ℝ)|^1091 ≤ (789434147921/2500000000000 : ℝ)^835
        have hw : |(827705603/2000000000 : ℝ)|=(827705603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122314413/2500000000 : ℝ)|^1091 ≤ (17559244634117/50000000000000 : ℝ)^835
        have hw : |(1122314413/2500000000 : ℝ)|=(1122314413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s5_4 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-39831653/200000000 : ℝ)*x 0 + (655837717/1250000000 : ℝ)*x 1 + (1352284999/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (39831653/200000000 : ℝ)^1091 ≤ (12143441236959/100000000000000 : ℝ)^835 := by
    have hnat : (39831653 : ℕ)^1091*100000000000000^835 ≤ 12143441236959^835*200000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39831653 200000000 12143441236959 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655837717/1250000000 : ℝ)^1091 ≤ (43053377705347/100000000000000 : ℝ)^835 := by
    have hnat : (655837717 : ℕ)^1091*100000000000000^835 ≤ 43053377705347^835*1250000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655837717 1250000000 43053377705347 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352284999/2500000000 : ℝ)^1091 ≤ (2800198815303/6250000000000 : ℝ)^835 := by
    have hnat : (1352284999 : ℕ)^1091*6250000000000^835 ≤ 2800198815303^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352284999 2500000000 2800198815303 6250000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-39831653/200000000 : ℝ), (655837717/1250000000 : ℝ), (1352284999/2500000000 : ℝ)] ![(12143441236959/100000000000000 : ℝ), (43053377705347/100000000000000 : ℝ), (2800198815303/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-39831653/200000000 : ℝ)|^1091 ≤ (12143441236959/100000000000000 : ℝ)^835
        have hw : |(-39831653/200000000 : ℝ)|=(39831653/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655837717/1250000000 : ℝ)|^1091 ≤ (43053377705347/100000000000000 : ℝ)^835
        have hw : |(655837717/1250000000 : ℝ)|=(655837717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352284999/2500000000 : ℝ)|^1091 ≤ (2800198815303/6250000000000 : ℝ)^835
        have hw : |(1352284999/2500000000 : ℝ)|=(1352284999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s5_5 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305467851/10000000000 : ℝ)*x 0 + (-955933307/5000000000 : ℝ)*x 1 + (1352284999/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305467851/10000000000 : ℝ)^1091 ≤ (43684522819111/100000000000000 : ℝ)^835 := by
    have hnat : (5305467851 : ℕ)^1091*100000000000000^835 ≤ 43684522819111^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305467851 10000000000 43684522819111 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (955933307/5000000000 : ℝ)^1091 ≤ (11512296122793/100000000000000 : ℝ)^835 := by
    have hnat : (955933307 : ℕ)^1091*100000000000000^835 ≤ 11512296122793^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955933307 5000000000 11512296122793 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352284999/2500000000 : ℝ)^1091 ≤ (2800198815303/6250000000000 : ℝ)^835 := by
    have hnat : (1352284999 : ℕ)^1091*6250000000000^835 ≤ 2800198815303^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352284999 2500000000 2800198815303 6250000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305467851/10000000000 : ℝ), (-955933307/5000000000 : ℝ), (1352284999/2500000000 : ℝ)] ![(43684522819111/100000000000000 : ℝ), (11512296122793/100000000000000 : ℝ), (2800198815303/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305467851/10000000000 : ℝ)|^1091 ≤ (43684522819111/100000000000000 : ℝ)^835
        have hw : |(5305467851/10000000000 : ℝ)|=(5305467851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-955933307/5000000000 : ℝ)|^1091 ≤ (11512296122793/100000000000000 : ℝ)^835
        have hw : |(-955933307/5000000000 : ℝ)|=(955933307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352284999/2500000000 : ℝ)|^1091 ≤ (2800198815303/6250000000000 : ℝ)^835
        have hw : |(1352284999/2500000000 : ℝ)|=(1352284999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s5_6 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305467849/10000000000 : ℝ)*x 0 + (2704569999/5000000000 : ℝ)*x 1 + (-955933307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305467849/10000000000 : ℝ)^1091 ≤ (21842261398797/50000000000000 : ℝ)^835 := by
    have hnat : (5305467849 : ℕ)^1091*50000000000000^835 ≤ 21842261398797^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305467849 10000000000 21842261398797 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704569999/5000000000 : ℝ)^1091 ≤ (11200795266623/25000000000000 : ℝ)^835 := by
    have hnat : (2704569999 : ℕ)^1091*25000000000000^835 ≤ 11200795266623^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704569999 5000000000 11200795266623 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (955933307/5000000000 : ℝ)^1091 ≤ (11512296122793/100000000000000 : ℝ)^835 := by
    have hnat : (955933307 : ℕ)^1091*100000000000000^835 ≤ 11512296122793^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955933307 5000000000 11512296122793 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305467849/10000000000 : ℝ), (2704569999/5000000000 : ℝ), (-955933307/5000000000 : ℝ)] ![(21842261398797/50000000000000 : ℝ), (11200795266623/25000000000000 : ℝ), (11512296122793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305467849/10000000000 : ℝ)|^1091 ≤ (21842261398797/50000000000000 : ℝ)^835
        have hw : |(5305467849/10000000000 : ℝ)|=(5305467849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704569999/5000000000 : ℝ)|^1091 ≤ (11200795266623/25000000000000 : ℝ)^835
        have hw : |(2704569999/5000000000 : ℝ)|=(2704569999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-955933307/5000000000 : ℝ)|^1091 ≤ (11512296122793/100000000000000 : ℝ)^835
        have hw : |(-955933307/5000000000 : ℝ)|=(955933307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s5_7 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4310674181/10000000000 : ℝ)*x 0 + (448799217/1000000000 : ℝ)*x 1 + (1034950019/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310674181/10000000000 : ℝ)^1091 ≤ (33304396662227/100000000000000 : ℝ)^835 := by
    have hnat : (4310674181 : ℕ)^1091*100000000000000^835 ≤ 33304396662227^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310674181 10000000000 33304396662227 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448799217/1000000000 : ℝ)^1091 ≤ (35105555151613/100000000000000 : ℝ)^835 := by
    have hnat : (448799217 : ℕ)^1091*100000000000000^835 ≤ 35105555151613^835*1000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448799217 1000000000 35105555151613 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034950019/2500000000 : ℝ)^1091 ≤ (31590048177479/100000000000000 : ℝ)^835 := by
    have hnat : (1034950019 : ℕ)^1091*100000000000000^835 ≤ 31590048177479^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034950019 2500000000 31590048177479 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310674181/10000000000 : ℝ), (448799217/1000000000 : ℝ), (1034950019/2500000000 : ℝ)] ![(33304396662227/100000000000000 : ℝ), (35105555151613/100000000000000 : ℝ), (31590048177479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310674181/10000000000 : ℝ)|^1091 ≤ (33304396662227/100000000000000 : ℝ)^835
        have hw : |(4310674181/10000000000 : ℝ)|=(4310674181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448799217/1000000000 : ℝ)|^1091 ≤ (35105555151613/100000000000000 : ℝ)^835
        have hw : |(448799217/1000000000 : ℝ)|=(448799217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1034950019/2500000000 : ℝ)|^1091 ≤ (31590048177479/100000000000000 : ℝ)^835
        have hw : |(1034950019/2500000000 : ℝ)|=(1034950019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1404_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7389/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2251/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11283/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14749/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7389/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2251/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7389/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2251/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7389/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2251/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7389/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2251/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7389/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2251/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7389/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2251/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2251/20000 : ℝ) ^ (4363/1024 : ℝ) ≤ (4539392669559119/50000000000000000000 : ℝ) := by
    have hpowers : (2251/20000 : ℝ)^4363 ≤ (4539392669559119/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2251 : ℕ)^4363*50000000000000000000^1024 ≤ 4539392669559119^1024*20000^4363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2251 20000 4539392669559119 50000000000000000000 4363 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2251/20000 : ℝ)) (X := (4539392669559119/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7389/50000 : ℝ) ^ (4363/1024 : ℝ) ≤ (28969861584904583/100000000000000000000 : ℝ) := by
    have hpowers : (7389/50000 : ℝ)^4363 ≤ (28969861584904583/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7389 : ℕ)^4363*100000000000000000000^1024 ≤ 28969861584904583^1024*50000^4363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7389 50000 28969861584904583 100000000000000000000 4363 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7389/50000 : ℝ)) (X := (28969861584904583/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004539392669559119/25000000000000000000 : ℝ) ≤ (10000426130200527/10000000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (25004539392669559119/25000000000000000000 : ℝ)^1024 ≤ (10000426130200527/10000000000000000 : ℝ)^4363 := by
      have hnat : (25004539392669559119 : ℕ)^1024*10000000000000000^4363 ≤ 10000426130200527^4363*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004539392669559119 25000000000000000000 10000426130200527 10000000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000426130200527/10000000000000000 : ℝ)) (X := (25004539392669559119/25000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038048646924022821/100000000000000000000 : ℝ) ≤ (400035715006329/400000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (100038048646924022821/100000000000000000000 : ℝ)^1024 ≤ (400035715006329/400000000000000 : ℝ)^4363 := by
      have hnat : (100038048646924022821 : ℕ)^1024*400000000000000^4363 ≤ 400035715006329^4363*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038048646924022821 100000000000000000000 400035715006329 400000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400035715006329/400000000000000 : ℝ)) (X := (100038048646924022821/100000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028969861584904583/50000000000000000000 : ℝ) ≤ (10001359620115923/10000000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (50028969861584904583/50000000000000000000 : ℝ)^1024 ≤ (10001359620115923/10000000000000000 : ℝ)^4363 := by
      have hnat : (50028969861584904583 : ℕ)^1024*10000000000000000^4363 ≤ 10001359620115923^4363*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028969861584904583 50000000000000000000 10001359620115923 10000000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001359620115923/10000000000000000 : ℝ)) (X := (50028969861584904583/50000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4539392669559119/50000000000000000000 : ℝ) ≤ ((35220994827698674641/35230000000000000000 : ℝ)+2*(233372478849/176150000000000 : ℝ)*(2251/20000 : ℝ))^(4363/1024 : ℝ) := by
    rw [show (35220994827698674641/35230000000000000000 : ℝ)+2*(233372478849/176150000000000 : ℝ)*(2251/20000 : ℝ)=(10000426130200527/10000000000000000 : ℝ) by norm_num, show 1+2*(4539392669559119/50000000000000000000 : ℝ)=(25004539392669559119/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28969861584904583/100000000000000000000 : ℝ)+(4539392669559119/50000000000000000000 : ℝ) ≤ ((35220994827698674641/35230000000000000000 : ℝ)+(233372478849/176150000000000 : ℝ)*((7389/50000 : ℝ)+(2251/20000 : ℝ)))^(4363/1024 : ℝ) := by
    rw [show (35220994827698674641/35230000000000000000 : ℝ)+(233372478849/176150000000000 : ℝ)*((7389/50000 : ℝ)+(2251/20000 : ℝ))=(400035715006329/400000000000000 : ℝ) by norm_num, show 1+(28969861584904583/100000000000000000000 : ℝ)+(4539392669559119/50000000000000000000 : ℝ)=(100038048646924022821/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28969861584904583/100000000000000000000 : ℝ) ≤ ((35220994827698674641/35230000000000000000 : ℝ)+2*(233372478849/176150000000000 : ℝ)*(7389/50000 : ℝ))^(4363/1024 : ℝ) := by
    rw [show (35220994827698674641/35230000000000000000 : ℝ)+2*(233372478849/176150000000000 : ℝ)*(7389/50000 : ℝ)=(10001359620115923/10000000000000000 : ℝ) by norm_num, show 1+2*(28969861584904583/100000000000000000000 : ℝ)=(50028969861584904583/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35220994827698674641/35230000000000000000 : ℝ)*(X 1 0+X 2 0)+(233372478849/176150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (2251/20000 : ℝ)) (hi := (7389/50000 : ℝ)) (c := (35220994827698674641/35230000000000000000 : ℝ)) (alpha := (233372478849/176150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35220994827698674641/35230000000000000000 : ℝ)*(X 0 1+X 2 1)+(233372478849/176150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (2251/20000 : ℝ)) (hi := (7389/50000 : ℝ)) (c := (35220994827698674641/35230000000000000000 : ℝ)) (alpha := (233372478849/176150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35220994827698674641/35230000000000000000 : ℝ)*(X 0 2+X 1 2)+(233372478849/176150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (2251/20000 : ℝ)) (hi := (7389/50000 : ℝ)) (c := (35220994827698674641/35230000000000000000 : ℝ)) (alpha := (233372478849/176150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1991570991/10000000000 : ℝ)*X 0 0+(5409733491/10000000000 : ℝ)*X 0 1+(524611131/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347898663/10000000000 : ℝ)*X 1 0+(-1037447613/5000000000 : ℝ)*X 1 1+(5246111391/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336974671/2500000000 : ℝ)*X 2 0+(2623055669/5000000000 : ℝ)*X 2 1+(-2074895267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((269415577/625000000 : ℝ)*X 0 0+(827705603/2000000000 : ℝ)*X 0 1+(1122314413/2500000000 : ℝ)*X 0 2+(269415577/625000000 : ℝ)*X 1 0+(827705603/2000000000 : ℝ)*X 1 1+(1122314413/2500000000 : ℝ)*X 1 2+(269415577/625000000 : ℝ)*X 2 0+(827705603/2000000000 : ℝ)*X 2 1+(1122314413/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-39831653/200000000 : ℝ)*X 0 0+(655837717/1250000000 : ℝ)*X 0 1+(1352284999/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305467851/10000000000 : ℝ)*X 1 0+(-955933307/5000000000 : ℝ)*X 1 1+(1352284999/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305467849/10000000000 : ℝ)*X 2 0+(2704569999/5000000000 : ℝ)*X 2 1+(-955933307/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4310674181/10000000000 : ℝ)*X 0 0+(448799217/1000000000 : ℝ)*X 0 1+(1034950019/2500000000 : ℝ)*X 0 2+(4310674181/10000000000 : ℝ)*X 1 0+(448799217/1000000000 : ℝ)*X 1 1+(1034950019/2500000000 : ℝ)*X 1 2+(4310674181/10000000000 : ℝ)*X 2 0+(448799217/1000000000 : ℝ)*X 2 1+(1034950019/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3358032206452174998728286663/352300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1746861359/100000000000000 : ℝ)*(base19) + (1632516587/100000000000000 : ℝ)*(base23) + (73985033/100000000000000 : ℝ)*(lower2) + (2692827/1000000000000 : ℝ)*(upper3) + (120017599/100000000000000 : ℝ)*(upper5) + (896295352488127/20000000000000 : ℝ)*(major0) + (896295352488127/20000000000000 : ℝ)*(major1) + (896295352488127/20000000000000 : ℝ)*(major2) + (3055840912053709/50000000000000 : ℝ)*(sp0) + (381982345906131/6250000000000 : ℝ)*(sp1) + (1527929412210717/25000000000000 : ℝ)*(sp2) + (44550233995773/1562500000000 : ℝ)*(sp3) + (9364313009/25000000000000 : ℝ)*(sp4) + (18950067641/100000000000000 : ℝ)*(sp7) + (356404240724639/12500000000000 : ℝ)*(f.failure) + (1222343856271891/20000000000000 : ℝ)*(f.sum) + (941994507651/704600000000000000000000000 : ℝ)*base66 + (14947234523053312593/704600000000000000000000000000000 : ℝ)*base68 + (1403054055968512593/704600000000000000000000000000000 : ℝ)*base70 + (12589211981942712593/704600000000000000000000000000000 : ℝ)*base72 + (1035895087031/220187500000000000000000000 : ℝ)*base74 + (3156579463628512593/704600000000000000000000000000000 : ℝ)*base76 + (8309147511037112593/704600000000000000000000000000000 : ℝ)*base78 + (14234437664643312593/704600000000000000000000000000000 : ℝ)*base80 + (4008258414727/1761500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (4001507/312500000000000000000 : ℝ)*base90 + (4001507/312500000000000000000 : ℝ)*base92 + (4001507/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5196294887904570996105674823/440375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1006669717/50000000000000 : ℝ)*(base19) + (2180711149/100000000000000 : ℝ)*(base23) + (12063119/5000000000000 : ℝ)*(upper3) + (19229333/25000000000000 : ℝ)*(lower4) + (48405033/20000000000000 : ℝ)*(upper5) + (2257040303588301/50000000000000 : ℝ)*(major0) + (2257040303588301/50000000000000 : ℝ)*(major1) + (2257040303588301/50000000000000 : ℝ)*(major2) + (209482737/500000000000 : ℝ)*(sp1) + (22493415829/50000000000000 : ℝ)*(sp2) + (6156183467753129/100000000000000 : ℝ)*(sp4) + (3078069778933147/50000000000000 : ℝ)*(sp5) + (3078068150105161/50000000000000 : ℝ)*(sp6) + (1435988676638291/50000000000000 : ℝ)*(sp7) + (1435988676638291/50000000000000 : ℝ)*(f.failure) + (6156183467753129/100000000000000 : ℝ)*(f.sum) + (1052627279923/2201875000000000000000000000 : ℝ)*base66 + (15537190854843225059/1761500000000000000000000000000000 : ℝ)*base68 + (10304783398411225059/1761500000000000000000000000000000 : ℝ)*base70 + (4035056093358774941/1761500000000000000000000000000000 : ℝ)*base71 + (35412685342641/4403750000000000000000000000 : ℝ)*base74 + (9739484121921225059/1761500000000000000000000000000000 : ℝ)*base76 + (21871386157785225059/1761500000000000000000000000000000 : ℝ)*base78 + (30210601789727225059/1761500000000000000000000000000000 : ℝ)*base80 + (14012819292087/8807500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (12914417/1250000000000000000000 : ℝ)*base89 + (12914417/1250000000000000000000 : ℝ)*base91 + (12914417/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1404_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7389/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2251/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11283/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1404_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1404_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15879/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1023/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11283/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1404_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1404_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1404_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15879/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1023/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11283/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1404_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

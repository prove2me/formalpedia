-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1226_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:13:12.897584+00:00
-- url     : https://prove2.me/submissions/2a9f5032-7b86-4b0e-8863-f45cfb84b776

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
theorem support_rectangle_w1226_s6_0 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2127330163/10000000000 : ℝ)*x 0 + (673963711/1250000000 : ℝ)*x 1 + (210671869/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127330163/10000000000 : ℝ)^8419 ≤ (1293489743523/10000000000000 : ℝ)^6371 := by
    have hnat : (2127330163 : ℕ)^8419*10000000000000^6371 ≤ 1293489743523^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127330163 10000000000 1293489743523 10000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673963711/1250000000 : ℝ)^8419 ≤ (44206711843713/100000000000000 : ℝ)^6371 := by
    have hnat : (673963711 : ℕ)^8419*100000000000000^6371 ≤ 44206711843713^6371*1250000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673963711 1250000000 44206711843713 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210671869/400000000 : ℝ)^8419 ≤ (21429195354817/50000000000000 : ℝ)^6371 := by
    have hnat : (210671869 : ℕ)^8419*50000000000000^6371 ≤ 21429195354817^6371*400000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210671869 400000000 21429195354817 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2127330163/10000000000 : ℝ), (673963711/1250000000 : ℝ), (210671869/400000000 : ℝ)] ![(1293489743523/10000000000000 : ℝ), (44206711843713/100000000000000 : ℝ), (21429195354817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2127330163/10000000000 : ℝ)|^8419 ≤ (1293489743523/10000000000000 : ℝ)^6371
        have hw : |(-2127330163/10000000000 : ℝ)|=(2127330163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673963711/1250000000 : ℝ)|^8419 ≤ (44206711843713/100000000000000 : ℝ)^6371
        have hw : |(673963711/1250000000 : ℝ)|=(673963711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210671869/400000000 : ℝ)|^8419 ≤ (21429195354817/50000000000000 : ℝ)^6371
        have hw : |(210671869/400000000 : ℝ)|=(210671869/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s6_1 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672223301/5000000000 : ℝ)*x 0 + (-109533559/500000000 : ℝ)*x 1 + (2633398223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672223301/5000000000 : ℝ)^8419 ≤ (43695356082867/100000000000000 : ℝ)^6371 := by
    have hnat : (2672223301 : ℕ)^8419*100000000000000^6371 ≤ 43695356082867^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672223301 5000000000 43695356082867 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109533559/500000000 : ℝ)^8419 ≤ (3361564048831/25000000000000 : ℝ)^6371 := by
    have hnat : (109533559 : ℕ)^8419*25000000000000^6371 ≤ 3361564048831^6371*500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109533559 500000000 3361564048831 25000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633398223/5000000000 : ℝ)^8419 ≤ (2142919385473/5000000000000 : ℝ)^6371 := by
    have hnat : (2633398223 : ℕ)^8419*5000000000000^6371 ≤ 2142919385473^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633398223 5000000000 2142919385473 5000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672223301/5000000000 : ℝ), (-109533559/500000000 : ℝ), (2633398223/5000000000 : ℝ)] ![(43695356082867/100000000000000 : ℝ), (3361564048831/25000000000000 : ℝ), (2142919385473/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672223301/5000000000 : ℝ)|^8419 ≤ (43695356082867/100000000000000 : ℝ)^6371
        have hw : |(2672223301/5000000000 : ℝ)|=(2672223301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-109533559/500000000 : ℝ)|^8419 ≤ (3361564048831/25000000000000 : ℝ)^6371
        have hw : |(-109533559/500000000 : ℝ)|=(109533559/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633398223/5000000000 : ℝ)|^8419 ≤ (2142919385473/5000000000000 : ℝ)^6371
        have hw : |(2633398223/5000000000 : ℝ)|=(2633398223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s6_2 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068889289/2000000000 : ℝ)*x 0 + (1053359309/2000000000 : ℝ)*x 1 + (-2190671257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068889289/2000000000 : ℝ)^8419 ≤ (8739070877327/20000000000000 : ℝ)^6371 := by
    have hnat : (1068889289 : ℕ)^8419*20000000000000^6371 ≤ 8739070877327^6371*2000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068889289 2000000000 8739070877327 20000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053359309/2000000000 : ℝ)^8419 ≤ (21429194387019/50000000000000 : ℝ)^6371 := by
    have hnat : (1053359309 : ℕ)^8419*50000000000000^6371 ≤ 21429194387019^6371*2000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053359309 2000000000 21429194387019 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190671257/10000000000 : ℝ)^8419 ≤ (107570054559/800000000000 : ℝ)^6371 := by
    have hnat : (2190671257 : ℕ)^8419*800000000000^6371 ≤ 107570054559^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190671257 10000000000 107570054559 800000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068889289/2000000000 : ℝ), (1053359309/2000000000 : ℝ), (-2190671257/10000000000 : ℝ)] ![(8739070877327/20000000000000 : ℝ), (21429194387019/50000000000000 : ℝ), (107570054559/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068889289/2000000000 : ℝ)|^8419 ≤ (8739070877327/20000000000000 : ℝ)^6371
        have hw : |(1068889289/2000000000 : ℝ)|=(1068889289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053359309/2000000000 : ℝ)|^8419 ≤ (21429194387019/50000000000000 : ℝ)^6371
        have hw : |(1053359309/2000000000 : ℝ)|=(1053359309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2190671257/10000000000 : ℝ)|^8419 ≤ (107570054559/800000000000 : ℝ)^6371
        have hw : |(-2190671257/10000000000 : ℝ)|=(2190671257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s6_3 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4352961343/10000000000 : ℝ)*x 0 + (4228443707/10000000000 : ℝ)*x 1 + (896211277/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352961343/10000000000 : ℝ)^8419 ≤ (16658650160511/50000000000000 : ℝ)^6371 := by
    have hnat : (4352961343 : ℕ)^8419*50000000000000^6371 ≤ 16658650160511^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352961343 10000000000 16658650160511 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4228443707/10000000000 : ℝ)^8419 ≤ (32063713904199/100000000000000 : ℝ)^6371 := by
    have hnat : (4228443707 : ℕ)^8419*100000000000000^6371 ≤ 32063713904199^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228443707 10000000000 32063713904199 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (896211277/2000000000 : ℝ)^8419 ≤ (17309492878217/50000000000000 : ℝ)^6371 := by
    have hnat : (896211277 : ℕ)^8419*50000000000000^6371 ≤ 17309492878217^6371*2000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896211277 2000000000 17309492878217 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352961343/10000000000 : ℝ), (4228443707/10000000000 : ℝ), (896211277/2000000000 : ℝ)] ![(16658650160511/50000000000000 : ℝ), (32063713904199/100000000000000 : ℝ), (17309492878217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352961343/10000000000 : ℝ)|^8419 ≤ (16658650160511/50000000000000 : ℝ)^6371
        have hw : |(4352961343/10000000000 : ℝ)|=(4352961343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4228443707/10000000000 : ℝ)|^8419 ≤ (32063713904199/100000000000000 : ℝ)^6371
        have hw : |(4228443707/10000000000 : ℝ)|=(4228443707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(896211277/2000000000 : ℝ)|^8419 ≤ (17309492878217/50000000000000 : ℝ)^6371
        have hw : |(896211277/2000000000 : ℝ)|=(896211277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s6_4 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-85093403/400000000 : ℝ)*x 0 + (2633556201/5000000000 : ℝ)*x 1 + (1347848183/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85093403/400000000 : ℝ)^8419 ≤ (12934936902721/100000000000000 : ℝ)^6371 := by
    have hnat : (85093403 : ℕ)^8419*100000000000000^6371 ≤ 12934936902721^6371*400000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85093403 400000000 12934936902721 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633556201/5000000000 : ℝ)^8419 ≤ (42861785315299/100000000000000 : ℝ)^6371 := by
    have hnat : (2633556201 : ℕ)^8419*100000000000000^6371 ≤ 42861785315299^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633556201 5000000000 42861785315299 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347848183/2500000000 : ℝ)^8419 ≤ (8840655554193/20000000000000 : ℝ)^6371 := by
    have hnat : (1347848183 : ℕ)^8419*20000000000000^6371 ≤ 8840655554193^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347848183 2500000000 8840655554193 20000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85093403/400000000 : ℝ), (2633556201/5000000000 : ℝ), (1347848183/2500000000 : ℝ)] ![(12934936902721/100000000000000 : ℝ), (42861785315299/100000000000000 : ℝ), (8840655554193/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85093403/400000000 : ℝ)|^8419 ≤ (12934936902721/100000000000000 : ℝ)^6371
        have hw : |(-85093403/400000000 : ℝ)|=(85093403/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633556201/5000000000 : ℝ)|^8419 ≤ (42861785315299/100000000000000 : ℝ)^6371
        have hw : |(2633556201/5000000000 : ℝ)|=(2633556201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347848183/2500000000 : ℝ)|^8419 ≤ (8840655554193/20000000000000 : ℝ)^6371
        have hw : |(1347848183/2500000000 : ℝ)|=(1347848183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s6_5 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328152251/2500000000 : ℝ)*x 0 + (-2066074901/10000000000 : ℝ)*x 1 + (539139279/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328152251/2500000000 : ℝ)^8419 ≤ (4335171177873/10000000000000 : ℝ)^6371 := by
    have hnat : (1328152251 : ℕ)^8419*10000000000000^6371 ≤ 4335171177873^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328152251 2500000000 4335171177873 10000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2066074901/10000000000 : ℝ)^8419 ≤ (6222504904617/50000000000000 : ℝ)^6371 := by
    have hnat : (2066074901 : ℕ)^8419*50000000000000^6371 ≤ 6222504904617^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066074901 10000000000 6222504904617 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539139279/1000000000 : ℝ)^8419 ≤ (44203278399363/100000000000000 : ℝ)^6371 := by
    have hnat : (539139279 : ℕ)^8419*100000000000000^6371 ≤ 44203278399363^6371*1000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539139279 1000000000 44203278399363 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328152251/2500000000 : ℝ), (-2066074901/10000000000 : ℝ), (539139279/1000000000 : ℝ)] ![(4335171177873/10000000000000 : ℝ), (6222504904617/50000000000000 : ℝ), (44203278399363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328152251/2500000000 : ℝ)|^8419 ≤ (4335171177873/10000000000000 : ℝ)^6371
        have hw : |(1328152251/2500000000 : ℝ)|=(1328152251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2066074901/10000000000 : ℝ)|^8419 ≤ (6222504904617/50000000000000 : ℝ)^6371
        have hw : |(-2066074901/10000000000 : ℝ)|=(2066074901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539139279/1000000000 : ℝ)|^8419 ≤ (44203278399363/100000000000000 : ℝ)^6371
        have hw : |(539139279/1000000000 : ℝ)|=(539139279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s6_6 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312608941/10000000000 : ℝ)*x 0 + (2695696411/5000000000 : ℝ)*x 1 + (-2066074943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312608941/10000000000 : ℝ)^8419 ≤ (21675855549691/50000000000000 : ℝ)^6371 := by
    have hnat : (5312608941 : ℕ)^8419*50000000000000^6371 ≤ 21675855549691^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312608941 10000000000 21675855549691 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695696411/5000000000 : ℝ)^8419 ≤ (8840655749213/20000000000000 : ℝ)^6371 := by
    have hnat : (2695696411 : ℕ)^8419*20000000000000^6371 ≤ 8840655749213^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695696411 5000000000 8840655749213 20000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066074943/10000000000 : ℝ)^8419 ≤ (6222505071773/50000000000000 : ℝ)^6371 := by
    have hnat : (2066074943 : ℕ)^8419*50000000000000^6371 ≤ 6222505071773^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066074943 10000000000 6222505071773 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312608941/10000000000 : ℝ), (2695696411/5000000000 : ℝ), (-2066074943/10000000000 : ℝ)] ![(21675855549691/50000000000000 : ℝ), (8840655749213/20000000000000 : ℝ), (6222505071773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312608941/10000000000 : ℝ)|^8419 ≤ (21675855549691/50000000000000 : ℝ)^6371
        have hw : |(5312608941/10000000000 : ℝ)|=(5312608941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695696411/5000000000 : ℝ)|^8419 ≤ (8840655749213/20000000000000 : ℝ)^6371
        have hw : |(2695696411/5000000000 : ℝ)|=(2695696411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2066074943/10000000000 : ℝ)|^8419 ≤ (6222505071773/50000000000000 : ℝ)^6371
        have hw : |(-2066074943/10000000000 : ℝ)|=(2066074943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s6_7 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (435297131/1000000000 : ℝ)*x 0 + (4480417431/10000000000 : ℝ)*x 1 + (21145423/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435297131/1000000000 : ℝ)^8419 ≤ (33317401130767/100000000000000 : ℝ)^6371 := by
    have hnat : (435297131 : ℕ)^8419*100000000000000^6371 ≤ 33317401130767^6371*1000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435297131 1000000000 33317401130767 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480417431/10000000000 : ℝ)^8419 ≤ (17306231384999/50000000000000 : ℝ)^6371 := by
    have hnat : (4480417431 : ℕ)^8419*50000000000000^6371 ≤ 17306231384999^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480417431 10000000000 17306231384999 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21145423/50000000 : ℝ)^8419 ≤ (16035068040693/50000000000000 : ℝ)^6371 := by
    have hnat : (21145423 : ℕ)^8419*50000000000000^6371 ≤ 16035068040693^6371*50000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21145423 50000000 16035068040693 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435297131/1000000000 : ℝ), (4480417431/10000000000 : ℝ), (21145423/50000000 : ℝ)] ![(33317401130767/100000000000000 : ℝ), (17306231384999/50000000000000 : ℝ), (16035068040693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435297131/1000000000 : ℝ)|^8419 ≤ (33317401130767/100000000000000 : ℝ)^6371
        have hw : |(435297131/1000000000 : ℝ)|=(435297131/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4480417431/10000000000 : ℝ)|^8419 ≤ (17306231384999/50000000000000 : ℝ)^6371
        have hw : |(4480417431/10000000000 : ℝ)|=(4480417431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21145423/50000000 : ℝ)|^8419 ≤ (16035068040693/50000000000000 : ℝ)^6371
        have hw : |(21145423/50000000 : ℝ)|=(21145423/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1226_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30223053/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3531/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11433/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2291/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14101/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3531/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11433/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3531/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11433/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3531/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11433/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3531/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11433/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3531/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11433/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3531/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11433/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11433/100000 : ℝ) ^ (4209/1024 : ℝ) ≤ (13449536590584217/100000000000000000000 : ℝ) := by
    have hpowers : (11433/100000 : ℝ)^4209 ≤ (13449536590584217/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11433 : ℕ)^4209*100000000000000000000^1024 ≤ 13449536590584217^1024*100000^4209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11433 100000 13449536590584217 100000000000000000000 4209 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11433/100000 : ℝ)) (X := (13449536590584217/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3531/25000 : ℝ) ^ (4209/1024 : ℝ) ≤ (16032355890748679/50000000000000000000 : ℝ) := by
    have hpowers : (3531/25000 : ℝ)^4209 ≤ (16032355890748679/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3531 : ℕ)^4209*50000000000000000000^1024 ≤ 16032355890748679^1024*25000^4209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3531 25000 16032355890748679 50000000000000000000 4209 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3531/25000 : ℝ)) (X := (16032355890748679/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013449536590584217/50000000000000000000 : ℝ) ≤ (5000327178047557/5000000000000000 : ℝ) ^ (4209/1024 : ℝ) := by
    have hpowers : (50013449536590584217/50000000000000000000 : ℝ)^1024 ≤ (5000327178047557/5000000000000000 : ℝ)^4209 := by
      have hnat : (50013449536590584217 : ℕ)^1024*5000000000000000^4209 ≤ 5000327178047557^4209*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013449536590584217 50000000000000000000 5000327178047557 5000000000000000 1024 4209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000327178047557/5000000000000000 : ℝ)) (X := (50013449536590584217/50000000000000000000 : ℝ)) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001820569934883263/4000000000000000000 : ℝ) ≤ (5000553558642719/5000000000000000 : ℝ) ^ (4209/1024 : ℝ) := by
    have hpowers : (4001820569934883263/4000000000000000000 : ℝ)^1024 ≤ (5000553558642719/5000000000000000 : ℝ)^4209 := by
      have hnat : (4001820569934883263 : ℕ)^1024*5000000000000000^4209 ≤ 5000553558642719^4209*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001820569934883263 4000000000000000000 5000553558642719 5000000000000000 1024 4209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000553558642719/5000000000000000 : ℝ)) (X := (4001820569934883263/4000000000000000000 : ℝ)) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016032355890748679/25000000000000000000 : ℝ) ≤ (5000779939237881/5000000000000000 : ℝ) ^ (4209/1024 : ℝ) := by
    have hpowers : (25016032355890748679/25000000000000000000 : ℝ)^1024 ≤ (5000779939237881/5000000000000000 : ℝ)^4209 := by
      have hnat : (25016032355890748679 : ℕ)^1024*5000000000000000^4209 ≤ 5000779939237881^4209*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016032355890748679 25000000000000000000 5000779939237881 5000000000000000 1024 4209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000779939237881/5000000000000000 : ℝ)) (X := (25016032355890748679/25000000000000000000 : ℝ)) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13449536590584217/100000000000000000000 : ℝ) ≤ ((896713601162466773/897000000000000000 : ℝ)+2*(113190297581/67275000000000 : ℝ)*(11433/100000 : ℝ))^(4209/1024 : ℝ) := by
    rw [show (896713601162466773/897000000000000000 : ℝ)+2*(113190297581/67275000000000 : ℝ)*(11433/100000 : ℝ)=(5000327178047557/5000000000000000 : ℝ) by norm_num, show 1+2*(13449536590584217/100000000000000000000 : ℝ)=(50013449536590584217/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16032355890748679/50000000000000000000 : ℝ)+(13449536590584217/100000000000000000000 : ℝ) ≤ ((896713601162466773/897000000000000000 : ℝ)+(113190297581/67275000000000 : ℝ)*((3531/25000 : ℝ)+(11433/100000 : ℝ)))^(4209/1024 : ℝ) := by
    rw [show (896713601162466773/897000000000000000 : ℝ)+(113190297581/67275000000000 : ℝ)*((3531/25000 : ℝ)+(11433/100000 : ℝ))=(5000553558642719/5000000000000000 : ℝ) by norm_num, show 1+(16032355890748679/50000000000000000000 : ℝ)+(13449536590584217/100000000000000000000 : ℝ)=(4001820569934883263/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16032355890748679/50000000000000000000 : ℝ) ≤ ((896713601162466773/897000000000000000 : ℝ)+2*(113190297581/67275000000000 : ℝ)*(3531/25000 : ℝ))^(4209/1024 : ℝ) := by
    rw [show (896713601162466773/897000000000000000 : ℝ)+2*(113190297581/67275000000000 : ℝ)*(3531/25000 : ℝ)=(5000779939237881/5000000000000000 : ℝ) by norm_num, show 1+2*(16032355890748679/50000000000000000000 : ℝ)=(25016032355890748679/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (896713601162466773/897000000000000000 : ℝ)*(X 1 0+X 2 0)+(113190297581/67275000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4209/1024 : ℝ)) (lo := (11433/100000 : ℝ)) (hi := (3531/25000 : ℝ)) (c := (896713601162466773/897000000000000000 : ℝ)) (alpha := (113190297581/67275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (896713601162466773/897000000000000000 : ℝ)*(X 0 1+X 2 1)+(113190297581/67275000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4209/1024 : ℝ)) (lo := (11433/100000 : ℝ)) (hi := (3531/25000 : ℝ)) (c := (896713601162466773/897000000000000000 : ℝ)) (alpha := (113190297581/67275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (896713601162466773/897000000000000000 : ℝ)*(X 0 2+X 1 2)+(113190297581/67275000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4209/1024 : ℝ)) (lo := (11433/100000 : ℝ)) (hi := (3531/25000 : ℝ)) (c := (896713601162466773/897000000000000000 : ℝ)) (alpha := (113190297581/67275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2127330163/10000000000 : ℝ)*X 0 0+(673963711/1250000000 : ℝ)*X 0 1+(210671869/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672223301/5000000000 : ℝ)*X 1 0+(-109533559/500000000 : ℝ)*X 1 1+(2633398223/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068889289/2000000000 : ℝ)*X 2 0+(1053359309/2000000000 : ℝ)*X 2 1+(-2190671257/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4352961343/10000000000 : ℝ)*X 0 0+(4228443707/10000000000 : ℝ)*X 0 1+(896211277/2000000000 : ℝ)*X 0 2+(4352961343/10000000000 : ℝ)*X 1 0+(4228443707/10000000000 : ℝ)*X 1 1+(896211277/2000000000 : ℝ)*X 1 2+(4352961343/10000000000 : ℝ)*X 2 0+(4228443707/10000000000 : ℝ)*X 2 1+(896211277/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-85093403/400000000 : ℝ)*X 0 0+(2633556201/5000000000 : ℝ)*X 0 1+(1347848183/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328152251/2500000000 : ℝ)*X 1 0+(-2066074901/10000000000 : ℝ)*X 1 1+(539139279/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312608941/10000000000 : ℝ)*X 2 0+(2695696411/5000000000 : ℝ)*X 2 1+(-2066074943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((435297131/1000000000 : ℝ)*X 0 0+(4480417431/10000000000 : ℝ)*X 0 1+(21145423/50000000 : ℝ)*X 0 2+(435297131/1000000000 : ℝ)*X 1 0+(4480417431/10000000000 : ℝ)*X 1 1+(21145423/50000000 : ℝ)*X 1 2+(435297131/1000000000 : ℝ)*X 2 0+(4480417431/10000000000 : ℝ)*X 2 1+(21145423/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27824105331423488741816457/7475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104840407/50000000000000 : ℝ)*(base19) + (461917/2500000000000 : ℝ)*(upper2) + (18303881/20000000000000 : ℝ)*(lower3) + (2807991/12500000000000 : ℝ)*(lower4) + (5982105852913509/100000000000000 : ℝ)*(major0) + (5982105852913509/100000000000000 : ℝ)*(major1) + (5982105852913509/100000000000000 : ℝ)*(major2) + (8005573880315657/100000000000000 : ℝ)*(sp0) + (8005571054995883/100000000000000 : ℝ)*(sp1) + (4002781342442661/50000000000000 : ℝ)*(sp2) + (3958635421353493/100000000000000 : ℝ)*(sp3) + (32695487/1250000000000 : ℝ)*(sp5) + (2239086067/20000000000000 : ℝ)*(sp6) + (2280081573/100000000000000 : ℝ)*(sp7) + (1979318850717533/50000000000000 : ℝ)*(f.failure) + (8005573880315657/100000000000000 : ℝ)*(f.sum) + (2840700616243/747500000000000000000000000 : ℝ)*base66 + (119201718268018819/29900000000000000000000000000000 : ℝ)*base67 + (1599602753791981181/29900000000000000000000000000000 : ℝ)*base70 + (111307087421481181/29900000000000000000000000000000 : ℝ)*base72 + (2115994115803/747500000000000000000000000 : ℝ)*base74 + (495165729892681181/29900000000000000000000000000000 : ℝ)*base76 + (61274523979581181/29900000000000000000000000000000 : ℝ)*base78 + (18514178767581181/29900000000000000000000000000000 : ℝ)*base80 + (54434869811027/747500000000000000000000000 : ℝ)*base81 + (2111751/1000000000000000000000 : ℝ)*base90 + (2111751/1000000000000000000000 : ℝ)*base92 + (2111751/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29955378595954166819/3450000000000000000000000 : ℝ) := by norm_num
    linear_combination (817593167/50000000000000 : ℝ)*(base19) + (819798047/50000000000000 : ℝ)*(base23) + (10543063/5000000000000 : ℝ)*(upper3) + (6543697/12500000000000 : ℝ)*(lower4) + (191702589/100000000000000 : ℝ)*(upper5) + (1202510946180401/20000000000000 : ℝ)*(major0) + (1202510946180401/20000000000000 : ℝ)*(major1) + (1202510946180401/20000000000000 : ℝ)*(major2) + (11826200971/25000000000000 : ℝ)*(sp1) + (2376004511/5000000000000 : ℝ)*(sp2) + (8046322032045813/100000000000000 : ℝ)*(sp4) + (2011568273013899/25000000000000 : ℝ)*(sp5) + (8046272872359499/100000000000000 : ℝ)*(sp6) + (3978787140334237/100000000000000 : ℝ)*(sp7) + (3978787140334237/100000000000000 : ℝ)*(f.failure) + (8046322032045813/100000000000000 : ℝ)*(f.sum) + (372433419317/207000000000000000000000000 : ℝ)*base66 + (36970202505486763/4140000000000000000000000000000 : ℝ)*base67 + (18110524134533237/4140000000000000000000000000000 : ℝ)*base70 + (69381309637373237/4140000000000000000000000000000 : ℝ)*base72 + (1795296137731/207000000000000000000000000 : ℝ)*base73 + (5766851395146763/4140000000000000000000000000000 : ℝ)*base75 + (45654552347646763/4140000000000000000000000000000 : ℝ)*base77 + (49191201157793237/4140000000000000000000000000000 : ℝ)*base80 + (767132865173/207000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (17434439/2000000000000000000000 : ℝ)*base90 + (17434439/2000000000000000000000 : ℝ)*base92 + (17434439/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1226_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30223053/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3531/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11433/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2291/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1226_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1226_s7_0 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-106367423/500000000 : ℝ)*x 0 + (5391495381/10000000000 : ℝ)*x 1 + (5266998979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106367423/500000000 : ℝ)^8419 ≤ (517401778007/4000000000000 : ℝ)^6371 := by
    have hnat : (106367423 : ℕ)^8419*4000000000000^6371 ≤ 517401778007^6371*500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106367423 500000000 517401778007 4000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391495381/10000000000 : ℝ)^8419 ≤ (44204389918649/100000000000000 : ℝ)^6371 := by
    have hnat : (5391495381 : ℕ)^8419*100000000000000^6371 ≤ 44204389918649^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391495381 10000000000 44204389918649 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266998979/10000000000 : ℝ)^8419 ≤ (21430282811613/50000000000000 : ℝ)^6371 := by
    have hnat : (5266998979 : ℕ)^8419*50000000000000^6371 ≤ 21430282811613^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266998979 10000000000 21430282811613 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106367423/500000000 : ℝ), (5391495381/10000000000 : ℝ), (5266998979/10000000000 : ℝ)] ![(517401778007/4000000000000 : ℝ), (44204389918649/100000000000000 : ℝ), (21430282811613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106367423/500000000 : ℝ)|^8419 ≤ (517401778007/4000000000000 : ℝ)^6371
        have hw : |(-106367423/500000000 : ℝ)|=(106367423/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391495381/10000000000 : ℝ)|^8419 ≤ (44204389918649/100000000000000 : ℝ)^6371
        have hw : |(5391495381/10000000000 : ℝ)|=(5391495381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266998979/10000000000 : ℝ)|^8419 ≤ (21430282811613/50000000000000 : ℝ)^6371
        have hw : |(5266998979/10000000000 : ℝ)|=(5266998979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s7_1 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068878433/2000000000 : ℝ)*x 0 + (-2190475077/10000000000 : ℝ)*x 1 + (5266999053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068878433/2000000000 : ℝ)^8419 ≤ (5461845993163/12500000000000 : ℝ)^6371 := by
    have hnat : (1068878433 : ℕ)^8419*12500000000000^6371 ≤ 5461845993163^6371*2000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068878433 2000000000 5461845993163 12500000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2190475077/10000000000 : ℝ)^8419 ≤ (537786624677/4000000000000 : ℝ)^6371 := by
    have hnat : (2190475077 : ℕ)^8419*4000000000000^6371 ≤ 537786624677^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190475077 10000000000 537786624677 4000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266999053/10000000000 : ℝ)^8419 ≤ (42860566418981/100000000000000 : ℝ)^6371 := by
    have hnat : (5266999053 : ℕ)^8419*100000000000000^6371 ≤ 42860566418981^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266999053 10000000000 42860566418981 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068878433/2000000000 : ℝ), (-2190475077/10000000000 : ℝ), (5266999053/10000000000 : ℝ)] ![(5461845993163/12500000000000 : ℝ), (537786624677/4000000000000 : ℝ), (42860566418981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068878433/2000000000 : ℝ)|^8419 ≤ (5461845993163/12500000000000 : ℝ)^6371
        have hw : |(1068878433/2000000000 : ℝ)|=(1068878433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2190475077/10000000000 : ℝ)|^8419 ≤ (537786624677/4000000000000 : ℝ)^6371
        have hw : |(-2190475077/10000000000 : ℝ)|=(2190475077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266999053/10000000000 : ℝ)|^8419 ≤ (42860566418981/100000000000000 : ℝ)^6371
        have hw : |(5266999053/10000000000 : ℝ)|=(5266999053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s7_2 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344392143/10000000000 : ℝ)*x 0 + (658374879/1250000000 : ℝ)*x 1 + (-438095027/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344392143/10000000000 : ℝ)^8419 ≤ (1365461490863/3125000000000 : ℝ)^6371 := by
    have hnat : (5344392143 : ℕ)^8419*3125000000000^6371 ≤ 1365461490863^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344392143 10000000000 1365461490863 3125000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658374879/1250000000 : ℝ)^8419 ≤ (21430283096579/50000000000000 : ℝ)^6371 := by
    have hnat : (658374879 : ℕ)^8419*50000000000000^6371 ≤ 21430283096579^6371*1250000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658374879 1250000000 21430283096579 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (438095027/2000000000 : ℝ)^8419 ≤ (1680583260919/12500000000000 : ℝ)^6371 := by
    have hnat : (438095027 : ℕ)^8419*12500000000000^6371 ≤ 1680583260919^6371*2000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438095027 2000000000 1680583260919 12500000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344392143/10000000000 : ℝ), (658374879/1250000000 : ℝ), (-438095027/2000000000 : ℝ)] ![(1365461490863/3125000000000 : ℝ), (21430283096579/50000000000000 : ℝ), (1680583260919/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344392143/10000000000 : ℝ)|^8419 ≤ (1365461490863/3125000000000 : ℝ)^6371
        have hw : |(5344392143/10000000000 : ℝ)|=(5344392143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658374879/1250000000 : ℝ)|^8419 ≤ (21430283096579/50000000000000 : ℝ)^6371
        have hw : |(658374879/1250000000 : ℝ)|=(658374879/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-438095027/2000000000 : ℝ)|^8419 ≤ (1680583260919/12500000000000 : ℝ)^6371
        have hw : |(-438095027/2000000000 : ℝ)|=(438095027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s7_3 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4352972427/10000000000 : ℝ)*x 0 + (4228863231/10000000000 : ℝ)*x 1 + (224031681/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352972427/10000000000 : ℝ)^8419 ≤ (16658706214251/50000000000000 : ℝ)^6371 := by
    have hnat : (4352972427 : ℕ)^8419*50000000000000^6371 ≤ 16658706214251^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352972427 10000000000 16658706214251 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4228863231/10000000000 : ℝ)^8419 ≤ (32067917780343/100000000000000 : ℝ)^6371 := by
    have hnat : (4228863231 : ℕ)^8419*100000000000000^6371 ≤ 32067917780343^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228863231 10000000000 32067917780343 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224031681/500000000 : ℝ)^8419 ≤ (34614669777903/100000000000000 : ℝ)^6371 := by
    have hnat : (224031681 : ℕ)^8419*100000000000000^6371 ≤ 34614669777903^6371*500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224031681 500000000 34614669777903 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352972427/10000000000 : ℝ), (4228863231/10000000000 : ℝ), (224031681/500000000 : ℝ)] ![(16658706214251/50000000000000 : ℝ), (32067917780343/100000000000000 : ℝ), (34614669777903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352972427/10000000000 : ℝ)|^8419 ≤ (16658706214251/50000000000000 : ℝ)^6371
        have hw : |(4352972427/10000000000 : ℝ)|=(4352972427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4228863231/10000000000 : ℝ)|^8419 ≤ (32067917780343/100000000000000 : ℝ)^6371
        have hw : |(4228863231/10000000000 : ℝ)|=(4228863231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224031681/500000000 : ℝ)|^8419 ≤ (34614669777903/100000000000000 : ℝ)^6371
        have hw : |(224031681/500000000 : ℝ)|=(224031681/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s7_4 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-425470647/2000000000 : ℝ)*x 0 + (5267312647/10000000000 : ℝ)*x 1 + (5391180513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425470647/2000000000 : ℝ)^8419 ≤ (3233770704247/25000000000000 : ℝ)^6371 := by
    have hnat : (425470647 : ℕ)^8419*25000000000000^6371 ≤ 3233770704247^6371*2000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425470647 2000000000 3233770704247 25000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267312647/10000000000 : ℝ)^8419 ≤ (4286393866671/10000000000000 : ℝ)^6371 := by
    have hnat : (5267312647 : ℕ)^8419*10000000000000^6371 ≤ 4286393866671^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267312647 10000000000 4286393866671 10000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391180513/10000000000 : ℝ)^8419 ≤ (44200978511801/100000000000000 : ℝ)^6371 := by
    have hnat : (5391180513 : ℕ)^8419*100000000000000^6371 ≤ 44200978511801^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391180513 10000000000 44200978511801 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-425470647/2000000000 : ℝ), (5267312647/10000000000 : ℝ), (5391180513/10000000000 : ℝ)] ![(3233770704247/25000000000000 : ℝ), (4286393866671/10000000000000 : ℝ), (44200978511801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-425470647/2000000000 : ℝ)|^8419 ≤ (3233770704247/25000000000000 : ℝ)^6371
        have hw : |(-425470647/2000000000 : ℝ)|=(425470647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267312647/10000000000 : ℝ)|^8419 ≤ (4286393866671/10000000000000 : ℝ)^6371
        have hw : |(5267312647/10000000000 : ℝ)|=(5267312647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391180513/10000000000 : ℝ)|^8419 ≤ (44200978511801/100000000000000 : ℝ)^6371
        have hw : |(5391180513/10000000000 : ℝ)|=(5391180513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s7_5 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312660881/10000000000 : ℝ)*x 0 + (-413258713/2000000000 : ℝ)*x 1 + (5391180507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312660881/10000000000 : ℝ)^8419 ≤ (43352271184363/100000000000000 : ℝ)^6371 := by
    have hnat : (5312660881 : ℕ)^8419*100000000000000^6371 ≤ 43352271184363^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312660881 10000000000 43352271184363 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (413258713/2000000000 : ℝ)^8419 ≤ (12446750360269/100000000000000 : ℝ)^6371 := by
    have hnat : (413258713 : ℕ)^8419*100000000000000^6371 ≤ 12446750360269^6371*2000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413258713 2000000000 12446750360269 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391180507/10000000000 : ℝ)^8419 ≤ (8840195689359/20000000000000 : ℝ)^6371 := by
    have hnat : (5391180507 : ℕ)^8419*20000000000000^6371 ≤ 8840195689359^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391180507 10000000000 8840195689359 20000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312660881/10000000000 : ℝ), (-413258713/2000000000 : ℝ), (5391180507/10000000000 : ℝ)] ![(43352271184363/100000000000000 : ℝ), (12446750360269/100000000000000 : ℝ), (8840195689359/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312660881/10000000000 : ℝ)|^8419 ≤ (43352271184363/100000000000000 : ℝ)^6371
        have hw : |(5312660881/10000000000 : ℝ)|=(5312660881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-413258713/2000000000 : ℝ)|^8419 ≤ (12446750360269/100000000000000 : ℝ)^6371
        have hw : |(-413258713/2000000000 : ℝ)|=(413258713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391180507/10000000000 : ℝ)|^8419 ≤ (8840195689359/20000000000000 : ℝ)^6371
        have hw : |(5391180507/10000000000 : ℝ)|=(5391180507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s7_6 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664082609/1250000000 : ℝ)*x 0 + (5391180527/10000000000 : ℝ)*x 1 + (-41325871/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664082609/1250000000 : ℝ)^8419 ≤ (21676135543657/50000000000000 : ℝ)^6371 := by
    have hnat : (664082609 : ℕ)^8419*50000000000000^6371 ≤ 21676135543657^6371*1250000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664082609 1250000000 21676135543657 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391180527/10000000000 : ℝ)^8419 ≤ (44200978663481/100000000000000 : ℝ)^6371 := by
    have hnat : (5391180527 : ℕ)^8419*100000000000000^6371 ≤ 44200978663481^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391180527 10000000000 44200978663481 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41325871/200000000 : ℝ)^8419 ≤ (3111687560217/25000000000000 : ℝ)^6371 := by
    have hnat : (41325871 : ℕ)^8419*25000000000000^6371 ≤ 3111687560217^6371*200000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41325871 200000000 3111687560217 25000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664082609/1250000000 : ℝ), (5391180527/10000000000 : ℝ), (-41325871/200000000 : ℝ)] ![(21676135543657/50000000000000 : ℝ), (44200978663481/100000000000000 : ℝ), (3111687560217/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664082609/1250000000 : ℝ)|^8419 ≤ (21676135543657/50000000000000 : ℝ)^6371
        have hw : |(664082609/1250000000 : ℝ)|=(664082609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391180527/10000000000 : ℝ)|^8419 ≤ (44200978663481/100000000000000 : ℝ)^6371
        have hw : |(5391180527/10000000000 : ℝ)|=(5391180527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41325871/200000000 : ℝ)|^8419 ≤ (3111687560217/25000000000000 : ℝ)^6371
        have hw : |(-41325871/200000000 : ℝ)|=(41325871/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s7_7 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4352981709/10000000000 : ℝ)*x 0 + (1119999747/2500000000 : ℝ)*x 1 + (1057375093/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352981709/10000000000 : ℝ)^8419 ≤ (33317506309991/100000000000000 : ℝ)^6371 := by
    have hnat : (4352981709 : ℕ)^8419*100000000000000^6371 ≤ 33317506309991^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352981709 10000000000 33317506309991 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119999747/2500000000 : ℝ)^8419 ≤ (34608191109629/100000000000000 : ℝ)^6371 := by
    have hnat : (1119999747 : ℕ)^8419*100000000000000^6371 ≤ 34608191109629^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119999747 2500000000 34608191109629 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057375093/2500000000 : ℝ)^8419 ≤ (8018575640667/25000000000000 : ℝ)^6371 := by
    have hnat : (1057375093 : ℕ)^8419*25000000000000^6371 ≤ 8018575640667^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057375093 2500000000 8018575640667 25000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352981709/10000000000 : ℝ), (1119999747/2500000000 : ℝ), (1057375093/2500000000 : ℝ)] ![(33317506309991/100000000000000 : ℝ), (34608191109629/100000000000000 : ℝ), (8018575640667/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352981709/10000000000 : ℝ)|^8419 ≤ (33317506309991/100000000000000 : ℝ)^6371
        have hw : |(4352981709/10000000000 : ℝ)|=(4352981709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1119999747/2500000000 : ℝ)|^8419 ≤ (34608191109629/100000000000000 : ℝ)^6371
        have hw : |(1119999747/2500000000 : ℝ)|=(1119999747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1057375093/2500000000 : ℝ)|^8419 ≤ (8018575640667/25000000000000 : ℝ)^6371
        have hw : |(1057375093/2500000000 : ℝ)|=(1057375093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1226_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30223053/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2291/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11459/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (881/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14101/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2291/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14101/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2291/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14101/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2291/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14101/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2291/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14101/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2291/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14101/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2291/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2291/20000 : ℝ) ^ (4209/1024 : ℝ) ≤ (135562326133849/1000000000000000000 : ℝ) := by
    have hpowers : (2291/20000 : ℝ)^4209 ≤ (135562326133849/1000000000000000000 : ℝ)^1024 := by
      have hnat : (2291 : ℕ)^4209*1000000000000000000^1024 ≤ 135562326133849^1024*20000^4209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2291 20000 135562326133849 1000000000000000000 4209 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2291/20000 : ℝ)) (X := (135562326133849/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14101/100000 : ℝ) ^ (4209/1024 : ℝ) ≤ (31850631605513833/100000000000000000000 : ℝ) := by
    have hpowers : (14101/100000 : ℝ)^4209 ≤ (31850631605513833/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14101 : ℕ)^4209*100000000000000000000^1024 ≤ 31850631605513833^1024*100000^4209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14101 100000 31850631605513833 100000000000000000000 4209 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14101/100000 : ℝ)) (X := (31850631605513833/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (500135562326133849/500000000000000000 : ℝ) ≤ (2500164886652733/2500000000000000 : ℝ) ^ (4209/1024 : ℝ) := by
    have hpowers : (500135562326133849/500000000000000000 : ℝ)^1024 ≤ (2500164886652733/2500000000000000 : ℝ)^4209 := by
      have hnat : (500135562326133849 : ℕ)^1024*2500000000000000^4209 ≤ 2500164886652733^4209*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500135562326133849 500000000000000000 2500164886652733 2500000000000000 1024 4209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500164886652733/2500000000000000 : ℝ)) (X := (500135562326133849/500000000000000000 : ℝ)) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045406864218898733/100000000000000000000 : ℝ) ≤ (10001104505654157/10000000000000000 : ℝ) ^ (4209/1024 : ℝ) := by
    have hpowers : (100045406864218898733/100000000000000000000 : ℝ)^1024 ≤ (10001104505654157/10000000000000000 : ℝ)^4209 := by
      have hnat : (100045406864218898733 : ℕ)^1024*10000000000000000^4209 ≤ 10001104505654157^4209*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045406864218898733 100000000000000000000 10001104505654157 10000000000000000 1024 4209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001104505654157/10000000000000000 : ℝ)) (X := (100045406864218898733/100000000000000000000 : ℝ)) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031850631605513833/50000000000000000000 : ℝ) ≤ (5000774732348691/5000000000000000 : ℝ) ^ (4209/1024 : ℝ) := by
    have hpowers : (50031850631605513833/50000000000000000000 : ℝ)^1024 ≤ (5000774732348691/5000000000000000 : ℝ)^4209 := by
      have hnat : (50031850631605513833 : ℕ)^1024*5000000000000000^4209 ≤ 5000774732348691^4209*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031850631605513833 50000000000000000000 5000774732348691 5000000000000000 1024 4209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000774732348691/5000000000000000 : ℝ)) (X := (50031850631605513833/50000000000000000000 : ℝ)) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(135562326133849/1000000000000000000 : ℝ) ≤ ((4408591858108706887/4410000000000000000 : ℝ)+2*(5932787243/3528000000000 : ℝ)*(2291/20000 : ℝ))^(4209/1024 : ℝ) := by
    rw [show (4408591858108706887/4410000000000000000 : ℝ)+2*(5932787243/3528000000000 : ℝ)*(2291/20000 : ℝ)=(2500164886652733/2500000000000000 : ℝ) by norm_num, show 1+2*(135562326133849/1000000000000000000 : ℝ)=(500135562326133849/500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31850631605513833/100000000000000000000 : ℝ)+(135562326133849/1000000000000000000 : ℝ) ≤ ((4408591858108706887/4410000000000000000 : ℝ)+(5932787243/3528000000000 : ℝ)*((14101/100000 : ℝ)+(2291/20000 : ℝ)))^(4209/1024 : ℝ) := by
    rw [show (4408591858108706887/4410000000000000000 : ℝ)+(5932787243/3528000000000 : ℝ)*((14101/100000 : ℝ)+(2291/20000 : ℝ))=(10001104505654157/10000000000000000 : ℝ) by norm_num, show 1+(31850631605513833/100000000000000000000 : ℝ)+(135562326133849/1000000000000000000 : ℝ)=(100045406864218898733/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31850631605513833/100000000000000000000 : ℝ) ≤ ((4408591858108706887/4410000000000000000 : ℝ)+2*(5932787243/3528000000000 : ℝ)*(14101/100000 : ℝ))^(4209/1024 : ℝ) := by
    rw [show (4408591858108706887/4410000000000000000 : ℝ)+2*(5932787243/3528000000000 : ℝ)*(14101/100000 : ℝ)=(5000774732348691/5000000000000000 : ℝ) by norm_num, show 1+2*(31850631605513833/100000000000000000000 : ℝ)=(50031850631605513833/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4408591858108706887/4410000000000000000 : ℝ)*(X 1 0+X 2 0)+(5932787243/3528000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4209/1024 : ℝ)) (lo := (2291/20000 : ℝ)) (hi := (14101/100000 : ℝ)) (c := (4408591858108706887/4410000000000000000 : ℝ)) (alpha := (5932787243/3528000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4408591858108706887/4410000000000000000 : ℝ)*(X 0 1+X 2 1)+(5932787243/3528000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4209/1024 : ℝ)) (lo := (2291/20000 : ℝ)) (hi := (14101/100000 : ℝ)) (c := (4408591858108706887/4410000000000000000 : ℝ)) (alpha := (5932787243/3528000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4408591858108706887/4410000000000000000 : ℝ)*(X 0 2+X 1 2)+(5932787243/3528000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4209/1024 : ℝ)) (lo := (2291/20000 : ℝ)) (hi := (14101/100000 : ℝ)) (c := (4408591858108706887/4410000000000000000 : ℝ)) (alpha := (5932787243/3528000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-106367423/500000000 : ℝ)*X 0 0+(5391495381/10000000000 : ℝ)*X 0 1+(5266998979/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068878433/2000000000 : ℝ)*X 1 0+(-2190475077/10000000000 : ℝ)*X 1 1+(5266999053/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344392143/10000000000 : ℝ)*X 2 0+(658374879/1250000000 : ℝ)*X 2 1+(-438095027/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4352972427/10000000000 : ℝ)*X 0 0+(4228863231/10000000000 : ℝ)*X 0 1+(224031681/500000000 : ℝ)*X 0 2+(4352972427/10000000000 : ℝ)*X 1 0+(4228863231/10000000000 : ℝ)*X 1 1+(224031681/500000000 : ℝ)*X 1 2+(4352972427/10000000000 : ℝ)*X 2 0+(4228863231/10000000000 : ℝ)*X 2 1+(224031681/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-425470647/2000000000 : ℝ)*X 0 0+(5267312647/10000000000 : ℝ)*X 0 1+(5391180513/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312660881/10000000000 : ℝ)*X 1 0+(-413258713/2000000000 : ℝ)*X 1 1+(5391180507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664082609/1250000000 : ℝ)*X 2 0+(5391180527/10000000000 : ℝ)*X 2 1+(-41325871/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4352981709/10000000000 : ℝ)*X 0 0+(1119999747/2500000000 : ℝ)*X 0 1+(1057375093/2500000000 : ℝ)*X 0 2+(4352981709/10000000000 : ℝ)*X 1 0+(1119999747/2500000000 : ℝ)*X 1 1+(1057375093/2500000000 : ℝ)*X 1 2+(4352981709/10000000000 : ℝ)*X 2 0+(1119999747/2500000000 : ℝ)*X 2 1+(1057375093/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (147780343434652112665260251/24500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (466612569/50000000000000 : ℝ)*(base19) + (139293117/20000000000000 : ℝ)*(base23) + (19354923/12500000000000 : ℝ)*(lower2) + (3909129/1562500000000 : ℝ)*(upper3) + (45977097/100000000000000 : ℝ)*(lower4) + (6002159525622573/100000000000000 : ℝ)*(major0) + (6002159525622573/100000000000000 : ℝ)*(major1) + (6002159525622573/100000000000000 : ℝ)*(major2) + (8032390492307667/100000000000000 : ℝ)*(sp0) + (4016204883746009/50000000000000 : ℝ)*(sp1) + (8032410004251571/100000000000000 : ℝ)*(sp2) + (1985943744402019/50000000000000 : ℝ)*(sp3) + (20208409489/100000000000000 : ℝ)*(sp4) + (2582582781/12500000000000 : ℝ)*(sp7) + (794381629893257/20000000000000 : ℝ)*(f.failure) + (2008102675179289/25000000000000 : ℝ)*(f.sum) + (2103542584103/294000000000000000000000000 : ℝ)*base65 + (1634844085548496583/147000000000000000000000000000000 : ℝ)*base68 + (1942037093586496583/147000000000000000000000000000000 : ℝ)*base70 + (894801355800496583/147000000000000000000000000000000 : ℝ)*base72 + (1002068819239/294000000000000000000000000 : ℝ)*base74 + (2489920661874496583/147000000000000000000000000000000 : ℝ)*base76 + (2357240805201496583/147000000000000000000000000000000 : ℝ)*base78 + (3180635192562496583/147000000000000000000000000000000 : ℝ)*base80 + (2968878931849/294000000000000000000000000 : ℝ)*base82 + (1346379/400000000000000000000 : ℝ)*base90 + (1346379/400000000000000000000 : ℝ)*base92 + (1346379/400000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (99608429473978348669/24500000000000000000000000 : ℝ) := by norm_num
    linear_combination (127370447/20000000000000 : ℝ)*(base19) + (177538919/25000000000000 : ℝ)*(base23) + (70526033/100000000000000 : ℝ)*(upper3) + (9540089/25000000000000 : ℝ)*(lower4) + (40975743/50000000000000 : ℝ)*(upper5) + (75407223667357/1250000000000 : ℝ)*(major0) + (75407223667357/1250000000000 : ℝ)*(major1) + (75407223667357/1250000000000 : ℝ)*(major2) + (878326779/5000000000000 : ℝ)*(sp1) + (10051591791/50000000000000 : ℝ)*(sp2) + (4036559126461699/50000000000000 : ℝ)*(sp4) + (8073100049535583/100000000000000 : ℝ)*(sp5) + (8073097439584139/100000000000000 : ℝ)*(sp6) + (1996018699166017/50000000000000 : ℝ)*(sp7) + (1996018699166017/50000000000000 : ℝ)*(f.failure) + (4036559126461699/50000000000000 : ℝ)*(f.sum) + (156926043949/27562500000000000000000000 : ℝ)*base65 + (75288251698487341/5512500000000000000000000000000 : ℝ)*base68 + (30171585772962659/5512500000000000000000000000000 : ℝ)*base69 + (34984739114375159/5512500000000000000000000000000 : ℝ)*base71 + (2764592375383/441000000000000000000000000 : ℝ)*base73 + (108985650824874841/5512500000000000000000000000000 : ℝ)*base76 + (21116778822512341/5512500000000000000000000000000 : ℝ)*base78 + (53376037518875159/5512500000000000000000000000000 : ℝ)*base79 + (1068152258563/110250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (12410099/1000000000000000000000 : ℝ)*base90 + (12410099/1000000000000000000000 : ℝ)*base92 + (12410099/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1226_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30223053/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2291/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11459/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (881/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1226_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1226_s8_0 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-425470917/2000000000 : ℝ)*x 0 + (1078290341/2000000000 : ℝ)*x 1 + (5267038407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425470917/2000000000 : ℝ)^8419 ≤ (2587018732831/20000000000000 : ℝ)^6371 := by
    have hnat : (425470917 : ℕ)^8419*20000000000000^6371 ≤ 2587018732831^6371*2000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425470917 2000000000 2587018732831 20000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078290341/2000000000 : ℝ)^8419 ≤ (5525489588929/12500000000000 : ℝ)^6371 := by
    have hnat : (1078290341 : ℕ)^8419*12500000000000^6371 ≤ 5525489588929^6371*2000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078290341 2000000000 5525489588929 12500000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267038407/10000000000 : ℝ)^8419 ≤ (42860989610517/100000000000000 : ℝ)^6371 := by
    have hnat : (5267038407 : ℕ)^8419*100000000000000^6371 ≤ 42860989610517^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267038407 10000000000 42860989610517 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-425470917/2000000000 : ℝ), (1078290341/2000000000 : ℝ), (5267038407/10000000000 : ℝ)] ![(2587018732831/20000000000000 : ℝ), (5525489588929/12500000000000 : ℝ), (42860989610517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-425470917/2000000000 : ℝ)|^8419 ≤ (2587018732831/20000000000000 : ℝ)^6371
        have hw : |(-425470917/2000000000 : ℝ)|=(425470917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078290341/2000000000 : ℝ)|^8419 ≤ (5525489588929/12500000000000 : ℝ)^6371
        have hw : |(1078290341/2000000000 : ℝ)|=(1078290341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267038407/10000000000 : ℝ)|^8419 ≤ (42860989610517/100000000000000 : ℝ)^6371
        have hw : |(5267038407/10000000000 : ℝ)|=(5267038407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s8_1 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344380541/10000000000 : ℝ)*x 0 + (-27380481/125000000 : ℝ)*x 1 + (1053407667/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344380541/10000000000 : ℝ)^8419 ≤ (10923660589953/25000000000000 : ℝ)^6371 := by
    have hnat : (5344380541 : ℕ)^8419*25000000000000^6371 ≤ 10923660589953^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344380541 10000000000 10923660589953 25000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27380481/125000000 : ℝ)^8419 ≤ (6722184393079/50000000000000 : ℝ)^6371 := by
    have hnat : (27380481 : ℕ)^8419*50000000000000^6371 ≤ 6722184393079^6371*125000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27380481 125000000 6722184393079 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053407667/2000000000 : ℝ)^8419 ≤ (42860988836267/100000000000000 : ℝ)^6371 := by
    have hnat : (1053407667 : ℕ)^8419*100000000000000^6371 ≤ 42860988836267^6371*2000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053407667 2000000000 42860988836267 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344380541/10000000000 : ℝ), (-27380481/125000000 : ℝ), (1053407667/2000000000 : ℝ)] ![(10923660589953/25000000000000 : ℝ), (6722184393079/50000000000000 : ℝ), (42860988836267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344380541/10000000000 : ℝ)|^8419 ≤ (10923660589953/25000000000000 : ℝ)^6371
        have hw : |(5344380541/10000000000 : ℝ)|=(5344380541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27380481/125000000 : ℝ)|^8419 ≤ (6722184393079/50000000000000 : ℝ)^6371
        have hw : |(-27380481/125000000 : ℝ)|=(27380481/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053407667/2000000000 : ℝ)|^8419 ≤ (42860988836267/100000000000000 : ℝ)^6371
        have hw : |(1053407667/2000000000 : ℝ)|=(1053407667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s8_2 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344380497/10000000000 : ℝ)*x 0 + (2633519191/5000000000 : ℝ)*x 1 + (-2190438477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344380497/10000000000 : ℝ)^8419 ≤ (43694641884437/100000000000000 : ℝ)^6371 := by
    have hnat : (5344380497 : ℕ)^8419*100000000000000^6371 ≤ 43694641884437^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344380497 10000000000 43694641884437 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633519191/5000000000 : ℝ)^8419 ≤ (535762366771/1250000000000 : ℝ)^6371 := by
    have hnat : (2633519191 : ℕ)^8419*1250000000000^6371 ≤ 535762366771^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633519191 5000000000 535762366771 1250000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190438477/10000000000 : ℝ)^8419 ≤ (6722184380913/50000000000000 : ℝ)^6371 := by
    have hnat : (2190438477 : ℕ)^8419*50000000000000^6371 ≤ 6722184380913^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190438477 10000000000 6722184380913 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344380497/10000000000 : ℝ), (2633519191/5000000000 : ℝ), (-2190438477/10000000000 : ℝ)] ![(43694641884437/100000000000000 : ℝ), (535762366771/1250000000000 : ℝ), (6722184380913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344380497/10000000000 : ℝ)|^8419 ≤ (43694641884437/100000000000000 : ℝ)^6371
        have hw : |(5344380497/10000000000 : ℝ)|=(5344380497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633519191/5000000000 : ℝ)|^8419 ≤ (535762366771/1250000000000 : ℝ)^6371
        have hw : |(2633519191/5000000000 : ℝ)|=(2633519191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2190438477/10000000000 : ℝ)|^8419 ≤ (6722184380913/50000000000000 : ℝ)^6371
        have hw : |(-2190438477/10000000000 : ℝ)|=(2190438477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s8_3 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (108824357/250000000 : ℝ)*x 0 + (4228947367/10000000000 : ℝ)*x 1 + (4480549197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108824357/250000000 : ℝ)^8419 ≤ (16658715585203/50000000000000 : ℝ)^6371 := by
    have hnat : (108824357 : ℕ)^8419*50000000000000^6371 ≤ 16658715585203^6371*250000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108824357 250000000 16658715585203 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4228947367/10000000000 : ℝ)^8419 ≤ (3206876088847/10000000000000 : ℝ)^6371 := by
    have hnat : (4228947367 : ℕ)^8419*10000000000000^6371 ≤ 3206876088847^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228947367 10000000000 3206876088847 10000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4480549197/10000000000 : ℝ)^8419 ≤ (17306903962519/50000000000000 : ℝ)^6371 := by
    have hnat : (4480549197 : ℕ)^8419*50000000000000^6371 ≤ 17306903962519^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480549197 10000000000 17306903962519 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108824357/250000000 : ℝ), (4228947367/10000000000 : ℝ), (4480549197/10000000000 : ℝ)] ![(16658715585203/50000000000000 : ℝ), (3206876088847/10000000000000 : ℝ), (17306903962519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108824357/250000000 : ℝ)|^8419 ≤ (16658715585203/50000000000000 : ℝ)^6371
        have hw : |(108824357/250000000 : ℝ)|=(108824357/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4228947367/10000000000 : ℝ)|^8419 ≤ (3206876088847/10000000000000 : ℝ)^6371
        have hw : |(4228947367/10000000000 : ℝ)|=(4228947367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4480549197/10000000000 : ℝ)|^8419 ≤ (17306903962519/50000000000000 : ℝ)^6371
        have hw : |(4480549197/10000000000 : ℝ)|=(4480549197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s8_4 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1063679647/5000000000 : ℝ)*x 0 + (1316837927/2500000000 : ℝ)*x 1 + (5391137249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063679647/5000000000 : ℝ)^8419 ≤ (6467565750349/50000000000000 : ℝ)^6371 := by
    have hnat : (1063679647 : ℕ)^8419*50000000000000^6371 ≤ 6467565750349^6371*5000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063679647 5000000000 6467565750349 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316837927/2500000000 : ℝ)^8419 ≤ (42864358715519/100000000000000 : ℝ)^6371 := by
    have hnat : (1316837927 : ℕ)^8419*100000000000000^6371 ≤ 42864358715519^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316837927 2500000000 42864358715519 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391137249/10000000000 : ℝ)^8419 ≤ (11050127444297/25000000000000 : ℝ)^6371 := by
    have hnat : (5391137249 : ℕ)^8419*25000000000000^6371 ≤ 11050127444297^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391137249 10000000000 11050127444297 25000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1063679647/5000000000 : ℝ), (1316837927/2500000000 : ℝ), (5391137249/10000000000 : ℝ)] ![(6467565750349/50000000000000 : ℝ), (42864358715519/100000000000000 : ℝ), (11050127444297/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1063679647/5000000000 : ℝ)|^8419 ≤ (6467565750349/50000000000000 : ℝ)^6371
        have hw : |(-1063679647/5000000000 : ℝ)|=(1063679647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316837927/2500000000 : ℝ)|^8419 ≤ (42864358715519/100000000000000 : ℝ)^6371
        have hw : |(1316837927/2500000000 : ℝ)|=(1316837927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391137249/10000000000 : ℝ)|^8419 ≤ (11050127444297/25000000000000 : ℝ)^6371
        have hw : |(5391137249/10000000000 : ℝ)|=(5391137249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s8_5 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328167591/2500000000 : ℝ)*x 0 + (-413267919/2000000000 : ℝ)*x 1 + (168473039/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328167591/2500000000 : ℝ)^8419 ≤ (43352373442657/100000000000000 : ℝ)^6371 := by
    have hnat : (1328167591 : ℕ)^8419*100000000000000^6371 ≤ 43352373442657^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328167591 2500000000 43352373442657 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (413267919/2000000000 : ℝ)^8419 ≤ (622355838179/5000000000000 : ℝ)^6371 := by
    have hnat : (413267919 : ℕ)^8419*5000000000000^6371 ≤ 622355838179^6371*2000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413267919 2000000000 622355838179 5000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168473039/312500000 : ℝ)^8419 ≤ (22100254883177/50000000000000 : ℝ)^6371 := by
    have hnat : (168473039 : ℕ)^8419*50000000000000^6371 ≤ 22100254883177^6371*312500000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168473039 312500000 22100254883177 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328167591/2500000000 : ℝ), (-413267919/2000000000 : ℝ), (168473039/312500000 : ℝ)] ![(43352373442657/100000000000000 : ℝ), (622355838179/5000000000000 : ℝ), (22100254883177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328167591/2500000000 : ℝ)|^8419 ≤ (43352373442657/100000000000000 : ℝ)^6371
        have hw : |(1328167591/2500000000 : ℝ)|=(1328167591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-413267919/2000000000 : ℝ)|^8419 ≤ (622355838179/5000000000000 : ℝ)^6371
        have hw : |(-413267919/2000000000 : ℝ)|=(413267919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168473039/312500000 : ℝ)|^8419 ≤ (22100254883177/50000000000000 : ℝ)^6371
        have hw : |(168473039/312500000 : ℝ)|=(168473039/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s8_6 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531267037/1000000000 : ℝ)*x 0 + (168473039/312500000 : ℝ)*x 1 + (-516584897/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531267037/1000000000 : ℝ)^8419 ≤ (43352373507357/100000000000000 : ℝ)^6371 := by
    have hnat : (531267037 : ℕ)^8419*100000000000000^6371 ≤ 43352373507357^6371*1000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531267037 1000000000 43352373507357 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168473039/312500000 : ℝ)^8419 ≤ (22100254883177/50000000000000 : ℝ)^6371 := by
    have hnat : (168473039 : ℕ)^8419*50000000000000^6371 ≤ 22100254883177^6371*312500000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168473039 312500000 22100254883177 50000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516584897/2500000000 : ℝ)^8419 ≤ (12447116707859/100000000000000 : ℝ)^6371 := by
    have hnat : (516584897 : ℕ)^8419*100000000000000^6371 ≤ 12447116707859^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516584897 2500000000 12447116707859 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531267037/1000000000 : ℝ), (168473039/312500000 : ℝ), (-516584897/2500000000 : ℝ)] ![(43352373507357/100000000000000 : ℝ), (22100254883177/50000000000000 : ℝ), (12447116707859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531267037/1000000000 : ℝ)|^8419 ≤ (43352373507357/100000000000000 : ℝ)^6371
        have hw : |(531267037/1000000000 : ℝ)|=(531267037/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168473039/312500000 : ℝ)|^8419 ≤ (22100254883177/50000000000000 : ℝ)^6371
        have hw : |(168473039/312500000 : ℝ)|=(168473039/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-516584897/2500000000 : ℝ)|^8419 ≤ (12447116707859/100000000000000 : ℝ)^6371
        have hw : |(-516584897/2500000000 : ℝ)|=(516584897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1226_s8_7 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4352983799/10000000000 : ℝ)*x 0 + (895983097/2000000000 : ℝ)*x 1 + (1057395831/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352983799/10000000000 : ℝ)^8419 ≤ (8329381862253/25000000000000 : ℝ)^6371 := by
    have hnat : (4352983799 : ℕ)^8419*25000000000000^6371 ≤ 8329381862253^6371*10000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352983799 10000000000 8329381862253 25000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895983097/2000000000 : ℝ)^8419 ≤ (34607338687597/100000000000000 : ℝ)^6371 := by
    have hnat : (895983097 : ℕ)^8419*100000000000000^6371 ≤ 34607338687597^6371*2000000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895983097 2000000000 34607338687597 100000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057395831/2500000000 : ℝ)^8419 ≤ (6415026769283/20000000000000 : ℝ)^6371 := by
    have hnat : (1057395831 : ℕ)^8419*20000000000000^6371 ≤ 6415026769283^6371*2500000000^8419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057395831 2500000000 6415026769283 20000000000000 8419 6371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8419/2048 : ℝ)) 8419 6371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352983799/10000000000 : ℝ), (895983097/2000000000 : ℝ), (1057395831/2500000000 : ℝ)] ![(8329381862253/25000000000000 : ℝ), (34607338687597/100000000000000 : ℝ), (6415026769283/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352983799/10000000000 : ℝ)|^8419 ≤ (8329381862253/25000000000000 : ℝ)^6371
        have hw : |(4352983799/10000000000 : ℝ)|=(4352983799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895983097/2000000000 : ℝ)|^8419 ≤ (34607338687597/100000000000000 : ℝ)^6371
        have hw : |(895983097/2000000000 : ℝ)|=(895983097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1057395831/2500000000 : ℝ)|^8419 ≤ (6415026769283/20000000000000 : ℝ)^6371
        have hw : |(1057395831/2500000000 : ℝ)|=(1057395831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1226_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30223053/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (881/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11459/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (573/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2819/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (881/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11459/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (881/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11459/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (881/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11459/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (881/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11459/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (881/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11459/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (881/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11459/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11459/100000 : ℝ) ^ (4209/1024 : ℝ) ≤ (13575700496014539/100000000000000000000 : ℝ) := by
    have hpowers : (11459/100000 : ℝ)^4209 ≤ (13575700496014539/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11459 : ℕ)^4209*100000000000000000000^1024 ≤ 13575700496014539^1024*100000^4209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11459 100000 13575700496014539 100000000000000000000 4209 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11459/100000 : ℝ)) (X := (13575700496014539/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (881/6250 : ℝ) ^ (4209/1024 : ℝ) ≤ (15902117958961831/50000000000000000000 : ℝ) := by
    have hpowers : (881/6250 : ℝ)^4209 ≤ (15902117958961831/50000000000000000000 : ℝ)^1024 := by
      have hnat : (881 : ℕ)^4209*50000000000000000000^1024 ≤ 15902117958961831^1024*6250^4209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        881 6250 15902117958961831 50000000000000000000 4209 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (881/6250 : ℝ)) (X := (15902117958961831/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013575700496014539/50000000000000000000 : ℝ) ≤ (10000660493677689/10000000000000000 : ℝ) ^ (4209/1024 : ℝ) := by
    have hpowers : (50013575700496014539/50000000000000000000 : ℝ)^1024 ≤ (10000660493677689/10000000000000000 : ℝ)^4209 := by
      have hnat : (50013575700496014539 : ℕ)^1024*10000000000000000^4209 ≤ 10000660493677689^4209*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013575700496014539 50000000000000000000 10000660493677689 10000000000000000 1024 4209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000660493677689/10000000000000000 : ℝ)) (X := (50013575700496014539/50000000000000000000 : ℝ)) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045379936413938201/100000000000000000000 : ℝ) ≤ (10001103850757401/10000000000000000 : ℝ) ^ (4209/1024 : ℝ) := by
    have hpowers : (100045379936413938201/100000000000000000000 : ℝ)^1024 ≤ (10001103850757401/10000000000000000 : ℝ)^4209 := by
      have hnat : (100045379936413938201 : ℕ)^1024*10000000000000000^4209 ≤ 10001103850757401^4209*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045379936413938201 100000000000000000000 10001103850757401 10000000000000000 1024 4209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001103850757401/10000000000000000 : ℝ)) (X := (100045379936413938201/100000000000000000000 : ℝ)) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015902117958961831/25000000000000000000 : ℝ) ≤ (10001547207837113/10000000000000000 : ℝ) ^ (4209/1024 : ℝ) := by
    have hpowers : (25015902117958961831/25000000000000000000 : ℝ)^1024 ≤ (10001547207837113/10000000000000000 : ℝ)^4209 := by
      have hnat : (25015902117958961831 : ℕ)^1024*10000000000000000^4209 ≤ 10001547207837113^4209*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015902117958961831 25000000000000000000 10001547207837113 10000000000000000 1024 4209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001547207837113/10000000000000000 : ℝ)) (X := (25015902117958961831/25000000000000000000 : ℝ)) (by norm_num) 4209 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13575700496014539/100000000000000000000 : ℝ) ≤ ((26361580864275226277/26370000000000000000 : ℝ)+2*(13854908741/8240625000000 : ℝ)*(11459/100000 : ℝ))^(4209/1024 : ℝ) := by
    rw [show (26361580864275226277/26370000000000000000 : ℝ)+2*(13854908741/8240625000000 : ℝ)*(11459/100000 : ℝ)=(10000660493677689/10000000000000000 : ℝ) by norm_num, show 1+2*(13575700496014539/100000000000000000000 : ℝ)=(50013575700496014539/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15902117958961831/50000000000000000000 : ℝ)+(13575700496014539/100000000000000000000 : ℝ) ≤ ((26361580864275226277/26370000000000000000 : ℝ)+(13854908741/8240625000000 : ℝ)*((881/6250 : ℝ)+(11459/100000 : ℝ)))^(4209/1024 : ℝ) := by
    rw [show (26361580864275226277/26370000000000000000 : ℝ)+(13854908741/8240625000000 : ℝ)*((881/6250 : ℝ)+(11459/100000 : ℝ))=(10001103850757401/10000000000000000 : ℝ) by norm_num, show 1+(15902117958961831/50000000000000000000 : ℝ)+(13575700496014539/100000000000000000000 : ℝ)=(100045379936413938201/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15902117958961831/50000000000000000000 : ℝ) ≤ ((26361580864275226277/26370000000000000000 : ℝ)+2*(13854908741/8240625000000 : ℝ)*(881/6250 : ℝ))^(4209/1024 : ℝ) := by
    rw [show (26361580864275226277/26370000000000000000 : ℝ)+2*(13854908741/8240625000000 : ℝ)*(881/6250 : ℝ)=(10001547207837113/10000000000000000 : ℝ) by norm_num, show 1+2*(15902117958961831/50000000000000000000 : ℝ)=(25015902117958961831/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26361580864275226277/26370000000000000000 : ℝ)*(X 1 0+X 2 0)+(13854908741/8240625000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4209/1024 : ℝ)) (lo := (11459/100000 : ℝ)) (hi := (881/6250 : ℝ)) (c := (26361580864275226277/26370000000000000000 : ℝ)) (alpha := (13854908741/8240625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26361580864275226277/26370000000000000000 : ℝ)*(X 0 1+X 2 1)+(13854908741/8240625000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4209/1024 : ℝ)) (lo := (11459/100000 : ℝ)) (hi := (881/6250 : ℝ)) (c := (26361580864275226277/26370000000000000000 : ℝ)) (alpha := (13854908741/8240625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26361580864275226277/26370000000000000000 : ℝ)*(X 0 2+X 1 2)+(13854908741/8240625000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4209/1024 : ℝ)) (lo := (11459/100000 : ℝ)) (hi := (881/6250 : ℝ)) (c := (26361580864275226277/26370000000000000000 : ℝ)) (alpha := (13854908741/8240625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-425470917/2000000000 : ℝ)*X 0 0+(1078290341/2000000000 : ℝ)*X 0 1+(5267038407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344380541/10000000000 : ℝ)*X 1 0+(-27380481/125000000 : ℝ)*X 1 1+(1053407667/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344380497/10000000000 : ℝ)*X 2 0+(2633519191/5000000000 : ℝ)*X 2 1+(-2190438477/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((108824357/250000000 : ℝ)*X 0 0+(4228947367/10000000000 : ℝ)*X 0 1+(4480549197/10000000000 : ℝ)*X 0 2+(108824357/250000000 : ℝ)*X 1 0+(4228947367/10000000000 : ℝ)*X 1 1+(4480549197/10000000000 : ℝ)*X 1 2+(108824357/250000000 : ℝ)*X 2 0+(4228947367/10000000000 : ℝ)*X 2 1+(4480549197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1063679647/5000000000 : ℝ)*X 0 0+(1316837927/2500000000 : ℝ)*X 0 1+(5391137249/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328167591/2500000000 : ℝ)*X 1 0+(-413267919/2000000000 : ℝ)*X 1 1+(168473039/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531267037/1000000000 : ℝ)*X 2 0+(168473039/312500000 : ℝ)*X 2 1+(-516584897/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4352983799/10000000000 : ℝ)*X 0 0+(895983097/2000000000 : ℝ)*X 0 1+(1057395831/2500000000 : ℝ)*X 0 2+(4352983799/10000000000 : ℝ)*X 1 0+(895983097/2000000000 : ℝ)*X 1 1+(1057395831/2500000000 : ℝ)*X 1 2+(4352983799/10000000000 : ℝ)*X 2 0+(895983097/2000000000 : ℝ)*X 2 1+(1057395831/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1226_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2799808093224085946636909/686718750000000000000000000000 : ℝ) := by norm_num
    linear_combination (93580109/12500000000000 : ℝ)*(base19) + (623102311/100000000000000 : ℝ)*(base23) + (31726437/100000000000000 : ℝ)*(lower2) + (43842393/50000000000000 : ℝ)*(upper3) + (1876147/5000000000000 : ℝ)*(upper5) + (4692311004629/78125000000 : ℝ)*(major0) + (4692311004629/78125000000 : ℝ)*(major1) + (4692311004629/78125000000 : ℝ)*(major2) + (1607549006015729/20000000000000 : ℝ)*(sp0) + (803776110449453/10000000000000 : ℝ)*(sp1) + (8037761230033091/100000000000000 : ℝ)*(sp2) + (993635877734223/25000000000000 : ℝ)*(sp3) + (16823056757/100000000000000 : ℝ)*(sp4) + (10671875227/100000000000000 : ℝ)*(sp7) + (99363854570303/2500000000000 : ℝ)*(f.failure) + (4018880926567701/50000000000000 : ℝ)*(f.sum) + (4052498823919/1318500000000000000000000000 : ℝ)*base65 + (5068065955239893/343359375000000000000000000000 : ℝ)*base67 + (4987383196598339/686718750000000000000000000000 : ℝ)*base70 + (23825306340946481/2746875000000000000000000000000 : ℝ)*base72 + (4112732046901/527400000000000000000000000 : ℝ)*base73 + (28263865810837697/1373437500000000000000000000000 : ℝ)*base75 + (8854764702370411/686718750000000000000000000000 : ℝ)*base77 + (35619743131922269/2746875000000000000000000000000 : ℝ)*base79 + (1841106086917/2637000000000000000000000000 : ℝ)*base82 + (204941/50000000000000000000 : ℝ)*base90 + (204941/50000000000000000000 : ℝ)*base92 + (204941/50000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (660813052002785046505222667/219750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (541941951/100000000000000 : ℝ)*(base19) + (120880327/20000000000000 : ℝ)*(base23) + (1165741/625000000000 : ℝ)*(lower1) + (7805903/12500000000000 : ℝ)*(upper3) + (4507809/20000000000000 : ℝ)*(lower4) + (7717807/12500000000000 : ℝ)*(upper5) + (3018289327491071/50000000000000 : ℝ)*(major0) + (3018289327491071/50000000000000 : ℝ)*(major1) + (3018289327491071/50000000000000 : ℝ)*(major2) + (1828005493/100000000000000 : ℝ)*(sp2) + (1615694464270519/20000000000000 : ℝ)*(sp4) + (2019617944852661/25000000000000 : ℝ)*(sp5) + (8078469888945467/100000000000000 : ℝ)*(sp6) + (3994684888374541/100000000000000 : ℝ)*(sp7) + (3994684888374541/100000000000000 : ℝ)*(f.failure) + (1615694464270519/20000000000000 : ℝ)*(f.sum) + (38796349539761/13185000000000000000000000000 : ℝ)*base66 + (37298563445518409111/439500000000000000000000000000000 : ℝ)*base68 + (5143080286981409111/439500000000000000000000000000000 : ℝ)*base70 + (68145866865703409111/439500000000000000000000000000000 : ℝ)*base72 + (87104250470179/13185000000000000000000000000 : ℝ)*base73 + (100605561206217090889/439500000000000000000000000000000 : ℝ)*base75 + (4202936445305909111/439500000000000000000000000000000 : ℝ)*base78 + (7276051808842590889/439500000000000000000000000000000 : ℝ)*base79 + (2104593565391/13185000000000000000000000000 : ℝ)*base82 + (3506327/2000000000000000000000 : ℝ)*base90 + (3506327/2000000000000000000000 : ℝ)*base92 + (3506327/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1226_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30223053/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (881/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11459/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (573/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1226_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1226_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30223053/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3531/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11433/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (573/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1226_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1226_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1226_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30223053/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3531/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11433/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (573/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1226_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

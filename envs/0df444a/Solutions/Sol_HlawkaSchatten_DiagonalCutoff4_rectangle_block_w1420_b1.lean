-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1420_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:51:27.103321+00:00
-- url     : https://prove2.me/submissions/b3e286a6-bd7d-4ad4-90bd-8412a56f9a52

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
theorem support_rectangle_w1420_s3_0 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1977342931/10000000000 : ℝ)*x 0 + (1354549053/2500000000 : ℝ)*x 1 + (163685053/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1977342931/10000000000 : ℝ)^1095 ≤ (12058656098591/100000000000000 : ℝ)^839 := by
    have hnat : (1977342931 : ℕ)^1095*100000000000000^839 ≤ 12058656098591^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977342931 10000000000 12058656098591 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354549053/2500000000 : ℝ)^1095 ≤ (44941453328907/100000000000000 : ℝ)^839 := by
    have hnat : (1354549053 : ℕ)^1095*100000000000000^839 ≤ 44941453328907^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354549053 2500000000 44941453328907 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163685053/312500000 : ℝ)^1095 ≤ (10749972639389/25000000000000 : ℝ)^839 := by
    have hnat : (163685053 : ℕ)^1095*25000000000000^839 ≤ 10749972639389^839*312500000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163685053 312500000 10749972639389 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1977342931/10000000000 : ℝ), (1354549053/2500000000 : ℝ), (163685053/312500000 : ℝ)] ![(12058656098591/100000000000000 : ℝ), (44941453328907/100000000000000 : ℝ), (10749972639389/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1977342931/10000000000 : ℝ)|^1095 ≤ (12058656098591/100000000000000 : ℝ)^839
        have hw : |(-1977342931/10000000000 : ℝ)|=(1977342931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354549053/2500000000 : ℝ)|^1095 ≤ (44941453328907/100000000000000 : ℝ)^839
        have hw : |(1354549053/2500000000 : ℝ)|=(1354549053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163685053/312500000 : ℝ)|^1095 ≤ (10749972639389/25000000000000 : ℝ)^839
        have hw : |(163685053/312500000 : ℝ)|=(163685053/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s3_1 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349968131/10000000000 : ℝ)*x 0 + (-103465821/500000000 : ℝ)*x 1 + (2618960827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349968131/10000000000 : ℝ)^1095 ≤ (1768171166339/4000000000000 : ℝ)^839 := by
    have hnat : (5349968131 : ℕ)^1095*4000000000000^839 ≤ 1768171166339^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349968131 10000000000 1768171166339 4000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103465821/500000000 : ℝ)^1095 ≤ (12795830719041/100000000000000 : ℝ)^839 := by
    have hnat : (103465821 : ℕ)^1095*100000000000000^839 ≤ 12795830719041^839*500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103465821 500000000 12795830719041 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2618960827/5000000000 : ℝ)^1095 ≤ (21499945053779/50000000000000 : ℝ)^839 := by
    have hnat : (2618960827 : ℕ)^1095*50000000000000^839 ≤ 21499945053779^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618960827 5000000000 21499945053779 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349968131/10000000000 : ℝ), (-103465821/500000000 : ℝ), (2618960827/5000000000 : ℝ)] ![(1768171166339/4000000000000 : ℝ), (12795830719041/100000000000000 : ℝ), (21499945053779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349968131/10000000000 : ℝ)|^1095 ≤ (1768171166339/4000000000000 : ℝ)^839
        have hw : |(5349968131/10000000000 : ℝ)|=(5349968131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103465821/500000000 : ℝ)|^1095 ≤ (12795830719041/100000000000000 : ℝ)^839
        have hw : |(-103465821/500000000 : ℝ)|=(103465821/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2618960827/5000000000 : ℝ)|^1095 ≤ (21499945053779/50000000000000 : ℝ)^839
        have hw : |(2618960827/5000000000 : ℝ)|=(2618960827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s3_2 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349968131/10000000000 : ℝ)*x 0 + (5237921667/10000000000 : ℝ)*x 1 + (-2069316403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349968131/10000000000 : ℝ)^1095 ≤ (1768171166339/4000000000000 : ℝ)^839 := by
    have hnat : (5349968131 : ℕ)^1095*4000000000000^839 ≤ 1768171166339^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349968131 10000000000 1768171166339 4000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237921667/10000000000 : ℝ)^1095 ≤ (42999890246843/100000000000000 : ℝ)^839 := by
    have hnat : (5237921667 : ℕ)^1095*100000000000000^839 ≤ 42999890246843^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237921667 10000000000 42999890246843 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2069316403/10000000000 : ℝ)^1095 ≤ (2559166116369/20000000000000 : ℝ)^839 := by
    have hnat : (2069316403 : ℕ)^1095*20000000000000^839 ≤ 2559166116369^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069316403 10000000000 2559166116369 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349968131/10000000000 : ℝ), (5237921667/10000000000 : ℝ), (-2069316403/10000000000 : ℝ)] ![(1768171166339/4000000000000 : ℝ), (42999890246843/100000000000000 : ℝ), (2559166116369/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349968131/10000000000 : ℝ)|^1095 ≤ (1768171166339/4000000000000 : ℝ)^839
        have hw : |(5349968131/10000000000 : ℝ)|=(5349968131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237921667/10000000000 : ℝ)|^1095 ≤ (42999890246843/100000000000000 : ℝ)^839
        have hw : |(5237921667/10000000000 : ℝ)|=(5237921667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2069316403/10000000000 : ℝ)|^1095 ≤ (2559166116369/20000000000000 : ℝ)^839
        have hw : |(-2069316403/10000000000 : ℝ)|=(2069316403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s3_3 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2152974533/5000000000 : ℝ)*x 0 + (4115554121/10000000000 : ℝ)*x 1 + (2252131237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152974533/5000000000 : ℝ)^1095 ≤ (33297689821383/100000000000000 : ℝ)^839 := by
    have hnat : (2152974533 : ℕ)^1095*100000000000000^839 ≤ 33297689821383^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152974533 5000000000 33297689821383 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4115554121/10000000000 : ℝ)^1095 ≤ (15694616364071/50000000000000 : ℝ)^839 := by
    have hnat : (4115554121 : ℕ)^1095*50000000000000^839 ≤ 15694616364071^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4115554121 10000000000 15694616364071 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252131237/5000000000 : ℝ)^1095 ≤ (1103533669801/3125000000000 : ℝ)^839 := by
    have hnat : (2252131237 : ℕ)^1095*3125000000000^839 ≤ 1103533669801^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252131237 5000000000 1103533669801 3125000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152974533/5000000000 : ℝ), (4115554121/10000000000 : ℝ), (2252131237/5000000000 : ℝ)] ![(33297689821383/100000000000000 : ℝ), (15694616364071/50000000000000 : ℝ), (1103533669801/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152974533/5000000000 : ℝ)|^1095 ≤ (33297689821383/100000000000000 : ℝ)^839
        have hw : |(2152974533/5000000000 : ℝ)|=(2152974533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4115554121/10000000000 : ℝ)|^1095 ≤ (15694616364071/50000000000000 : ℝ)^839
        have hw : |(4115554121/10000000000 : ℝ)|=(4115554121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2252131237/5000000000 : ℝ)|^1095 ≤ (1103533669801/3125000000000 : ℝ)^839
        have hw : |(2252131237/5000000000 : ℝ)|=(2252131237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s3_4 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-494339597/2500000000 : ℝ)*x 0 + (130966107/250000000 : ℝ)*x 1 + (677183707/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (494339597/2500000000 : ℝ)^1095 ≤ (2411755824799/20000000000000 : ℝ)^839 := by
    have hnat : (494339597 : ℕ)^1095*20000000000000^839 ≤ 2411755824799^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494339597 2500000000 2411755824799 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130966107/250000000 : ℝ)^1095 ≤ (43007632643493/100000000000000 : ℝ)^839 := by
    have hnat : (130966107 : ℕ)^1095*100000000000000^839 ≤ 43007632643493^839*250000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130966107 250000000 43007632643493 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677183707/1250000000 : ℝ)^1095 ≤ (4493358821981/10000000000000 : ℝ)^839 := by
    have hnat : (677183707 : ℕ)^1095*10000000000000^839 ≤ 4493358821981^839*1250000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677183707 1250000000 4493358821981 10000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-494339597/2500000000 : ℝ), (130966107/250000000 : ℝ), (677183707/1250000000 : ℝ)] ![(2411755824799/20000000000000 : ℝ), (43007632643493/100000000000000 : ℝ), (4493358821981/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-494339597/2500000000 : ℝ)|^1095 ≤ (2411755824799/20000000000000 : ℝ)^839
        have hw : |(-494339597/2500000000 : ℝ)|=(494339597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130966107/250000000 : ℝ)|^1095 ≤ (43007632643493/100000000000000 : ℝ)^839
        have hw : |(130966107/250000000 : ℝ)|=(130966107/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677183707/1250000000 : ℝ)|^1095 ≤ (4493358821981/10000000000000 : ℝ)^839
        have hw : |(677183707/1250000000 : ℝ)|=(677183707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s3_5 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5303143857/10000000000 : ℝ)*x 0 + (-944884243/5000000000 : ℝ)*x 1 + (5417469653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303143857/10000000000 : ℝ)^1095 ≤ (2185000938103/5000000000000 : ℝ)^839 := by
    have hnat : (5303143857 : ℕ)^1095*5000000000000^839 ≤ 2185000938103^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303143857 10000000000 2185000938103 5000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (944884243/5000000000 : ℝ)^1095 ≤ (2841598259123/25000000000000 : ℝ)^839 := by
    have hnat : (944884243 : ℕ)^1095*25000000000000^839 ≤ 2841598259123^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944884243 5000000000 2841598259123 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417469653/10000000000 : ℝ)^1095 ≤ (8986717637467/20000000000000 : ℝ)^839 := by
    have hnat : (5417469653 : ℕ)^1095*20000000000000^839 ≤ 8986717637467^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417469653 10000000000 8986717637467 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303143857/10000000000 : ℝ), (-944884243/5000000000 : ℝ), (5417469653/10000000000 : ℝ)] ![(2185000938103/5000000000000 : ℝ), (2841598259123/25000000000000 : ℝ), (8986717637467/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303143857/10000000000 : ℝ)|^1095 ≤ (2185000938103/5000000000000 : ℝ)^839
        have hw : |(5303143857/10000000000 : ℝ)|=(5303143857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-944884243/5000000000 : ℝ)|^1095 ≤ (2841598259123/25000000000000 : ℝ)^839
        have hw : |(-944884243/5000000000 : ℝ)|=(944884243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417469653/10000000000 : ℝ)|^1095 ≤ (8986717637467/20000000000000 : ℝ)^839
        have hw : |(5417469653/10000000000 : ℝ)|=(5417469653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s3_6 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1325785921/2500000000 : ℝ)*x 0 + (1354367461/2500000000 : ℝ)*x 1 + (-94488423/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325785921/2500000000 : ℝ)^1095 ≤ (2731251056343/6250000000000 : ℝ)^839 := by
    have hnat : (1325785921 : ℕ)^1095*6250000000000^839 ≤ 2731251056343^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325785921 2500000000 2731251056343 6250000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354367461/2500000000 : ℝ)^1095 ≤ (8986718050981/20000000000000 : ℝ)^839 := by
    have hnat : (1354367461 : ℕ)^1095*20000000000000^839 ≤ 8986718050981^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354367461 2500000000 8986718050981 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94488423/500000000 : ℝ)^1095 ≤ (5683196416197/50000000000000 : ℝ)^839 := by
    have hnat : (94488423 : ℕ)^1095*50000000000000^839 ≤ 5683196416197^839*500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94488423 500000000 5683196416197 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325785921/2500000000 : ℝ), (1354367461/2500000000 : ℝ), (-94488423/500000000 : ℝ)] ![(2731251056343/6250000000000 : ℝ), (8986718050981/20000000000000 : ℝ), (5683196416197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325785921/2500000000 : ℝ)|^1095 ≤ (2731251056343/6250000000000 : ℝ)^839
        have hw : |(1325785921/2500000000 : ℝ)|=(1325785921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354367461/2500000000 : ℝ)|^1095 ≤ (8986718050981/20000000000000 : ℝ)^839
        have hw : |(1354367461/2500000000 : ℝ)|=(1354367461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94488423/500000000 : ℝ)|^1095 ≤ (5683196416197/50000000000000 : ℝ)^839
        have hw : |(-94488423/500000000 : ℝ)|=(94488423/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s3_7 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4305982701/10000000000 : ℝ)*x 0 + (900540963/2000000000 : ℝ)*x 1 + (4117120993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4305982701/10000000000 : ℝ)^1095 ≤ (16649014640971/50000000000000 : ℝ)^839 := by
    have hnat : (4305982701 : ℕ)^1095*50000000000000^839 ≤ 16649014640971^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305982701 10000000000 16649014640971 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900540963/2000000000 : ℝ)^1095 ≤ (3529714017911/10000000000000 : ℝ)^839 := by
    have hnat : (900540963 : ℕ)^1095*10000000000000^839 ≤ 3529714017911^839*2000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900540963 2000000000 3529714017911 10000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4117120993/10000000000 : ℝ)^1095 ≤ (31404830525843/100000000000000 : ℝ)^839 := by
    have hnat : (4117120993 : ℕ)^1095*100000000000000^839 ≤ 31404830525843^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4117120993 10000000000 31404830525843 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4305982701/10000000000 : ℝ), (900540963/2000000000 : ℝ), (4117120993/10000000000 : ℝ)] ![(16649014640971/50000000000000 : ℝ), (3529714017911/10000000000000 : ℝ), (31404830525843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4305982701/10000000000 : ℝ)|^1095 ≤ (16649014640971/50000000000000 : ℝ)^839
        have hw : |(4305982701/10000000000 : ℝ)|=(4305982701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900540963/2000000000 : ℝ)|^1095 ≤ (3529714017911/10000000000000 : ℝ)^839
        have hw : |(900540963/2000000000 : ℝ)|=(900540963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4117120993/10000000000 : ℝ)|^1095 ≤ (31404830525843/100000000000000 : ℝ)^839
        have hw : |(4117120993/10000000000 : ℝ)|=(4117120993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1420_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15827/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10319/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5567/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14951/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15827/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10319/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15827/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10319/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15827/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10319/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15827/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10319/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15827/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10319/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15827/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10319/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10319/100000 : ℝ) ^ (4379/1024 : ℝ) ≤ (3026371617000649/50000000000000000000 : ℝ) := by
    have hpowers : (10319/100000 : ℝ)^4379 ≤ (3026371617000649/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10319 : ℕ)^4379*50000000000000000000^1024 ≤ 3026371617000649^1024*100000^4379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10319 100000 3026371617000649 50000000000000000000 4379 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10319/100000 : ℝ)) (X := (3026371617000649/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15827/100000 : ℝ) ^ (4379/1024 : ℝ) ≤ (9424850316012141/25000000000000000000 : ℝ) := by
    have hpowers : (15827/100000 : ℝ)^4379 ≤ (9424850316012141/25000000000000000000 : ℝ)^1024 := by
      have hnat : (15827 : ℕ)^4379*25000000000000000000^1024 ≤ 9424850316012141^1024*100000^4379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15827 100000 9424850316012141 25000000000000000000 4379 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15827/100000 : ℝ)) (X := (9424850316012141/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003026371617000649/25000000000000000000 : ℝ) ≤ (5000141532808147/5000000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (25003026371617000649/25000000000000000000 : ℝ)^1024 ≤ (5000141532808147/5000000000000000 : ℝ)^4379 := by
      have hnat : (25003026371617000649 : ℕ)^1024*5000000000000000^4379 ≤ 5000141532808147^4379*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003026371617000649 25000000000000000000 5000141532808147 5000000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000141532808147/5000000000000000 : ℝ)) (X := (25003026371617000649/25000000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021876072249024931/50000000000000000000 : ℝ) ≤ (2500255735834827/2500000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (50021876072249024931/50000000000000000000 : ℝ)^1024 ≤ (2500255735834827/2500000000000000 : ℝ)^4379 := by
      have hnat : (50021876072249024931 : ℕ)^1024*2500000000000000^4379 ≤ 2500255735834827^4379*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021876072249024931 50000000000000000000 2500255735834827 2500000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500255735834827/2500000000000000 : ℝ)) (X := (50021876072249024931/50000000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509424850316012141/12500000000000000000 : ℝ) ≤ (5000881410531161/5000000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (12509424850316012141/12500000000000000000 : ℝ)^1024 ≤ (5000881410531161/5000000000000000 : ℝ)^4379 := by
      have hnat : (12509424850316012141 : ℕ)^1024*5000000000000000^4379 ≤ 5000881410531161^4379*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509424850316012141 12500000000000000000 5000881410531161 5000000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000881410531161/5000000000000000 : ℝ)) (X := (12509424850316012141/12500000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3026371617000649/50000000000000000000 : ℝ) ≤ ((161959675085197013/162000000000000000 : ℝ)+2*(369938861507/275400000000000 : ℝ)*(10319/100000 : ℝ))^(4379/1024 : ℝ) := by
    rw [show (161959675085197013/162000000000000000 : ℝ)+2*(369938861507/275400000000000 : ℝ)*(10319/100000 : ℝ)=(5000141532808147/5000000000000000 : ℝ) by norm_num, show 1+2*(3026371617000649/50000000000000000000 : ℝ)=(25003026371617000649/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9424850316012141/25000000000000000000 : ℝ)+(3026371617000649/50000000000000000000 : ℝ) ≤ ((161959675085197013/162000000000000000 : ℝ)+(369938861507/275400000000000 : ℝ)*((15827/100000 : ℝ)+(10319/100000 : ℝ)))^(4379/1024 : ℝ) := by
    rw [show (161959675085197013/162000000000000000 : ℝ)+(369938861507/275400000000000 : ℝ)*((15827/100000 : ℝ)+(10319/100000 : ℝ))=(2500255735834827/2500000000000000 : ℝ) by norm_num, show 1+(9424850316012141/25000000000000000000 : ℝ)+(3026371617000649/50000000000000000000 : ℝ)=(50021876072249024931/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9424850316012141/25000000000000000000 : ℝ) ≤ ((161959675085197013/162000000000000000 : ℝ)+2*(369938861507/275400000000000 : ℝ)*(15827/100000 : ℝ))^(4379/1024 : ℝ) := by
    rw [show (161959675085197013/162000000000000000 : ℝ)+2*(369938861507/275400000000000 : ℝ)*(15827/100000 : ℝ)=(5000881410531161/5000000000000000 : ℝ) by norm_num, show 1+2*(9424850316012141/25000000000000000000 : ℝ)=(12509424850316012141/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (161959675085197013/162000000000000000 : ℝ)*(X 1 0+X 2 0)+(369938861507/275400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (10319/100000 : ℝ)) (hi := (15827/100000 : ℝ)) (c := (161959675085197013/162000000000000000 : ℝ)) (alpha := (369938861507/275400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (161959675085197013/162000000000000000 : ℝ)*(X 0 1+X 2 1)+(369938861507/275400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (10319/100000 : ℝ)) (hi := (15827/100000 : ℝ)) (c := (161959675085197013/162000000000000000 : ℝ)) (alpha := (369938861507/275400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (161959675085197013/162000000000000000 : ℝ)*(X 0 2+X 1 2)+(369938861507/275400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (10319/100000 : ℝ)) (hi := (15827/100000 : ℝ)) (c := (161959675085197013/162000000000000000 : ℝ)) (alpha := (369938861507/275400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1977342931/10000000000 : ℝ)*X 0 0+(1354549053/2500000000 : ℝ)*X 0 1+(163685053/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349968131/10000000000 : ℝ)*X 1 0+(-103465821/500000000 : ℝ)*X 1 1+(2618960827/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349968131/10000000000 : ℝ)*X 2 0+(5237921667/10000000000 : ℝ)*X 2 1+(-2069316403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2152974533/5000000000 : ℝ)*X 0 0+(4115554121/10000000000 : ℝ)*X 0 1+(2252131237/5000000000 : ℝ)*X 0 2+(2152974533/5000000000 : ℝ)*X 1 0+(4115554121/10000000000 : ℝ)*X 1 1+(2252131237/5000000000 : ℝ)*X 1 2+(2152974533/5000000000 : ℝ)*X 2 0+(4115554121/10000000000 : ℝ)*X 2 1+(2252131237/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-494339597/2500000000 : ℝ)*X 0 0+(130966107/250000000 : ℝ)*X 0 1+(677183707/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303143857/10000000000 : ℝ)*X 1 0+(-944884243/5000000000 : ℝ)*X 1 1+(5417469653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325785921/2500000000 : ℝ)*X 2 0+(1354367461/2500000000 : ℝ)*X 2 1+(-94488423/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4305982701/10000000000 : ℝ)*X 0 0+(900540963/2000000000 : ℝ)*X 0 1+(4117120993/10000000000 : ℝ)*X 0 2+(4305982701/10000000000 : ℝ)*X 1 0+(900540963/2000000000 : ℝ)*X 1 1+(4117120993/10000000000 : ℝ)*X 1 2+(4305982701/10000000000 : ℝ)*X 2 0+(900540963/2000000000 : ℝ)*X 2 1+(4117120993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14110214230669730063273/2295000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1194996803/100000000000000 : ℝ)*(base19) + (1152416897/100000000000000 : ℝ)*(base23) + (169552217/100000000000000 : ℝ)*(upper3) + (4556023/20000000000000 : ℝ)*(upper4) + (39762153/25000000000000 : ℝ)*(upper5) + (2029944792529219/50000000000000 : ℝ)*(major0) + (2029944792529219/50000000000000 : ℝ)*(major1) + (2029944792529219/50000000000000 : ℝ)*(major2) + (1109423276893699/20000000000000 : ℝ)*(sp0) + (5547136143017909/100000000000000 : ℝ)*(sp1) + (1109427237119563/20000000000000 : ℝ)*(sp2) + (2572632068780607/100000000000000 : ℝ)*(sp3) + (20953546217/100000000000000 : ℝ)*(sp4) + (2389595041/25000000000000 : ℝ)*(sp7) + (2572641627160771/100000000000000 : ℝ)*(f.failure) + (693392167251839/12500000000000 : ℝ)*(f.sum) + (1281766827827/1721250000000000000000000000 : ℝ)*base65 + (30727146826131289/15300000000000000000000000000000 : ℝ)*base68 + (141793406141631289/15300000000000000000000000000000 : ℝ)*base70 + (89802989714468711/15300000000000000000000000000000 : ℝ)*base71 + (5196640526681/3442500000000000000000000000 : ℝ)*base74 + (120129701864168711/15300000000000000000000000000000 : ℝ)*base75 + (240952061718668711/15300000000000000000000000000000 : ℝ)*base77 + (151464463772631289/15300000000000000000000000000000 : ℝ)*base80 + (2030241938287/430312500000000000000000000 : ℝ)*base82 + (81535121/10000000000000000000000 : ℝ)*base90 + (81535121/10000000000000000000000 : ℝ)*base92 + (81535121/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2735876457529321220978893/540000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47162519/20000000000000 : ℝ)*(base19) + (8162253/5000000000000 : ℝ)*(base23) + (37286281/100000000000000 : ℝ)*(upper3) + (4908569/10000000000000 : ℝ)*(lower4) + (18029239/50000000000000 : ℝ)*(upper5) + (818551441884761/20000000000000 : ℝ)*(major0) + (818551441884761/20000000000000 : ℝ)*(major1) + (818551441884761/20000000000000 : ℝ)*(major2) + (3848438407/100000000000000 : ℝ)*(sp1) + (5807461473/100000000000000 : ℝ)*(sp2) + (2796022651516637/50000000000000 : ℝ)*(sp4) + (87375644043473/1562500000000 : ℝ)*(sp5) + (279601966616337/5000000000000 : ℝ)*(sp6) + (648367236733267/25000000000000 : ℝ)*(sp7) + (648367236733267/25000000000000 : ℝ)*(f.failure) + (2796022651516637/50000000000000 : ℝ)*(f.sum) + (5138970101597/2754000000000000000000000000 : ℝ)*base66 + (50186455666312091/6120000000000000000000000000000 : ℝ)*base68 + (17469929350327909/6120000000000000000000000000000 : ℝ)*base69 + (6362187994192091/6120000000000000000000000000000 : ℝ)*base72 + (96759350227/110160000000000000000000000 : ℝ)*base73 + (53715603715672091/6120000000000000000000000000000 : ℝ)*base76 + (9250318210432091/6120000000000000000000000000000 : ℝ)*base78 + (69095457387967909/6120000000000000000000000000000 : ℝ)*base79 + (185117368057/2754000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (13526783/2500000000000000000000 : ℝ)*base89 + (13526783/2500000000000000000000 : ℝ)*base91 + (13526783/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1420_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15827/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10319/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5567/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14951/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1420_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1420_s4_0 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-98914501/500000000 : ℝ)*x 0 + (1082029497/2000000000 : ℝ)*x 1 + (2622673449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98914501/500000000 : ℝ)^1095 ≤ (12066194714131/100000000000000 : ℝ)^839 := by
    have hnat : (98914501 : ℕ)^1095*100000000000000^839 ≤ 12066194714131^839*500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98914501 500000000 12066194714131 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082029497/2000000000 : ℝ)^1095 ≤ (11213585568661/25000000000000 : ℝ)^839 := by
    have hnat : (1082029497 : ℕ)^1095*25000000000000^839 ≤ 11213585568661^839*2000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082029497 2000000000 11213585568661 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622673449/5000000000 : ℝ)^1095 ≤ (2153973149773/5000000000000 : ℝ)^839 := by
    have hnat : (2622673449 : ℕ)^1095*5000000000000^839 ≤ 2153973149773^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622673449 5000000000 2153973149773 5000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98914501/500000000 : ℝ), (1082029497/2000000000 : ℝ), (2622673449/5000000000 : ℝ)] ![(12066194714131/100000000000000 : ℝ), (11213585568661/25000000000000 : ℝ), (2153973149773/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98914501/500000000 : ℝ)|^1095 ≤ (12066194714131/100000000000000 : ℝ)^839
        have hw : |(-98914501/500000000 : ℝ)|=(98914501/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082029497/2000000000 : ℝ)|^1095 ≤ (11213585568661/25000000000000 : ℝ)^839
        have hw : |(1082029497/2000000000 : ℝ)|=(1082029497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622673449/5000000000 : ℝ)|^1095 ≤ (2153973149773/5000000000000 : ℝ)^839
        have hw : |(2622673449/5000000000 : ℝ)|=(2622673449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s4_1 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2673946579/5000000000 : ℝ)*x 0 + (-412445029/2000000000 : ℝ)*x 1 + (2622673489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673946579/5000000000 : ℝ)^1095 ≤ (22090952363073/50000000000000 : ℝ)^839 := by
    have hnat : (2673946579 : ℕ)^1095*50000000000000^839 ≤ 22090952363073^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673946579 5000000000 22090952363073 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (412445029/2000000000 : ℝ)^1095 ≤ (796164463197/6250000000000 : ℝ)^839 := by
    have hnat : (412445029 : ℕ)^1095*6250000000000^839 ≤ 796164463197^839*2000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412445029 2000000000 796164463197 6250000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622673489/5000000000 : ℝ)^1095 ≤ (5384932981621/12500000000000 : ℝ)^839 := by
    have hnat : (2622673489 : ℕ)^1095*12500000000000^839 ≤ 5384932981621^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622673489 5000000000 5384932981621 12500000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673946579/5000000000 : ℝ), (-412445029/2000000000 : ℝ), (2622673489/5000000000 : ℝ)] ![(22090952363073/50000000000000 : ℝ), (796164463197/6250000000000 : ℝ), (5384932981621/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673946579/5000000000 : ℝ)|^1095 ≤ (22090952363073/50000000000000 : ℝ)^839
        have hw : |(2673946579/5000000000 : ℝ)|=(2673946579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-412445029/2000000000 : ℝ)|^1095 ≤ (796164463197/6250000000000 : ℝ)^839
        have hw : |(-412445029/2000000000 : ℝ)|=(412445029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622673489/5000000000 : ℝ)|^1095 ≤ (5384932981621/12500000000000 : ℝ)^839
        have hw : |(2622673489/5000000000 : ℝ)|=(2622673489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s4_2 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (167121659/312500000 : ℝ)*x 0 + (209813883/400000000 : ℝ)*x 1 + (-206222511/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167121659/312500000 : ℝ)^1095 ≤ (2209095198569/5000000000000 : ℝ)^839 := by
    have hnat : (167121659 : ℕ)^1095*5000000000000^839 ≤ 2209095198569^839*312500000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167121659 312500000 2209095198569 5000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209813883/400000000 : ℝ)^1095 ≤ (43079464892697/100000000000000 : ℝ)^839 := by
    have hnat : (209813883 : ℕ)^1095*100000000000000^839 ≤ 43079464892697^839*400000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209813883 400000000 43079464892697 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206222511/1000000000 : ℝ)^1095 ≤ (2547726225797/20000000000000 : ℝ)^839 := by
    have hnat : (206222511 : ℕ)^1095*20000000000000^839 ≤ 2547726225797^839*1000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206222511 1000000000 2547726225797 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167121659/312500000 : ℝ), (209813883/400000000 : ℝ), (-206222511/1000000000 : ℝ)] ![(2209095198569/5000000000000 : ℝ), (43079464892697/100000000000000 : ℝ), (2547726225797/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167121659/312500000 : ℝ)|^1095 ≤ (2209095198569/5000000000000 : ℝ)^839
        have hw : |(167121659/312500000 : ℝ)|=(167121659/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209813883/400000000 : ℝ)|^1095 ≤ (43079464892697/100000000000000 : ℝ)^839
        have hw : |(209813883/400000000 : ℝ)|=(209813883/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-206222511/1000000000 : ℝ)|^1095 ≤ (2547726225797/20000000000000 : ℝ)^839
        have hw : |(-206222511/1000000000 : ℝ)|=(206222511/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s4_3 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2153264451/5000000000 : ℝ)*x 0 + (103304163/250000000 : ℝ)*x 1 + (4487509909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153264451/5000000000 : ℝ)^1095 ≤ (16651770958887/50000000000000 : ℝ)^839 := by
    have hnat : (2153264451 : ℕ)^1095*50000000000000^839 ≤ 16651770958887^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153264451 5000000000 16651770958887 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103304163/250000000 : ℝ)^1095 ≤ (6310939382977/20000000000000 : ℝ)^839 := by
    have hnat : (103304163 : ℕ)^1095*20000000000000^839 ≤ 6310939382977^839*250000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103304163 250000000 6310939382977 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487509909/10000000000 : ℝ)^1095 ≤ (7028352230669/20000000000000 : ℝ)^839 := by
    have hnat : (4487509909 : ℕ)^1095*20000000000000^839 ≤ 7028352230669^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487509909 10000000000 7028352230669 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2153264451/5000000000 : ℝ), (103304163/250000000 : ℝ), (4487509909/10000000000 : ℝ)] ![(16651770958887/50000000000000 : ℝ), (6310939382977/20000000000000 : ℝ), (7028352230669/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2153264451/5000000000 : ℝ)|^1095 ≤ (16651770958887/50000000000000 : ℝ)^839
        have hw : |(2153264451/5000000000 : ℝ)|=(2153264451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103304163/250000000 : ℝ)|^1095 ≤ (6310939382977/20000000000000 : ℝ)^839
        have hw : |(103304163/250000000 : ℝ)|=(103304163/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4487509909/10000000000 : ℝ)|^1095 ≤ (7028352230669/20000000000000 : ℝ)^839
        have hw : |(4487509909/10000000000 : ℝ)|=(4487509909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s4_4 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-989151029/5000000000 : ℝ)*x 0 + (5245951113/10000000000 : ℝ)*x 1 + (540954007/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (989151029/5000000000 : ℝ)^1095 ≤ (6033145270497/50000000000000 : ℝ)^839 := by
    have hnat : (989151029 : ℕ)^1095*50000000000000^839 ≤ 6033145270497^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989151029 5000000000 6033145270497 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245951113/10000000000 : ℝ)^1095 ≤ (43085939599683/100000000000000 : ℝ)^839 := by
    have hnat : (5245951113 : ℕ)^1095*100000000000000^839 ≤ 43085939599683^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245951113 10000000000 43085939599683 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540954007/1000000000 : ℝ)^1095 ≤ (4484776984993/10000000000000 : ℝ)^839 := by
    have hnat : (540954007 : ℕ)^1095*10000000000000^839 ≤ 4484776984993^839*1000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540954007 1000000000 4484776984993 10000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-989151029/5000000000 : ℝ), (5245951113/10000000000 : ℝ), (540954007/1000000000 : ℝ)] ![(6033145270497/50000000000000 : ℝ), (43085939599683/100000000000000 : ℝ), (4484776984993/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-989151029/5000000000 : ℝ)|^1095 ≤ (6033145270497/50000000000000 : ℝ)^839
        have hw : |(-989151029/5000000000 : ℝ)|=(989151029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245951113/10000000000 : ℝ)|^1095 ≤ (43085939599683/100000000000000 : ℝ)^839
        have hw : |(5245951113/10000000000 : ℝ)|=(5245951113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540954007/1000000000 : ℝ)|^1095 ≤ (4484776984993/10000000000000 : ℝ)^839
        have hw : |(540954007/1000000000 : ℝ)|=(540954007/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s4_5 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652543837/5000000000 : ℝ)*x 0 + (-118627/625000 : ℝ)*x 1 + (1352385031/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652543837/5000000000 : ℝ)^1095 ≤ (1748837007979/4000000000000 : ℝ)^839 := by
    have hnat : (2652543837 : ℕ)^1095*4000000000000^839 ≤ 1748837007979^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652543837 5000000000 1748837007979 4000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118627/625000 : ℝ)^1095 ≤ (11431304339921/100000000000000 : ℝ)^839 := by
    have hnat : (118627 : ℕ)^1095*100000000000000^839 ≤ 11431304339921^839*625000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118627 625000 11431304339921 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352385031/2500000000 : ℝ)^1095 ≤ (22423885217109/50000000000000 : ℝ)^839 := by
    have hnat : (1352385031 : ℕ)^1095*50000000000000^839 ≤ 22423885217109^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352385031 2500000000 22423885217109 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652543837/5000000000 : ℝ), (-118627/625000 : ℝ), (1352385031/2500000000 : ℝ)] ![(1748837007979/4000000000000 : ℝ), (11431304339921/100000000000000 : ℝ), (22423885217109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652543837/5000000000 : ℝ)|^1095 ≤ (1748837007979/4000000000000 : ℝ)^839
        have hw : |(2652543837/5000000000 : ℝ)|=(2652543837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-118627/625000 : ℝ)|^1095 ≤ (11431304339921/100000000000000 : ℝ)^839
        have hw : |(-118627/625000 : ℝ)|=(118627/625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352385031/2500000000 : ℝ)|^1095 ≤ (22423885217109/50000000000000 : ℝ)^839
        have hw : |(1352385031/2500000000 : ℝ)|=(1352385031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s4_6 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305087717/10000000000 : ℝ)*x 0 + (2704770057/5000000000 : ℝ)*x 1 + (-1898031957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305087717/10000000000 : ℝ)^1095 ≤ (43720925661981/100000000000000 : ℝ)^839 := by
    have hnat : (5305087717 : ℕ)^1095*100000000000000^839 ≤ 43720925661981^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305087717 10000000000 43720925661981 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704770057/5000000000 : ℝ)^1095 ≤ (43796650709/97656250000 : ℝ)^839 := by
    have hnat : (2704770057 : ℕ)^1095*97656250000^839 ≤ 43796650709^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704770057 5000000000 43796650709 97656250000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1898031957/10000000000 : ℝ)^1095 ≤ (2857826000481/25000000000000 : ℝ)^839 := by
    have hnat : (1898031957 : ℕ)^1095*25000000000000^839 ≤ 2857826000481^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898031957 10000000000 2857826000481 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305087717/10000000000 : ℝ), (2704770057/5000000000 : ℝ), (-1898031957/10000000000 : ℝ)] ![(43720925661981/100000000000000 : ℝ), (43796650709/97656250000 : ℝ), (2857826000481/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305087717/10000000000 : ℝ)|^1095 ≤ (43720925661981/100000000000000 : ℝ)^839
        have hw : |(5305087717/10000000000 : ℝ)|=(5305087717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704770057/5000000000 : ℝ)|^1095 ≤ (43796650709/97656250000 : ℝ)^839
        have hw : |(2704770057/5000000000 : ℝ)|=(2704770057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1898031957/10000000000 : ℝ)|^1095 ≤ (2857826000481/25000000000000 : ℝ)^839
        have hw : |(-1898031957/10000000000 : ℝ)|=(1898031957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s4_7 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2153277383/5000000000 : ℝ)*x 0 + (1121551791/2500000000 : ℝ)*x 1 + (2066738079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153277383/5000000000 : ℝ)^1095 ≤ (1332152118413/4000000000000 : ℝ)^839 := by
    have hnat : (2153277383 : ℕ)^1095*4000000000000^839 ≤ 1332152118413^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153277383 5000000000 1332152118413 4000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121551791/2500000000 : ℝ)^1095 ≤ (7025689419103/20000000000000 : ℝ)^839 := by
    have hnat : (1121551791 : ℕ)^1095*20000000000000^839 ≤ 7025689419103^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121551791 2500000000 7025689419103 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066738079/5000000000 : ℝ)^1095 ≤ (15783874961711/50000000000000 : ℝ)^839 := by
    have hnat : (2066738079 : ℕ)^1095*50000000000000^839 ≤ 15783874961711^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066738079 5000000000 15783874961711 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2153277383/5000000000 : ℝ), (1121551791/2500000000 : ℝ), (2066738079/5000000000 : ℝ)] ![(1332152118413/4000000000000 : ℝ), (7025689419103/20000000000000 : ℝ), (15783874961711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2153277383/5000000000 : ℝ)|^1095 ≤ (1332152118413/4000000000000 : ℝ)^839
        have hw : |(2153277383/5000000000 : ℝ)|=(2153277383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121551791/2500000000 : ℝ)|^1095 ≤ (7025689419103/20000000000000 : ℝ)^839
        have hw : |(1121551791/2500000000 : ℝ)|=(1121551791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2066738079/5000000000 : ℝ)|^1095 ≤ (15783874961711/50000000000000 : ℝ)^839
        have hw : |(2066738079/5000000000 : ℝ)|=(2066738079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1420_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14951/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5567/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2823/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14783/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14951/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5567/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14951/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5567/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14951/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5567/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14951/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5567/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14951/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5567/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14951/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5567/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5567/50000 : ℝ) ^ (4379/1024 : ℝ) ≤ (837781075659273/10000000000000000000 : ℝ) := by
    have hpowers : (5567/50000 : ℝ)^4379 ≤ (837781075659273/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5567 : ℕ)^4379*10000000000000000000^1024 ≤ 837781075659273^1024*50000^4379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5567 50000 837781075659273 10000000000000000000 4379 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5567/50000 : ℝ)) (X := (837781075659273/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14951/100000 : ℝ) ^ (4379/1024 : ℝ) ≤ (29552001614850159/100000000000000000000 : ℝ) := by
    have hpowers : (14951/100000 : ℝ)^4379 ≤ (29552001614850159/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14951 : ℕ)^4379*100000000000000000000^1024 ≤ 29552001614850159^1024*100000^4379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14951 100000 29552001614850159 100000000000000000000 4379 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14951/100000 : ℝ)) (X := (29552001614850159/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000837781075659273/5000000000000000000 : ℝ) ≤ (10000391793907983/10000000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (5000837781075659273/5000000000000000000 : ℝ)^1024 ≤ (10000391793907983/10000000000000000 : ℝ)^4379 := by
      have hnat : (5000837781075659273 : ℕ)^1024*10000000000000000^4379 ≤ 10000391793907983^4379*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000837781075659273 5000000000000000000 10000391793907983 10000000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000391793907983/10000000000000000 : ℝ)) (X := (5000837781075659273/5000000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037929812371442889/100000000000000000000 : ℝ) ≤ (1250110854320687/1250000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (100037929812371442889/100000000000000000000 : ℝ)^1024 ≤ (1250110854320687/1250000000000000 : ℝ)^4379 := by
      have hnat : (100037929812371442889 : ℕ)^1024*1250000000000000^4379 ≤ 1250110854320687^4379*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037929812371442889 100000000000000000000 1250110854320687 1250000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250110854320687/1250000000000000 : ℝ)) (X := (100037929812371442889/100000000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029552001614850159/50000000000000000000 : ℝ) ≤ (10001381875223009/10000000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (50029552001614850159/50000000000000000000 : ℝ)^1024 ≤ (10001381875223009/10000000000000000 : ℝ)^4379 := by
      have hnat : (50029552001614850159 : ℕ)^1024*10000000000000000^4379 ≤ 10001381875223009^4379*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029552001614850159 50000000000000000000 10001381875223009 10000000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001381875223009/10000000000000000 : ℝ)) (X := (50029552001614850159/50000000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(837781075659273/10000000000000000000 : ℝ) ≤ ((38160471911985271627/38170000000000000000 : ℝ)+2*(495040657513/381700000000000 : ℝ)*(5567/50000 : ℝ))^(4379/1024 : ℝ) := by
    rw [show (38160471911985271627/38170000000000000000 : ℝ)+2*(495040657513/381700000000000 : ℝ)*(5567/50000 : ℝ)=(10000391793907983/10000000000000000 : ℝ) by norm_num, show 1+2*(837781075659273/10000000000000000000 : ℝ)=(5000837781075659273/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29552001614850159/100000000000000000000 : ℝ)+(837781075659273/10000000000000000000 : ℝ) ≤ ((38160471911985271627/38170000000000000000 : ℝ)+(495040657513/381700000000000 : ℝ)*((14951/100000 : ℝ)+(5567/50000 : ℝ)))^(4379/1024 : ℝ) := by
    rw [show (38160471911985271627/38170000000000000000 : ℝ)+(495040657513/381700000000000 : ℝ)*((14951/100000 : ℝ)+(5567/50000 : ℝ))=(1250110854320687/1250000000000000 : ℝ) by norm_num, show 1+(29552001614850159/100000000000000000000 : ℝ)+(837781075659273/10000000000000000000 : ℝ)=(100037929812371442889/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29552001614850159/100000000000000000000 : ℝ) ≤ ((38160471911985271627/38170000000000000000 : ℝ)+2*(495040657513/381700000000000 : ℝ)*(14951/100000 : ℝ))^(4379/1024 : ℝ) := by
    rw [show (38160471911985271627/38170000000000000000 : ℝ)+2*(495040657513/381700000000000 : ℝ)*(14951/100000 : ℝ)=(10001381875223009/10000000000000000 : ℝ) by norm_num, show 1+2*(29552001614850159/100000000000000000000 : ℝ)=(50029552001614850159/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38160471911985271627/38170000000000000000 : ℝ)*(X 1 0+X 2 0)+(495040657513/381700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (5567/50000 : ℝ)) (hi := (14951/100000 : ℝ)) (c := (38160471911985271627/38170000000000000000 : ℝ)) (alpha := (495040657513/381700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38160471911985271627/38170000000000000000 : ℝ)*(X 0 1+X 2 1)+(495040657513/381700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (5567/50000 : ℝ)) (hi := (14951/100000 : ℝ)) (c := (38160471911985271627/38170000000000000000 : ℝ)) (alpha := (495040657513/381700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38160471911985271627/38170000000000000000 : ℝ)*(X 0 2+X 1 2)+(495040657513/381700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (5567/50000 : ℝ)) (hi := (14951/100000 : ℝ)) (c := (38160471911985271627/38170000000000000000 : ℝ)) (alpha := (495040657513/381700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-98914501/500000000 : ℝ)*X 0 0+(1082029497/2000000000 : ℝ)*X 0 1+(2622673449/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673946579/5000000000 : ℝ)*X 1 0+(-412445029/2000000000 : ℝ)*X 1 1+(2622673489/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167121659/312500000 : ℝ)*X 2 0+(209813883/400000000 : ℝ)*X 2 1+(-206222511/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2153264451/5000000000 : ℝ)*X 0 0+(103304163/250000000 : ℝ)*X 0 1+(4487509909/10000000000 : ℝ)*X 0 2+(2153264451/5000000000 : ℝ)*X 1 0+(103304163/250000000 : ℝ)*X 1 1+(4487509909/10000000000 : ℝ)*X 1 2+(2153264451/5000000000 : ℝ)*X 2 0+(103304163/250000000 : ℝ)*X 2 1+(4487509909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-989151029/5000000000 : ℝ)*X 0 0+(5245951113/10000000000 : ℝ)*X 0 1+(540954007/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652543837/5000000000 : ℝ)*X 1 0+(-118627/625000 : ℝ)*X 1 1+(1352385031/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305087717/10000000000 : ℝ)*X 2 0+(2704770057/5000000000 : ℝ)*X 2 1+(-1898031957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2153277383/5000000000 : ℝ)*X 0 0+(1121551791/2500000000 : ℝ)*X 0 1+(2066738079/5000000000 : ℝ)*X 0 2+(2153277383/5000000000 : ℝ)*X 1 0+(1121551791/2500000000 : ℝ)*X 1 1+(2066738079/5000000000 : ℝ)*X 1 2+(2153277383/5000000000 : ℝ)*X 2 0+(1121551791/2500000000 : ℝ)*X 2 1+(2066738079/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2350780243229441815872767601/190850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25744707/1250000000000 : ℝ)*(base19) + (883218913/50000000000000 : ℝ)*(base23) + (114291269/100000000000000 : ℝ)*(lower2) + (155207857/50000000000000 : ℝ)*(upper3) + (184598891/100000000000000 : ℝ)*(upper5) + (444112493807121/10000000000000 : ℝ)*(major0) + (444112493807121/10000000000000 : ℝ)*(major1) + (444112493807121/10000000000000 : ℝ)*(major2) + (3033992835389469/50000000000000 : ℝ)*(sp0) + (6068027302770287/100000000000000 : ℝ)*(sp1) + (303401379795451/5000000000000 : ℝ)*(sp2) + (2814198389536803/100000000000000 : ℝ)*(sp3) + (10922891977/25000000000000 : ℝ)*(sp4) + (4342735597/20000000000000 : ℝ)*(sp7) + (703555025803697/25000000000000 : ℝ)*(f.failure) + (6068029362346847/100000000000000 : ℝ)*(f.sum) + (12888671748559/1908500000000000000000000000 : ℝ)*base66 + (568801931141355867/381700000000000000000000000000000 : ℝ)*base67 + (833473548209455867/381700000000000000000000000000000 : ℝ)*base69 + (4673133991396244133/381700000000000000000000000000000 : ℝ)*base72 + (1469165547901/3817000000000000000000000000 : ℝ)*base73 + (1002325885713944133/381700000000000000000000000000000 : ℝ)*base76 + (5757870966320044133/381700000000000000000000000000000 : ℝ)*base78 + (1310598774680844133/381700000000000000000000000000000 : ℝ)*base80 + (2232882847477/3817000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (18320853/2500000000000000000000 : ℝ)*base89 + (18320853/2500000000000000000000 : ℝ)*base91 + (18320853/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6823812572055071222871152337/954250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (526542699/50000000000000 : ℝ)*(base19) + (1237987443/100000000000000 : ℝ)*(base23) + (1449097/1000000000000 : ℝ)*(upper3) + (54275719/100000000000000 : ℝ)*(lower4) + (36112733/25000000000000 : ℝ)*(upper5) + (2236975737628859/50000000000000 : ℝ)*(major0) + (2236975737628859/50000000000000 : ℝ)*(major1) + (2236975737628859/50000000000000 : ℝ)*(major2) + (1131333721/5000000000000 : ℝ)*(sp1) + (6680565107/25000000000000 : ℝ)*(sp2) + (764110165623829/12500000000000 : ℝ)*(sp4) + (3056428822615407/50000000000000 : ℝ)*(sp5) + (152821334118569/2500000000000 : ℝ)*(sp6) + (708755346789787/25000000000000 : ℝ)*(sp7) + (708755346789787/25000000000000 : ℝ)*(f.failure) + (764110165623829/12500000000000 : ℝ)*(f.sum) + (12425024108407/9542500000000000000000000000 : ℝ)*base65 + (17307984382752216407/1908500000000000000000000000000000 : ℝ)*base68 + (23680290178608216407/1908500000000000000000000000000000 : ℝ)*base70 + (35853250421898216407/1908500000000000000000000000000000 : ℝ)*base72 + (10971455454643/9542500000000000000000000000 : ℝ)*base74 + (24696489050384216407/1908500000000000000000000000000000 : ℝ)*base76 + (17397665301596216407/1908500000000000000000000000000000 : ℝ)*base78 + (10159028367606216407/1908500000000000000000000000000000 : ℝ)*base80 + (21552824642153/9542500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (8148263/2500000000000000000000 : ℝ)*base89 + (8148263/2500000000000000000000 : ℝ)*base91 + (8148263/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1420_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14951/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5567/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14783/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1420_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1420_s5_0 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-989217103/5000000000 : ℝ)*x 0 + (2704439669/5000000000 : ℝ)*x 1 + (1049303981/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (989217103/5000000000 : ℝ)^1095 ≤ (6033671249441/50000000000000 : ℝ)^839 := by
    have hnat : (989217103 : ℕ)^1095*50000000000000^839 ≤ 6033671249441^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989217103 5000000000 6033671249441 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704439669/5000000000 : ℝ)^1095 ≤ (2802538798369/6250000000000 : ℝ)^839 := by
    have hnat : (2704439669 : ℕ)^1095*6250000000000^839 ≤ 2802538798369^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704439669 5000000000 2802538798369 6250000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049303981/2000000000 : ℝ)^1095 ≤ (43092036711373/100000000000000 : ℝ)^839 := by
    have hnat : (1049303981 : ℕ)^1095*100000000000000^839 ≤ 43092036711373^839*2000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049303981 2000000000 43092036711373 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-989217103/5000000000 : ℝ), (2704439669/5000000000 : ℝ), (1049303981/2000000000 : ℝ)] ![(6033671249441/50000000000000 : ℝ), (2802538798369/6250000000000 : ℝ), (43092036711373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-989217103/5000000000 : ℝ)|^1095 ≤ (6033671249441/50000000000000 : ℝ)^839
        have hw : |(-989217103/5000000000 : ℝ)|=(989217103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704439669/5000000000 : ℝ)|^1095 ≤ (2802538798369/6250000000000 : ℝ)^839
        have hw : |(2704439669/5000000000 : ℝ)|=(2704439669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049303981/2000000000 : ℝ)|^1095 ≤ (43092036711373/100000000000000 : ℝ)^839
        have hw : |(1049303981/2000000000 : ℝ)|=(1049303981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s5_1 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2673782781/5000000000 : ℝ)*x 0 + (-103055211/500000000 : ℝ)*x 1 + (5246519479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673782781/5000000000 : ℝ)^1095 ≤ (27611482813/62500000000 : ℝ)^839 := by
    have hnat : (2673782781 : ℕ)^1095*62500000000^839 ≤ 27611482813^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673782781 5000000000 27611482813 62500000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103055211/500000000 : ℝ)^1095 ≤ (6364797672651/50000000000000 : ℝ)^839 := by
    have hnat : (103055211 : ℕ)^1095*50000000000000^839 ≤ 6364797672651^839*500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103055211 500000000 6364797672651 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246519479/10000000000 : ℝ)^1095 ≤ (43092032144831/100000000000000 : ℝ)^839 := by
    have hnat : (5246519479 : ℕ)^1095*100000000000000^839 ≤ 43092032144831^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246519479 10000000000 43092032144831 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673782781/5000000000 : ℝ), (-103055211/500000000 : ℝ), (5246519479/10000000000 : ℝ)] ![(27611482813/62500000000 : ℝ), (6364797672651/50000000000000 : ℝ), (43092032144831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673782781/5000000000 : ℝ)|^1095 ≤ (27611482813/62500000000 : ℝ)^839
        have hw : |(2673782781/5000000000 : ℝ)|=(2673782781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103055211/500000000 : ℝ)|^1095 ≤ (6364797672651/50000000000000 : ℝ)^839
        have hw : |(-103055211/500000000 : ℝ)|=(103055211/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246519479/10000000000 : ℝ)|^1095 ≤ (43092032144831/100000000000000 : ℝ)^839
        have hw : |(5246519479/10000000000 : ℝ)|=(5246519479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s5_2 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5347565383/10000000000 : ℝ)*x 0 + (5246519623/10000000000 : ℝ)*x 1 + (-2061104267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347565383/10000000000 : ℝ)^1095 ≤ (22089185285397/50000000000000 : ℝ)^839 := by
    have hnat : (5347565383 : ℕ)^1095*50000000000000^839 ≤ 22089185285397^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347565383 10000000000 22089185285397 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246519623/10000000000 : ℝ)^1095 ≤ (861840673769/2000000000000 : ℝ)^839 := by
    have hnat : (5246519623 : ℕ)^1095*2000000000000^839 ≤ 861840673769^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246519623 10000000000 861840673769 2000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2061104267/10000000000 : ℝ)^1095 ≤ (254591914483/2000000000000 : ℝ)^839 := by
    have hnat : (2061104267 : ℕ)^1095*2000000000000^839 ≤ 254591914483^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061104267 10000000000 254591914483 2000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347565383/10000000000 : ℝ), (5246519623/10000000000 : ℝ), (-2061104267/10000000000 : ℝ)] ![(22089185285397/50000000000000 : ℝ), (861840673769/2000000000000 : ℝ), (254591914483/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347565383/10000000000 : ℝ)|^1095 ≤ (22089185285397/50000000000000 : ℝ)^839
        have hw : |(5347565383/10000000000 : ℝ)|=(5347565383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246519623/10000000000 : ℝ)|^1095 ≤ (861840673769/2000000000000 : ℝ)^839
        have hw : |(5246519623/10000000000 : ℝ)|=(5246519623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2061104267/10000000000 : ℝ)|^1095 ≤ (254591914483/2000000000000 : ℝ)^839
        have hw : |(-2061104267/10000000000 : ℝ)|=(2061104267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s5_3 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (861323059/2000000000 : ℝ)*x 0 + (2067393519/5000000000 : ℝ)*x 1 + (4484868731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861323059/2000000000 : ℝ)^1095 ≤ (16652206937419/50000000000000 : ℝ)^839 := by
    have hnat : (861323059 : ℕ)^1095*50000000000000^839 ≤ 16652206937419^839*2000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861323059 2000000000 16652206937419 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2067393519/5000000000 : ℝ)^1095 ≤ (31580816574583/100000000000000 : ℝ)^839 := by
    have hnat : (2067393519 : ℕ)^1095*100000000000000^839 ≤ 31580816574583^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067393519 5000000000 31580816574583 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4484868731/10000000000 : ℝ)^1095 ≤ (4389346191847/12500000000000 : ℝ)^839 := by
    have hnat : (4484868731 : ℕ)^1095*12500000000000^839 ≤ 4389346191847^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484868731 10000000000 4389346191847 12500000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(861323059/2000000000 : ℝ), (2067393519/5000000000 : ℝ), (4484868731/10000000000 : ℝ)] ![(16652206937419/50000000000000 : ℝ), (31580816574583/100000000000000 : ℝ), (4389346191847/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(861323059/2000000000 : ℝ)|^1095 ≤ (16652206937419/50000000000000 : ℝ)^839
        have hw : |(861323059/2000000000 : ℝ)|=(861323059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2067393519/5000000000 : ℝ)|^1095 ≤ (31580816574583/100000000000000 : ℝ)^839
        have hw : |(2067393519/5000000000 : ℝ)|=(2067393519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4484868731/10000000000 : ℝ)|^1095 ≤ (4389346191847/12500000000000 : ℝ)^839
        have hw : |(4484868731/10000000000 : ℝ)|=(4484868731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s5_4 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-49461143/250000000 : ℝ)*x 0 + (5247105979/10000000000 : ℝ)*x 1 + (2704145099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (49461143/250000000 : ℝ)^1095 ≤ (3016858539137/25000000000000 : ℝ)^839 := by
    have hnat : (49461143 : ℕ)^1095*25000000000000^839 ≤ 3016858539137^839*250000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49461143 250000000 3016858539137 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247105979/10000000000 : ℝ)^1095 ≤ (21549159643397/50000000000000 : ℝ)^839 := by
    have hnat : (5247105979 : ℕ)^1095*50000000000000^839 ≤ 21549159643397^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247105979 10000000000 21549159643397 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704145099/5000000000 : ℝ)^1095 ≤ (8966849308649/20000000000000 : ℝ)^839 := by
    have hnat : (2704145099 : ℕ)^1095*20000000000000^839 ≤ 8966849308649^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704145099 5000000000 8966849308649 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-49461143/250000000 : ℝ), (5247105979/10000000000 : ℝ), (2704145099/5000000000 : ℝ)] ![(3016858539137/25000000000000 : ℝ), (21549159643397/50000000000000 : ℝ), (8966849308649/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-49461143/250000000 : ℝ)|^1095 ≤ (3016858539137/25000000000000 : ℝ)^839
        have hw : |(-49461143/250000000 : ℝ)|=(49461143/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247105979/10000000000 : ℝ)|^1095 ≤ (21549159643397/50000000000000 : ℝ)^839
        have hw : |(5247105979/10000000000 : ℝ)|=(5247105979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704145099/5000000000 : ℝ)|^1095 ≤ (8966849308649/20000000000000 : ℝ)^839
        have hw : |(2704145099/5000000000 : ℝ)|=(2704145099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s5_5 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (663174233/1250000000 : ℝ)*x 0 + (-189933339/1000000000 : ℝ)*x 1 + (2704145099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663174233/1250000000 : ℝ)^1095 ≤ (4372421859403/10000000000000 : ℝ)^839 := by
    have hnat : (663174233 : ℕ)^1095*10000000000000^839 ≤ 4372421859403^839*1250000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663174233 1250000000 4372421859403 10000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (189933339/1000000000 : ℝ)^1095 ≤ (11441534850303/100000000000000 : ℝ)^839 := by
    have hnat : (189933339 : ℕ)^1095*100000000000000^839 ≤ 11441534850303^839*1000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189933339 1000000000 11441534850303 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704145099/5000000000 : ℝ)^1095 ≤ (8966849308649/20000000000000 : ℝ)^839 := by
    have hnat : (2704145099 : ℕ)^1095*20000000000000^839 ≤ 8966849308649^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704145099 5000000000 8966849308649 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663174233/1250000000 : ℝ), (-189933339/1000000000 : ℝ), (2704145099/5000000000 : ℝ)] ![(4372421859403/10000000000000 : ℝ), (11441534850303/100000000000000 : ℝ), (8966849308649/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663174233/1250000000 : ℝ)|^1095 ≤ (4372421859403/10000000000000 : ℝ)^839
        have hw : |(663174233/1250000000 : ℝ)|=(663174233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-189933339/1000000000 : ℝ)|^1095 ≤ (11441534850303/100000000000000 : ℝ)^839
        have hw : |(-189933339/1000000000 : ℝ)|=(189933339/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704145099/5000000000 : ℝ)|^1095 ≤ (8966849308649/20000000000000 : ℝ)^839
        have hw : |(2704145099/5000000000 : ℝ)|=(2704145099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s5_6 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1061078773/2000000000 : ℝ)*x 0 + (2704145099/5000000000 : ℝ)*x 1 + (-1899333389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061078773/2000000000 : ℝ)^1095 ≤ (43724218604787/100000000000000 : ℝ)^839 := by
    have hnat : (1061078773 : ℕ)^1095*100000000000000^839 ≤ 43724218604787^839*2000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061078773 2000000000 43724218604787 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704145099/5000000000 : ℝ)^1095 ≤ (8966849308649/20000000000000 : ℝ)^839 := by
    have hnat : (2704145099 : ℕ)^1095*20000000000000^839 ≤ 8966849308649^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704145099 5000000000 8966849308649 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1899333389/10000000000 : ℝ)^1095 ≤ (11441534842441/100000000000000 : ℝ)^839 := by
    have hnat : (1899333389 : ℕ)^1095*100000000000000^839 ≤ 11441534842441^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899333389 10000000000 11441534842441 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061078773/2000000000 : ℝ), (2704145099/5000000000 : ℝ), (-1899333389/10000000000 : ℝ)] ![(43724218604787/100000000000000 : ℝ), (8966849308649/20000000000000 : ℝ), (11441534842441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061078773/2000000000 : ℝ)|^1095 ≤ (43724218604787/100000000000000 : ℝ)^839
        have hw : |(1061078773/2000000000 : ℝ)|=(1061078773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704145099/5000000000 : ℝ)|^1095 ≤ (8966849308649/20000000000000 : ℝ)^839
        have hw : |(2704145099/5000000000 : ℝ)|=(2704145099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1899333389/10000000000 : ℝ)|^1095 ≤ (11441534842441/100000000000000 : ℝ)^839
        have hw : |(-1899333389/10000000000 : ℝ)|=(1899333389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s5_7 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (538330041/1250000000 : ℝ)*x 0 + (4483603977/10000000000 : ℝ)*x 1 + (4136058087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538330041/1250000000 : ℝ)^1095 ≤ (4163083316467/12500000000000 : ℝ)^839 := by
    have hnat : (538330041 : ℕ)^1095*12500000000000^839 ≤ 4163083316467^839*1250000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538330041 1250000000 4163083316467 12500000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4483603977/10000000000 : ℝ)^1095 ≤ (35101846050467/100000000000000 : ℝ)^839 := by
    have hnat : (4483603977 : ℕ)^1095*100000000000000^839 ≤ 35101846050467^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483603977 10000000000 35101846050467 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4136058087/10000000000 : ℝ)^1095 ≤ (31593487403483/100000000000000 : ℝ)^839 := by
    have hnat : (4136058087 : ℕ)^1095*100000000000000^839 ≤ 31593487403483^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4136058087 10000000000 31593487403483 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538330041/1250000000 : ℝ), (4483603977/10000000000 : ℝ), (4136058087/10000000000 : ℝ)] ![(4163083316467/12500000000000 : ℝ), (35101846050467/100000000000000 : ℝ), (31593487403483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538330041/1250000000 : ℝ)|^1095 ≤ (4163083316467/12500000000000 : ℝ)^839
        have hw : |(538330041/1250000000 : ℝ)|=(538330041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4483603977/10000000000 : ℝ)|^1095 ≤ (35101846050467/100000000000000 : ℝ)^839
        have hw : |(4483603977/10000000000 : ℝ)|=(4483603977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4136058087/10000000000 : ℝ)|^1095 ≤ (31593487403483/100000000000000 : ℝ)^839
        have hw : |(4136058087/10000000000 : ℝ)|=(4136058087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1420_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14783/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5659/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3689/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14783/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2823/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14783/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2823/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14783/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2823/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14783/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2823/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14783/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2823/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14783/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2823/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (2823/25000 : ℝ) ^ (4379/1024 : ℝ) ≤ (1779632887329/20000000000000000 : ℝ) := by
    have hpowers : (2823/25000 : ℝ)^4379 ≤ (1779632887329/20000000000000000 : ℝ)^1024 := by
      have hnat : (2823 : ℕ)^4379*20000000000000000^1024 ≤ 1779632887329^1024*25000^4379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2823 25000 1779632887329 20000000000000000 4379 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2823/25000 : ℝ)) (X := (1779632887329/20000000000000000 : ℝ)) (by norm_num) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14783/100000 : ℝ) ^ (4379/1024 : ℝ) ≤ (14078939100694737/50000000000000000000 : ℝ) := by
    have hpowers : (14783/100000 : ℝ)^4379 ≤ (14078939100694737/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14783 : ℕ)^4379*50000000000000000000^1024 ≤ 14078939100694737^1024*100000^4379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14783 100000 14078939100694737 50000000000000000000 4379 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14783/100000 : ℝ)) (X := (14078939100694737/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001779632887329/10000000000000000 : ℝ) ≤ (2000083225387229/2000000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (10001779632887329/10000000000000000 : ℝ)^1024 ≤ (2000083225387229/2000000000000000 : ℝ)^4379 := by
      have hnat : (10001779632887329 : ℕ)^1024*2000000000000000^4379 ≤ 2000083225387229^4379*10000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001779632887329 10000000000000000 2000083225387229 2000000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000083225387229/2000000000000000 : ℝ)) (X := (10001779632887329/10000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018528021319017237/50000000000000000000 : ℝ) ≤ (10000866407909321/10000000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (50018528021319017237/50000000000000000000 : ℝ)^1024 ≤ (10000866407909321/10000000000000000 : ℝ)^4379 := by
      have hnat : (50018528021319017237 : ℕ)^1024*10000000000000000^4379 ≤ 10000866407909321^4379*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018528021319017237 50000000000000000000 10000866407909321 10000000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000866407909321/10000000000000000 : ℝ)) (X := (50018528021319017237/50000000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014078939100694737/25000000000000000000 : ℝ) ≤ (10001316688882497/10000000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (25014078939100694737/25000000000000000000 : ℝ)^1024 ≤ (10001316688882497/10000000000000000 : ℝ)^4379 := by
      have hnat : (25014078939100694737 : ℕ)^1024*10000000000000000^4379 ≤ 10001316688882497^4379*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014078939100694737 25000000000000000000 10001316688882497 10000000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001316688882497/10000000000000000 : ℝ)) (X := (25014078939100694737/25000000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1779632887329/20000000000000000 : ℝ) ≤ ((34901283553635875411/34910000000000000000 : ℝ)+2*(56285121647/43637500000000 : ℝ)*(2823/25000 : ℝ))^(4379/1024 : ℝ) := by
    rw [show (34901283553635875411/34910000000000000000 : ℝ)+2*(56285121647/43637500000000 : ℝ)*(2823/25000 : ℝ)=(2000083225387229/2000000000000000 : ℝ) by norm_num, show 1+2*(1779632887329/20000000000000000 : ℝ)=(10001779632887329/10000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14078939100694737/50000000000000000000 : ℝ)+(1779632887329/20000000000000000 : ℝ) ≤ ((34901283553635875411/34910000000000000000 : ℝ)+(56285121647/43637500000000 : ℝ)*((14783/100000 : ℝ)+(2823/25000 : ℝ)))^(4379/1024 : ℝ) := by
    rw [show (34901283553635875411/34910000000000000000 : ℝ)+(56285121647/43637500000000 : ℝ)*((14783/100000 : ℝ)+(2823/25000 : ℝ))=(10000866407909321/10000000000000000 : ℝ) by norm_num, show 1+(14078939100694737/50000000000000000000 : ℝ)+(1779632887329/20000000000000000 : ℝ)=(50018528021319017237/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14078939100694737/50000000000000000000 : ℝ) ≤ ((34901283553635875411/34910000000000000000 : ℝ)+2*(56285121647/43637500000000 : ℝ)*(14783/100000 : ℝ))^(4379/1024 : ℝ) := by
    rw [show (34901283553635875411/34910000000000000000 : ℝ)+2*(56285121647/43637500000000 : ℝ)*(14783/100000 : ℝ)=(10001316688882497/10000000000000000 : ℝ) by norm_num, show 1+2*(14078939100694737/50000000000000000000 : ℝ)=(25014078939100694737/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34901283553635875411/34910000000000000000 : ℝ)*(X 1 0+X 2 0)+(56285121647/43637500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (2823/25000 : ℝ)) (hi := (14783/100000 : ℝ)) (c := (34901283553635875411/34910000000000000000 : ℝ)) (alpha := (56285121647/43637500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34901283553635875411/34910000000000000000 : ℝ)*(X 0 1+X 2 1)+(56285121647/43637500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (2823/25000 : ℝ)) (hi := (14783/100000 : ℝ)) (c := (34901283553635875411/34910000000000000000 : ℝ)) (alpha := (56285121647/43637500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34901283553635875411/34910000000000000000 : ℝ)*(X 0 2+X 1 2)+(56285121647/43637500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (2823/25000 : ℝ)) (hi := (14783/100000 : ℝ)) (c := (34901283553635875411/34910000000000000000 : ℝ)) (alpha := (56285121647/43637500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-989217103/5000000000 : ℝ)*X 0 0+(2704439669/5000000000 : ℝ)*X 0 1+(1049303981/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673782781/5000000000 : ℝ)*X 1 0+(-103055211/500000000 : ℝ)*X 1 1+(5246519479/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347565383/10000000000 : ℝ)*X 2 0+(5246519623/10000000000 : ℝ)*X 2 1+(-2061104267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((861323059/2000000000 : ℝ)*X 0 0+(2067393519/5000000000 : ℝ)*X 0 1+(4484868731/10000000000 : ℝ)*X 0 2+(861323059/2000000000 : ℝ)*X 1 0+(2067393519/5000000000 : ℝ)*X 1 1+(4484868731/10000000000 : ℝ)*X 1 2+(861323059/2000000000 : ℝ)*X 2 0+(2067393519/5000000000 : ℝ)*X 2 1+(4484868731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-49461143/250000000 : ℝ)*X 0 0+(5247105979/10000000000 : ℝ)*X 0 1+(2704145099/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663174233/1250000000 : ℝ)*X 1 0+(-189933339/1000000000 : ℝ)*X 1 1+(2704145099/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061078773/2000000000 : ℝ)*X 2 0+(2704145099/5000000000 : ℝ)*X 2 1+(-1899333389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((538330041/1250000000 : ℝ)*X 0 0+(4483603977/10000000000 : ℝ)*X 0 1+(4136058087/10000000000 : ℝ)*X 0 2+(538330041/1250000000 : ℝ)*X 1 0+(4483603977/10000000000 : ℝ)*X 1 1+(4136058087/10000000000 : ℝ)*X 1 2+(538330041/1250000000 : ℝ)*X 2 0+(4483603977/10000000000 : ℝ)*X 2 1+(4136058087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2905641697142729784437682291/872750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10367599/20000000000000 : ℝ)*(base21) + (62067859/100000000000000 : ℝ)*(upper2) + (24636077/100000000000000 : ℝ)*(lower4) + (41851293/100000000000000 : ℝ)*(upper5) + (4507833478678027/100000000000000 : ℝ)*(major0) + (4507833478678027/100000000000000 : ℝ)*(major1) + (4507833478678027/100000000000000 : ℝ)*(major2) + (3079587677512797/50000000000000 : ℝ)*(sp0) + (3079579567860087/50000000000000 : ℝ)*(sp1) + (769894868522523/12500000000000 : ℝ)*(sp2) + (114259384542557/4000000000000 : ℝ)*(sp3) + (810965271/5000000000000 : ℝ)*(sp5) + (8177503707/50000000000000 : ℝ)*(sp6) + (214930939/3125000000000 : ℝ)*(sp7) + (2856491491353973/100000000000000 : ℝ)*(f.failure) + (3079587677512797/50000000000000 : ℝ)*(f.sum) + (83704754052727/17455000000000000000000000000 : ℝ)*base65 + (43394823005107505903/3491000000000000000000000000000000 : ℝ)*base68 + (24844675718680505903/3491000000000000000000000000000000 : ℝ)*base70 + (8882020149386505903/3491000000000000000000000000000000 : ℝ)*base72 + (3091601018889/8727500000000000000000000000 : ℝ)*base74 + (18676406649256505903/3491000000000000000000000000000000 : ℝ)*base76 + (39983670494160505903/3491000000000000000000000000000000 : ℝ)*base78 + (22928934099380494097/3491000000000000000000000000000000 : ℝ)*base79 + (20576374034217/17455000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (9128023/10000000000000000000000 : ℝ)*base90 + (9128023/10000000000000000000000 : ℝ)*base92 + (9128023/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (922993177244797510817400063/436375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36114303/10000000000000 : ℝ)*(base19) + (24518601/6250000000000 : ℝ)*(base23) + (10835907/25000000000000 : ℝ)*(upper3) + (26409/195312500000 : ℝ)*(lower4) + (8904041/20000000000000 : ℝ)*(upper5) + (1135174861440511/25000000000000 : ℝ)*(major0) + (1135174861440511/25000000000000 : ℝ)*(major1) + (1135174861440511/25000000000000 : ℝ)*(major2) + (7571380691/100000000000000 : ℝ)*(sp1) + (813741569/10000000000000 : ℝ)*(sp2) + (124081621201347/2000000000000 : ℝ)*(sp4) + (6204073127543629/100000000000000 : ℝ)*(sp5) + (6204072530354043/100000000000000 : ℝ)*(sp6) + (575463552190429/20000000000000 : ℝ)*(sp7) + (575463552190429/20000000000000 : ℝ)*(f.failure) + (124081621201347/2000000000000 : ℝ)*(f.sum) + (6289422425243/2181875000000000000000000000 : ℝ)*base65 + (1342359592138474979/872750000000000000000000000000000 : ℝ)*base68 + (795689742961525021/872750000000000000000000000000000 : ℝ)*base69 + (3370100870416724979/872750000000000000000000000000000 : ℝ)*base72 + (56591796275681/17455000000000000000000000000 : ℝ)*base74 + (10174073649393724979/872750000000000000000000000000000 : ℝ)*base76 + (1854090192290974979/872750000000000000000000000000000 : ℝ)*base78 + (10883148822513025021/872750000000000000000000000000000 : ℝ)*base79 + (12427809710677/8727500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3136079/2000000000000000000000 : ℝ)*base90 + (3136079/2000000000000000000000 : ℝ)*base92 + (3136079/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1420_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14783/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1420_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1420_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15827/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10319/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1420_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1420_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1420_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15827/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10319/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1420_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

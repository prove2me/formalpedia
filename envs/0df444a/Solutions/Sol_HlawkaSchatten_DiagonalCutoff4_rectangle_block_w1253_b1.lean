-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1253_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:24:39.049108+00:00
-- url     : https://prove2.me/submissions/aa75978e-11f7-4965-a6d5-683ea6a55fc1

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
theorem support_rectangle_w1253_s3_0 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056077053/5000000000 : ℝ)*x 0 + (1354673913/2500000000 : ℝ)*x 1 + (2620731319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056077053/5000000000 : ℝ)^4223 ≤ (6420077196747/50000000000000 : ℝ)^3199 := by
    have hnat : (1056077053 : ℕ)^4223*50000000000000^3199 ≤ 6420077196747^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056077053 5000000000 6420077196747 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354673913/2500000000 : ℝ)^4223 ≤ (22268166883309/50000000000000 : ℝ)^3199 := by
    have hnat : (1354673913 : ℕ)^4223*50000000000000^3199 ≤ 22268166883309^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354673913 2500000000 22268166883309 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620731319/5000000000 : ℝ)^4223 ≤ (42623511823923/100000000000000 : ℝ)^3199 := by
    have hnat : (2620731319 : ℕ)^4223*100000000000000^3199 ≤ 42623511823923^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620731319 5000000000 42623511823923 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056077053/5000000000 : ℝ), (1354673913/2500000000 : ℝ), (2620731319/5000000000 : ℝ)] ![(6420077196747/50000000000000 : ℝ), (22268166883309/50000000000000 : ℝ), (42623511823923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056077053/5000000000 : ℝ)|^4223 ≤ (6420077196747/50000000000000 : ℝ)^3199
        have hw : |(-1056077053/5000000000 : ℝ)|=(1056077053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354673913/2500000000 : ℝ)|^4223 ≤ (22268166883309/50000000000000 : ℝ)^3199
        have hw : |(1354673913/2500000000 : ℝ)|=(1354673913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620731319/5000000000 : ℝ)|^4223 ≤ (42623511823923/100000000000000 : ℝ)^3199
        have hw : |(2620731319/5000000000 : ℝ)|=(2620731319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s3_1 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337811623/2500000000 : ℝ)*x 0 + (-2202549423/10000000000 : ℝ)*x 1 + (327591421/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337811623/2500000000 : ℝ)^4223 ≤ (2190298891923/5000000000000 : ℝ)^3199 := by
    have hnat : (1337811623 : ℕ)^4223*5000000000000^3199 ≤ 2190298891923^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337811623 2500000000 2190298891923 5000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2202549423/10000000000 : ℝ)^4223 ≤ (13570509278063/100000000000000 : ℝ)^3199 := by
    have hnat : (2202549423 : ℕ)^4223*100000000000000^3199 ≤ 13570509278063^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202549423 10000000000 13570509278063 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327591421/625000000 : ℝ)^4223 ≤ (10655878218989/25000000000000 : ℝ)^3199 := by
    have hnat : (327591421 : ℕ)^4223*25000000000000^3199 ≤ 10655878218989^3199*625000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327591421 625000000 10655878218989 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337811623/2500000000 : ℝ), (-2202549423/10000000000 : ℝ), (327591421/625000000 : ℝ)] ![(2190298891923/5000000000000 : ℝ), (13570509278063/100000000000000 : ℝ), (10655878218989/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337811623/2500000000 : ℝ)|^4223 ≤ (2190298891923/5000000000000 : ℝ)^3199
        have hw : |(1337811623/2500000000 : ℝ)|=(1337811623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2202549423/10000000000 : ℝ)|^4223 ≤ (13570509278063/100000000000000 : ℝ)^3199
        have hw : |(-2202549423/10000000000 : ℝ)|=(2202549423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327591421/625000000 : ℝ)|^4223 ≤ (10655878218989/25000000000000 : ℝ)^3199
        have hw : |(327591421/625000000 : ℝ)|=(327591421/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s3_2 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351246449/10000000000 : ℝ)*x 0 + (2620731601/5000000000 : ℝ)*x 1 + (-17207413/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351246449/10000000000 : ℝ)^4223 ≤ (2190298868689/5000000000000 : ℝ)^3199 := by
    have hnat : (5351246449 : ℕ)^4223*5000000000000^3199 ≤ 2190298868689^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351246449 10000000000 2190298868689 5000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620731601/5000000000 : ℝ)^4223 ≤ (10655879469621/25000000000000 : ℝ)^3199 := by
    have hnat : (2620731601 : ℕ)^4223*25000000000000^3199 ≤ 10655879469621^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620731601 5000000000 10655879469621 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17207413/78125000 : ℝ)^4223 ≤ (6785252365719/50000000000000 : ℝ)^3199 := by
    have hnat : (17207413 : ℕ)^4223*50000000000000^3199 ≤ 6785252365719^3199*78125000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17207413 78125000 6785252365719 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351246449/10000000000 : ℝ), (2620731601/5000000000 : ℝ), (-17207413/78125000 : ℝ)] ![(2190298868689/5000000000000 : ℝ), (10655879469621/25000000000000 : ℝ), (6785252365719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351246449/10000000000 : ℝ)|^4223 ≤ (2190298868689/5000000000000 : ℝ)^3199
        have hw : |(5351246449/10000000000 : ℝ)|=(5351246449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620731601/5000000000 : ℝ)|^4223 ≤ (10655879469621/25000000000000 : ℝ)^3199
        have hw : |(2620731601/5000000000 : ℝ)|=(2620731601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17207413/78125000 : ℝ)|^4223 ≤ (6785252365719/50000000000000 : ℝ)^3199
        have hw : |(-17207413/78125000 : ℝ)|=(17207413/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s3_3 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1086905273/2500000000 : ℝ)*x 0 + (521386389/1250000000 : ℝ)*x 1 + (113284573/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086905273/2500000000 : ℝ)^4223 ≤ (33300905343603/100000000000000 : ℝ)^3199 := by
    have hnat : (1086905273 : ℕ)^4223*100000000000000^3199 ≤ 33300905343603^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086905273 2500000000 33300905343603 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521386389/1250000000 : ℝ)^4223 ≤ (7881912237009/25000000000000 : ℝ)^3199 := by
    have hnat : (521386389 : ℕ)^4223*25000000000000^3199 ≤ 7881912237009^3199*1250000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521386389 1250000000 7881912237009 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113284573/250000000 : ℝ)^4223 ≤ (35171445689637/100000000000000 : ℝ)^3199 := by
    have hnat : (113284573 : ℕ)^4223*100000000000000^3199 ≤ 35171445689637^3199*250000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113284573 250000000 35171445689637 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086905273/2500000000 : ℝ), (521386389/1250000000 : ℝ), (113284573/250000000 : ℝ)] ![(33300905343603/100000000000000 : ℝ), (7881912237009/25000000000000 : ℝ), (35171445689637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086905273/2500000000 : ℝ)|^4223 ≤ (33300905343603/100000000000000 : ℝ)^3199
        have hw : |(1086905273/2500000000 : ℝ)|=(1086905273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521386389/1250000000 : ℝ)|^4223 ≤ (7881912237009/25000000000000 : ℝ)^3199
        have hw : |(521386389/1250000000 : ℝ)|=(521386389/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(113284573/250000000 : ℝ)|^4223 ≤ (35171445689637/100000000000000 : ℝ)^3199
        have hw : |(113284573/250000000 : ℝ)|=(113284573/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s3_4 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-21121683/100000000 : ℝ)*x 0 + (81907849/156250000 : ℝ)*x 1 + (1083610441/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21121683/100000000 : ℝ)^4223 ≤ (12840268302157/100000000000000 : ℝ)^3199 := by
    have hnat : (21121683 : ℕ)^4223*100000000000000^3199 ≤ 12840268302157^3199*100000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21121683 100000000 12840268302157 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81907849/156250000 : ℝ)^4223 ≤ (21315189570119/50000000000000 : ℝ)^3199 := by
    have hnat : (81907849 : ℕ)^4223*50000000000000^3199 ≤ 21315189570119^3199*156250000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81907849 156250000 21315189570119 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083610441/2000000000 : ℝ)^4223 ≤ (44529352550679/100000000000000 : ℝ)^3199 := by
    have hnat : (1083610441 : ℕ)^4223*100000000000000^3199 ≤ 44529352550679^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083610441 2000000000 44529352550679 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21121683/100000000 : ℝ), (81907849/156250000 : ℝ), (1083610441/2000000000 : ℝ)] ![(12840268302157/100000000000000 : ℝ), (21315189570119/50000000000000 : ℝ), (44529352550679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21121683/100000000 : ℝ)|^4223 ≤ (12840268302157/100000000000000 : ℝ)^3199
        have hw : |(-21121683/100000000 : ℝ)|=(21121683/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81907849/156250000 : ℝ)|^4223 ≤ (21315189570119/50000000000000 : ℝ)^3199
        have hw : |(81907849/156250000 : ℝ)|=(81907849/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083610441/2000000000 : ℝ)|^4223 ≤ (44529352550679/100000000000000 : ℝ)^3199
        have hw : |(1083610441/2000000000 : ℝ)|=(1083610441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s3_5 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652998749/5000000000 : ℝ)*x 0 + (-1012979681/5000000000 : ℝ)*x 1 + (1354513011/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652998749/5000000000 : ℝ)^4223 ≤ (21658828695063/50000000000000 : ℝ)^3199 := by
    have hnat : (2652998749 : ℕ)^4223*50000000000000^3199 ≤ 21658828695063^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652998749 5000000000 21658828695063 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1012979681/5000000000 : ℝ)^4223 ≤ (607649589721/5000000000000 : ℝ)^3199 := by
    have hnat : (1012979681 : ℕ)^4223*5000000000000^3199 ≤ 607649589721^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012979681 5000000000 607649589721 5000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354513011/2500000000 : ℝ)^4223 ≤ (11132337700977/25000000000000 : ℝ)^3199 := by
    have hnat : (1354513011 : ℕ)^4223*25000000000000^3199 ≤ 11132337700977^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354513011 2500000000 11132337700977 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652998749/5000000000 : ℝ), (-1012979681/5000000000 : ℝ), (1354513011/2500000000 : ℝ)] ![(21658828695063/50000000000000 : ℝ), (607649589721/5000000000000 : ℝ), (11132337700977/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652998749/5000000000 : ℝ)|^4223 ≤ (21658828695063/50000000000000 : ℝ)^3199
        have hw : |(2652998749/5000000000 : ℝ)|=(2652998749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1012979681/5000000000 : ℝ)|^4223 ≤ (607649589721/5000000000000 : ℝ)^3199
        have hw : |(-1012979681/5000000000 : ℝ)|=(1012979681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1354513011/2500000000 : ℝ)|^4223 ≤ (11132337700977/25000000000000 : ℝ)^3199
        have hw : |(1354513011/2500000000 : ℝ)|=(1354513011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s3_6 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326499211/2500000000 : ℝ)*x 0 + (1083610503/2000000000 : ℝ)*x 1 + (-1012979803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326499211/2500000000 : ℝ)^4223 ≤ (1353676573183/3125000000000 : ℝ)^3199 := by
    have hnat : (1326499211 : ℕ)^4223*3125000000000^3199 ≤ 1353676573183^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326499211 2500000000 1353676573183 3125000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083610503/2000000000 : ℝ)^4223 ≤ (22264677957013/50000000000000 : ℝ)^3199 := by
    have hnat : (1083610503 : ℕ)^4223*50000000000000^3199 ≤ 22264677957013^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083610503 2000000000 22264677957013 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1012979803/5000000000 : ℝ)^4223 ≤ (12152993726607/100000000000000 : ℝ)^3199 := by
    have hnat : (1012979803 : ℕ)^4223*100000000000000^3199 ≤ 12152993726607^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012979803 5000000000 12152993726607 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326499211/2500000000 : ℝ), (1083610503/2000000000 : ℝ), (-1012979803/5000000000 : ℝ)] ![(1353676573183/3125000000000 : ℝ), (22264677957013/50000000000000 : ℝ), (12152993726607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326499211/2500000000 : ℝ)|^4223 ≤ (1353676573183/3125000000000 : ℝ)^3199
        have hw : |(1326499211/2500000000 : ℝ)|=(1326499211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083610503/2000000000 : ℝ)|^4223 ≤ (22264677957013/50000000000000 : ℝ)^3199
        have hw : |(1083610503/2000000000 : ℝ)|=(1083610503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1012979803/5000000000 : ℝ)|^4223 ≤ (12152993726607/100000000000000 : ℝ)^3199
        have hw : |(-1012979803/5000000000 : ℝ)|=(1012979803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s3_7 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2173824759/5000000000 : ℝ)*x 0 + (906016337/2000000000 : ℝ)*x 1 + (2086199193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173824759/5000000000 : ℝ)^4223 ≤ (33301192770497/100000000000000 : ℝ)^3199 := by
    have hnat : (2173824759 : ℕ)^4223*100000000000000^3199 ≤ 33301192770497^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173824759 5000000000 33301192770497 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (906016337/2000000000 : ℝ)^4223 ≤ (7031622696379/20000000000000 : ℝ)^3199 := by
    have hnat : (906016337 : ℕ)^4223*20000000000000^3199 ≤ 7031622696379^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906016337 2000000000 7031622696379 20000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086199193/5000000000 : ℝ)^4223 ≤ (31540693740003/100000000000000 : ℝ)^3199 := by
    have hnat : (2086199193 : ℕ)^4223*100000000000000^3199 ≤ 31540693740003^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086199193 5000000000 31540693740003 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173824759/5000000000 : ℝ), (906016337/2000000000 : ℝ), (2086199193/5000000000 : ℝ)] ![(33301192770497/100000000000000 : ℝ), (7031622696379/20000000000000 : ℝ), (31540693740003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173824759/5000000000 : ℝ)|^4223 ≤ (33301192770497/100000000000000 : ℝ)^3199
        have hw : |(2173824759/5000000000 : ℝ)|=(2173824759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(906016337/2000000000 : ℝ)|^4223 ≤ (7031622696379/20000000000000 : ℝ)^3199
        have hw : |(906016337/2000000000 : ℝ)|=(906016337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086199193/5000000000 : ℝ)|^4223 ≤ (31540693740003/100000000000000 : ℝ)^3199
        have hw : |(2086199193/5000000000 : ℝ)|=(2086199193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1253_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8097/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1193/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10939/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14691/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8097/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1193/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8097/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1193/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8097/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1193/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8097/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1193/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8097/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1193/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8097/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1193/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1193/12500 : ℝ) ^ (8445/2048 : ℝ) ≤ (1551752917738887/25000000000000000000 : ℝ) := by
    have hpowers : (1193/12500 : ℝ)^8445 ≤ (1551752917738887/25000000000000000000 : ℝ)^2048 := by
      have hnat : (1193 : ℕ)^8445*25000000000000000000^2048 ≤ 1551752917738887^2048*12500^8445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1193 12500 1551752917738887 25000000000000000000 8445 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1193/12500 : ℝ)) (X := (1551752917738887/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (8097/50000 : ℝ) ^ (8445/2048 : ℝ) ≤ (2196868039071801/4000000000000000000 : ℝ) := by
    have hpowers : (8097/50000 : ℝ)^8445 ≤ (2196868039071801/4000000000000000000 : ℝ)^2048 := by
      have hnat : (8097 : ℕ)^8445*4000000000000000000^2048 ≤ 2196868039071801^2048*50000^8445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8097 50000 2196868039071801 4000000000000000000 8445 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8097/50000 : ℝ)) (X := (2196868039071801/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501551752917738887/12500000000000000000 : ℝ) ≤ (10000301038774693/10000000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (12501551752917738887/12500000000000000000 : ℝ)^2048 ≤ (10000301038774693/10000000000000000 : ℝ)^8445 := by
      have hnat : (12501551752917738887 : ℕ)^2048*10000000000000000^8445 ≤ 10000301038774693^8445*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501551752917738887 12500000000000000000 10000301038774693 10000000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000301038774693/10000000000000000 : ℝ)) (X := (12501551752917738887/12500000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100061128712647750573/100000000000000000000 : ℝ) ≤ (10001482091525027/10000000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (100061128712647750573/100000000000000000000 : ℝ)^2048 ≤ (10001482091525027/10000000000000000 : ℝ)^8445 := by
      have hnat : (100061128712647750573 : ℕ)^2048*10000000000000000^8445 ≤ 10001482091525027^8445*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100061128712647750573 100000000000000000000 10001482091525027 10000000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001482091525027/10000000000000000 : ℝ)) (X := (100061128712647750573/100000000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2002196868039071801/2000000000000000000 : ℝ) ≤ (10002663144275361/10000000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (2002196868039071801/2000000000000000000 : ℝ)^2048 ≤ (10002663144275361/10000000000000000 : ℝ)^8445 := by
      have hnat : (2002196868039071801 : ℕ)^2048*10000000000000000^8445 ≤ 10002663144275361^8445*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2002196868039071801 2000000000000000000 10002663144275361 10000000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002663144275361/10000000000000000 : ℝ)) (X := (2002196868039071801/2000000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1551752917738887/25000000000000000000 : ℝ) ≤ ((33239728986476666529/33250000000000000000 : ℝ)+2*(590526375167/332500000000000 : ℝ)*(1193/12500 : ℝ))^(8445/2048 : ℝ) := by
    rw [show (33239728986476666529/33250000000000000000 : ℝ)+2*(590526375167/332500000000000 : ℝ)*(1193/12500 : ℝ)=(10000301038774693/10000000000000000 : ℝ) by norm_num, show 1+2*(1551752917738887/25000000000000000000 : ℝ)=(12501551752917738887/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2196868039071801/4000000000000000000 : ℝ)+(1551752917738887/25000000000000000000 : ℝ) ≤ ((33239728986476666529/33250000000000000000 : ℝ)+(590526375167/332500000000000 : ℝ)*((8097/50000 : ℝ)+(1193/12500 : ℝ)))^(8445/2048 : ℝ) := by
    rw [show (33239728986476666529/33250000000000000000 : ℝ)+(590526375167/332500000000000 : ℝ)*((8097/50000 : ℝ)+(1193/12500 : ℝ))=(10001482091525027/10000000000000000 : ℝ) by norm_num, show 1+(2196868039071801/4000000000000000000 : ℝ)+(1551752917738887/25000000000000000000 : ℝ)=(100061128712647750573/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2196868039071801/4000000000000000000 : ℝ) ≤ ((33239728986476666529/33250000000000000000 : ℝ)+2*(590526375167/332500000000000 : ℝ)*(8097/50000 : ℝ))^(8445/2048 : ℝ) := by
    rw [show (33239728986476666529/33250000000000000000 : ℝ)+2*(590526375167/332500000000000 : ℝ)*(8097/50000 : ℝ)=(10002663144275361/10000000000000000 : ℝ) by norm_num, show 1+2*(2196868039071801/4000000000000000000 : ℝ)=(2002196868039071801/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33239728986476666529/33250000000000000000 : ℝ)*(X 1 0+X 2 0)+(590526375167/332500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (1193/12500 : ℝ)) (hi := (8097/50000 : ℝ)) (c := (33239728986476666529/33250000000000000000 : ℝ)) (alpha := (590526375167/332500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33239728986476666529/33250000000000000000 : ℝ)*(X 0 1+X 2 1)+(590526375167/332500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (1193/12500 : ℝ)) (hi := (8097/50000 : ℝ)) (c := (33239728986476666529/33250000000000000000 : ℝ)) (alpha := (590526375167/332500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33239728986476666529/33250000000000000000 : ℝ)*(X 0 2+X 1 2)+(590526375167/332500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (1193/12500 : ℝ)) (hi := (8097/50000 : ℝ)) (c := (33239728986476666529/33250000000000000000 : ℝ)) (alpha := (590526375167/332500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1056077053/5000000000 : ℝ)*X 0 0+(1354673913/2500000000 : ℝ)*X 0 1+(2620731319/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337811623/2500000000 : ℝ)*X 1 0+(-2202549423/10000000000 : ℝ)*X 1 1+(327591421/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351246449/10000000000 : ℝ)*X 2 0+(2620731601/5000000000 : ℝ)*X 2 1+(-17207413/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1086905273/2500000000 : ℝ)*X 0 0+(521386389/1250000000 : ℝ)*X 0 1+(113284573/250000000 : ℝ)*X 0 2+(1086905273/2500000000 : ℝ)*X 1 0+(521386389/1250000000 : ℝ)*X 1 1+(113284573/250000000 : ℝ)*X 1 2+(1086905273/2500000000 : ℝ)*X 2 0+(521386389/1250000000 : ℝ)*X 2 1+(113284573/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-21121683/100000000 : ℝ)*X 0 0+(81907849/156250000 : ℝ)*X 0 1+(1083610441/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652998749/5000000000 : ℝ)*X 1 0+(-1012979681/5000000000 : ℝ)*X 1 1+(1354513011/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326499211/2500000000 : ℝ)*X 2 0+(1083610503/2000000000 : ℝ)*X 2 1+(-1012979803/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2173824759/5000000000 : ℝ)*X 0 0+(906016337/2000000000 : ℝ)*X 0 1+(2086199193/5000000000 : ℝ)*X 0 2+(2173824759/5000000000 : ℝ)*X 1 0+(906016337/2000000000 : ℝ)*X 1 1+(2086199193/5000000000 : ℝ)*X 1 2+(2173824759/5000000000 : ℝ)*X 2 0+(906016337/2000000000 : ℝ)*X 2 1+(2086199193/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10931018279807042907357/1187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (258826909/20000000000000 : ℝ)*(base19) + (1687301/200000000000 : ℝ)*(base23) + (241722571/100000000000000 : ℝ)*(lower2) + (55677973/50000000000000 : ℝ)*(upper5) + (2104480322508417/50000000000000 : ℝ)*(major0) + (2104480322508417/50000000000000 : ℝ)*(major1) + (2104480322508417/50000000000000 : ℝ)*(major2) + (5642323813572987/100000000000000 : ℝ)*(sp0) + (705295065449719/12500000000000 : ℝ)*(sp1) + (5642366481304727/100000000000000 : ℝ)*(sp2) + (277554067517639/10000000000000 : ℝ)*(sp3) + (43511382239/100000000000000 : ℝ)*(sp4) + (550722293/10000000000000 : ℝ)*(sp5) + (6491533221/50000000000000 : ℝ)*(sp7) + (2775553658242833/100000000000000 : ℝ)*(f.failure) + (5642367324955227/100000000000000 : ℝ)*(f.sum) + (2815776009501/593750000000000000000000000 : ℝ)*base65 + (36253904013367799/237500000000000000000000000000000 : ℝ)*base67 + (1030798255700867799/237500000000000000000000000000000 : ℝ)*base69 + (1808333707961632201/237500000000000000000000000000000 : ℝ)*base72 + (2028012920063/296875000000000000000000000 : ℝ)*base73 + (1706915229088367799/237500000000000000000000000000000 : ℝ)*base75 + (413816666474132201/237500000000000000000000000000000 : ℝ)*base78 + (1537609439661632201/237500000000000000000000000000000 : ℝ)*base80 + (4934481479627/1187500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (41968833/5000000000000000000000 : ℝ)*base89 + (41968833/5000000000000000000000 : ℝ)*base91 + (41968833/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20243954195538885119268417/3125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2906375419/100000000000000 : ℝ)*(base19) + (2241793923/100000000000000 : ℝ)*(base23) + (8029177/12500000000000 : ℝ)*(upper3) + (4159293/4000000000000 : ℝ)*(lower4) + (11829639/2500000000000 : ℝ)*(upper5) + (1059900408716103/25000000000000 : ℝ)*(major0) + (1059900408716103/25000000000000 : ℝ)*(major1) + (1059900408716103/25000000000000 : ℝ)*(major2) + (66592323611/100000000000000 : ℝ)*(sp1) + (9565233793/20000000000000 : ℝ)*(sp2) + (1136688705117921/20000000000000 : ℝ)*(sp4) + (355210876680661/6250000000000 : ℝ)*(sp5) + (5683393457626717/100000000000000 : ℝ)*(sp6) + (1397879764101851/50000000000000 : ℝ)*(sp7) + (1397879764101851/50000000000000 : ℝ)*(f.failure) + (1136688705117921/20000000000000 : ℝ)*(f.sum) + (15072215913549/4156250000000000000000000000 : ℝ)*base66 + (3061560427853983513/831250000000000000000000000000000 : ℝ)*base68 + (1544779155577266487/831250000000000000000000000000000 : ℝ)*base69 + (2411192045466483513/831250000000000000000000000000000 : ℝ)*base72 + (120632705438821/16625000000000000000000000000 : ℝ)*base74 + (1510287381891483513/831250000000000000000000000000000 : ℝ)*base76 + (4816858616772733513/831250000000000000000000000000000 : ℝ)*base78 + (6491869551114766487/831250000000000000000000000000000 : ℝ)*base79 + (56638294285973/8312500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (10623851/2500000000000000000000 : ℝ)*base89 + (10623851/2500000000000000000000 : ℝ)*base91 + (10623851/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1253_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8097/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1193/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10939/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14691/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1253_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1253_s4_0 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1057188641/5000000000 : ℝ)*x 0 + (5397055253/10000000000 : ℝ)*x 1 + (131541149/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057188641/5000000000 : ℝ)^4223 ≤ (25715997301/200000000000 : ℝ)^3199 := by
    have hnat : (1057188641 : ℕ)^4223*200000000000^3199 ≤ 25715997301^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057188641 5000000000 25715997301 200000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397055253/10000000000 : ℝ)^4223 ≤ (22150843689021/50000000000000 : ℝ)^3199 := by
    have hnat : (5397055253 : ℕ)^4223*50000000000000^3199 ≤ 22150843689021^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397055253 10000000000 22150843689021 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131541149/250000000 : ℝ)^4223 ≤ (10710078491317/25000000000000 : ℝ)^3199 := by
    have hnat : (131541149 : ℕ)^4223*25000000000000^3199 ≤ 10710078491317^3199*250000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131541149 250000000 10710078491317 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1057188641/5000000000 : ℝ), (5397055253/10000000000 : ℝ), (131541149/250000000 : ℝ)] ![(25715997301/200000000000 : ℝ), (22150843689021/50000000000000 : ℝ), (10710078491317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1057188641/5000000000 : ℝ)|^4223 ≤ (25715997301/200000000000 : ℝ)^3199
        have hw : |(-1057188641/5000000000 : ℝ)|=(1057188641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397055253/10000000000 : ℝ)|^4223 ≤ (22150843689021/50000000000000 : ℝ)^3199
        have hw : |(5397055253/10000000000 : ℝ)|=(5397055253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131541149/250000000 : ℝ)|^4223 ≤ (10710078491317/25000000000000 : ℝ)^3199
        have hw : |(131541149/250000000 : ℝ)|=(131541149/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s4_1 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336446457/2500000000 : ℝ)*x 0 + (-2183120677/10000000000 : ℝ)*x 1 + (2630822983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336446457/2500000000 : ℝ)^4223 ≤ (10936744196223/25000000000000 : ℝ)^3199 := by
    have hnat : (1336446457 : ℕ)^4223*25000000000000^3199 ≤ 10936744196223^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336446457 2500000000 10936744196223 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2183120677/10000000000 : ℝ)^4223 ≤ (13412709171791/100000000000000 : ℝ)^3199 := by
    have hnat : (2183120677 : ℕ)^4223*100000000000000^3199 ≤ 13412709171791^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183120677 10000000000 13412709171791 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630822983/5000000000 : ℝ)^4223 ≤ (42840314029757/100000000000000 : ℝ)^3199 := by
    have hnat : (2630822983 : ℕ)^4223*100000000000000^3199 ≤ 42840314029757^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630822983 5000000000 42840314029757 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336446457/2500000000 : ℝ), (-2183120677/10000000000 : ℝ), (2630822983/5000000000 : ℝ)] ![(10936744196223/25000000000000 : ℝ), (13412709171791/100000000000000 : ℝ), (42840314029757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336446457/2500000000 : ℝ)|^4223 ≤ (10936744196223/25000000000000 : ℝ)^3199
        have hw : |(1336446457/2500000000 : ℝ)|=(1336446457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2183120677/10000000000 : ℝ)|^4223 ≤ (13412709171791/100000000000000 : ℝ)^3199
        have hw : |(-2183120677/10000000000 : ℝ)|=(2183120677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630822983/5000000000 : ℝ)|^4223 ≤ (42840314029757/100000000000000 : ℝ)^3199
        have hw : |(2630822983/5000000000 : ℝ)|=(2630822983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s4_2 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345785939/10000000000 : ℝ)*x 0 + (1052329171/2000000000 : ℝ)*x 1 + (-87324827/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345785939/10000000000 : ℝ)^4223 ≤ (21873488992011/50000000000000 : ℝ)^3199 := by
    have hnat : (5345785939 : ℕ)^4223*50000000000000^3199 ≤ 21873488992011^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345785939 10000000000 21873488992011 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052329171/2000000000 : ℝ)^4223 ≤ (42840312836701/100000000000000 : ℝ)^3199 := by
    have hnat : (1052329171 : ℕ)^4223*100000000000000^3199 ≤ 42840312836701^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052329171 2000000000 42840312836701 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87324827/400000000 : ℝ)^4223 ≤ (1341270915557/10000000000000 : ℝ)^3199 := by
    have hnat : (87324827 : ℕ)^4223*10000000000000^3199 ≤ 1341270915557^3199*400000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87324827 400000000 1341270915557 10000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345785939/10000000000 : ℝ), (1052329171/2000000000 : ℝ), (-87324827/400000000 : ℝ)] ![(21873488992011/50000000000000 : ℝ), (42840312836701/100000000000000 : ℝ), (1341270915557/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345785939/10000000000 : ℝ)|^4223 ≤ (21873488992011/50000000000000 : ℝ)^3199
        have hw : |(5345785939/10000000000 : ℝ)|=(5345785939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052329171/2000000000 : ℝ)|^4223 ≤ (42840312836701/100000000000000 : ℝ)^3199
        have hw : |(1052329171/2000000000 : ℝ)|=(1052329171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-87324827/400000000 : ℝ)|^4223 ≤ (1341270915557/10000000000000 : ℝ)^3199
        have hw : |(-87324827/400000000 : ℝ)|=(87324827/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s4_3 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (543619417/1250000000 : ℝ)*x 0 + (1053357891/2500000000 : ℝ)*x 1 + (2244351263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543619417/1250000000 : ℝ)^4223 ≤ (33314397078007/100000000000000 : ℝ)^3199 := by
    have hnat : (543619417 : ℕ)^4223*100000000000000^3199 ≤ 33314397078007^3199*1250000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543619417 1250000000 33314397078007 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053357891/2500000000 : ℝ)^4223 ≤ (31950811895983/100000000000000 : ℝ)^3199 := by
    have hnat : (1053357891 : ℕ)^4223*100000000000000^3199 ≤ 31950811895983^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053357891 2500000000 31950811895983 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2244351263/5000000000 : ℝ)^4223 ≤ (8683697750779/25000000000000 : ℝ)^3199 := by
    have hnat : (2244351263 : ℕ)^4223*25000000000000^3199 ≤ 8683697750779^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244351263 5000000000 8683697750779 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543619417/1250000000 : ℝ), (1053357891/2500000000 : ℝ), (2244351263/5000000000 : ℝ)] ![(33314397078007/100000000000000 : ℝ), (31950811895983/100000000000000 : ℝ), (8683697750779/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543619417/1250000000 : ℝ)|^4223 ≤ (33314397078007/100000000000000 : ℝ)^3199
        have hw : |(543619417/1250000000 : ℝ)|=(543619417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053357891/2500000000 : ℝ)|^4223 ≤ (31950811895983/100000000000000 : ℝ)^3199
        have hw : |(1053357891/2500000000 : ℝ)|=(1053357891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2244351263/5000000000 : ℝ)|^4223 ≤ (8683697750779/25000000000000 : ℝ)^3199
        have hw : |(2244351263/5000000000 : ℝ)|=(2244351263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s4_4 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-33037237/156250000 : ℝ)*x 0 + (328876243/625000000 : ℝ)*x 1 + (337292499/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33037237/156250000 : ℝ)^4223 ≤ (12858045902281/100000000000000 : ℝ)^3199 := by
    have hnat : (33037237 : ℕ)^4223*100000000000000^3199 ≤ 12858045902281^3199*156250000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33037237 156250000 12858045902281 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328876243/625000000 : ℝ)^4223 ≤ (21422166541787/50000000000000 : ℝ)^3199 := by
    have hnat : (328876243 : ℕ)^4223*50000000000000^3199 ≤ 21422166541787^3199*625000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328876243 625000000 21422166541787 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337292499/625000000 : ℝ)^4223 ≤ (44297620996719/100000000000000 : ℝ)^3199 := by
    have hnat : (337292499 : ℕ)^4223*100000000000000^3199 ≤ 44297620996719^3199*625000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337292499 625000000 44297620996719 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-33037237/156250000 : ℝ), (328876243/625000000 : ℝ), (337292499/625000000 : ℝ)] ![(12858045902281/100000000000000 : ℝ), (21422166541787/50000000000000 : ℝ), (44297620996719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-33037237/156250000 : ℝ)|^4223 ≤ (12858045902281/100000000000000 : ℝ)^3199
        have hw : |(-33037237/156250000 : ℝ)|=(33037237/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328876243/625000000 : ℝ)|^4223 ≤ (21422166541787/50000000000000 : ℝ)^3199
        have hw : |(328876243/625000000 : ℝ)|=(328876243/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337292499/625000000 : ℝ)|^4223 ≤ (44297620996719/100000000000000 : ℝ)^3199
        have hw : |(337292499/625000000 : ℝ)|=(337292499/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s4_5 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663901461/1250000000 : ℝ)*x 0 + (-409617327/2000000000 : ℝ)*x 1 + (1349169991/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663901461/1250000000 : ℝ)^4223 ≤ (43373860442221/100000000000000 : ℝ)^3199 := by
    have hnat : (663901461 : ℕ)^4223*100000000000000^3199 ≤ 43373860442221^3199*1250000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663901461 1250000000 43373860442221 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (409617327/2000000000 : ℝ)^4223 ≤ (12328518760821/100000000000000 : ℝ)^3199 := by
    have hnat : (409617327 : ℕ)^4223*100000000000000^3199 ≤ 12328518760821^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409617327 2000000000 12328518760821 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349169991/2500000000 : ℝ)^4223 ≤ (44297620780003/100000000000000 : ℝ)^3199 := by
    have hnat : (1349169991 : ℕ)^4223*100000000000000^3199 ≤ 44297620780003^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349169991 2500000000 44297620780003 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663901461/1250000000 : ℝ), (-409617327/2000000000 : ℝ), (1349169991/2500000000 : ℝ)] ![(43373860442221/100000000000000 : ℝ), (12328518760821/100000000000000 : ℝ), (44297620780003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663901461/1250000000 : ℝ)|^4223 ≤ (43373860442221/100000000000000 : ℝ)^3199
        have hw : |(663901461/1250000000 : ℝ)|=(663901461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-409617327/2000000000 : ℝ)|^4223 ≤ (12328518760821/100000000000000 : ℝ)^3199
        have hw : |(-409617327/2000000000 : ℝ)|=(409617327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349169991/2500000000 : ℝ)|^4223 ≤ (44297620780003/100000000000000 : ℝ)^3199
        have hw : |(1349169991/2500000000 : ℝ)|=(1349169991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s4_6 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1327802949/2500000000 : ℝ)*x 0 + (5396679881/10000000000 : ℝ)*x 1 + (-2048086601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327802949/2500000000 : ℝ)^4223 ≤ (21686930803261/50000000000000 : ℝ)^3199 := by
    have hnat : (1327802949 : ℕ)^4223*50000000000000^3199 ≤ 21686930803261^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327802949 2500000000 21686930803261 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396679881/10000000000 : ℝ)^4223 ≤ (5537202485079/12500000000000 : ℝ)^3199 := by
    have hnat : (5396679881 : ℕ)^4223*12500000000000^3199 ≤ 5537202485079^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396679881 10000000000 5537202485079 12500000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2048086601/10000000000 : ℝ)^4223 ≤ (3082129622661/25000000000000 : ℝ)^3199 := by
    have hnat : (2048086601 : ℕ)^4223*25000000000000^3199 ≤ 3082129622661^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048086601 10000000000 3082129622661 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327802949/2500000000 : ℝ), (5396679881/10000000000 : ℝ), (-2048086601/10000000000 : ℝ)] ![(21686930803261/50000000000000 : ℝ), (5537202485079/12500000000000 : ℝ), (3082129622661/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327802949/2500000000 : ℝ)|^4223 ≤ (21686930803261/50000000000000 : ℝ)^3199
        have hw : |(1327802949/2500000000 : ℝ)|=(1327802949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396679881/10000000000 : ℝ)|^4223 ≤ (5537202485079/12500000000000 : ℝ)^3199
        have hw : |(5396679881/10000000000 : ℝ)|=(5396679881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2048086601/10000000000 : ℝ)|^4223 ≤ (3082129622661/25000000000000 : ℝ)^3199
        have hw : |(-2048086601/10000000000 : ℝ)|=(2048086601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s4_7 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2174483889/5000000000 : ℝ)*x 0 + (2243971171/5000000000 : ℝ)*x 1 + (2107097347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174483889/5000000000 : ℝ)^4223 ≤ (33314522896433/100000000000000 : ℝ)^3199 := by
    have hnat : (2174483889 : ℕ)^4223*100000000000000^3199 ≤ 33314522896433^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174483889 5000000000 33314522896433 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243971171/5000000000 : ℝ)^4223 ≤ (6945405142697/20000000000000 : ℝ)^3199 := by
    have hnat : (2243971171 : ℕ)^4223*20000000000000^3199 ≤ 6945405142697^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243971171 5000000000 6945405142697 20000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107097347/5000000000 : ℝ)^4223 ≤ (15979225688981/50000000000000 : ℝ)^3199 := by
    have hnat : (2107097347 : ℕ)^4223*50000000000000^3199 ≤ 15979225688981^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107097347 5000000000 15979225688981 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174483889/5000000000 : ℝ), (2243971171/5000000000 : ℝ), (2107097347/5000000000 : ℝ)] ![(33314522896433/100000000000000 : ℝ), (6945405142697/20000000000000 : ℝ), (15979225688981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174483889/5000000000 : ℝ)|^4223 ≤ (33314522896433/100000000000000 : ℝ)^3199
        have hw : |(2174483889/5000000000 : ℝ)|=(2174483889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243971171/5000000000 : ℝ)|^4223 ≤ (6945405142697/20000000000000 : ℝ)^3199
        have hw : |(2243971171/5000000000 : ℝ)|=(2243971171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2107097347/5000000000 : ℝ)|^4223 ≤ (15979225688981/50000000000000 : ℝ)^3199
        have hw : |(2107097347/5000000000 : ℝ)|=(2107097347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1253_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14691/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10939/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1137/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7119/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14691/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10939/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14691/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10939/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14691/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10939/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14691/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10939/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14691/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10939/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14691/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10939/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10939/100000 : ℝ) ^ (8445/2048 : ℝ) ≤ (10894076979382249/100000000000000000000 : ℝ) := by
    have hpowers : (10939/100000 : ℝ)^8445 ≤ (10894076979382249/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10939 : ℕ)^8445*100000000000000000000^2048 ≤ 10894076979382249^2048*100000^8445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10939 100000 10894076979382249 100000000000000000000 8445 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10939/100000 : ℝ)) (X := (10894076979382249/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14691/100000 : ℝ) ^ (8445/2048 : ℝ) ≤ (9188550426653851/25000000000000000000 : ℝ) := by
    have hpowers : (14691/100000 : ℝ)^8445 ≤ (9188550426653851/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14691 : ℕ)^8445*25000000000000000000^2048 ≤ 9188550426653851^2048*100000^8445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14691 100000 9188550426653851 25000000000000000000 8445 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14691/100000 : ℝ)) (X := (9188550426653851/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010894076979382249/50000000000000000000 : ℝ) ≤ (10000528341710971/10000000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (50010894076979382249/50000000000000000000 : ℝ)^2048 ≤ (10000528341710971/10000000000000000 : ℝ)^8445 := by
      have hnat : (50010894076979382249 : ℕ)^2048*10000000000000000^8445 ≤ 10000528341710971^8445*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010894076979382249 50000000000000000000 10000528341710971 10000000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000528341710971/10000000000000000 : ℝ)) (X := (50010894076979382249/50000000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047648278685997653/100000000000000000000 : ℝ) ≤ (2000231062330817/2000000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (100047648278685997653/100000000000000000000 : ℝ)^2048 ≤ (2000231062330817/2000000000000000 : ℝ)^8445 := by
      have hnat : (100047648278685997653 : ℕ)^2048*2000000000000000^8445 ≤ 2000231062330817^8445*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047648278685997653 100000000000000000000 2000231062330817 2000000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000231062330817/2000000000000000 : ℝ)) (X := (100047648278685997653/100000000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509188550426653851/12500000000000000000 : ℝ) ≤ (10001782281597199/10000000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (12509188550426653851/12500000000000000000 : ℝ)^2048 ≤ (10001782281597199/10000000000000000 : ℝ)^8445 := by
      have hnat : (12509188550426653851 : ℕ)^2048*10000000000000000^8445 ≤ 10001782281597199^8445*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509188550426653851 12500000000000000000 10001782281597199 10000000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001782281597199/10000000000000000 : ℝ)) (X := (12509188550426653851/12500000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10894076979382249/100000000000000000000 : ℝ) ≤ ((375082654896841151/375200000000000000 : ℝ)+2*(313484971557/187600000000000 : ℝ)*(10939/100000 : ℝ))^(8445/2048 : ℝ) := by
    rw [show (375082654896841151/375200000000000000 : ℝ)+2*(313484971557/187600000000000 : ℝ)*(10939/100000 : ℝ)=(10000528341710971/10000000000000000 : ℝ) by norm_num, show 1+2*(10894076979382249/100000000000000000000 : ℝ)=(50010894076979382249/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9188550426653851/25000000000000000000 : ℝ)+(10894076979382249/100000000000000000000 : ℝ) ≤ ((375082654896841151/375200000000000000 : ℝ)+(313484971557/187600000000000 : ℝ)*((14691/100000 : ℝ)+(10939/100000 : ℝ)))^(8445/2048 : ℝ) := by
    rw [show (375082654896841151/375200000000000000 : ℝ)+(313484971557/187600000000000 : ℝ)*((14691/100000 : ℝ)+(10939/100000 : ℝ))=(2000231062330817/2000000000000000 : ℝ) by norm_num, show 1+(9188550426653851/25000000000000000000 : ℝ)+(10894076979382249/100000000000000000000 : ℝ)=(100047648278685997653/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9188550426653851/25000000000000000000 : ℝ) ≤ ((375082654896841151/375200000000000000 : ℝ)+2*(313484971557/187600000000000 : ℝ)*(14691/100000 : ℝ))^(8445/2048 : ℝ) := by
    rw [show (375082654896841151/375200000000000000 : ℝ)+2*(313484971557/187600000000000 : ℝ)*(14691/100000 : ℝ)=(10001782281597199/10000000000000000 : ℝ) by norm_num, show 1+2*(9188550426653851/25000000000000000000 : ℝ)=(12509188550426653851/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (375082654896841151/375200000000000000 : ℝ)*(X 1 0+X 2 0)+(313484971557/187600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (10939/100000 : ℝ)) (hi := (14691/100000 : ℝ)) (c := (375082654896841151/375200000000000000 : ℝ)) (alpha := (313484971557/187600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (375082654896841151/375200000000000000 : ℝ)*(X 0 1+X 2 1)+(313484971557/187600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (10939/100000 : ℝ)) (hi := (14691/100000 : ℝ)) (c := (375082654896841151/375200000000000000 : ℝ)) (alpha := (313484971557/187600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (375082654896841151/375200000000000000 : ℝ)*(X 0 2+X 1 2)+(313484971557/187600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (10939/100000 : ℝ)) (hi := (14691/100000 : ℝ)) (c := (375082654896841151/375200000000000000 : ℝ)) (alpha := (313484971557/187600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1057188641/5000000000 : ℝ)*X 0 0+(5397055253/10000000000 : ℝ)*X 0 1+(131541149/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336446457/2500000000 : ℝ)*X 1 0+(-2183120677/10000000000 : ℝ)*X 1 1+(2630822983/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345785939/10000000000 : ℝ)*X 2 0+(1052329171/2000000000 : ℝ)*X 2 1+(-87324827/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((543619417/1250000000 : ℝ)*X 0 0+(1053357891/2500000000 : ℝ)*X 0 1+(2244351263/5000000000 : ℝ)*X 0 2+(543619417/1250000000 : ℝ)*X 1 0+(1053357891/2500000000 : ℝ)*X 1 1+(2244351263/5000000000 : ℝ)*X 1 2+(543619417/1250000000 : ℝ)*X 2 0+(1053357891/2500000000 : ℝ)*X 2 1+(2244351263/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-33037237/156250000 : ℝ)*X 0 0+(328876243/625000000 : ℝ)*X 0 1+(337292499/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663901461/1250000000 : ℝ)*X 1 0+(-409617327/2000000000 : ℝ)*X 1 1+(1349169991/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327802949/2500000000 : ℝ)*X 2 0+(5396679881/10000000000 : ℝ)*X 2 1+(-2048086601/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2174483889/5000000000 : ℝ)*X 0 0+(2243971171/5000000000 : ℝ)*X 0 1+(2107097347/5000000000 : ℝ)*X 0 2+(2174483889/5000000000 : ℝ)*X 1 0+(2243971171/5000000000 : ℝ)*X 1 1+(2107097347/5000000000 : ℝ)*X 1 2+(2174483889/5000000000 : ℝ)*X 2 0+(2243971171/5000000000 : ℝ)*X 2 1+(2107097347/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11396242033019489177723103/4690000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (168232809/25000000000000 : ℝ)*(base19) + (126611007/20000000000000 : ℝ)*(base23) + (40091801/25000000000000 : ℝ)*(upper3) + (103290923/100000000000000 : ℝ)*(upper4) + (51442361/100000000000000 : ℝ)*(upper5) + (2754460026803949/50000000000000 : ℝ)*(major0) + (2754460026803949/50000000000000 : ℝ)*(major1) + (2754460026803949/50000000000000 : ℝ)*(major2) + (923128763099707/12500000000000 : ℝ)*(sp0) + (7385041497156379/100000000000000 : ℝ)*(sp1) + (7385041537032581/100000000000000 : ℝ)*(sp2) + (1816394577054011/50000000000000 : ℝ)*(sp3) + (301632249/2500000000000 : ℝ)*(sp4) + (1740404681/20000000000000 : ℝ)*(sp7) + (3632797856131427/100000000000000 : ℝ)*(f.failure) + (1477008434017523/20000000000000 : ℝ)*(f.sum) + (17291119156307/4690000000000000000000000000 : ℝ)*base66 + (1778405191694497/280000000000000000000000000000 : ℝ)*base67 + (1455124282414497/280000000000000000000000000000 : ℝ)*base69 + (2187201291854497/280000000000000000000000000000 : ℝ)*base71 + (36098333972557/4690000000000000000000000000 : ℝ)*base74 + (4132348002494497/280000000000000000000000000000 : ℝ)*base75 + (2331069597305503/280000000000000000000000000000 : ℝ)*base78 + (3179807905734497/280000000000000000000000000000 : ℝ)*base79 + (5499799071637/4690000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (14125427/5000000000000000000000 : ℝ)*base89 + (14125427/5000000000000000000000 : ℝ)*base91 + (14125427/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21304266651834242613752721/2345000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (377428563/25000000000000 : ℝ)*(base19) + (384477187/20000000000000 : ℝ)*(base23) + (18732717/12500000000000 : ℝ)*(upper3) + (116994079/100000000000000 : ℝ)*(lower4) + (53168967/25000000000000 : ℝ)*(upper5) + (1384888090489643/25000000000000 : ℝ)*(major0) + (1384888090489643/25000000000000 : ℝ)*(major1) + (1384888090489643/25000000000000 : ℝ)*(major2) + (39268321073/100000000000000 : ℝ)*(sp1) + (5703304859/12500000000000 : ℝ)*(sp2) + (116032912811121/1562500000000 : ℝ)*(sp4) + (371303282093821/5000000000000 : ℝ)*(sp5) + (7426058871086937/100000000000000 : ℝ)*(sp6) + (1826499000586443/50000000000000 : ℝ)*(sp7) + (1826499000586443/50000000000000 : ℝ)*(f.failure) + (116032912811121/1562500000000 : ℝ)*(f.sum) + (15831334353131/2345000000000000000000000000 : ℝ)*base65 + (1381209032747479/140000000000000000000000000000 : ℝ)*base67 + (672814308692521/140000000000000000000000000000 : ℝ)*base70 + (1037213068827479/140000000000000000000000000000 : ℝ)*base71 + (5590643267439/586250000000000000000000000 : ℝ)*base73 + (358991529027479/140000000000000000000000000000 : ℝ)*base75 + (1574283972987479/140000000000000000000000000000 : ℝ)*base77 + (170667478847479/140000000000000000000000000000 : ℝ)*base79 + (420978643609/586250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (18267557/2500000000000000000000 : ℝ)*base90 + (18267557/2500000000000000000000 : ℝ)*base92 + (18267557/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1253_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14691/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10939/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1137/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1253_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1253_s5_0 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2114807761/10000000000 : ℝ)*x 0 + (1078429309/2000000000 : ℝ)*x 1 + (5266271851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114807761/10000000000 : ℝ)^4223 ≤ (12861454571883/100000000000000 : ℝ)^3199 := by
    have hnat : (2114807761 : ℕ)^4223*100000000000000^3199 ≤ 12861454571883^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114807761 10000000000 12861454571883 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078429309/2000000000 : ℝ)^4223 ≤ (44248504209693/100000000000000 : ℝ)^3199 := by
    have hnat : (1078429309 : ℕ)^4223*100000000000000^3199 ≤ 44248504209693^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078429309 2000000000 44248504209693 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266271851/10000000000 : ℝ)^4223 ≤ (21445020602497/50000000000000 : ℝ)^3199 := by
    have hnat : (5266271851 : ℕ)^4223*50000000000000^3199 ≤ 21445020602497^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266271851 10000000000 21445020602497 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2114807761/10000000000 : ℝ), (1078429309/2000000000 : ℝ), (5266271851/10000000000 : ℝ)] ![(12861454571883/100000000000000 : ℝ), (44248504209693/100000000000000 : ℝ), (21445020602497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2114807761/10000000000 : ℝ)|^4223 ≤ (12861454571883/100000000000000 : ℝ)^3199
        have hw : |(-2114807761/10000000000 : ℝ)|=(2114807761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078429309/2000000000 : ℝ)|^4223 ≤ (44248504209693/100000000000000 : ℝ)^3199
        have hw : |(1078429309/2000000000 : ℝ)|=(1078429309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266271851/10000000000 : ℝ)|^4223 ≤ (21445020602497/50000000000000 : ℝ)^3199
        have hw : |(5266271851/10000000000 : ℝ)|=(5266271851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s5_1 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344543361/10000000000 : ℝ)*x 0 + (-435728571/2000000000 : ℝ)*x 1 + (1053254369/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344543361/10000000000 : ℝ)^4223 ≤ (4373355494549/10000000000000 : ℝ)^3199 := by
    have hnat : (5344543361 : ℕ)^4223*10000000000000^3199 ≤ 4373355494549^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344543361 10000000000 4373355494549 10000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (435728571/2000000000 : ℝ)^4223 ≤ (1672050486669/12500000000000 : ℝ)^3199 := by
    have hnat : (435728571 : ℕ)^4223*12500000000000^3199 ≤ 1672050486669^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435728571 2000000000 1672050486669 12500000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053254369/2000000000 : ℝ)^4223 ≤ (21445020570243/50000000000000 : ℝ)^3199 := by
    have hnat : (1053254369 : ℕ)^4223*50000000000000^3199 ≤ 21445020570243^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053254369 2000000000 21445020570243 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344543361/10000000000 : ℝ), (-435728571/2000000000 : ℝ), (1053254369/2000000000 : ℝ)] ![(4373355494549/10000000000000 : ℝ), (1672050486669/12500000000000 : ℝ), (21445020570243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344543361/10000000000 : ℝ)|^4223 ≤ (4373355494549/10000000000000 : ℝ)^3199
        have hw : |(5344543361/10000000000 : ℝ)|=(5344543361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-435728571/2000000000 : ℝ)|^4223 ≤ (1672050486669/12500000000000 : ℝ)^3199
        have hw : |(-435728571/2000000000 : ℝ)|=(435728571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053254369/2000000000 : ℝ)|^4223 ≤ (21445020570243/50000000000000 : ℝ)^3199
        have hw : |(1053254369/2000000000 : ℝ)|=(1053254369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s5_2 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344543339/10000000000 : ℝ)*x 0 + (2633135919/5000000000 : ℝ)*x 1 + (-1089321447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344543339/10000000000 : ℝ)^4223 ≤ (21866777353921/50000000000000 : ℝ)^3199 := by
    have hnat : (5344543339 : ℕ)^4223*50000000000000^3199 ≤ 21866777353921^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344543339 10000000000 21866777353921 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633135919/5000000000 : ℝ)^4223 ≤ (42890041065227/100000000000000 : ℝ)^3199 := by
    have hnat : (2633135919 : ℕ)^4223*100000000000000^3199 ≤ 42890041065227^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633135919 5000000000 42890041065227 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089321447/5000000000 : ℝ)^4223 ≤ (3344101052363/25000000000000 : ℝ)^3199 := by
    have hnat : (1089321447 : ℕ)^4223*25000000000000^3199 ≤ 3344101052363^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089321447 5000000000 3344101052363 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344543339/10000000000 : ℝ), (2633135919/5000000000 : ℝ), (-1089321447/5000000000 : ℝ)] ![(21866777353921/50000000000000 : ℝ), (42890041065227/100000000000000 : ℝ), (3344101052363/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344543339/10000000000 : ℝ)|^4223 ≤ (21866777353921/50000000000000 : ℝ)^3199
        have hw : |(5344543339/10000000000 : ℝ)|=(5344543339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633135919/5000000000 : ℝ)|^4223 ≤ (42890041065227/100000000000000 : ℝ)^3199
        have hw : |(2633135919/5000000000 : ℝ)|=(2633135919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1089321447/5000000000 : ℝ)|^4223 ≤ (3344101052363/25000000000000 : ℝ)^3199
        have hw : |(-1089321447/5000000000 : ℝ)|=(1089321447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s5_3 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2174604779/5000000000 : ℝ)*x 0 + (844618109/2000000000 : ℝ)*x 1 + (4478978741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174604779/5000000000 : ℝ)^4223 ≤ (33316967894313/100000000000000 : ℝ)^3199 := by
    have hnat : (2174604779 : ℕ)^4223*100000000000000^3199 ≤ 33316967894313^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174604779 5000000000 33316967894313 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (844618109/2000000000 : ℝ)^4223 ≤ (16023768960329/50000000000000 : ℝ)^3199 := by
    have hnat : (844618109 : ℕ)^4223*50000000000000^3199 ≤ 16023768960329^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844618109 2000000000 16023768960329 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4478978741/10000000000 : ℝ)^4223 ≤ (3463549417439/10000000000000 : ℝ)^3199 := by
    have hnat : (4478978741 : ℕ)^4223*10000000000000^3199 ≤ 3463549417439^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478978741 10000000000 3463549417439 10000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174604779/5000000000 : ℝ), (844618109/2000000000 : ℝ), (4478978741/10000000000 : ℝ)] ![(33316967894313/100000000000000 : ℝ), (16023768960329/50000000000000 : ℝ), (3463549417439/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174604779/5000000000 : ℝ)|^4223 ≤ (33316967894313/100000000000000 : ℝ)^3199
        have hw : |(2174604779/5000000000 : ℝ)|=(2174604779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(844618109/2000000000 : ℝ)|^4223 ≤ (16023768960329/50000000000000 : ℝ)^3199
        have hw : |(844618109/2000000000 : ℝ)|=(844618109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4478978741/10000000000 : ℝ)|^4223 ≤ (3463549417439/10000000000000 : ℝ)^3199
        have hw : |(4478978741/10000000000 : ℝ)|=(4478978741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s5_4 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-105740631/500000000 : ℝ)*x 0 + (1316648827/2500000000 : ℝ)*x 1 + (5391821917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105740631/500000000 : ℝ)^4223 ≤ (6430746790813/50000000000000 : ℝ)^3199 := by
    have hnat : (105740631 : ℕ)^4223*50000000000000^3199 ≤ 6430746790813^3199*500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105740631 500000000 6430746790813 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316648827/2500000000 : ℝ)^4223 ≤ (21446759407409/50000000000000 : ℝ)^3199 := by
    have hnat : (1316648827 : ℕ)^4223*50000000000000^3199 ≤ 21446759407409^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316648827 2500000000 21446759407409 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391821917/10000000000 : ℝ)^4223 ≤ (1382655862153/3125000000000 : ℝ)^3199 := by
    have hnat : (5391821917 : ℕ)^4223*3125000000000^3199 ≤ 1382655862153^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391821917 10000000000 1382655862153 3125000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-105740631/500000000 : ℝ), (1316648827/2500000000 : ℝ), (5391821917/10000000000 : ℝ)] ![(6430746790813/50000000000000 : ℝ), (21446759407409/50000000000000 : ℝ), (1382655862153/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-105740631/500000000 : ℝ)|^4223 ≤ (6430746790813/50000000000000 : ℝ)^3199
        have hw : |(-105740631/500000000 : ℝ)|=(105740631/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316648827/2500000000 : ℝ)|^4223 ≤ (21446759407409/50000000000000 : ℝ)^3199
        have hw : |(1316648827/2500000000 : ℝ)|=(1316648827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391821917/10000000000 : ℝ)|^4223 ≤ (1382655862153/3125000000000 : ℝ)^3199
        have hw : |(5391821917/10000000000 : ℝ)|=(5391821917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s5_5 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656201089/5000000000 : ℝ)*x 0 + (-1026546371/5000000000 : ℝ)*x 1 + (1347955539/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656201089/5000000000 : ℝ)^4223 ≤ (43386695051101/100000000000000 : ℝ)^3199 := by
    have hnat : (2656201089 : ℕ)^4223*100000000000000^3199 ≤ 43386695051101^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656201089 5000000000 43386695051101 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026546371/5000000000 : ℝ)^4223 ≤ (12368314751301/100000000000000 : ℝ)^3199 := by
    have hnat : (1026546371 : ℕ)^4223*100000000000000^3199 ≤ 12368314751301^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026546371 5000000000 12368314751301 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347955539/2500000000 : ℝ)^4223 ≤ (44244990177903/100000000000000 : ℝ)^3199 := by
    have hnat : (1347955539 : ℕ)^4223*100000000000000^3199 ≤ 44244990177903^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347955539 2500000000 44244990177903 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656201089/5000000000 : ℝ), (-1026546371/5000000000 : ℝ), (1347955539/2500000000 : ℝ)] ![(43386695051101/100000000000000 : ℝ), (12368314751301/100000000000000 : ℝ), (44244990177903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656201089/5000000000 : ℝ)|^4223 ≤ (43386695051101/100000000000000 : ℝ)^3199
        have hw : |(2656201089/5000000000 : ℝ)|=(2656201089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1026546371/5000000000 : ℝ)|^4223 ≤ (12368314751301/100000000000000 : ℝ)^3199
        have hw : |(-1026546371/5000000000 : ℝ)|=(1026546371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347955539/2500000000 : ℝ)|^4223 ≤ (44244990177903/100000000000000 : ℝ)^3199
        have hw : |(1347955539/2500000000 : ℝ)|=(1347955539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s5_6 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312401917/10000000000 : ℝ)*x 0 + (673977807/1250000000 : ℝ)*x 1 + (-2053092689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312401917/10000000000 : ℝ)^4223 ≤ (43386692237173/100000000000000 : ℝ)^3199 := by
    have hnat : (5312401917 : ℕ)^4223*100000000000000^3199 ≤ 43386692237173^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312401917 10000000000 43386692237173 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673977807/1250000000 : ℝ)^4223 ≤ (44244993427703/100000000000000 : ℝ)^3199 := by
    have hnat : (673977807 : ℕ)^4223*100000000000000^3199 ≤ 44244993427703^3199*1250000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673977807 1250000000 44244993427703 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2053092689/10000000000 : ℝ)^4223 ≤ (6184157164907/50000000000000 : ℝ)^3199 := by
    have hnat : (2053092689 : ℕ)^4223*50000000000000^3199 ≤ 6184157164907^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053092689 10000000000 6184157164907 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312401917/10000000000 : ℝ), (673977807/1250000000 : ℝ), (-2053092689/10000000000 : ℝ)] ![(43386692237173/100000000000000 : ℝ), (44244993427703/100000000000000 : ℝ), (6184157164907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312401917/10000000000 : ℝ)|^4223 ≤ (43386692237173/100000000000000 : ℝ)^3199
        have hw : |(5312401917/10000000000 : ℝ)|=(5312401917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673977807/1250000000 : ℝ)|^4223 ≤ (44244993427703/100000000000000 : ℝ)^3199
        have hw : |(673977807/1250000000 : ℝ)|=(673977807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2053092689/10000000000 : ℝ)|^4223 ≤ (6184157164907/50000000000000 : ℝ)^3199
        have hw : |(-2053092689/10000000000 : ℝ)|=(2053092689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s5_7 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4349219693/10000000000 : ℝ)*x 0 + (4478321407/10000000000 : ℝ)*x 1 + (4223750111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349219693/10000000000 : ℝ)^4223 ≤ (4164633798169/12500000000000 : ℝ)^3199 := by
    have hnat : (4349219693 : ℕ)^4223*12500000000000^3199 ≤ 4164633798169^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349219693 10000000000 4164633798169 12500000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4478321407/10000000000 : ℝ)^4223 ≤ (34628784134167/100000000000000 : ℝ)^3199 := by
    have hnat : (4478321407 : ℕ)^4223*100000000000000^3199 ≤ 34628784134167^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478321407 10000000000 34628784134167 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4223750111/10000000000 : ℝ)^4223 ≤ (32054145467247/100000000000000 : ℝ)^3199 := by
    have hnat : (4223750111 : ℕ)^4223*100000000000000^3199 ≤ 32054145467247^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223750111 10000000000 32054145467247 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349219693/10000000000 : ℝ), (4478321407/10000000000 : ℝ), (4223750111/10000000000 : ℝ)] ![(4164633798169/12500000000000 : ℝ), (34628784134167/100000000000000 : ℝ), (32054145467247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349219693/10000000000 : ℝ)|^4223 ≤ (4164633798169/12500000000000 : ℝ)^3199
        have hw : |(4349219693/10000000000 : ℝ)|=(4349219693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4478321407/10000000000 : ℝ)|^4223 ≤ (34628784134167/100000000000000 : ℝ)^3199
        have hw : |(4478321407/10000000000 : ℝ)|=(4478321407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4223750111/10000000000 : ℝ)|^4223 ≤ (32054145467247/100000000000000 : ℝ)^3199
        have hw : |(4223750111/10000000000 : ℝ)|=(4223750111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1253_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1137/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2867/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2827/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1137/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1137/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1137/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1137/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1137/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1137/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1137/10000 : ℝ) ^ (8445/2048 : ℝ) ≤ (12776005209553607/100000000000000000000 : ℝ) := by
    have hpowers : (1137/10000 : ℝ)^8445 ≤ (12776005209553607/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1137 : ℕ)^8445*100000000000000000000^2048 ≤ 12776005209553607^2048*10000^8445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1137 10000 12776005209553607 100000000000000000000 8445 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1137/10000 : ℝ)) (X := (12776005209553607/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7119/50000 : ℝ) ^ (8445/2048 : ℝ) ≤ (16150543701963121/50000000000000000000 : ℝ) := by
    have hpowers : (7119/50000 : ℝ)^8445 ≤ (16150543701963121/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7119 : ℕ)^8445*50000000000000000000^2048 ≤ 16150543701963121^2048*50000^8445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7119 50000 16150543701963121 50000000000000000000 8445 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7119/50000 : ℝ)) (X := (16150543701963121/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50012776005209553607/50000000000000000000 : ℝ) ≤ (125007745034593/125000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (50012776005209553607/50000000000000000000 : ℝ)^2048 ≤ (125007745034593/125000000000000 : ℝ)^8445 := by
      have hnat : (50012776005209553607 : ℕ)^2048*125000000000000^8445 ≤ 125007745034593^8445*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012776005209553607 50000000000000000000 125007745034593 125000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125007745034593/125000000000000 : ℝ)) (X := (50012776005209553607/50000000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045077092613479849/100000000000000000000 : ℝ) ≤ (10001092979617093/10000000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (100045077092613479849/100000000000000000000 : ℝ)^2048 ≤ (10001092979617093/10000000000000000 : ℝ)^8445 := by
      have hnat : (100045077092613479849 : ℕ)^2048*10000000000000000^8445 ≤ 10001092979617093^8445*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045077092613479849 100000000000000000000 10001092979617093 10000000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001092979617093/10000000000000000 : ℝ)) (X := (100045077092613479849/100000000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016150543701963121/25000000000000000000 : ℝ) ≤ (5000783178233373/5000000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (25016150543701963121/25000000000000000000 : ℝ)^2048 ≤ (5000783178233373/5000000000000000 : ℝ)^8445 := by
      have hnat : (25016150543701963121 : ℕ)^2048*5000000000000000^8445 ≤ 5000783178233373^8445*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016150543701963121 25000000000000000000 5000783178233373 5000000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000783178233373/5000000000000000 : ℝ)) (X := (25016150543701963121/25000000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12776005209553607/100000000000000000000 : ℝ) ≤ ((95570041437253029/95600000000000000 : ℝ)+2*(473376849653/286800000000000 : ℝ)*(1137/10000 : ℝ))^(8445/2048 : ℝ) := by
    rw [show (95570041437253029/95600000000000000 : ℝ)+2*(473376849653/286800000000000 : ℝ)*(1137/10000 : ℝ)=(125007745034593/125000000000000 : ℝ) by norm_num, show 1+2*(12776005209553607/100000000000000000000 : ℝ)=(50012776005209553607/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16150543701963121/50000000000000000000 : ℝ)+(12776005209553607/100000000000000000000 : ℝ) ≤ ((95570041437253029/95600000000000000 : ℝ)+(473376849653/286800000000000 : ℝ)*((7119/50000 : ℝ)+(1137/10000 : ℝ)))^(8445/2048 : ℝ) := by
    rw [show (95570041437253029/95600000000000000 : ℝ)+(473376849653/286800000000000 : ℝ)*((7119/50000 : ℝ)+(1137/10000 : ℝ))=(10001092979617093/10000000000000000 : ℝ) by norm_num, show 1+(16150543701963121/50000000000000000000 : ℝ)+(12776005209553607/100000000000000000000 : ℝ)=(100045077092613479849/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16150543701963121/50000000000000000000 : ℝ) ≤ ((95570041437253029/95600000000000000 : ℝ)+2*(473376849653/286800000000000 : ℝ)*(7119/50000 : ℝ))^(8445/2048 : ℝ) := by
    rw [show (95570041437253029/95600000000000000 : ℝ)+2*(473376849653/286800000000000 : ℝ)*(7119/50000 : ℝ)=(5000783178233373/5000000000000000 : ℝ) by norm_num, show 1+2*(16150543701963121/50000000000000000000 : ℝ)=(25016150543701963121/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (95570041437253029/95600000000000000 : ℝ)*(X 1 0+X 2 0)+(473376849653/286800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (1137/10000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (95570041437253029/95600000000000000 : ℝ)) (alpha := (473376849653/286800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (95570041437253029/95600000000000000 : ℝ)*(X 0 1+X 2 1)+(473376849653/286800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (1137/10000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (95570041437253029/95600000000000000 : ℝ)) (alpha := (473376849653/286800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (95570041437253029/95600000000000000 : ℝ)*(X 0 2+X 1 2)+(473376849653/286800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (1137/10000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (95570041437253029/95600000000000000 : ℝ)) (alpha := (473376849653/286800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2114807761/10000000000 : ℝ)*X 0 0+(1078429309/2000000000 : ℝ)*X 0 1+(5266271851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344543361/10000000000 : ℝ)*X 1 0+(-435728571/2000000000 : ℝ)*X 1 1+(1053254369/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344543339/10000000000 : ℝ)*X 2 0+(2633135919/5000000000 : ℝ)*X 2 1+(-1089321447/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2174604779/5000000000 : ℝ)*X 0 0+(844618109/2000000000 : ℝ)*X 0 1+(4478978741/10000000000 : ℝ)*X 0 2+(2174604779/5000000000 : ℝ)*X 1 0+(844618109/2000000000 : ℝ)*X 1 1+(4478978741/10000000000 : ℝ)*X 1 2+(2174604779/5000000000 : ℝ)*X 2 0+(844618109/2000000000 : ℝ)*X 2 1+(4478978741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-105740631/500000000 : ℝ)*X 0 0+(1316648827/2500000000 : ℝ)*X 0 1+(5391821917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656201089/5000000000 : ℝ)*X 1 0+(-1026546371/5000000000 : ℝ)*X 1 1+(1347955539/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312401917/10000000000 : ℝ)*X 2 0+(673977807/1250000000 : ℝ)*X 2 1+(-2053092689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4349219693/10000000000 : ℝ)*X 0 0+(4478321407/10000000000 : ℝ)*X 0 1+(4223750111/10000000000 : ℝ)*X 0 2+(4349219693/10000000000 : ℝ)*X 1 0+(4478321407/10000000000 : ℝ)*X 1 1+(4223750111/10000000000 : ℝ)*X 1 2+(4349219693/10000000000 : ℝ)*X 2 0+(4478321407/10000000000 : ℝ)*X 2 1+(4223750111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2517337796384315025673949/298750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1564739897/100000000000000 : ℝ)*(base19) + (289314159/20000000000000 : ℝ)*(base23) + (45678101/100000000000000 : ℝ)*(lower2) + (225103507/100000000000000 : ℝ)*(upper3) + (93303947/100000000000000 : ℝ)*(upper5) + (740780989244077/12500000000000 : ℝ)*(major0) + (740780989244077/12500000000000 : ℝ)*(major1) + (740780989244077/12500000000000 : ℝ)*(major2) + (7944454651022089/100000000000000 : ℝ)*(sp0) + (7944493774044781/100000000000000 : ℝ)*(sp1) + (7944493892213883/100000000000000 : ℝ)*(sp2) + (6106213979553/156250000000 : ℝ)*(sp3) + (4068776259/10000000000000 : ℝ)*(sp4) + (1453833257/6250000000000 : ℝ)*(sp7) + (3908000208246031/100000000000000 : ℝ)*(f.failure) + (3972247669392339/50000000000000 : ℝ)*(f.sum) + (4180746941933/3585000000000000000000000000 : ℝ)*base66 + (91904497008306301/3585000000000000000000000000000 : ℝ)*base68 + (76530126680826301/3585000000000000000000000000000 : ℝ)*base70 + (1604834811486301/3585000000000000000000000000000 : ℝ)*base72 + (30408276340403/3585000000000000000000000000 : ℝ)*base74 + (4166504376786301/3585000000000000000000000000000 : ℝ)*base76 + (51582338941146301/3585000000000000000000000000000 : ℝ)*base78 + (8175916268228699/3585000000000000000000000000000 : ℝ)*base79 + (4704872415797/896250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (29271969/5000000000000000000000 : ℝ)*base90 + (29271969/5000000000000000000000 : ℝ)*base92 + (29271969/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12602105603041306908915053/1195000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (517211437/50000000000000 : ℝ)*(base19) + (105469403/10000000000000 : ℝ)*(base23) + (165103587/50000000000000 : ℝ)*(upper3) + (1262431/781250000000 : ℝ)*(lower4) + (25705353/20000000000000 : ℝ)*(upper5) + (1489209894488219/25000000000000 : ℝ)*(major0) + (1489209894488219/25000000000000 : ℝ)*(major1) + (1489209894488219/25000000000000 : ℝ)*(major2) + (26867863353/100000000000000 : ℝ)*(sp1) + (11197064917/25000000000000 : ℝ)*(sp2) + (7985505253573179/100000000000000 : ℝ)*(sp4) + (7985477351286951/100000000000000 : ℝ)*(sp5) + (7985459410619481/100000000000000 : ℝ)*(sp6) + (3928173550809399/100000000000000 : ℝ)*(sp7) + (3928173550809399/100000000000000 : ℝ)*(f.failure) + (7985505253573179/100000000000000 : ℝ)*(f.sum) + (282958404607/224062500000000000000000000 : ℝ)*base65 + (5110996698546947/7170000000000000000000000000000 : ℝ)*base68 + (8244498438263053/7170000000000000000000000000000 : ℝ)*base69 + (56833044247356947/7170000000000000000000000000000 : ℝ)*base72 + (2476774702553/3585000000000000000000000000 : ℝ)*base74 + (154289378807603053/7170000000000000000000000000000 : ℝ)*base75 + (41826003502416947/7170000000000000000000000000000 : ℝ)*base78 + (7910530282506947/7170000000000000000000000000000 : ℝ)*base80 + (3615792843473/3585000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1787399/5000000000000000000000 : ℝ)*base89 + (1787399/5000000000000000000000 : ℝ)*base91 + (1787399/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1253_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1137/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2867/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2827/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1253_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1253_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8097/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1193/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2867/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2827/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1253_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1253_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1253_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8097/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1193/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2867/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2827/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1253_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

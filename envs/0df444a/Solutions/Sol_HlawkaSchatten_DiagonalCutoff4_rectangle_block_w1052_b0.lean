-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1052_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:56:08.502988+00:00
-- url     : https://prove2.me/submissions/5aac9782-9fd0-482e-a015-01698130edd4

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
theorem support_rectangle_w1052_s0_0 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1920625787/10000000000 : ℝ)*x 0 + (1518841491/2500000000 : ℝ)*x 1 + (238449273/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1920625787/10000000000 : ℝ)^8245 ≤ (11133536367937/100000000000000 : ℝ)^6197 := by
    have hnat : (1920625787 : ℕ)^8245*100000000000000^6197 ≤ 11133536367937^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920625787 10000000000 11133536367937 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1518841491/2500000000 : ℝ)^8245 ≤ (51528431838549/100000000000000 : ℝ)^6197 := by
    have hnat : (1518841491 : ℕ)^8245*100000000000000^6197 ≤ 51528431838549^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1518841491 2500000000 51528431838549 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (238449273/500000000 : ℝ)^8245 ≤ (37338031782793/100000000000000 : ℝ)^6197 := by
    have hnat : (238449273 : ℕ)^8245*100000000000000^6197 ≤ 37338031782793^6197*500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238449273 500000000 37338031782793 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1920625787/10000000000 : ℝ), (1518841491/2500000000 : ℝ), (238449273/500000000 : ℝ)] ![(11133536367937/100000000000000 : ℝ), (51528431838549/100000000000000 : ℝ), (37338031782793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1920625787/10000000000 : ℝ)|^8245 ≤ (11133536367937/100000000000000 : ℝ)^6197
        have hw : |(-1920625787/10000000000 : ℝ)|=(1920625787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1518841491/2500000000 : ℝ)|^8245 ≤ (51528431838549/100000000000000 : ℝ)^6197
        have hw : |(1518841491/2500000000 : ℝ)|=(1518841491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(238449273/500000000 : ℝ)|^8245 ≤ (37338031782793/100000000000000 : ℝ)^6197
        have hw : |(238449273/500000000 : ℝ)|=(238449273/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s0_1 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5521860677/10000000000 : ℝ)*x 0 + (-2673005441/10000000000 : ℝ)*x 1 + (190759423/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5521860677/10000000000 : ℝ)^8245 ≤ (45378402177599/100000000000000 : ℝ)^6197 := by
    have hnat : (5521860677 : ℕ)^8245*100000000000000^6197 ≤ 45378402177599^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521860677 10000000000 45378402177599 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2673005441/10000000000 : ℝ)^8245 ≤ (4320891209249/25000000000000 : ℝ)^6197 := by
    have hnat : (2673005441 : ℕ)^8245*25000000000000^6197 ≤ 4320891209249^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673005441 10000000000 4320891209249 25000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190759423/400000000 : ℝ)^8245 ≤ (1493521319229/4000000000000 : ℝ)^6197 := by
    have hnat : (190759423 : ℕ)^8245*4000000000000^6197 ≤ 1493521319229^6197*400000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190759423 400000000 1493521319229 4000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5521860677/10000000000 : ℝ), (-2673005441/10000000000 : ℝ), (190759423/400000000 : ℝ)] ![(45378402177599/100000000000000 : ℝ), (4320891209249/25000000000000 : ℝ), (1493521319229/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5521860677/10000000000 : ℝ)|^8245 ≤ (45378402177599/100000000000000 : ℝ)^6197
        have hw : |(5521860677/10000000000 : ℝ)|=(5521860677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2673005441/10000000000 : ℝ)|^8245 ≤ (4320891209249/25000000000000 : ℝ)^6197
        have hw : |(-2673005441/10000000000 : ℝ)|=(2673005441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(190759423/400000000 : ℝ)|^8245 ≤ (1493521319229/4000000000000 : ℝ)^6197
        have hw : |(190759423/400000000 : ℝ)|=(190759423/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s0_2 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5521860771/10000000000 : ℝ)*x 0 + (4768985627/10000000000 : ℝ)*x 1 + (-1336502629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5521860771/10000000000 : ℝ)^8245 ≤ (2268920160269/5000000000000 : ℝ)^6197 := by
    have hnat : (5521860771 : ℕ)^8245*5000000000000^6197 ≤ 2268920160269^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521860771 10000000000 2268920160269 5000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4768985627/10000000000 : ℝ)^8245 ≤ (37338033522399/100000000000000 : ℝ)^6197 := by
    have hnat : (4768985627 : ℕ)^8245*100000000000000^6197 ≤ 37338033522399^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4768985627 10000000000 37338033522399 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1336502629/5000000000 : ℝ)^8245 ≤ (8641781631337/50000000000000 : ℝ)^6197 := by
    have hnat : (1336502629 : ℕ)^8245*50000000000000^6197 ≤ 8641781631337^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336502629 5000000000 8641781631337 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5521860771/10000000000 : ℝ), (4768985627/10000000000 : ℝ), (-1336502629/5000000000 : ℝ)] ![(2268920160269/5000000000000 : ℝ), (37338033522399/100000000000000 : ℝ), (8641781631337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5521860771/10000000000 : ℝ)|^8245 ≤ (2268920160269/5000000000000 : ℝ)^6197
        have hw : |(5521860771/10000000000 : ℝ)|=(5521860771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4768985627/10000000000 : ℝ)|^8245 ≤ (37338033522399/100000000000000 : ℝ)^6197
        have hw : |(4768985627/10000000000 : ℝ)|=(4768985627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1336502629/5000000000 : ℝ)|^8245 ≤ (8641781631337/50000000000000 : ℝ)^6197
        have hw : |(-1336502629/5000000000 : ℝ)|=(1336502629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s0_3 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4208370849/10000000000 : ℝ)*x 0 + (1562811957/5000000000 : ℝ)*x 1 + (5678834089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4208370849/10000000000 : ℝ)^8245 ≤ (6322957441407/20000000000000 : ℝ)^6197 := by
    have hnat : (4208370849 : ℕ)^8245*20000000000000^6197 ≤ 6322957441407^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4208370849 10000000000 6322957441407 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1562811957/5000000000 : ℝ)^8245 ≤ (21282475894903/100000000000000 : ℝ)^6197 := by
    have hnat : (1562811957 : ℕ)^8245*100000000000000^6197 ≤ 21282475894903^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1562811957 5000000000 21282475894903 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5678834089/10000000000 : ℝ)^8245 ≤ (9420547378121/20000000000000 : ℝ)^6197 := by
    have hnat : (5678834089 : ℕ)^8245*20000000000000^6197 ≤ 9420547378121^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5678834089 10000000000 9420547378121 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4208370849/10000000000 : ℝ), (1562811957/5000000000 : ℝ), (5678834089/10000000000 : ℝ)] ![(6322957441407/20000000000000 : ℝ), (21282475894903/100000000000000 : ℝ), (9420547378121/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4208370849/10000000000 : ℝ)|^8245 ≤ (6322957441407/20000000000000 : ℝ)^6197
        have hw : |(4208370849/10000000000 : ℝ)|=(4208370849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1562811957/5000000000 : ℝ)|^8245 ≤ (21282475894903/100000000000000 : ℝ)^6197
        have hw : |(1562811957/5000000000 : ℝ)|=(1562811957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5678834089/10000000000 : ℝ)|^8245 ≤ (9420547378121/20000000000000 : ℝ)^6197
        have hw : |(5678834089/10000000000 : ℝ)|=(5678834089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s0_4 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-96302041/500000000 : ℝ)*x 0 + (4802722691/10000000000 : ℝ)*x 1 + (1510112679/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (96302041/500000000 : ℝ)^8245 ≤ (2793829918597/25000000000000 : ℝ)^6197 := by
    have hnat : (96302041 : ℕ)^8245*25000000000000^6197 ≤ 2793829918597^6197*500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96302041 500000000 2793829918597 25000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4802722691/10000000000 : ℝ)^8245 ≤ (37689876149561/100000000000000 : ℝ)^6197 := by
    have hnat : (4802722691 : ℕ)^8245*100000000000000^6197 ≤ 37689876149561^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4802722691 10000000000 37689876149561 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1510112679/2500000000 : ℝ)^8245 ≤ (25567402081863/50000000000000 : ℝ)^6197 := by
    have hnat : (1510112679 : ℕ)^8245*50000000000000^6197 ≤ 25567402081863^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510112679 2500000000 25567402081863 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-96302041/500000000 : ℝ), (4802722691/10000000000 : ℝ), (1510112679/2500000000 : ℝ)] ![(2793829918597/25000000000000 : ℝ), (37689876149561/100000000000000 : ℝ), (25567402081863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-96302041/500000000 : ℝ)|^8245 ≤ (2793829918597/25000000000000 : ℝ)^6197
        have hw : |(-96302041/500000000 : ℝ)|=(96302041/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4802722691/10000000000 : ℝ)|^8245 ≤ (37689876149561/100000000000000 : ℝ)^6197
        have hw : |(4802722691/10000000000 : ℝ)|=(4802722691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1510112679/2500000000 : ℝ)|^8245 ≤ (25567402081863/50000000000000 : ℝ)^6197
        have hw : |(1510112679/2500000000 : ℝ)|=(1510112679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s0_5 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (161480191/312500000 : ℝ)*x 0 + (-1401541641/10000000000 : ℝ)*x 1 + (1510112569/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (161480191/312500000 : ℝ)^8245 ≤ (20772068147209/50000000000000 : ℝ)^6197 := by
    have hnat : (161480191 : ℕ)^8245*50000000000000^6197 ≤ 20772068147209^6197*312500000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161480191 312500000 20772068147209 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1401541641/10000000000 : ℝ)^8245 ≤ (3660532240877/50000000000000 : ℝ)^6197 := by
    have hnat : (1401541641 : ℕ)^8245*50000000000000^6197 ≤ 3660532240877^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401541641 10000000000 3660532240877 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1510112569/2500000000 : ℝ)^8245 ≤ (51134799207979/100000000000000 : ℝ)^6197 := by
    have hnat : (1510112569 : ℕ)^8245*100000000000000^6197 ≤ 51134799207979^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510112569 2500000000 51134799207979 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(161480191/312500000 : ℝ), (-1401541641/10000000000 : ℝ), (1510112569/2500000000 : ℝ)] ![(20772068147209/50000000000000 : ℝ), (3660532240877/50000000000000 : ℝ), (51134799207979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(161480191/312500000 : ℝ)|^8245 ≤ (20772068147209/50000000000000 : ℝ)^6197
        have hw : |(161480191/312500000 : ℝ)|=(161480191/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1401541641/10000000000 : ℝ)|^8245 ≤ (3660532240877/50000000000000 : ℝ)^6197
        have hw : |(-1401541641/10000000000 : ℝ)|=(1401541641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1510112569/2500000000 : ℝ)|^8245 ≤ (51134799207979/100000000000000 : ℝ)^6197
        have hw : |(1510112569/2500000000 : ℝ)|=(1510112569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s0_6 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2583683651/5000000000 : ℝ)*x 0 + (3020224721/5000000000 : ℝ)*x 1 + (-1401541161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2583683651/5000000000 : ℝ)^8245 ≤ (41544149023487/100000000000000 : ℝ)^6197 := by
    have hnat : (2583683651 : ℕ)^8245*100000000000000^6197 ≤ 41544149023487^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583683651 5000000000 41544149023487 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3020224721/5000000000 : ℝ)^8245 ≤ (51134789814587/100000000000000 : ℝ)^6197 := by
    have hnat : (3020224721 : ℕ)^8245*100000000000000^6197 ≤ 51134789814587^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3020224721 5000000000 51134789814587 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1401541161/10000000000 : ℝ)^8245 ≤ (1830265286453/25000000000000 : ℝ)^6197 := by
    have hnat : (1401541161 : ℕ)^8245*25000000000000^6197 ≤ 1830265286453^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401541161 10000000000 1830265286453 25000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2583683651/5000000000 : ℝ), (3020224721/5000000000 : ℝ), (-1401541161/10000000000 : ℝ)] ![(41544149023487/100000000000000 : ℝ), (51134789814587/100000000000000 : ℝ), (1830265286453/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2583683651/5000000000 : ℝ)|^8245 ≤ (41544149023487/100000000000000 : ℝ)^6197
        have hw : |(2583683651/5000000000 : ℝ)|=(2583683651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3020224721/5000000000 : ℝ)|^8245 ≤ (51134789814587/100000000000000 : ℝ)^6197
        have hw : |(3020224721/5000000000 : ℝ)|=(3020224721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1401541161/10000000000 : ℝ)|^8245 ≤ (1830265286453/25000000000000 : ℝ)^6197
        have hw : |(-1401541161/10000000000 : ℝ)|=(1401541161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s0_7 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2109478023/5000000000 : ℝ)*x 0 + (2806448063/5000000000 : ℝ)*x 1 + (3193863457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109478023/5000000000 : ℝ)^8245 ≤ (15860315419493/50000000000000 : ℝ)^6197 := by
    have hnat : (2109478023 : ℕ)^8245*50000000000000^6197 ≤ 15860315419493^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109478023 5000000000 15860315419493 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2806448063/5000000000 : ℝ)^8245 ≤ (2898529461259/6250000000000 : ℝ)^6197 := by
    have hnat : (2806448063 : ℕ)^8245*6250000000000^6197 ≤ 2898529461259^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2806448063 5000000000 2898529461259 6250000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3193863457/10000000000 : ℝ)^8245 ≤ (10951448886677/50000000000000 : ℝ)^6197 := by
    have hnat : (3193863457 : ℕ)^8245*50000000000000^6197 ≤ 10951448886677^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3193863457 10000000000 10951448886677 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2109478023/5000000000 : ℝ), (2806448063/5000000000 : ℝ), (3193863457/10000000000 : ℝ)] ![(15860315419493/50000000000000 : ℝ), (2898529461259/6250000000000 : ℝ), (10951448886677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2109478023/5000000000 : ℝ)|^8245 ≤ (15860315419493/50000000000000 : ℝ)^6197
        have hw : |(2109478023/5000000000 : ℝ)|=(2109478023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2806448063/5000000000 : ℝ)|^8245 ≤ (2898529461259/6250000000000 : ℝ)^6197
        have hw : |(2806448063/5000000000 : ℝ)|=(2806448063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3193863457/10000000000 : ℝ)|^8245 ≤ (10951448886677/50000000000000 : ℝ)^6197
        have hw : |(3193863457/10000000000 : ℝ)|=(3193863457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1052_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73860383/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (37/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7041/25000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (2061/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2061 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2061*1^512 ≤ 0^512*1^2061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2061 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2061/512 : ℝ) ≤ (2501128585297624471/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2061 ≤ (2501128585297624471/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2061*100000000000000000000^512 ≤ 2501128585297624471^512*5^2061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2501128585297624471 100000000000000000000 2061 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2501128585297624471/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2061/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2061 := by
      have hnat : (1 : ℕ)^512*1^2061 ≤ 1^2061*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (102501128585297624471/100000000000000000000 : ℝ) ≤ (2515389550472503/2500000000000000 : ℝ) ^ (2061/512 : ℝ) := by
    have hpowers : (102501128585297624471/100000000000000000000 : ℝ)^512 ≤ (2515389550472503/2500000000000000 : ℝ)^2061 := by
      have hnat : (102501128585297624471 : ℕ)^512*2500000000000000^2061 ≤ 2515389550472503^2061*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102501128585297624471 100000000000000000000 2515389550472503 2500000000000000 512 2061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2515389550472503/2500000000000000 : ℝ)) (X := (102501128585297624471/100000000000000000000 : ℝ)) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (52501128585297624471/50000000000000000000 : ℝ) ≤ (1265389550472503/1250000000000000 : ℝ) ^ (2061/512 : ℝ) := by
    have hpowers : (52501128585297624471/50000000000000000000 : ℝ)^512 ≤ (1265389550472503/1250000000000000 : ℝ)^2061 := by
      have hnat : (52501128585297624471 : ℕ)^512*1250000000000000^2061 ≤ 1265389550472503^2061*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52501128585297624471 50000000000000000000 1265389550472503 1250000000000000 512 2061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1265389550472503/1250000000000000 : ℝ)) (X := (52501128585297624471/50000000000000000000 : ℝ)) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(15389550472503/1000000000000000 : ℝ)*(0 : ℝ))^(2061/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(15389550472503/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2501128585297624471/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(15389550472503/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2061/512 : ℝ) := by
    rw [show (1 : ℝ)+(15389550472503/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2515389550472503/2500000000000000 : ℝ) by norm_num, show 1+(2501128585297624471/100000000000000000000 : ℝ)+(0 : ℝ)=(102501128585297624471/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2501128585297624471/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(15389550472503/1000000000000000 : ℝ)*(2/5 : ℝ))^(2061/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(15389550472503/1000000000000000 : ℝ)*(2/5 : ℝ)=(1265389550472503/1250000000000000 : ℝ) by norm_num, show 1+2*(2501128585297624471/100000000000000000000 : ℝ)=(52501128585297624471/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(15389550472503/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2061/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15389550472503/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(15389550472503/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2061/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15389550472503/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(15389550472503/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2061/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15389550472503/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1920625787/10000000000 : ℝ)*X 0 0+(1518841491/2500000000 : ℝ)*X 0 1+(238449273/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5521860677/10000000000 : ℝ)*X 1 0+(-2673005441/10000000000 : ℝ)*X 1 1+(190759423/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5521860771/10000000000 : ℝ)*X 2 0+(4768985627/10000000000 : ℝ)*X 2 1+(-1336502629/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4208370849/10000000000 : ℝ)*X 0 0+(1562811957/5000000000 : ℝ)*X 0 1+(5678834089/10000000000 : ℝ)*X 0 2+(4208370849/10000000000 : ℝ)*X 1 0+(1562811957/5000000000 : ℝ)*X 1 1+(5678834089/10000000000 : ℝ)*X 1 2+(4208370849/10000000000 : ℝ)*X 2 0+(1562811957/5000000000 : ℝ)*X 2 1+(5678834089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-96302041/500000000 : ℝ)*X 0 0+(4802722691/10000000000 : ℝ)*X 0 1+(1510112679/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((161480191/312500000 : ℝ)*X 1 0+(-1401541641/10000000000 : ℝ)*X 1 1+(1510112569/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2583683651/5000000000 : ℝ)*X 2 0+(3020224721/5000000000 : ℝ)*X 2 1+(-1401541161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2109478023/5000000000 : ℝ)*X 0 0+(2806448063/5000000000 : ℝ)*X 0 1+(3193863457/10000000000 : ℝ)*X 0 2+(2109478023/5000000000 : ℝ)*X 1 0+(2806448063/5000000000 : ℝ)*X 1 1+(3193863457/10000000000 : ℝ)*X 1 2+(2109478023/5000000000 : ℝ)*X 2 0+(2806448063/5000000000 : ℝ)*X 2 1+(3193863457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (286871252147359586937021/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1833769/25000000000000 : ℝ)*(base1) + (1443681203/100000000000000 : ℝ)*(base19) + (1342174609/100000000000000 : ℝ)*(base23) + (2863439/2500000000000 : ℝ)*(base24) + (167322187/50000000000000 : ℝ)*(upper3) + (578575194430723/100000000000000 : ℝ)*(major0) + (578575194430723/100000000000000 : ℝ)*(major1) + (578575194430723/100000000000000 : ℝ)*(major2) + (765478703565453/100000000000000 : ℝ)*(sp0) + (765480601852669/100000000000000 : ℝ)*(sp1) + (765480588821703/100000000000000 : ℝ)*(sp2) + (195832718016963/50000000000000 : ℝ)*(sp3) + (669860699/20000000000000 : ℝ)*(sp4) + (677177767/25000000000000 : ℝ)*(sp7) + (391668152080069/100000000000000 : ℝ)*(f.failure) + (47842627845867/6250000000000 : ℝ)*(f.sum) + (39078144640331/50000000000000000000000000000 : ℝ)*base66 + (505358816990331/100000000000000000000000000000 : ℝ)*base68 + (509292379090331/100000000000000000000000000000 : ℝ)*base70 + (337534971590331/100000000000000000000000000000 : ℝ)*base72 + (28464095240331/50000000000000000000000000000 : ℝ)*base74 + (183980766590331/100000000000000000000000000000 : ℝ)*base76 + (1413418409669/100000000000000000000000000000 : ℝ)*base77 + (44170421390331/100000000000000000000000000000 : ℝ)*base80 + (76117194109669/50000000000000000000000000000 : ℝ)*base81 + (6993573/5000000000000000000000 : ℝ)*base90 + (6993573/5000000000000000000000 : ℝ)*base92 + (6993573/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31189279200152772566553/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (140759063/100000000000000 : ℝ)*(base1) + (1403218883/100000000000000 : ℝ)*(base19) + (6239727/390625000000 : ℝ)*(base23) + (71813411/25000000000000 : ℝ)*(base45) + (147784107/100000000000000 : ℝ)*(upper3) + (55900017/25000000000000 : ℝ)*(upper5) + (122131757202883/20000000000000 : ℝ)*(major0) + (122131757202883/20000000000000 : ℝ)*(major1) + (122131757202883/20000000000000 : ℝ)*(major2) + (117958519/100000000000000 : ℝ)*(sp2) + (80793027261713/10000000000000 : ℝ)*(sp4) + (50495545539949/6250000000000 : ℝ)*(sp5) + (201982104132359/25000000000000 : ℝ)*(sp6) + (413387091483163/100000000000000 : ℝ)*(sp7) + (206693616121113/50000000000000 : ℝ)*(f.failure) + (201982532964517/25000000000000 : ℝ)*(f.sum) + (601785153851/10000000000000000000000000000 : ℝ)*base66 + (21681816466149/20000000000000000000000000000 : ℝ)*base67 + (122969492406149/20000000000000000000000000000 : ℝ)*base69 + (71286561706149/20000000000000000000000000000 : ℝ)*base71 + (25820372113851/10000000000000000000000000000 : ℝ)*base74 + (323072498326149/20000000000000000000000000000 : ℝ)*base75 + (85260017446149/20000000000000000000000000000 : ℝ)*base77 + (206688130566149/20000000000000000000000000000 : ℝ)*base79 + (35731619896149/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (5566279/2500000000000000000000 : ℝ)*base89 + (5566279/2500000000000000000000 : ℝ)*base91 + (5566279/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1052_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73860383/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (37/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7041/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1052_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1052_s1_0 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-266469661/1250000000 : ℝ)*x 0 + (1145253559/2000000000 : ℝ)*x 1 + (4982862281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266469661/1250000000 : ℝ)^8245 ≤ (2558157817187/20000000000000 : ℝ)^6197 := by
    have hnat : (266469661 : ℕ)^8245*20000000000000^6197 ≤ 2558157817187^6197*1250000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266469661 1250000000 2558157817187 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1145253559/2000000000 : ℝ)^8245 ≤ (11906729412897/25000000000000 : ℝ)^6197 := by
    have hnat : (1145253559 : ℕ)^8245*25000000000000^6197 ≤ 11906729412897^6197*2000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145253559 2000000000 11906729412897 25000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4982862281/10000000000 : ℝ)^8245 ≤ (39582293245181/100000000000000 : ℝ)^6197 := by
    have hnat : (4982862281 : ℕ)^8245*100000000000000^6197 ≤ 39582293245181^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4982862281 10000000000 39582293245181 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-266469661/1250000000 : ℝ), (1145253559/2000000000 : ℝ), (4982862281/10000000000 : ℝ)] ![(2558157817187/20000000000000 : ℝ), (11906729412897/25000000000000 : ℝ), (39582293245181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-266469661/1250000000 : ℝ)|^8245 ≤ (2558157817187/20000000000000 : ℝ)^6197
        have hw : |(-266469661/1250000000 : ℝ)|=(266469661/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1145253559/2000000000 : ℝ)|^8245 ≤ (11906729412897/25000000000000 : ℝ)^6197
        have hw : |(1145253559/2000000000 : ℝ)|=(1145253559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4982862281/10000000000 : ℝ)|^8245 ≤ (39582293245181/100000000000000 : ℝ)^6197
        have hw : |(4982862281/10000000000 : ℝ)|=(4982862281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s1_1 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1356021777/2500000000 : ℝ)*x 0 + (-2534837927/10000000000 : ℝ)*x 1 + (4982862607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1356021777/2500000000 : ℝ)^8245 ≤ (44312501437933/100000000000000 : ℝ)^6197 := by
    have hnat : (1356021777 : ℕ)^8245*100000000000000^6197 ≤ 44312501437933^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356021777 2500000000 44312501437933 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2534837927/10000000000 : ℝ)^8245 ≤ (16105201854729/100000000000000 : ℝ)^6197 := by
    have hnat : (2534837927 : ℕ)^8245*100000000000000^6197 ≤ 16105201854729^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2534837927 10000000000 16105201854729 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4982862607/10000000000 : ℝ)^8245 ≤ (19791148345327/50000000000000 : ℝ)^6197 := by
    have hnat : (4982862607 : ℕ)^8245*50000000000000^6197 ≤ 19791148345327^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4982862607 10000000000 19791148345327 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1356021777/2500000000 : ℝ), (-2534837927/10000000000 : ℝ), (4982862607/10000000000 : ℝ)] ![(44312501437933/100000000000000 : ℝ), (16105201854729/100000000000000 : ℝ), (19791148345327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1356021777/2500000000 : ℝ)|^8245 ≤ (44312501437933/100000000000000 : ℝ)^6197
        have hw : |(1356021777/2500000000 : ℝ)|=(1356021777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2534837927/10000000000 : ℝ)|^8245 ≤ (16105201854729/100000000000000 : ℝ)^6197
        have hw : |(-2534837927/10000000000 : ℝ)|=(2534837927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4982862607/10000000000 : ℝ)|^8245 ≤ (19791148345327/50000000000000 : ℝ)^6197
        have hw : |(4982862607/10000000000 : ℝ)|=(4982862607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s1_2 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5424087561/10000000000 : ℝ)*x 0 + (2491431031/5000000000 : ℝ)*x 1 + (-1267419013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5424087561/10000000000 : ℝ)^8245 ≤ (2769531647613/6250000000000 : ℝ)^6197 := by
    have hnat : (5424087561 : ℕ)^8245*6250000000000^6197 ≤ 2769531647613^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424087561 10000000000 2769531647613 6250000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2491431031/5000000000 : ℝ)^8245 ≤ (4947786366323/12500000000000 : ℝ)^6197 := by
    have hnat : (2491431031 : ℕ)^8245*12500000000000^6197 ≤ 4947786366323^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2491431031 5000000000 4947786366323 12500000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1267419013/5000000000 : ℝ)^8245 ≤ (16105202691603/100000000000000 : ℝ)^6197 := by
    have hnat : (1267419013 : ℕ)^8245*100000000000000^6197 ≤ 16105202691603^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1267419013 5000000000 16105202691603 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5424087561/10000000000 : ℝ), (2491431031/5000000000 : ℝ), (-1267419013/5000000000 : ℝ)] ![(2769531647613/6250000000000 : ℝ), (4947786366323/12500000000000 : ℝ), (16105202691603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5424087561/10000000000 : ℝ)|^8245 ≤ (2769531647613/6250000000000 : ℝ)^6197
        have hw : |(5424087561/10000000000 : ℝ)|=(5424087561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2491431031/5000000000 : ℝ)|^8245 ≤ (4947786366323/12500000000000 : ℝ)^6197
        have hw : |(2491431031/5000000000 : ℝ)|=(2491431031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1267419013/5000000000 : ℝ)|^8245 ≤ (16105202691603/100000000000000 : ℝ)^6197
        have hw : |(-1267419013/5000000000 : ℝ)|=(1267419013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s1_3 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (67577463/156250000 : ℝ)*x 0 + (146392883/400000000 : ℝ)*x 1 + (5112743861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67577463/156250000 : ℝ)^8245 ≤ (16392690488343/50000000000000 : ℝ)^6197 := by
    have hnat : (67577463 : ℕ)^8245*50000000000000^6197 ≤ 16392690488343^6197*156250000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67577463 156250000 16392690488343 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (146392883/400000000 : ℝ)^8245 ≤ (3281717170611/12500000000000 : ℝ)^6197 := by
    have hnat : (146392883 : ℕ)^8245*12500000000000^6197 ≤ 3281717170611^6197*400000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146392883 400000000 3281717170611 12500000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5112743861/10000000000 : ℝ)^8245 ≤ (1638435265659/4000000000000 : ℝ)^6197 := by
    have hnat : (5112743861 : ℕ)^8245*4000000000000^6197 ≤ 1638435265659^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5112743861 10000000000 1638435265659 4000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67577463/156250000 : ℝ), (146392883/400000000 : ℝ), (5112743861/10000000000 : ℝ)] ![(16392690488343/50000000000000 : ℝ), (3281717170611/12500000000000 : ℝ), (1638435265659/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67577463/156250000 : ℝ)|^8245 ≤ (16392690488343/50000000000000 : ℝ)^6197
        have hw : |(67577463/156250000 : ℝ)|=(67577463/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(146392883/400000000 : ℝ)|^8245 ≤ (3281717170611/12500000000000 : ℝ)^6197
        have hw : |(146392883/400000000 : ℝ)|=(146392883/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5112743861/10000000000 : ℝ)|^8245 ≤ (1638435265659/4000000000000 : ℝ)^6197
        have hw : |(5112743861/10000000000 : ℝ)|=(5112743861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s1_4 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-533175397/2500000000 : ℝ)*x 0 + (4993364847/10000000000 : ℝ)*x 1 + (5715548889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533175397/2500000000 : ℝ)^8245 ≤ (1279832802997/10000000000000 : ℝ)^6197 := by
    have hnat : (533175397 : ℕ)^8245*10000000000000^6197 ≤ 1279832802997^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533175397 2500000000 1279832802997 10000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4993364847/10000000000 : ℝ)^8245 ≤ (39693332825593/100000000000000 : ℝ)^6197 := by
    have hnat : (4993364847 : ℕ)^8245*100000000000000^6197 ≤ 39693332825593^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4993364847 10000000000 39693332825593 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5715548889/10000000000 : ℝ)^8245 ≤ (23754169564137/50000000000000 : ℝ)^6197 := by
    have hnat : (5715548889 : ℕ)^8245*50000000000000^6197 ≤ 23754169564137^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5715548889 10000000000 23754169564137 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-533175397/2500000000 : ℝ), (4993364847/10000000000 : ℝ), (5715548889/10000000000 : ℝ)] ![(1279832802997/10000000000000 : ℝ), (39693332825593/100000000000000 : ℝ), (23754169564137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-533175397/2500000000 : ℝ)|^8245 ≤ (1279832802997/10000000000000 : ℝ)^6197
        have hw : |(-533175397/2500000000 : ℝ)|=(533175397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4993364847/10000000000 : ℝ)|^8245 ≤ (39693332825593/100000000000000 : ℝ)^6197
        have hw : |(4993364847/10000000000 : ℝ)|=(4993364847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5715548889/10000000000 : ℝ)|^8245 ≤ (23754169564137/50000000000000 : ℝ)^6197
        have hw : |(5715548889/10000000000 : ℝ)|=(5715548889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s1_5 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5234372873/10000000000 : ℝ)*x 0 + (-360429967/2000000000 : ℝ)*x 1 + (5715550261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5234372873/10000000000 : ℝ)^8245 ≤ (42262418651401/100000000000000 : ℝ)^6197 := by
    have hnat : (5234372873 : ℕ)^8245*100000000000000^6197 ≤ 42262418651401^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234372873 10000000000 42262418651401 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (360429967/2000000000 : ℝ)^8245 ≤ (319663344753/3125000000000 : ℝ)^6197 := by
    have hnat : (360429967 : ℕ)^8245*3125000000000^6197 ≤ 319663344753^6197*2000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360429967 2000000000 319663344753 3125000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5715550261/10000000000 : ℝ)^8245 ≤ (9501670860281/20000000000000 : ℝ)^6197 := by
    have hnat : (5715550261 : ℕ)^8245*20000000000000^6197 ≤ 9501670860281^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5715550261 10000000000 9501670860281 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5234372873/10000000000 : ℝ), (-360429967/2000000000 : ℝ), (5715550261/10000000000 : ℝ)] ![(42262418651401/100000000000000 : ℝ), (319663344753/3125000000000 : ℝ), (9501670860281/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5234372873/10000000000 : ℝ)|^8245 ≤ (42262418651401/100000000000000 : ℝ)^6197
        have hw : |(5234372873/10000000000 : ℝ)|=(5234372873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-360429967/2000000000 : ℝ)|^8245 ≤ (319663344753/3125000000000 : ℝ)^6197
        have hw : |(-360429967/2000000000 : ℝ)|=(360429967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5715550261/10000000000 : ℝ)|^8245 ≤ (9501670860281/20000000000000 : ℝ)^6197
        have hw : |(5715550261/10000000000 : ℝ)|=(5715550261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s1_6 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1308592731/2500000000 : ℝ)*x 0 + (5715552403/10000000000 : ℝ)*x 1 + (-1802149471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1308592731/2500000000 : ℝ)^8245 ≤ (5282799714323/12500000000000 : ℝ)^6197 := by
    have hnat : (1308592731 : ℕ)^8245*12500000000000^6197 ≤ 5282799714323^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308592731 2500000000 5282799714323 12500000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5715552403/10000000000 : ℝ)^8245 ≤ (4750837799007/10000000000000 : ℝ)^6197 := by
    have hnat : (5715552403 : ℕ)^8245*10000000000000^6197 ≤ 4750837799007^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5715552403 10000000000 4750837799007 10000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1802149471/10000000000 : ℝ)^8245 ≤ (5114612141587/50000000000000 : ℝ)^6197 := by
    have hnat : (1802149471 : ℕ)^8245*50000000000000^6197 ≤ 5114612141587^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1802149471 10000000000 5114612141587 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1308592731/2500000000 : ℝ), (5715552403/10000000000 : ℝ), (-1802149471/10000000000 : ℝ)] ![(5282799714323/12500000000000 : ℝ), (4750837799007/10000000000000 : ℝ), (5114612141587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1308592731/2500000000 : ℝ)|^8245 ≤ (5282799714323/12500000000000 : ℝ)^6197
        have hw : |(1308592731/2500000000 : ℝ)|=(1308592731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5715552403/10000000000 : ℝ)|^8245 ≤ (4750837799007/10000000000000 : ℝ)^6197
        have hw : |(5715552403/10000000000 : ℝ)|=(5715552403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1802149471/10000000000 : ℝ)|^8245 ≤ (5114612141587/50000000000000 : ℝ)^6197
        have hw : |(-1802149471/10000000000 : ℝ)|=(1802149471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s1_7 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2163399889/5000000000 : ℝ)*x 0 + (5092214083/10000000000 : ℝ)*x 1 + (3680768377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163399889/5000000000 : ℝ)^8245 ≤ (8200990420023/25000000000000 : ℝ)^6197 := by
    have hnat : (2163399889 : ℕ)^8245*25000000000000^6197 ≤ 8200990420023^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163399889 5000000000 8200990420023 25000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5092214083/10000000000 : ℝ)^8245 ≤ (2546387253339/6250000000000 : ℝ)^6197 := by
    have hnat : (5092214083 : ℕ)^8245*6250000000000^6197 ≤ 2546387253339^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5092214083 10000000000 2546387253339 6250000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3680768377/10000000000 : ℝ)^8245 ≤ (41334128519/156250000000 : ℝ)^6197 := by
    have hnat : (3680768377 : ℕ)^8245*156250000000^6197 ≤ 41334128519^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3680768377 10000000000 41334128519 156250000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163399889/5000000000 : ℝ), (5092214083/10000000000 : ℝ), (3680768377/10000000000 : ℝ)] ![(8200990420023/25000000000000 : ℝ), (2546387253339/6250000000000 : ℝ), (41334128519/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163399889/5000000000 : ℝ)|^8245 ≤ (8200990420023/25000000000000 : ℝ)^6197
        have hw : |(2163399889/5000000000 : ℝ)|=(2163399889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5092214083/10000000000 : ℝ)|^8245 ≤ (2546387253339/6250000000000 : ℝ)^6197
        have hw : |(5092214083/10000000000 : ℝ)|=(5092214083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3680768377/10000000000 : ℝ)|^8245 ≤ (41334128519/156250000000 : ℝ)^6197
        have hw : |(3680768377/10000000000 : ℝ)|=(3680768377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1052_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73860383/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7041/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (37/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (513/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10429/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7041/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (37/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7041/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (37/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7041/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (37/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7041/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (37/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7041/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (37/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7041/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (37/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (37/100000 : ℝ) ^ (2061/512 : ℝ) ≤ (1533457/100000000000000000000 : ℝ) := by
    have hpowers : (37/100000 : ℝ)^2061 ≤ (1533457/100000000000000000000 : ℝ)^512 := by
      have hnat : (37 : ℕ)^2061*100000000000000000000^512 ≤ 1533457^512*100000^2061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37 100000 1533457 100000000000000000000 2061 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37/100000 : ℝ)) (X := (1533457/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7041/25000 : ℝ) ^ (2061/512 : ℝ) ≤ (152315726578273243/25000000000000000000 : ℝ) := by
    have hpowers : (7041/25000 : ℝ)^2061 ≤ (152315726578273243/25000000000000000000 : ℝ)^512 := by
      have hnat : (7041 : ℕ)^2061*25000000000000000000^512 ≤ 152315726578273243^512*25000^2061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7041 25000 152315726578273243 25000000000000000000 2061 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7041/25000 : ℝ)) (X := (152315726578273243/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000000001533457/50000000000000000000 : ℝ) ≤ (10000000000000077/10000000000000000 : ℝ) ^ (2061/512 : ℝ) := by
    have hpowers : (50000000000001533457/50000000000000000000 : ℝ)^512 ≤ (10000000000000077/10000000000000000 : ℝ)^2061 := by
      have hnat : (50000000000001533457 : ℕ)^512*10000000000000000^2061 ≤ 10000000000000077^2061*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000000001533457 50000000000000000000 10000000000000077 10000000000000000 512 2061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000000077/10000000000000000 : ℝ)) (X := (50000000000001533457/50000000000000000000 : ℝ)) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100609262906314626429/100000000000000000000 : ℝ) ≤ (10015100967154837/10000000000000000 : ℝ) ^ (2061/512 : ℝ) := by
    have hpowers : (100609262906314626429/100000000000000000000 : ℝ)^512 ≤ (10015100967154837/10000000000000000 : ℝ)^2061 := by
      have hnat : (100609262906314626429 : ℕ)^512*10000000000000000^2061 ≤ 10015100967154837^2061*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100609262906314626429 100000000000000000000 10015100967154837 10000000000000000 512 2061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015100967154837/10000000000000000 : ℝ)) (X := (100609262906314626429/100000000000000000000 : ℝ)) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12652315726578273243/12500000000000000000 : ℝ) ≤ (10030201934309597/10000000000000000 : ℝ) ^ (2061/512 : ℝ) := by
    have hpowers : (12652315726578273243/12500000000000000000 : ℝ)^512 ≤ (10030201934309597/10000000000000000 : ℝ)^2061 := by
      have hnat : (12652315726578273243 : ℕ)^512*10000000000000000^2061 ≤ 10030201934309597^2061*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12652315726578273243 12500000000000000000 10030201934309597 10000000000000000 512 2061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10030201934309597/10000000000000000 : ℝ)) (X := (12652315726578273243/12500000000000000000 : ℝ)) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1533457/100000000000000000000 : ℝ) ≤ ((281268882528432713539/281270000000000000000 : ℝ)+2*(377524178869/70317500000000 : ℝ)*(37/100000 : ℝ))^(2061/512 : ℝ) := by
    rw [show (281268882528432713539/281270000000000000000 : ℝ)+2*(377524178869/70317500000000 : ℝ)*(37/100000 : ℝ)=(10000000000000077/10000000000000000 : ℝ) by norm_num, show 1+2*(1533457/100000000000000000000 : ℝ)=(50000000000001533457/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(152315726578273243/25000000000000000000 : ℝ)+(1533457/100000000000000000000 : ℝ) ≤ ((281268882528432713539/281270000000000000000 : ℝ)+(377524178869/70317500000000 : ℝ)*((7041/25000 : ℝ)+(37/100000 : ℝ)))^(2061/512 : ℝ) := by
    rw [show (281268882528432713539/281270000000000000000 : ℝ)+(377524178869/70317500000000 : ℝ)*((7041/25000 : ℝ)+(37/100000 : ℝ))=(10015100967154837/10000000000000000 : ℝ) by norm_num, show 1+(152315726578273243/25000000000000000000 : ℝ)+(1533457/100000000000000000000 : ℝ)=(100609262906314626429/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(152315726578273243/25000000000000000000 : ℝ) ≤ ((281268882528432713539/281270000000000000000 : ℝ)+2*(377524178869/70317500000000 : ℝ)*(7041/25000 : ℝ))^(2061/512 : ℝ) := by
    rw [show (281268882528432713539/281270000000000000000 : ℝ)+2*(377524178869/70317500000000 : ℝ)*(7041/25000 : ℝ)=(10030201934309597/10000000000000000 : ℝ) by norm_num, show 1+2*(152315726578273243/25000000000000000000 : ℝ)=(12652315726578273243/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (281268882528432713539/281270000000000000000 : ℝ)*(X 1 0+X 2 0)+(377524178869/70317500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2061/512 : ℝ)) (lo := (37/100000 : ℝ)) (hi := (7041/25000 : ℝ)) (c := (281268882528432713539/281270000000000000000 : ℝ)) (alpha := (377524178869/70317500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (281268882528432713539/281270000000000000000 : ℝ)*(X 0 1+X 2 1)+(377524178869/70317500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2061/512 : ℝ)) (lo := (37/100000 : ℝ)) (hi := (7041/25000 : ℝ)) (c := (281268882528432713539/281270000000000000000 : ℝ)) (alpha := (377524178869/70317500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (281268882528432713539/281270000000000000000 : ℝ)*(X 0 2+X 1 2)+(377524178869/70317500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2061/512 : ℝ)) (lo := (37/100000 : ℝ)) (hi := (7041/25000 : ℝ)) (c := (281268882528432713539/281270000000000000000 : ℝ)) (alpha := (377524178869/70317500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-266469661/1250000000 : ℝ)*X 0 0+(1145253559/2000000000 : ℝ)*X 0 1+(4982862281/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1356021777/2500000000 : ℝ)*X 1 0+(-2534837927/10000000000 : ℝ)*X 1 1+(4982862607/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5424087561/10000000000 : ℝ)*X 2 0+(2491431031/5000000000 : ℝ)*X 2 1+(-1267419013/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((67577463/156250000 : ℝ)*X 0 0+(146392883/400000000 : ℝ)*X 0 1+(5112743861/10000000000 : ℝ)*X 0 2+(67577463/156250000 : ℝ)*X 1 0+(146392883/400000000 : ℝ)*X 1 1+(5112743861/10000000000 : ℝ)*X 1 2+(67577463/156250000 : ℝ)*X 2 0+(146392883/400000000 : ℝ)*X 2 1+(5112743861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-533175397/2500000000 : ℝ)*X 0 0+(4993364847/10000000000 : ℝ)*X 0 1+(5715548889/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5234372873/10000000000 : ℝ)*X 1 0+(-360429967/2000000000 : ℝ)*X 1 1+(5715550261/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1308592731/2500000000 : ℝ)*X 2 0+(5715552403/10000000000 : ℝ)*X 2 1+(-1802149471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2163399889/5000000000 : ℝ)*X 0 0+(5092214083/10000000000 : ℝ)*X 0 1+(3680768377/10000000000 : ℝ)*X 0 2+(2163399889/5000000000 : ℝ)*X 1 0+(5092214083/10000000000 : ℝ)*X 1 1+(3680768377/10000000000 : ℝ)*X 1 2+(2163399889/5000000000 : ℝ)*X 2 0+(5092214083/10000000000 : ℝ)*X 2 1+(3680768377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (103494296394604766964709598451/14063500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60374469/50000000000000 : ℝ)*(base1) + (817122751/50000000000000 : ℝ)*(base19) + (873294839/50000000000000 : ℝ)*(base23) + (17539697/10000000000000 : ℝ)*(upper3) + (172908981/100000000000000 : ℝ)*(upper5) + (1016726982966601/100000000000000 : ℝ)*(major0) + (1016726982966601/100000000000000 : ℝ)*(major1) + (1016726982966601/100000000000000 : ℝ)*(major2) + (8407306213097/625000000000 : ℝ)*(sp0) + (5254593020257/390625000000 : ℝ)*(sp1) + (84073481302601/6250000000000 : ℝ)*(sp2) + (172068026269587/25000000000000 : ℝ)*(sp3) + (1071760589/12500000000000 : ℝ)*(sp4) + (4047372247/100000000000000 : ℝ)*(sp7) + (172069068299883/25000000000000 : ℝ)*(f.failure) + (672588723715647/50000000000000 : ℝ)*(f.sum) + (15669845903/2812700000000000000000000000 : ℝ)*base65 + (120691509180541489061/28127000000000000000000000000000000 : ℝ)*base68 + (328995480010331489061/28127000000000000000000000000000000 : ℝ)*base70 + (224342276743312489061/28127000000000000000000000000000000 : ℝ)*base72 + (45550505674193/28127000000000000000000000000 : ℝ)*base73 + (112921437412643489061/28127000000000000000000000000000000 : ℝ)*base76 + (105667967531392489061/28127000000000000000000000000000000 : ℝ)*base78 + (188378423854997489061/28127000000000000000000000000000000 : ℝ)*base80 + (37318638870937/5625400000000000000000000000 : ℝ)*base82 + (4735189/1250000000000000000000 : ℝ)*base89 + (4735189/1250000000000000000000 : ℝ)*base91 + (4735189/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8454594668769572580582566649/14063500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36545587/2000000000000 : ℝ)*(base19) + (1747155389/100000000000000 : ℝ)*(base23) + (10535809/5000000000000 : ℝ)*(upper2) + (300715493/100000000000000 : ℝ)*(upper3) + (224067087/50000000000000 : ℝ)*(upper5) + (1046590049513499/100000000000000 : ℝ)*(major0) + (1046590049513499/100000000000000 : ℝ)*(major1) + (1046590049513499/100000000000000 : ℝ)*(major2) + (2293447759/25000000000000 : ℝ)*(sp1) + (10081306687/100000000000000 : ℝ)*(sp2) + (173085989559419/12500000000000 : ℝ)*(sp4) + (692338457702483/50000000000000 : ℝ)*(sp5) + (346169022003319/25000000000000 : ℝ)*(sp6) + (708492162512547/100000000000000 : ℝ)*(sp7) + (708492162512547/100000000000000 : ℝ)*(f.failure) + (173085989559419/12500000000000 : ℝ)*(f.sum) + (65591352670559/14063500000000000000000000000 : ℝ)*base65 + (82908990525310437039/28127000000000000000000000000000000 : ℝ)*base68 + (241828216950764437039/28127000000000000000000000000000000 : ℝ)*base70 + (96863223515139437039/28127000000000000000000000000000000 : ℝ)*base72 + (15387727488767/5625400000000000000000000000 : ℝ)*base73 + (48840517638114437039/28127000000000000000000000000000000 : ℝ)*base76 + (4318536855714437039/28127000000000000000000000000000000 : ℝ)*base78 + (92982947788416437039/28127000000000000000000000000000000 : ℝ)*base80 + (76808408895799/28127000000000000000000000000 : ℝ)*base82 + (13725501/5000000000000000000000 : ℝ)*base89 + (13725501/5000000000000000000000 : ℝ)*base91 + (13725501/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1052_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73860383/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7041/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (37/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (513/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10429/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1052_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1052_s2_0 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2189974921/10000000000 : ℝ)*x 0 + (1382206959/2500000000 : ℝ)*x 1 + (5143381409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189974921/10000000000 : ℝ)^8245 ≤ (3314406975203/25000000000000 : ℝ)^6197 := by
    have hnat : (2189974921 : ℕ)^8245*25000000000000^6197 ≤ 3314406975203^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189974921 10000000000 3314406975203 25000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1382206959/2500000000 : ℝ)^8245 ≤ (45454595893227/100000000000000 : ℝ)^6197 := by
    have hnat : (1382206959 : ℕ)^8245*100000000000000^6197 ≤ 45454595893227^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382206959 2500000000 45454595893227 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5143381409/10000000000 : ℝ)^8245 ≤ (5160972023597/12500000000000 : ℝ)^6197 := by
    have hnat : (5143381409 : ℕ)^8245*12500000000000^6197 ≤ 5160972023597^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143381409 10000000000 5160972023597 12500000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2189974921/10000000000 : ℝ), (1382206959/2500000000 : ℝ), (5143381409/10000000000 : ℝ)] ![(3314406975203/25000000000000 : ℝ), (45454595893227/100000000000000 : ℝ), (5160972023597/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2189974921/10000000000 : ℝ)|^8245 ≤ (3314406975203/25000000000000 : ℝ)^6197
        have hw : |(-2189974921/10000000000 : ℝ)|=(2189974921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1382206959/2500000000 : ℝ)|^8245 ≤ (45454595893227/100000000000000 : ℝ)^6197
        have hw : |(1382206959/2500000000 : ℝ)|=(1382206959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5143381409/10000000000 : ℝ)|^8245 ≤ (5160972023597/12500000000000 : ℝ)^6197
        have hw : |(5143381409/10000000000 : ℝ)|=(5143381409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s2_1 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5377832857/10000000000 : ℝ)*x 0 + (-478221907/2000000000 : ℝ)*x 1 + (5143382837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377832857/10000000000 : ℝ)^8245 ≤ (8762090313561/20000000000000 : ℝ)^6197 := by
    have hnat : (5377832857 : ℕ)^8245*20000000000000^6197 ≤ 8762090313561^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377832857 10000000000 8762090313561 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (478221907/2000000000 : ℝ)^8245 ≤ (7450878485537/50000000000000 : ℝ)^6197 := by
    have hnat : (478221907 : ℕ)^8245*50000000000000^6197 ≤ 7450878485537^6197*2000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478221907 2000000000 7450878485537 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5143382837/10000000000 : ℝ)^8245 ≤ (645121741253/1562500000000 : ℝ)^6197 := by
    have hnat : (5143382837 : ℕ)^8245*1562500000000^6197 ≤ 645121741253^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143382837 10000000000 645121741253 1562500000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377832857/10000000000 : ℝ), (-478221907/2000000000 : ℝ), (5143382837/10000000000 : ℝ)] ![(8762090313561/20000000000000 : ℝ), (7450878485537/50000000000000 : ℝ), (645121741253/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377832857/10000000000 : ℝ)|^8245 ≤ (8762090313561/20000000000000 : ℝ)^6197
        have hw : |(5377832857/10000000000 : ℝ)|=(5377832857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-478221907/2000000000 : ℝ)|^8245 ≤ (7450878485537/50000000000000 : ℝ)^6197
        have hw : |(-478221907/2000000000 : ℝ)|=(478221907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5143382837/10000000000 : ℝ)|^8245 ≤ (645121741253/1562500000000 : ℝ)^6197
        have hw : |(5143382837/10000000000 : ℝ)|=(5143382837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s2_2 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (268891663/500000000 : ℝ)*x 0 + (2571691081/5000000000 : ℝ)*x 1 + (-1195554939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268891663/500000000 : ℝ)^8245 ≤ (1752418237433/4000000000000 : ℝ)^6197 := by
    have hnat : (268891663 : ℕ)^8245*4000000000000^6197 ≤ 1752418237433^6197*500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268891663 500000000 1752418237433 4000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2571691081/5000000000 : ℝ)^8245 ≤ (20643892115507/50000000000000 : ℝ)^6197 := by
    have hnat : (2571691081 : ℕ)^8245*50000000000000^6197 ≤ 20643892115507^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571691081 5000000000 20643892115507 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1195554939/5000000000 : ℝ)^8245 ≤ (298035196303/2000000000000 : ℝ)^6197 := by
    have hnat : (1195554939 : ℕ)^8245*2000000000000^6197 ≤ 298035196303^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195554939 5000000000 298035196303 2000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268891663/500000000 : ℝ), (2571691081/5000000000 : ℝ), (-1195554939/5000000000 : ℝ)] ![(1752418237433/4000000000000 : ℝ), (20643892115507/50000000000000 : ℝ), (298035196303/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268891663/500000000 : ℝ)|^8245 ≤ (1752418237433/4000000000000 : ℝ)^6197
        have hw : |(268891663/500000000 : ℝ)|=(268891663/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2571691081/5000000000 : ℝ)|^8245 ≤ (20643892115507/50000000000000 : ℝ)^6197
        have hw : |(2571691081/5000000000 : ℝ)|=(2571691081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1195554939/5000000000 : ℝ)|^8245 ≤ (298035196303/2000000000000 : ℝ)^6197
        have hw : |(-1195554939/5000000000 : ℝ)|=(1195554939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s2_3 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364640317/10000000000 : ℝ)*x 0 + (1001105943/2500000000 : ℝ)*x 1 + (594717749/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364640317/10000000000 : ℝ)^8245 ≤ (6637243114773/20000000000000 : ℝ)^6197 := by
    have hnat : (4364640317 : ℕ)^8245*20000000000000^6197 ≤ 6637243114773^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364640317 10000000000 6637243114773 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1001105943/2500000000 : ℝ)^8245 ≤ (5918565600831/20000000000000 : ℝ)^6197 := by
    have hnat : (1001105943 : ℕ)^8245*20000000000000^6197 ≤ 5918565600831^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001105943 2500000000 5918565600831 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (594717749/1250000000 : ℝ)^8245 ≤ (9305239101667/25000000000000 : ℝ)^6197 := by
    have hnat : (594717749 : ℕ)^8245*25000000000000^6197 ≤ 9305239101667^6197*1250000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594717749 1250000000 9305239101667 25000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364640317/10000000000 : ℝ), (1001105943/2500000000 : ℝ), (594717749/1250000000 : ℝ)] ![(6637243114773/20000000000000 : ℝ), (5918565600831/20000000000000 : ℝ), (9305239101667/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364640317/10000000000 : ℝ)|^8245 ≤ (6637243114773/20000000000000 : ℝ)^6197
        have hw : |(4364640317/10000000000 : ℝ)|=(4364640317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1001105943/2500000000 : ℝ)|^8245 ≤ (5918565600831/20000000000000 : ℝ)^6197
        have hw : |(1001105943/2500000000 : ℝ)|=(1001105943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(594717749/1250000000 : ℝ)|^8245 ≤ (9305239101667/25000000000000 : ℝ)^6197
        have hw : |(594717749/1250000000 : ℝ)|=(594717749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s2_4 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2190105519/10000000000 : ℝ)*x 0 + (1286553489/2500000000 : ℝ)*x 1 + (172686421/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2190105519/10000000000 : ℝ)^8245 ≤ (13258679806137/100000000000000 : ℝ)^6197 := by
    have hnat : (2190105519 : ℕ)^8245*100000000000000^6197 ≤ 13258679806137^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190105519 10000000000 13258679806137 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1286553489/2500000000 : ℝ)^8245 ≤ (41318031286801/100000000000000 : ℝ)^6197 := by
    have hnat : (1286553489 : ℕ)^8245*100000000000000^6197 ≤ 41318031286801^6197*2500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286553489 2500000000 41318031286801 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (172686421/312500000 : ℝ)^8245 ≤ (9084657776521/20000000000000 : ℝ)^6197 := by
    have hnat : (172686421 : ℕ)^8245*20000000000000^6197 ≤ 9084657776521^6197*312500000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172686421 312500000 9084657776521 20000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2190105519/10000000000 : ℝ), (1286553489/2500000000 : ℝ), (172686421/312500000 : ℝ)] ![(13258679806137/100000000000000 : ℝ), (41318031286801/100000000000000 : ℝ), (9084657776521/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2190105519/10000000000 : ℝ)|^8245 ≤ (13258679806137/100000000000000 : ℝ)^6197
        have hw : |(-2190105519/10000000000 : ℝ)|=(2190105519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1286553489/2500000000 : ℝ)|^8245 ≤ (41318031286801/100000000000000 : ℝ)^6197
        have hw : |(1286553489/2500000000 : ℝ)|=(1286553489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(172686421/312500000 : ℝ)|^8245 ≤ (9084657776521/20000000000000 : ℝ)^6197
        have hw : |(172686421/312500000 : ℝ)|=(172686421/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s2_5 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (211225567/400000000 : ℝ)*x 0 + (-1004263627/5000000000 : ℝ)*x 1 + (2762982771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211225567/400000000 : ℝ)^8245 ≤ (42760151436043/100000000000000 : ℝ)^6197 := by
    have hnat : (211225567 : ℕ)^8245*100000000000000^6197 ≤ 42760151436043^6197*400000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211225567 400000000 42760151436043 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004263627/5000000000 : ℝ)^8245 ≤ (11816558901791/100000000000000 : ℝ)^6197 := by
    have hnat : (1004263627 : ℕ)^8245*100000000000000^6197 ≤ 11816558901791^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004263627 5000000000 11816558901791 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2762982771/5000000000 : ℝ)^8245 ≤ (22711644824081/50000000000000 : ℝ)^6197 := by
    have hnat : (2762982771 : ℕ)^8245*50000000000000^6197 ≤ 22711644824081^6197*5000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2762982771 5000000000 22711644824081 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211225567/400000000 : ℝ), (-1004263627/5000000000 : ℝ), (2762982771/5000000000 : ℝ)] ![(42760151436043/100000000000000 : ℝ), (11816558901791/100000000000000 : ℝ), (22711644824081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211225567/400000000 : ℝ)|^8245 ≤ (42760151436043/100000000000000 : ℝ)^6197
        have hw : |(211225567/400000000 : ℝ)|=(211225567/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1004263627/5000000000 : ℝ)|^8245 ≤ (11816558901791/100000000000000 : ℝ)^6197
        have hw : |(-1004263627/5000000000 : ℝ)|=(1004263627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2762982771/5000000000 : ℝ)|^8245 ≤ (22711644824081/50000000000000 : ℝ)^6197
        have hw : |(2762982771/5000000000 : ℝ)|=(2762982771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s2_6 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (330039963/625000000 : ℝ)*x 0 + (276298269/500000000 : ℝ)*x 1 + (-2008527159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330039963/625000000 : ℝ)^8245 ≤ (21380076973149/50000000000000 : ℝ)^6197 := by
    have hnat : (330039963 : ℕ)^8245*50000000000000^6197 ≤ 21380076973149^6197*625000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330039963 625000000 21380076973149 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (276298269/500000000 : ℝ)^8245 ≤ (11355821969111/25000000000000 : ℝ)^6197 := by
    have hnat : (276298269 : ℕ)^8245*25000000000000^6197 ≤ 11355821969111^6197*500000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276298269 500000000 11355821969111 25000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2008527159/10000000000 : ℝ)^8245 ≤ (590827907909/5000000000000 : ℝ)^6197 := by
    have hnat : (2008527159 : ℕ)^8245*5000000000000^6197 ≤ 590827907909^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008527159 10000000000 590827907909 5000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330039963/625000000 : ℝ), (276298269/500000000 : ℝ), (-2008527159/10000000000 : ℝ)] ![(21380076973149/50000000000000 : ℝ), (11355821969111/25000000000000 : ℝ), (590827907909/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330039963/625000000 : ℝ)|^8245 ≤ (21380076973149/50000000000000 : ℝ)^6197
        have hw : |(330039963/625000000 : ℝ)|=(330039963/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(276298269/500000000 : ℝ)|^8245 ≤ (11355821969111/25000000000000 : ℝ)^6197
        have hw : |(276298269/500000000 : ℝ)|=(276298269/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2008527159/10000000000 : ℝ)|^8245 ≤ (590827907909/5000000000000 : ℝ)^6197
        have hw : |(-2008527159/10000000000 : ℝ)|=(2008527159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1052_s2_7 (p : ℝ) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364895853/10000000000 : ℝ)*x 0 + (4752208587/10000000000 : ℝ)*x 1 + (4010016213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364895853/10000000000 : ℝ)^8245 ≤ (33188800658269/100000000000000 : ℝ)^6197 := by
    have hnat : (4364895853 : ℕ)^8245*100000000000000^6197 ≤ 33188800658269^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364895853 10000000000 33188800658269 100000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4752208587/10000000000 : ℝ)^8245 ≤ (18581686008337/50000000000000 : ℝ)^6197 := by
    have hnat : (4752208587 : ℕ)^8245*50000000000000^6197 ≤ 18581686008337^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4752208587 10000000000 18581686008337 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4010016213/10000000000 : ℝ)^8245 ≤ (14823913654063/50000000000000 : ℝ)^6197 := by
    have hnat : (4010016213 : ℕ)^8245*50000000000000^6197 ≤ 14823913654063^6197*10000000000^8245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4010016213 10000000000 14823913654063 50000000000000 8245 6197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8245/2048 : ℝ)) 8245 6197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364895853/10000000000 : ℝ), (4752208587/10000000000 : ℝ), (4010016213/10000000000 : ℝ)] ![(33188800658269/100000000000000 : ℝ), (18581686008337/50000000000000 : ℝ), (14823913654063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364895853/10000000000 : ℝ)|^8245 ≤ (33188800658269/100000000000000 : ℝ)^6197
        have hw : |(4364895853/10000000000 : ℝ)|=(4364895853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4752208587/10000000000 : ℝ)|^8245 ≤ (18581686008337/50000000000000 : ℝ)^6197
        have hw : |(4752208587/10000000000 : ℝ)|=(4752208587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4010016213/10000000000 : ℝ)|^8245 ≤ (14823913654063/50000000000000 : ℝ)^6197
        have hw : |(4010016213/10000000000 : ℝ)|=(4010016213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1052_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73860383/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10429/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (513/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (4321/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16787/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10429/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (513/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10429/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (513/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10429/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (513/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10429/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (513/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10429/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (513/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10429/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (513/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (513/10000 : ℝ) ^ (2061/512 : ℝ) ≤ (642271326981323/100000000000000000000 : ℝ) := by
    have hpowers : (513/10000 : ℝ)^2061 ≤ (642271326981323/100000000000000000000 : ℝ)^512 := by
      have hnat : (513 : ℕ)^2061*100000000000000000000^512 ≤ 642271326981323^512*10000^2061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        513 10000 642271326981323 100000000000000000000 2061 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (513/10000 : ℝ)) (X := (642271326981323/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hpowhi : (10429/50000 : ℝ) ^ (2061/512 : ℝ) ≤ (181889052217051461/100000000000000000000 : ℝ) := by
    have hpowers : (10429/50000 : ℝ)^2061 ≤ (181889052217051461/100000000000000000000 : ℝ)^512 := by
      have hnat : (10429 : ℕ)^2061*100000000000000000000^512 ≤ 181889052217051461^512*50000^2061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10429 50000 181889052217051461 100000000000000000000 2061 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10429/50000 : ℝ)) (X := (181889052217051461/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000642271326981323/50000000000000000000 : ℝ) ≤ (10000031910852213/10000000000000000 : ℝ) ^ (2061/512 : ℝ) := by
    have hpowers : (50000642271326981323/50000000000000000000 : ℝ)^512 ≤ (10000031910852213/10000000000000000 : ℝ)^2061 := by
      have hnat : (50000642271326981323 : ℕ)^512*10000000000000000^2061 ≤ 10000031910852213^2061*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000642271326981323 50000000000000000000 10000031910852213 10000000000000000 512 2061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000031910852213/10000000000000000 : ℝ)) (X := (50000642271326981323/50000000000000000000 : ℝ)) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (6261408207721502049/6250000000000000000 : ℝ) ≤ (10004531392597471/10000000000000000 : ℝ) ^ (2061/512 : ℝ) := by
    have hpowers : (6261408207721502049/6250000000000000000 : ℝ)^512 ≤ (10004531392597471/10000000000000000 : ℝ)^2061 := by
      have hnat : (6261408207721502049 : ℕ)^512*10000000000000000^2061 ≤ 10004531392597471^2061*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6261408207721502049 6250000000000000000 10004531392597471 10000000000000000 512 2061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004531392597471/10000000000000000 : ℝ)) (X := (6261408207721502049/6250000000000000000 : ℝ)) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50181889052217051461/50000000000000000000 : ℝ) ≤ (10009030874342729/10000000000000000 : ℝ) ^ (2061/512 : ℝ) := by
    have hpowers : (50181889052217051461/50000000000000000000 : ℝ)^512 ≤ (10009030874342729/10000000000000000 : ℝ)^2061 := by
      have hnat : (50181889052217051461 : ℕ)^512*10000000000000000^2061 ≤ 10009030874342729^2061*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50181889052217051461 50000000000000000000 10009030874342729 10000000000000000 512 2061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009030874342729/10000000000000000 : ℝ)) (X := (50181889052217051461/50000000000000000000 : ℝ)) (by norm_num) 2061 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(642271326981323/100000000000000000000 : ℝ) ≤ ((19654292151397157373/19660000000000000000 : ℝ)+2*(2249740872629/786400000000000 : ℝ)*(513/10000 : ℝ))^(2061/512 : ℝ) := by
    rw [show (19654292151397157373/19660000000000000000 : ℝ)+2*(2249740872629/786400000000000 : ℝ)*(513/10000 : ℝ)=(10000031910852213/10000000000000000 : ℝ) by norm_num, show 1+2*(642271326981323/100000000000000000000 : ℝ)=(50000642271326981323/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(181889052217051461/100000000000000000000 : ℝ)+(642271326981323/100000000000000000000 : ℝ) ≤ ((19654292151397157373/19660000000000000000 : ℝ)+(2249740872629/786400000000000 : ℝ)*((10429/50000 : ℝ)+(513/10000 : ℝ)))^(2061/512 : ℝ) := by
    rw [show (19654292151397157373/19660000000000000000 : ℝ)+(2249740872629/786400000000000 : ℝ)*((10429/50000 : ℝ)+(513/10000 : ℝ))=(10004531392597471/10000000000000000 : ℝ) by norm_num, show 1+(181889052217051461/100000000000000000000 : ℝ)+(642271326981323/100000000000000000000 : ℝ)=(6261408207721502049/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(181889052217051461/100000000000000000000 : ℝ) ≤ ((19654292151397157373/19660000000000000000 : ℝ)+2*(2249740872629/786400000000000 : ℝ)*(10429/50000 : ℝ))^(2061/512 : ℝ) := by
    rw [show (19654292151397157373/19660000000000000000 : ℝ)+2*(2249740872629/786400000000000 : ℝ)*(10429/50000 : ℝ)=(10009030874342729/10000000000000000 : ℝ) by norm_num, show 1+2*(181889052217051461/100000000000000000000 : ℝ)=(50181889052217051461/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19654292151397157373/19660000000000000000 : ℝ)*(X 1 0+X 2 0)+(2249740872629/786400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2061/512 : ℝ)) (lo := (513/10000 : ℝ)) (hi := (10429/50000 : ℝ)) (c := (19654292151397157373/19660000000000000000 : ℝ)) (alpha := (2249740872629/786400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19654292151397157373/19660000000000000000 : ℝ)*(X 0 1+X 2 1)+(2249740872629/786400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2061/512 : ℝ)) (lo := (513/10000 : ℝ)) (hi := (10429/50000 : ℝ)) (c := (19654292151397157373/19660000000000000000 : ℝ)) (alpha := (2249740872629/786400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19654292151397157373/19660000000000000000 : ℝ)*(X 0 2+X 1 2)+(2249740872629/786400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2061/512 : ℝ)) (lo := (513/10000 : ℝ)) (hi := (10429/50000 : ℝ)) (c := (19654292151397157373/19660000000000000000 : ℝ)) (alpha := (2249740872629/786400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2189974921/10000000000 : ℝ)*X 0 0+(1382206959/2500000000 : ℝ)*X 0 1+(5143381409/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5377832857/10000000000 : ℝ)*X 1 0+(-478221907/2000000000 : ℝ)*X 1 1+(5143382837/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((268891663/500000000 : ℝ)*X 2 0+(2571691081/5000000000 : ℝ)*X 2 1+(-1195554939/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364640317/10000000000 : ℝ)*X 0 0+(1001105943/2500000000 : ℝ)*X 0 1+(594717749/1250000000 : ℝ)*X 0 2+(4364640317/10000000000 : ℝ)*X 1 0+(1001105943/2500000000 : ℝ)*X 1 1+(594717749/1250000000 : ℝ)*X 1 2+(4364640317/10000000000 : ℝ)*X 2 0+(1001105943/2500000000 : ℝ)*X 2 1+(594717749/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2190105519/10000000000 : ℝ)*X 0 0+(1286553489/2500000000 : ℝ)*X 0 1+(172686421/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((211225567/400000000 : ℝ)*X 1 0+(-1004263627/5000000000 : ℝ)*X 1 1+(2762982771/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330039963/625000000 : ℝ)*X 2 0+(276298269/500000000 : ℝ)*X 2 1+(-2008527159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4364895853/10000000000 : ℝ)*X 0 0+(4752208587/10000000000 : ℝ)*X 0 1+(4010016213/10000000000 : ℝ)*X 0 2+(4364895853/10000000000 : ℝ)*X 1 0+(4752208587/10000000000 : ℝ)*X 1 1+(4010016213/10000000000 : ℝ)*X 1 2+(4364895853/10000000000 : ℝ)*X 2 0+(4752208587/10000000000 : ℝ)*X 2 1+(4010016213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1052_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1983915521433538021648930863/245750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1997621/50000000000000 : ℝ)*(base1) + (95515859/4000000000000 : ℝ)*(base19) + (1291158919/50000000000000 : ℝ)*(base23) + (33419413/10000000000000 : ℝ)*(upper3) + (44629789/25000000000000 : ℝ)*(upper5) + (980486037705877/50000000000000 : ℝ)*(major0) + (980486037705877/50000000000000 : ℝ)*(major1) + (980486037705877/50000000000000 : ℝ)*(major2) + (1297213478671737/50000000000000 : ℝ)*(sp0) + (129722788647949/5000000000000 : ℝ)*(sp1) + (162153473658601/6250000000000 : ℝ)*(sp2) + (165934017108433/12500000000000 : ℝ)*(sp3) + (31207507223/100000000000000 : ℝ)*(sp4) + (6790004313/50000000000000 : ℝ)*(sp7) + (1327485720871333/100000000000000 : ℝ)*(f.failure) + (1297229080427727/50000000000000 : ℝ)*(f.sum) + (51133450464133/19660000000000000000000000000 : ℝ)*base65 + (2004375580354193879/983000000000000000000000000000000 : ℝ)*base68 + (10953910959712193879/983000000000000000000000000000000 : ℝ)*base70 + (2789800251686193879/983000000000000000000000000000000 : ℝ)*base72 + (58988473806433/19660000000000000000000000000 : ℝ)*base73 + (5792519196366193879/983000000000000000000000000000000 : ℝ)*base76 + (1540114612586193879/983000000000000000000000000000000 : ℝ)*base78 + (410993688425806121/983000000000000000000000000000000 : ℝ)*base79 + (80886123354847/19660000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (49100539/5000000000000000000000 : ℝ)*base89 + (49100539/5000000000000000000000 : ℝ)*base91 + (49100539/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19242289999129587269166807/7679687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (438029913/100000000000000 : ℝ)*(base19) + (144422269/25000000000000 : ℝ)*(base23) + (20022691/25000000000000 : ℝ)*(upper3) + (711181/100000000000000 : ℝ)*(lower4) + (6992867/12500000000000 : ℝ)*(upper5) + (31098914115577/1562500000000 : ℝ)*(major0) + (31098914115577/1562500000000 : ℝ)*(major1) + (31098914115577/1562500000000 : ℝ)*(major2) + (1755416983/50000000000000 : ℝ)*(sp1) + (4712743951/100000000000000 : ℝ)*(sp2) + (2633300929623839/100000000000000 : ℝ)*(sp4) + (65832424518999/2500000000000 : ℝ)*(sp5) + (658323909797703/25000000000000 : ℝ)*(sp6) + (21052499900777/1562500000000 : ℝ)*(sp7) + (21052499900777/1562500000000 : ℝ)*(f.failure) + (2633300929623839/100000000000000 : ℝ)*(f.sum) + (6200364416619/4915000000000000000000000000 : ℝ)*base65 + (278033760705100779/30718750000000000000000000000000 : ℝ)*base68 + (312334797764975779/30718750000000000000000000000000 : ℝ)*base70 + (171836597541288279/30718750000000000000000000000000 : ℝ)*base72 + (6684324903113/2457500000000000000000000000 : ℝ)*base74 + (126555565123788279/30718750000000000000000000000000 : ℝ)*base76 + (256512085266350779/30718750000000000000000000000000 : ℝ)*base78 + (151496887200538279/30718750000000000000000000000000 : ℝ)*base80 + (17107885595703/2457500000000000000000000000 : ℝ)*base82 + (1217591/78125000000000000000 : ℝ)*base89 + (1217591/78125000000000000000 : ℝ)*base91 + (1217591/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1052_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73860383/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10429/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (513/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4321/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16787/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1052_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1052_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73860383/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4321/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16787/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1052_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1052_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1052_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2061/512 : ℝ) ≤ p) (hpb : p ≤ (8245/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73860383/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4321/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16787/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1052_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

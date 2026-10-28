-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1040_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:46:36.861453+00:00
-- url     : https://prove2.me/submissions/78ea7ee1-d36e-4061-8d74-cdaa6b765f80

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
theorem support_rectangle_w1040_s9_0 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1108318051/5000000000 : ℝ)*x 0 + (5394786061/10000000000 : ℝ)*x 1 + (26319931/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1108318051/5000000000 : ℝ)^8233 ≤ (672989556799/5000000000000 : ℝ)^6185 := by
    have hnat : (1108318051 : ℕ)^8233*5000000000000^6185 ≤ 672989556799^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108318051 5000000000 672989556799 5000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394786061/10000000000 : ℝ)^8233 ≤ (439768931761/1000000000000 : ℝ)^6185 := by
    have hnat : (5394786061 : ℕ)^8233*1000000000000^6185 ≤ 439768931761^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394786061 10000000000 439768931761 1000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26319931/50000000 : ℝ)^8233 ≤ (4256331568097/10000000000000 : ℝ)^6185 := by
    have hnat : (26319931 : ℕ)^8233*10000000000000^6185 ≤ 4256331568097^6185*50000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26319931 50000000 4256331568097 10000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1108318051/5000000000 : ℝ), (5394786061/10000000000 : ℝ), (26319931/50000000 : ℝ)] ![(672989556799/5000000000000 : ℝ), (439768931761/1000000000000 : ℝ), (4256331568097/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1108318051/5000000000 : ℝ)|^8233 ≤ (672989556799/5000000000000 : ℝ)^6185
        have hw : |(-1108318051/5000000000 : ℝ)|=(1108318051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394786061/10000000000 : ℝ)|^8233 ≤ (439768931761/1000000000000 : ℝ)^6185
        have hw : |(5394786061/10000000000 : ℝ)|=(5394786061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26319931/50000000 : ℝ)|^8233 ≤ (4256331568097/10000000000000 : ℝ)^6185
        have hw : |(26319931/50000000 : ℝ)|=(26319931/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s9_1 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672513799/5000000000 : ℝ)*x 0 + (-1141503279/5000000000 : ℝ)*x 1 + (2631993101/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672513799/5000000000 : ℝ)^8233 ≤ (678715493407/1562500000000 : ℝ)^6185 := by
    have hnat : (2672513799 : ℕ)^8233*1562500000000^6185 ≤ 678715493407^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672513799 5000000000 678715493407 1562500000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1141503279/5000000000 : ℝ)^8233 ≤ (13998892700657/100000000000000 : ℝ)^6185 := by
    have hnat : (1141503279 : ℕ)^8233*100000000000000^6185 ≤ 13998892700657^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141503279 5000000000 13998892700657 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631993101/5000000000 : ℝ)^8233 ≤ (1330103615703/3125000000000 : ℝ)^6185 := by
    have hnat : (2631993101 : ℕ)^8233*3125000000000^6185 ≤ 1330103615703^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631993101 5000000000 1330103615703 3125000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672513799/5000000000 : ℝ), (-1141503279/5000000000 : ℝ), (2631993101/5000000000 : ℝ)] ![(678715493407/1562500000000 : ℝ), (13998892700657/100000000000000 : ℝ), (1330103615703/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672513799/5000000000 : ℝ)|^8233 ≤ (678715493407/1562500000000 : ℝ)^6185
        have hw : |(2672513799/5000000000 : ℝ)|=(2672513799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1141503279/5000000000 : ℝ)|^8233 ≤ (13998892700657/100000000000000 : ℝ)^6185
        have hw : |(-1141503279/5000000000 : ℝ)|=(1141503279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631993101/5000000000 : ℝ)|^8233 ≤ (1330103615703/3125000000000 : ℝ)^6185
        have hw : |(2631993101/5000000000 : ℝ)|=(2631993101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s9_2 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2138011/4000000 : ℝ)*x 0 + (5263986253/10000000000 : ℝ)*x 1 + (-1141503311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138011/4000000 : ℝ)^8233 ≤ (4343779051791/10000000000000 : ℝ)^6185 := by
    have hnat : (2138011 : ℕ)^8233*10000000000000^6185 ≤ 4343779051791^6185*4000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138011 4000000 4343779051791 10000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263986253/10000000000 : ℝ)^8233 ≤ (42563316251417/100000000000000 : ℝ)^6185 := by
    have hnat : (5263986253 : ℕ)^8233*100000000000000^6185 ≤ 42563316251417^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263986253 10000000000 42563316251417 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1141503311/5000000000 : ℝ)^8233 ≤ (2799778644607/20000000000000 : ℝ)^6185 := by
    have hnat : (1141503311 : ℕ)^8233*20000000000000^6185 ≤ 2799778644607^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141503311 5000000000 2799778644607 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2138011/4000000 : ℝ), (5263986253/10000000000 : ℝ), (-1141503311/5000000000 : ℝ)] ![(4343779051791/10000000000000 : ℝ), (42563316251417/100000000000000 : ℝ), (2799778644607/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2138011/4000000 : ℝ)|^8233 ≤ (4343779051791/10000000000000 : ℝ)^6185
        have hw : |(2138011/4000000 : ℝ)|=(2138011/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263986253/10000000000 : ℝ)|^8233 ≤ (42563316251417/100000000000000 : ℝ)^6185
        have hw : |(5263986253/10000000000 : ℝ)|=(5263986253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1141503311/5000000000 : ℝ)|^8233 ≤ (2799778644607/20000000000000 : ℝ)^6185
        have hw : |(-1141503311/5000000000 : ℝ)|=(1141503311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s9_3 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4379245903/10000000000 : ℝ)*x 0 + (850724957/2000000000 : ℝ)*x 1 + (2254325937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379245903/10000000000 : ℝ)^8233 ≤ (16658203441139/50000000000000 : ℝ)^6185 := by
    have hnat : (4379245903 : ℕ)^8233*50000000000000^6185 ≤ 16658203441139^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379245903 10000000000 16658203441139 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (850724957/2000000000 : ℝ)^8233 ≤ (32050333158961/100000000000000 : ℝ)^6185 := by
    have hnat : (850724957 : ℕ)^8233*100000000000000^6185 ≤ 32050333158961^6185*2000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850724957 2000000000 32050333158961 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254325937/5000000000 : ℝ)^8233 ≤ (17316629975031/50000000000000 : ℝ)^6185 := by
    have hnat : (2254325937 : ℕ)^8233*50000000000000^6185 ≤ 17316629975031^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254325937 5000000000 17316629975031 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379245903/10000000000 : ℝ), (850724957/2000000000 : ℝ), (2254325937/5000000000 : ℝ)] ![(16658203441139/50000000000000 : ℝ), (32050333158961/100000000000000 : ℝ), (17316629975031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379245903/10000000000 : ℝ)|^8233 ≤ (16658203441139/50000000000000 : ℝ)^6185
        have hw : |(4379245903/10000000000 : ℝ)|=(4379245903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(850724957/2000000000 : ℝ)|^8233 ≤ (32050333158961/100000000000000 : ℝ)^6185
        have hw : |(850724957/2000000000 : ℝ)|=(850724957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2254325937/5000000000 : ℝ)|^8233 ≤ (17316629975031/50000000000000 : ℝ)^6185
        have hw : |(2254325937/5000000000 : ℝ)|=(2254325937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s9_4 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2216641231/10000000000 : ℝ)*x 0 + (2632156637/5000000000 : ℝ)*x 1 + (5394457807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2216641231/10000000000 : ℝ)^8233 ≤ (538393303709/4000000000000 : ℝ)^6185 := by
    have hnat : (2216641231 : ℕ)^8233*4000000000000^6185 ≤ 538393303709^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216641231 10000000000 538393303709 4000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632156637/5000000000 : ℝ)^8233 ≤ (42566836061507/100000000000000 : ℝ)^6185 := by
    have hnat : (2632156637 : ℕ)^8233*100000000000000^6185 ≤ 42566836061507^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632156637 5000000000 42566836061507 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394457807/10000000000 : ℝ)^8233 ≤ (4397333133631/10000000000000 : ℝ)^6185 := by
    have hnat : (5394457807 : ℕ)^8233*10000000000000^6185 ≤ 4397333133631^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394457807 10000000000 4397333133631 10000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2216641231/10000000000 : ℝ), (2632156637/5000000000 : ℝ), (5394457807/10000000000 : ℝ)] ![(538393303709/4000000000000 : ℝ), (42566836061507/100000000000000 : ℝ), (4397333133631/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2216641231/10000000000 : ℝ)|^8233 ≤ (538393303709/4000000000000 : ℝ)^6185
        have hw : |(-2216641231/10000000000 : ℝ)|=(2216641231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632156637/5000000000 : ℝ)|^8233 ≤ (42566836061507/100000000000000 : ℝ)^6185
        have hw : |(2632156637/5000000000 : ℝ)|=(2632156637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394457807/10000000000 : ℝ)|^8233 ≤ (4397333133631/10000000000000 : ℝ)^6185
        have hw : |(5394457807/10000000000 : ℝ)|=(5394457807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s9_5 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (16600469/31250000 : ℝ)*x 0 + (-1076267761/5000000000 : ℝ)*x 1 + (5394457751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16600469/31250000 : ℝ)^8233 ≤ (43082494111697/100000000000000 : ℝ)^6185 := by
    have hnat : (16600469 : ℕ)^8233*100000000000000^6185 ≤ 43082494111697^6185*31250000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16600469 31250000 43082494111697 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076267761/5000000000 : ℝ)^8233 ≤ (12944175137893/100000000000000 : ℝ)^6185 := by
    have hnat : (1076267761 : ℕ)^8233*100000000000000^6185 ≤ 12944175137893^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076267761 5000000000 12944175137893 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394457751/10000000000 : ℝ)^8233 ≤ (43973330728667/100000000000000 : ℝ)^6185 := by
    have hnat : (5394457751 : ℕ)^8233*100000000000000^6185 ≤ 43973330728667^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394457751 10000000000 43973330728667 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16600469/31250000 : ℝ), (-1076267761/5000000000 : ℝ), (5394457751/10000000000 : ℝ)] ![(43082494111697/100000000000000 : ℝ), (12944175137893/100000000000000 : ℝ), (43973330728667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16600469/31250000 : ℝ)|^8233 ≤ (43082494111697/100000000000000 : ℝ)^6185
        have hw : |(16600469/31250000 : ℝ)|=(16600469/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1076267761/5000000000 : ℝ)|^8233 ≤ (12944175137893/100000000000000 : ℝ)^6185
        have hw : |(-1076267761/5000000000 : ℝ)|=(1076267761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394457751/10000000000 : ℝ)|^8233 ≤ (43973330728667/100000000000000 : ℝ)^6185
        have hw : |(5394457751/10000000000 : ℝ)|=(5394457751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s9_6 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656075397/5000000000 : ℝ)*x 0 + (2697228663/5000000000 : ℝ)*x 1 + (-67266723/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656075397/5000000000 : ℝ)^8233 ≤ (43082501819793/100000000000000 : ℝ)^6185 := by
    have hnat : (2656075397 : ℕ)^8233*100000000000000^6185 ≤ 43082501819793^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656075397 5000000000 43082501819793 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697228663/5000000000 : ℝ)^8233 ≤ (5496665764637/12500000000000 : ℝ)^6185 := by
    have hnat : (2697228663 : ℕ)^8233*12500000000000^6185 ≤ 5496665764637^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697228663 5000000000 5496665764637 12500000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67266723/312500000 : ℝ)^8233 ≤ (12944172048097/100000000000000 : ℝ)^6185 := by
    have hnat : (67266723 : ℕ)^8233*100000000000000^6185 ≤ 12944172048097^6185*312500000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67266723 312500000 12944172048097 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656075397/5000000000 : ℝ), (2697228663/5000000000 : ℝ), (-67266723/312500000 : ℝ)] ![(43082501819793/100000000000000 : ℝ), (5496665764637/12500000000000 : ℝ), (12944172048097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656075397/5000000000 : ℝ)|^8233 ≤ (43082501819793/100000000000000 : ℝ)^6185
        have hw : |(2656075397/5000000000 : ℝ)|=(2656075397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697228663/5000000000 : ℝ)|^8233 ≤ (5496665764637/12500000000000 : ℝ)^6185
        have hw : |(2697228663/5000000000 : ℝ)|=(2697228663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-67266723/312500000 : ℝ)|^8233 ≤ (12944172048097/100000000000000 : ℝ)^6185
        have hw : |(-67266723/312500000 : ℝ)|=(67266723/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_s9_7 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1094813991/2500000000 : ℝ)*x 0 + (4508013989/10000000000 : ℝ)*x 1 + (4254264897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094813991/2500000000 : ℝ)^8233 ≤ (16658254384613/50000000000000 : ℝ)^6185 := by
    have hnat : (1094813991 : ℕ)^8233*50000000000000^6185 ≤ 16658254384613^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094813991 2500000000 16658254384613 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508013989/10000000000 : ℝ)^8233 ≤ (34626737702229/100000000000000 : ℝ)^6185 := by
    have hnat : (4508013989 : ℕ)^8233*100000000000000^6185 ≤ 34626737702229^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508013989 10000000000 34626737702229 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4254264897/10000000000 : ℝ)^8233 ≤ (32056753506991/100000000000000 : ℝ)^6185 := by
    have hnat : (4254264897 : ℕ)^8233*100000000000000^6185 ≤ 32056753506991^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254264897 10000000000 32056753506991 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094813991/2500000000 : ℝ), (4508013989/10000000000 : ℝ), (4254264897/10000000000 : ℝ)] ![(16658254384613/50000000000000 : ℝ), (34626737702229/100000000000000 : ℝ), (32056753506991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094813991/2500000000 : ℝ)|^8233 ≤ (16658254384613/50000000000000 : ℝ)^6185
        have hw : |(1094813991/2500000000 : ℝ)|=(1094813991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508013989/10000000000 : ℝ)|^8233 ≤ (34626737702229/100000000000000 : ℝ)^6185
        have hw : |(4508013989/10000000000 : ℝ)|=(4508013989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4254264897/10000000000 : ℝ)|^8233 ≤ (32056753506991/100000000000000 : ℝ)^6185
        have hw : |(4254264897/10000000000 : ℝ)|=(4254264897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1040_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2243/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (701/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6993/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13987/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2243/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13987/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2243/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13987/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2243/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13987/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2243/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13987/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2243/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13987/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2243/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2243/20000 : ℝ) ^ (1029/256 : ℝ) ≤ (15157881369823217/100000000000000000000 : ℝ) := by
    have hpowers : (2243/20000 : ℝ)^1029 ≤ (15157881369823217/100000000000000000000 : ℝ)^256 := by
      have hnat : (2243 : ℕ)^1029*100000000000000000000^256 ≤ 15157881369823217^256*20000^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2243 20000 15157881369823217 100000000000000000000 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2243/20000 : ℝ)) (X := (15157881369823217/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hpowhi : (13987/100000 : ℝ) ^ (1029/256 : ℝ) ≤ (18415488214588267/50000000000000000000 : ℝ) := by
    have hpowers : (13987/100000 : ℝ)^1029 ≤ (18415488214588267/50000000000000000000 : ℝ)^256 := by
      have hnat : (13987 : ℕ)^1029*50000000000000000000^256 ≤ 18415488214588267^256*100000^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13987 100000 18415488214588267 50000000000000000000 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13987/100000 : ℝ)) (X := (18415488214588267/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015157881369823217/50000000000000000000 : ℝ) ≤ (10000754125530129/10000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (50015157881369823217/50000000000000000000 : ℝ)^256 ≤ (10000754125530129/10000000000000000 : ℝ)^1029 := by
      have hnat : (50015157881369823217 : ℕ)^256*10000000000000000^1029 ≤ 10000754125530129^1029*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015157881369823217 50000000000000000000 10000754125530129 10000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000754125530129/10000000000000000 : ℝ)) (X := (50015157881369823217/50000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051988857798999751/100000000000000000000 : ℝ) ≤ (5000646576747067/5000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (100051988857798999751/100000000000000000000 : ℝ)^256 ≤ (5000646576747067/5000000000000000 : ℝ)^1029 := by
      have hnat : (100051988857798999751 : ℕ)^256*5000000000000000^1029 ≤ 5000646576747067^1029*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051988857798999751 100000000000000000000 5000646576747067 5000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000646576747067/5000000000000000 : ℝ)) (X := (100051988857798999751/100000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018415488214588267/25000000000000000000 : ℝ) ≤ (10001832181458139/10000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (25018415488214588267/25000000000000000000 : ℝ)^256 ≤ (10001832181458139/10000000000000000 : ℝ)^1029 := by
      have hnat : (25018415488214588267 : ℕ)^256*10000000000000000^1029 ≤ 10001832181458139^1029*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018415488214588267 25000000000000000000 10001832181458139 10000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001832181458139/10000000000000000 : ℝ)) (X := (25018415488214588267/25000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15157881369823217/100000000000000000000 : ℝ) ≤ ((13855000019368442719/13860000000000000000 : ℝ)+2*(107805592801/55440000000000 : ℝ)*(2243/20000 : ℝ))^(1029/256 : ℝ) := by
    rw [show (13855000019368442719/13860000000000000000 : ℝ)+2*(107805592801/55440000000000 : ℝ)*(2243/20000 : ℝ)=(10000754125530129/10000000000000000 : ℝ) by norm_num, show 1+2*(15157881369823217/100000000000000000000 : ℝ)=(50015157881369823217/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18415488214588267/50000000000000000000 : ℝ)+(15157881369823217/100000000000000000000 : ℝ) ≤ ((13855000019368442719/13860000000000000000 : ℝ)+(107805592801/55440000000000 : ℝ)*((13987/100000 : ℝ)+(2243/20000 : ℝ)))^(1029/256 : ℝ) := by
    rw [show (13855000019368442719/13860000000000000000 : ℝ)+(107805592801/55440000000000 : ℝ)*((13987/100000 : ℝ)+(2243/20000 : ℝ))=(5000646576747067/5000000000000000 : ℝ) by norm_num, show 1+(18415488214588267/50000000000000000000 : ℝ)+(15157881369823217/100000000000000000000 : ℝ)=(100051988857798999751/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18415488214588267/50000000000000000000 : ℝ) ≤ ((13855000019368442719/13860000000000000000 : ℝ)+2*(107805592801/55440000000000 : ℝ)*(13987/100000 : ℝ))^(1029/256 : ℝ) := by
    rw [show (13855000019368442719/13860000000000000000 : ℝ)+2*(107805592801/55440000000000 : ℝ)*(13987/100000 : ℝ)=(10001832181458139/10000000000000000 : ℝ) by norm_num, show 1+2*(18415488214588267/50000000000000000000 : ℝ)=(25018415488214588267/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13855000019368442719/13860000000000000000 : ℝ)*(X 1 0+X 2 0)+(107805592801/55440000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (2243/20000 : ℝ)) (hi := (13987/100000 : ℝ)) (c := (13855000019368442719/13860000000000000000 : ℝ)) (alpha := (107805592801/55440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13855000019368442719/13860000000000000000 : ℝ)*(X 0 1+X 2 1)+(107805592801/55440000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (2243/20000 : ℝ)) (hi := (13987/100000 : ℝ)) (c := (13855000019368442719/13860000000000000000 : ℝ)) (alpha := (107805592801/55440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13855000019368442719/13860000000000000000 : ℝ)*(X 0 2+X 1 2)+(107805592801/55440000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (2243/20000 : ℝ)) (hi := (13987/100000 : ℝ)) (c := (13855000019368442719/13860000000000000000 : ℝ)) (alpha := (107805592801/55440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1108318051/5000000000 : ℝ)*X 0 0+(5394786061/10000000000 : ℝ)*X 0 1+(26319931/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672513799/5000000000 : ℝ)*X 1 0+(-1141503279/5000000000 : ℝ)*X 1 1+(2631993101/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2138011/4000000 : ℝ)*X 2 0+(5263986253/10000000000 : ℝ)*X 2 1+(-1141503311/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4379245903/10000000000 : ℝ)*X 0 0+(850724957/2000000000 : ℝ)*X 0 1+(2254325937/5000000000 : ℝ)*X 0 2+(4379245903/10000000000 : ℝ)*X 1 0+(850724957/2000000000 : ℝ)*X 1 1+(2254325937/5000000000 : ℝ)*X 1 2+(4379245903/10000000000 : ℝ)*X 2 0+(850724957/2000000000 : ℝ)*X 2 1+(2254325937/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2216641231/10000000000 : ℝ)*X 0 0+(2632156637/5000000000 : ℝ)*X 0 1+(5394457807/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((16600469/31250000 : ℝ)*X 1 0+(-1076267761/5000000000 : ℝ)*X 1 1+(5394457751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s9_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656075397/5000000000 : ℝ)*X 2 0+(2697228663/5000000000 : ℝ)*X 2 1+(-67266723/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s9_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1094813991/2500000000 : ℝ)*X 0 0+(4508013989/10000000000 : ℝ)*X 0 1+(4254264897/10000000000 : ℝ)*X 0 2+(1094813991/2500000000 : ℝ)*X 1 0+(4508013989/10000000000 : ℝ)*X 1 1+(4254264897/10000000000 : ℝ)*X 1 2+(1094813991/2500000000 : ℝ)*X 2 0+(4508013989/10000000000 : ℝ)*X 2 1+(4254264897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_s9_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (553249864075248857611/308000000000000000000000000 : ℝ) := by norm_num
    linear_combination (100130273/20000000000000 : ℝ)*(base19) + (371735727/100000000000000 : ℝ)*(base23) + (21626713/25000000000000 : ℝ)*(upper3) + (4714717/50000000000000 : ℝ)*(lower4) + (5783232482338697/100000000000000 : ℝ)*(major0) + (5783232482338697/100000000000000 : ℝ)*(major1) + (5783232482338697/100000000000000 : ℝ)*(major2) + (4778303516839/62500000000 : ℝ)*(sp0) + (955662098300663/12500000000000 : ℝ)*(sp1) + (7645295877720571/100000000000000 : ℝ)*(sp2) + (98028985055371/2500000000000 : ℝ)*(sp3) + (2915028567/25000000000000 : ℝ)*(sp4) + (103760037/10000000000000 : ℝ)*(sp6) + (2053882587/25000000000000 : ℝ)*(sp7) + (980291904436297/25000000000000 : ℝ)*(f.failure) + (1911324321764167/25000000000000 : ℝ)*(f.sum) + (3461668969049/2772000000000000000000000000 : ℝ)*base65 + (2916264980131847143/1386000000000000000000000000000000 : ℝ)*base67 + (15143214377563847143/1386000000000000000000000000000000 : ℝ)*base69 + (10899172874548152857/1386000000000000000000000000000000 : ℝ)*base72 + (3140736078617/2772000000000000000000000000 : ℝ)*base73 + (6666375824611847143/1386000000000000000000000000000000 : ℝ)*base75 + (7527473526916152857/1386000000000000000000000000000000 : ℝ)*base78 + (23649254193754152857/1386000000000000000000000000000000 : ℝ)*base80 + (4354542504449/2772000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2684953/250000000000000000000 : ℝ)*base90 + (2684953/250000000000000000000 : ℝ)*base92 + (2684953/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (108102548900448056636205261/19250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (420702661/100000000000000 : ℝ)*(base19) + (351464879/20000000000000 : ℝ)*(base23) + (3627517/6250000000000 : ℝ)*(lower1) + (23171743/25000000000000 : ℝ)*(upper3) + (30781293/50000000000000 : ℝ)*(lower4) + (89315169/50000000000000 : ℝ)*(upper5) + (1453084756223257/25000000000000 : ℝ)*(major0) + (1453084756223257/25000000000000 : ℝ)*(major1) + (1453084756223257/25000000000000 : ℝ)*(major2) + (30370896097/100000000000000 : ℝ)*(sp2) + (3841887662274003/50000000000000 : ℝ)*(sp4) + (1536754980769069/20000000000000 : ℝ)*(sp5) + (3841871598163757/50000000000000 : ℝ)*(sp6) + (1970451269023739/50000000000000 : ℝ)*(sp7) + (1970451269023739/50000000000000 : ℝ)*(f.failure) + (3841887662274003/50000000000000 : ℝ)*(f.sum) + (5642110847501/693000000000000000000000000 : ℝ)*base66 + (3895426955054634217/346500000000000000000000000000000 : ℝ)*base68 + (4816843881522365783/346500000000000000000000000000000 : ℝ)*base69 + (13553849384633634217/346500000000000000000000000000000 : ℝ)*base72 + (4017096010979/693000000000000000000000000 : ℝ)*base74 + (2573147430142134217/346500000000000000000000000000000 : ℝ)*base76 + (1090129035822365783/346500000000000000000000000000000 : ℝ)*base77 + (5300827649791134217/346500000000000000000000000000000 : ℝ)*base80 + (2262891557953/693000000000000000000000000 : ℝ)*base81 + (400011/500000000000000000000 : ℝ)*base90 + (400011/500000000000000000000 : ℝ)*base92 + (400011/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1040_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2243/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6993/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1040_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1040_box_0 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2086271981/10000000000 : ℝ)*x 0 + (2688857757/5000000000 : ℝ)*x 1 + (2688857889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086271981/10000000000 : ℝ)^8233 ≤ (12416480684053/100000000000000 : ℝ)^6185 := by
    have hnat : (2086271981 : ℕ)^8233*100000000000000^6185 ≤ 12416480684053^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086271981 10000000000 12416480684053 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688857757/5000000000 : ℝ)^8233 ≤ (43791758219963/100000000000000 : ℝ)^6185 := by
    have hnat : (2688857757 : ℕ)^8233*100000000000000^6185 ≤ 43791758219963^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688857757 5000000000 43791758219963 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688857889/5000000000 : ℝ)^8233 ≤ (8758352216323/20000000000000 : ℝ)^6185 := by
    have hnat : (2688857889 : ℕ)^8233*20000000000000^6185 ≤ 8758352216323^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688857889 5000000000 8758352216323 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2086271981/10000000000 : ℝ), (2688857757/5000000000 : ℝ), (2688857889/5000000000 : ℝ)] ![(12416480684053/100000000000000 : ℝ), (43791758219963/100000000000000 : ℝ), (8758352216323/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2086271981/10000000000 : ℝ)|^8233 ≤ (12416480684053/100000000000000 : ℝ)^6185
        have hw : |(-2086271981/10000000000 : ℝ)|=(2086271981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688857757/5000000000 : ℝ)|^8233 ≤ (43791758219963/100000000000000 : ℝ)^6185
        have hw : |(2688857757/5000000000 : ℝ)|=(2688857757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688857889/5000000000 : ℝ)|^8233 ≤ (8758352216323/20000000000000 : ℝ)^6185
        have hw : |(2688857889/5000000000 : ℝ)|=(2688857889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_box_1 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5294902147/10000000000 : ℝ)*x 0 + (-2198307383/10000000000 : ℝ)*x 1 + (1344428957/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294902147/10000000000 : ℝ)^8233 ≤ (42896391581597/100000000000000 : ℝ)^6185 := by
    have hnat : (5294902147 : ℕ)^8233*100000000000000^6185 ≤ 42896391581597^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294902147 10000000000 42896391581597 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2198307383/10000000000 : ℝ)^8233 ≤ (13311846783079/100000000000000 : ℝ)^6185 := by
    have hnat : (2198307383 : ℕ)^8233*100000000000000^6185 ≤ 13311846783079^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198307383 10000000000 13311846783079 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344428957/2500000000 : ℝ)^8233 ≤ (8758352324719/20000000000000 : ℝ)^6185 := by
    have hnat : (1344428957 : ℕ)^8233*20000000000000^6185 ≤ 8758352324719^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344428957 2500000000 8758352324719 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294902147/10000000000 : ℝ), (-2198307383/10000000000 : ℝ), (1344428957/2500000000 : ℝ)] ![(42896391581597/100000000000000 : ℝ), (13311846783079/100000000000000 : ℝ), (8758352324719/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294902147/10000000000 : ℝ)|^8233 ≤ (42896391581597/100000000000000 : ℝ)^6185
        have hw : |(5294902147/10000000000 : ℝ)|=(5294902147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2198307383/10000000000 : ℝ)|^8233 ≤ (13311846783079/100000000000000 : ℝ)^6185
        have hw : |(-2198307383/10000000000 : ℝ)|=(2198307383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344428957/2500000000 : ℝ)|^8233 ≤ (8758352324719/20000000000000 : ℝ)^6185
        have hw : |(1344428957/2500000000 : ℝ)|=(1344428957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_box_2 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2647450941/5000000000 : ℝ)*x 0 + (5377716073/10000000000 : ℝ)*x 1 + (-137394213/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647450941/5000000000 : ℝ)^8233 ≤ (10724097180957/25000000000000 : ℝ)^6185 := by
    have hnat : (2647450941 : ℕ)^8233*25000000000000^6185 ≤ 10724097180957^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647450941 5000000000 10724097180957 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377716073/10000000000 : ℝ)^8233 ≤ (8758352855859/20000000000000 : ℝ)^6185 := by
    have hnat : (5377716073 : ℕ)^8233*20000000000000^6185 ≤ 8758352855859^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377716073 10000000000 8758352855859 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137394213/625000000 : ℝ)^8233 ≤ (6655923492297/50000000000000 : ℝ)^6185 := by
    have hnat : (137394213 : ℕ)^8233*50000000000000^6185 ≤ 6655923492297^6185*625000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137394213 625000000 6655923492297 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647450941/5000000000 : ℝ), (5377716073/10000000000 : ℝ), (-137394213/625000000 : ℝ)] ![(10724097180957/25000000000000 : ℝ), (8758352855859/20000000000000 : ℝ), (6655923492297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647450941/5000000000 : ℝ)|^8233 ≤ (10724097180957/25000000000000 : ℝ)^6185
        have hw : |(2647450941/5000000000 : ℝ)|=(2647450941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377716073/10000000000 : ℝ)|^8233 ≤ (8758352855859/20000000000000 : ℝ)^6185
        have hw : |(5377716073/10000000000 : ℝ)|=(5377716073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137394213/625000000 : ℝ)|^8233 ≤ (6655923492297/50000000000000 : ℝ)^6185
        have hw : |(-137394213/625000000 : ℝ)|=(137394213/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_box_3 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4487932089/10000000000 : ℝ)*x 0 + (4327084781/10000000000 : ℝ)*x 1 + (865416943/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4487932089/10000000000 : ℝ)^8233 ≤ (17210780323761/50000000000000 : ℝ)^6185 := by
    have hnat : (4487932089 : ℕ)^8233*50000000000000^6185 ≤ 17210780323761^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487932089 10000000000 17210780323761 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4327084781/10000000000 : ℝ)^8233 ≤ (32789220000883/100000000000000 : ℝ)^6185 := by
    have hnat : (4327084781 : ℕ)^8233*100000000000000^6185 ≤ 32789220000883^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327084781 10000000000 32789220000883 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (865416943/2000000000 : ℝ)^8233 ≤ (32789219335153/100000000000000 : ℝ)^6185 := by
    have hnat : (865416943 : ℕ)^8233*100000000000000^6185 ≤ 32789219335153^6185*2000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865416943 2000000000 32789219335153 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4487932089/10000000000 : ℝ), (4327084781/10000000000 : ℝ), (865416943/2000000000 : ℝ)] ![(17210780323761/50000000000000 : ℝ), (32789220000883/100000000000000 : ℝ), (32789219335153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4487932089/10000000000 : ℝ)|^8233 ≤ (17210780323761/50000000000000 : ℝ)^6185
        have hw : |(4487932089/10000000000 : ℝ)|=(4487932089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4327084781/10000000000 : ℝ)|^8233 ≤ (32789220000883/100000000000000 : ℝ)^6185
        have hw : |(4327084781/10000000000 : ℝ)|=(4327084781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(865416943/2000000000 : ℝ)|^8233 ≤ (32789219335153/100000000000000 : ℝ)^6185
        have hw : |(865416943/2000000000 : ℝ)|=(865416943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_box_4 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2348388411/10000000000 : ℝ)*x 0 + (1319923577/2500000000 : ℝ)*x 1 + (329980897/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2348388411/10000000000 : ℝ)^8233 ≤ (2907012795501/20000000000000 : ℝ)^6185 := by
    have hnat : (2348388411 : ℕ)^8233*20000000000000^6185 ≤ 2907012795501^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2348388411 10000000000 2907012795501 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1319923577/2500000000 : ℝ)^8233 ≤ (42732467770519/100000000000000 : ℝ)^6185 := by
    have hnat : (1319923577 : ℕ)^8233*100000000000000^6185 ≤ 42732467770519^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319923577 2500000000 42732467770519 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329980897/625000000 : ℝ)^8233 ≤ (8546493648913/20000000000000 : ℝ)^6185 := by
    have hnat : (329980897 : ℕ)^8233*20000000000000^6185 ≤ 8546493648913^6185*625000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329980897 625000000 8546493648913 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2348388411/10000000000 : ℝ), (1319923577/2500000000 : ℝ), (329980897/625000000 : ℝ)] ![(2907012795501/20000000000000 : ℝ), (42732467770519/100000000000000 : ℝ), (8546493648913/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2348388411/10000000000 : ℝ)|^8233 ≤ (2907012795501/20000000000000 : ℝ)^6185
        have hw : |(-2348388411/10000000000 : ℝ)|=(2348388411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1319923577/2500000000 : ℝ)|^8233 ≤ (42732467770519/100000000000000 : ℝ)^6185
        have hw : |(1319923577/2500000000 : ℝ)|=(1319923577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329980897/625000000 : ℝ)|^8233 ≤ (8546493648913/20000000000000 : ℝ)^6185
        have hw : |(329980897/625000000 : ℝ)|=(329980897/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_box_5 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2682157529/5000000000 : ℝ)*x 0 + (-2236547101/10000000000 : ℝ)*x 1 + (32998091/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682157529/5000000000 : ℝ)^8233 ≤ (872931253843/2000000000000 : ℝ)^6185 := by
    have hnat : (2682157529 : ℕ)^8233*2000000000000^6185 ≤ 872931253843^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682157529 5000000000 872931253843 2000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2236547101/10000000000 : ℝ)^8233 ≤ (13620966804821/100000000000000 : ℝ)^6185 := by
    have hnat : (2236547101 : ℕ)^8233*100000000000000^6185 ≤ 13620966804821^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236547101 10000000000 13620966804821 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32998091/62500000 : ℝ)^8233 ≤ (42732470485509/100000000000000 : ℝ)^6185 := by
    have hnat : (32998091 : ℕ)^8233*100000000000000^6185 ≤ 42732470485509^6185*62500000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32998091 62500000 42732470485509 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682157529/5000000000 : ℝ), (-2236547101/10000000000 : ℝ), (32998091/62500000 : ℝ)] ![(872931253843/2000000000000 : ℝ), (13620966804821/100000000000000 : ℝ), (42732470485509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682157529/5000000000 : ℝ)|^8233 ≤ (872931253843/2000000000000 : ℝ)^6185
        have hw : |(2682157529/5000000000 : ℝ)|=(2682157529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2236547101/10000000000 : ℝ)|^8233 ≤ (13620966804821/100000000000000 : ℝ)^6185
        have hw : |(-2236547101/10000000000 : ℝ)|=(2236547101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32998091/62500000 : ℝ)|^8233 ≤ (42732470485509/100000000000000 : ℝ)^6185
        have hw : |(32998091/62500000 : ℝ)|=(32998091/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_box_6 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2682157967/5000000000 : ℝ)*x 0 + (5279693949/10000000000 : ℝ)*x 1 + (-2236546743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682157967/5000000000 : ℝ)^8233 ≤ (2727910761237/6250000000000 : ℝ)^6185 := by
    have hnat : (2682157967 : ℕ)^8233*6250000000000^6185 ≤ 2727910761237^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682157967 5000000000 2727910761237 6250000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279693949/10000000000 : ℝ)^8233 ≤ (42732463902737/100000000000000 : ℝ)^6185 := by
    have hnat : (5279693949 : ℕ)^8233*100000000000000^6185 ≤ 42732463902737^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279693949 10000000000 42732463902737 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2236546743/10000000000 : ℝ)^8233 ≤ (6810481951297/50000000000000 : ℝ)^6185 := by
    have hnat : (2236546743 : ℕ)^8233*50000000000000^6185 ≤ 6810481951297^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236546743 10000000000 6810481951297 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682157967/5000000000 : ℝ), (5279693949/10000000000 : ℝ), (-2236546743/10000000000 : ℝ)] ![(2727910761237/6250000000000 : ℝ), (42732463902737/100000000000000 : ℝ), (6810481951297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682157967/5000000000 : ℝ)|^8233 ≤ (2727910761237/6250000000000 : ℝ)^6185
        have hw : |(2682157967/5000000000 : ℝ)|=(2682157967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279693949/10000000000 : ℝ)|^8233 ≤ (42732463902737/100000000000000 : ℝ)^6185
        have hw : |(5279693949/10000000000 : ℝ)|=(5279693949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2236546743/10000000000 : ℝ)|^8233 ≤ (6810481951297/50000000000000 : ℝ)^6185
        have hw : |(-2236546743/10000000000 : ℝ)|=(2236546743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_box_7 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4270243649/10000000000 : ℝ)*x 0 + (2217953509/5000000000 : ℝ)*x 1 + (4435907569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4270243649/10000000000 : ℝ)^8233 ≤ (32217124577901/100000000000000 : ℝ)^6185 := by
    have hnat : (4270243649 : ℕ)^8233*100000000000000^6185 ≤ 32217124577901^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4270243649 10000000000 32217124577901 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2217953509/5000000000 : ℝ)^8233 ≤ (33891434905501/100000000000000 : ℝ)^6185 := by
    have hnat : (2217953509 : ℕ)^8233*100000000000000^6185 ≤ 33891434905501^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217953509 5000000000 33891434905501 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4435907569/10000000000 : ℝ)^8233 ≤ (8472860127309/25000000000000 : ℝ)^6185 := by
    have hnat : (4435907569 : ℕ)^8233*25000000000000^6185 ≤ 8472860127309^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4435907569 10000000000 8472860127309 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4270243649/10000000000 : ℝ), (2217953509/5000000000 : ℝ), (4435907569/10000000000 : ℝ)] ![(32217124577901/100000000000000 : ℝ), (33891434905501/100000000000000 : ℝ), (8472860127309/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4270243649/10000000000 : ℝ)|^8233 ≤ (32217124577901/100000000000000 : ℝ)^6185
        have hw : |(4270243649/10000000000 : ℝ)|=(4270243649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2217953509/5000000000 : ℝ)|^8233 ≤ (33891434905501/100000000000000 : ℝ)^6185
        have hw : |(2217953509/5000000000 : ℝ)|=(2217953509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4435907569/10000000000 : ℝ)|^8233 ≤ (8472860127309/25000000000000 : ℝ)^6185
        have hw : |(4435907569/10000000000 : ℝ)|=(4435907569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_box_8 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1146851159/5000000000 : ℝ)*x 0 + (521323279/1000000000 : ℝ)*x 1 + (5387312451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1146851159/5000000000 : ℝ)^8233 ≤ (14086260815449/100000000000000 : ℝ)^6185 := by
    have hnat : (1146851159 : ℕ)^8233*100000000000000^6185 ≤ 14086260815449^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146851159 5000000000 14086260815449 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521323279/1000000000 : ℝ)^8233 ≤ (42017923336699/100000000000000 : ℝ)^6185 := by
    have hnat : (521323279 : ℕ)^8233*100000000000000^6185 ≤ 42017923336699^6185*1000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521323279 1000000000 42017923336699 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387312451/10000000000 : ℝ)^8233 ≤ (8779163166591/20000000000000 : ℝ)^6185 := by
    have hnat : (5387312451 : ℕ)^8233*20000000000000^6185 ≤ 8779163166591^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387312451 10000000000 8779163166591 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1146851159/5000000000 : ℝ), (521323279/1000000000 : ℝ), (5387312451/10000000000 : ℝ)] ![(14086260815449/100000000000000 : ℝ), (42017923336699/100000000000000 : ℝ), (8779163166591/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1146851159/5000000000 : ℝ)|^8233 ≤ (14086260815449/100000000000000 : ℝ)^6185
        have hw : |(-1146851159/5000000000 : ℝ)|=(1146851159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521323279/1000000000 : ℝ)|^8233 ≤ (42017923336699/100000000000000 : ℝ)^6185
        have hw : |(521323279/1000000000 : ℝ)|=(521323279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387312451/10000000000 : ℝ)|^8233 ≤ (8779163166591/20000000000000 : ℝ)^6185
        have hw : |(5387312451/10000000000 : ℝ)|=(5387312451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_box_9 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288102289/10000000000 : ℝ)*x 0 + (-274311617/1250000000 : ℝ)*x 1 + (336707017/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288102289/10000000000 : ℝ)^8233 ≤ (42823077279953/100000000000000 : ℝ)^6185 := by
    have hnat : (5288102289 : ℕ)^8233*100000000000000^6185 ≤ 42823077279953^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288102289 10000000000 42823077279953 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274311617/1250000000 : ℝ)^8233 ≤ (3320277205463/25000000000000 : ℝ)^6185 := by
    have hnat : (274311617 : ℕ)^8233*25000000000000^6185 ≤ 3320277205463^6185*1250000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274311617 1250000000 3320277205463 25000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336707017/625000000 : ℝ)^8233 ≤ (21947906945761/50000000000000 : ℝ)^6185 := by
    have hnat : (336707017 : ℕ)^8233*50000000000000^6185 ≤ 21947906945761^6185*625000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336707017 625000000 21947906945761 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288102289/10000000000 : ℝ), (-274311617/1250000000 : ℝ), (336707017/625000000 : ℝ)] ![(42823077279953/100000000000000 : ℝ), (3320277205463/25000000000000 : ℝ), (21947906945761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288102289/10000000000 : ℝ)|^8233 ≤ (42823077279953/100000000000000 : ℝ)^6185
        have hw : |(5288102289/10000000000 : ℝ)|=(5288102289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-274311617/1250000000 : ℝ)|^8233 ≤ (3320277205463/25000000000000 : ℝ)^6185
        have hw : |(-274311617/1250000000 : ℝ)|=(274311617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336707017/625000000 : ℝ)|^8233 ≤ (21947906945761/50000000000000 : ℝ)^6185
        have hw : |(336707017/625000000 : ℝ)|=(336707017/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_box_10 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288102609/10000000000 : ℝ)*x 0 + (2693656191/5000000000 : ℝ)*x 1 + (-2194492359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288102609/10000000000 : ℝ)^8233 ≤ (68516929167/160000000000 : ℝ)^6185 := by
    have hnat : (5288102609 : ℕ)^8233*160000000000^6185 ≤ 68516929167^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288102609 10000000000 68516929167 160000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693656191/5000000000 : ℝ)^8233 ≤ (43895815084581/100000000000000 : ℝ)^6185 := by
    have hnat : (2693656191 : ℕ)^8233*100000000000000^6185 ≤ 43895815084581^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693656191 5000000000 43895815084581 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2194492359/10000000000 : ℝ)^8233 ≤ (13281104173549/100000000000000 : ℝ)^6185 := by
    have hnat : (2194492359 : ℕ)^8233*100000000000000^6185 ≤ 13281104173549^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194492359 10000000000 13281104173549 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288102609/10000000000 : ℝ), (2693656191/5000000000 : ℝ), (-2194492359/10000000000 : ℝ)] ![(68516929167/160000000000 : ℝ), (43895815084581/100000000000000 : ℝ), (13281104173549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288102609/10000000000 : ℝ)|^8233 ≤ (68516929167/160000000000 : ℝ)^6185
        have hw : |(5288102609/10000000000 : ℝ)|=(5288102609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693656191/5000000000 : ℝ)|^8233 ≤ (43895815084581/100000000000000 : ℝ)^6185
        have hw : |(2693656191/5000000000 : ℝ)|=(2693656191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2194492359/10000000000 : ℝ)|^8233 ≤ (13281104173549/100000000000000 : ℝ)^6185
        have hw : |(-2194492359/10000000000 : ℝ)|=(2194492359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_box_11 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (901794173/2000000000 : ℝ)*x 0 + (2158212367/5000000000 : ℝ)*x 1 + (4316424973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (901794173/2000000000 : ℝ)^8233 ≤ (3463652168449/10000000000000 : ℝ)^6185 := by
    have hnat : (901794173 : ℕ)^8233*10000000000000^6185 ≤ 3463652168449^6185*2000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901794173 2000000000 3463652168449 10000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2158212367/5000000000 : ℝ)^8233 ≤ (6536347590133/20000000000000 : ℝ)^6185 := by
    have hnat : (2158212367 : ℕ)^8233*20000000000000^6185 ≤ 6536347590133^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158212367 5000000000 6536347590133 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4316424973/10000000000 : ℝ)^8233 ≤ (16340870179723/50000000000000 : ℝ)^6185 := by
    have hnat : (4316424973 : ℕ)^8233*50000000000000^6185 ≤ 16340870179723^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316424973 10000000000 16340870179723 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(901794173/2000000000 : ℝ), (2158212367/5000000000 : ℝ), (4316424973/10000000000 : ℝ)] ![(3463652168449/10000000000000 : ℝ), (6536347590133/20000000000000 : ℝ), (16340870179723/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(901794173/2000000000 : ℝ)|^8233 ≤ (3463652168449/10000000000000 : ℝ)^6185
        have hw : |(901794173/2000000000 : ℝ)|=(901794173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2158212367/5000000000 : ℝ)|^8233 ≤ (6536347590133/20000000000000 : ℝ)^6185
        have hw : |(2158212367/5000000000 : ℝ)|=(2158212367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4316424973/10000000000 : ℝ)|^8233 ≤ (16340870179723/50000000000000 : ℝ)^6185
        have hw : |(4316424973/10000000000 : ℝ)|=(4316424973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_box_12 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2141343747/10000000000 : ℝ)*x 0 + (5442820999/10000000000 : ℝ)*x 1 + (2635854061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141343747/10000000000 : ℝ)^8233 ≤ (6427333039269/50000000000000 : ℝ)^6185 := by
    have hnat : (2141343747 : ℕ)^8233*50000000000000^6185 ≤ 6427333039269^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141343747 10000000000 6427333039269 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442820999/10000000000 : ℝ)^8233 ≤ (44498885895403/100000000000000 : ℝ)^6185 := by
    have hnat : (5442820999 : ℕ)^8233*100000000000000^6185 ≤ 44498885895403^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442820999 10000000000 44498885895403 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2635854061/5000000000 : ℝ)^8233 ≤ (42646448012533/100000000000000 : ℝ)^6185 := by
    have hnat : (2635854061 : ℕ)^8233*100000000000000^6185 ≤ 42646448012533^6185*5000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635854061 5000000000 42646448012533 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2141343747/10000000000 : ℝ), (5442820999/10000000000 : ℝ), (2635854061/5000000000 : ℝ)] ![(6427333039269/50000000000000 : ℝ), (44498885895403/100000000000000 : ℝ), (42646448012533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2141343747/10000000000 : ℝ)|^8233 ≤ (6427333039269/50000000000000 : ℝ)^6185
        have hw : |(-2141343747/10000000000 : ℝ)|=(2141343747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442820999/10000000000 : ℝ)|^8233 ≤ (44498885895403/100000000000000 : ℝ)^6185
        have hw : |(5442820999/10000000000 : ℝ)|=(5442820999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2635854061/5000000000 : ℝ)|^8233 ≤ (42646448012533/100000000000000 : ℝ)^6185
        have hw : |(2635854061/5000000000 : ℝ)|=(2635854061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_box_13 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369968339/10000000000 : ℝ)*x 0 + (-2239603869/10000000000 : ℝ)*x 1 + (5271707843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369968339/10000000000 : ℝ)^8233 ≤ (43707802032797/100000000000000 : ℝ)^6185 := by
    have hnat : (5369968339 : ℕ)^8233*100000000000000^6185 ≤ 43707802032797^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369968339 10000000000 43707802032797 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2239603869/10000000000 : ℝ)^8233 ≤ (13645752950979/100000000000000 : ℝ)^6185 := by
    have hnat : (2239603869 : ℕ)^8233*100000000000000^6185 ≤ 13645752950979^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239603869 10000000000 13645752950979 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271707843/10000000000 : ℝ)^8233 ≤ (42646445008159/100000000000000 : ℝ)^6185 := by
    have hnat : (5271707843 : ℕ)^8233*100000000000000^6185 ≤ 42646445008159^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271707843 10000000000 42646445008159 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369968339/10000000000 : ℝ), (-2239603869/10000000000 : ℝ), (5271707843/10000000000 : ℝ)] ![(43707802032797/100000000000000 : ℝ), (13645752950979/100000000000000 : ℝ), (42646445008159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369968339/10000000000 : ℝ)|^8233 ≤ (43707802032797/100000000000000 : ℝ)^6185
        have hw : |(5369968339/10000000000 : ℝ)|=(5369968339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2239603869/10000000000 : ℝ)|^8233 ≤ (13645752950979/100000000000000 : ℝ)^6185
        have hw : |(-2239603869/10000000000 : ℝ)|=(2239603869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271707843/10000000000 : ℝ)|^8233 ≤ (42646445008159/100000000000000 : ℝ)^6185
        have hw : |(5271707843/10000000000 : ℝ)|=(5271707843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_box_14 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1073993641/2000000000 : ℝ)*x 0 + (1317926999/2500000000 : ℝ)*x 1 + (-447920769/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073993641/2000000000 : ℝ)^8233 ≤ (8741560116197/20000000000000 : ℝ)^6185 := by
    have hnat : (1073993641 : ℕ)^8233*20000000000000^6185 ≤ 8741560116197^6185*2000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073993641 2000000000 8741560116197 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1317926999/2500000000 : ℝ)^8233 ≤ (42646446655719/100000000000000 : ℝ)^6185 := by
    have hnat : (1317926999 : ℕ)^8233*100000000000000^6185 ≤ 42646446655719^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317926999 2500000000 42646446655719 100000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447920769/2000000000 : ℝ)^8233 ≤ (1705719094541/12500000000000 : ℝ)^6185 := by
    have hnat : (447920769 : ℕ)^8233*12500000000000^6185 ≤ 1705719094541^6185*2000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447920769 2000000000 1705719094541 12500000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073993641/2000000000 : ℝ), (1317926999/2500000000 : ℝ), (-447920769/2000000000 : ℝ)] ![(8741560116197/20000000000000 : ℝ), (42646446655719/100000000000000 : ℝ), (1705719094541/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073993641/2000000000 : ℝ)|^8233 ≤ (8741560116197/20000000000000 : ℝ)^6185
        have hw : |(1073993641/2000000000 : ℝ)|=(1073993641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1317926999/2500000000 : ℝ)|^8233 ≤ (42646446655719/100000000000000 : ℝ)^6185
        have hw : |(1317926999/2500000000 : ℝ)|=(1317926999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-447920769/2000000000 : ℝ)|^8233 ≤ (1705719094541/12500000000000 : ℝ)^6185
        have hw : |(-447920769/2000000000 : ℝ)|=(447920769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1040_box_15 (p : ℝ) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4252276323/10000000000 : ℝ)*x 0 + (4444769289/10000000000 : ℝ)*x 1 + (1111192343/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4252276323/10000000000 : ℝ)^8233 ≤ (6407361815999/20000000000000 : ℝ)^6185 := by
    have hnat : (4252276323 : ℕ)^8233*20000000000000^6185 ≤ 6407361815999^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252276323 10000000000 6407361815999 20000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4444769289/10000000000 : ℝ)^8233 ≤ (16990797517081/50000000000000 : ℝ)^6185 := by
    have hnat : (4444769289 : ℕ)^8233*50000000000000^6185 ≤ 16990797517081^6185*10000000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4444769289 10000000000 16990797517081 50000000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1111192343/2500000000 : ℝ)^8233 ≤ (849539896971/2500000000000 : ℝ)^6185 := by
    have hnat : (1111192343 : ℕ)^8233*2500000000000^6185 ≤ 849539896971^6185*2500000000^8233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111192343 2500000000 849539896971 2500000000000 8233 6185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8233/2048 : ℝ)) 8233 6185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4252276323/10000000000 : ℝ), (4444769289/10000000000 : ℝ), (1111192343/2500000000 : ℝ)] ![(6407361815999/20000000000000 : ℝ), (16990797517081/50000000000000 : ℝ), (849539896971/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4252276323/10000000000 : ℝ)|^8233 ≤ (6407361815999/20000000000000 : ℝ)^6185
        have hw : |(4252276323/10000000000 : ℝ)|=(4252276323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4444769289/10000000000 : ℝ)|^8233 ≤ (16990797517081/50000000000000 : ℝ)^6185
        have hw : |(4444769289/10000000000 : ℝ)|=(4444769289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1111192343/2500000000 : ℝ)|^8233 ≤ (849539896971/2500000000000 : ℝ)^6185
        have hw : |(1111192343/2500000000 : ℝ)|=(1111192343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1040_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6993/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29611/50000 : ℝ) ∧ (7949/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82893/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6993/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (701/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6993/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (701/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6993/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (701/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6993/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (701/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6993/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (701/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6993/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (701/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (701/6250 : ℝ) ^ (1029/256 : ℝ) ≤ (947707174225327/6250000000000000000 : ℝ) := by
    have hpowers : (701/6250 : ℝ)^1029 ≤ (947707174225327/6250000000000000000 : ℝ)^256 := by
      have hnat : (701 : ℕ)^1029*6250000000000000000^256 ≤ 947707174225327^256*6250^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        701 6250 947707174225327 6250000000000000000 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (701/6250 : ℝ)) (X := (947707174225327/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hpowhi : (6993/50000 : ℝ) ^ (1029/256 : ℝ) ≤ (36820393224657267/100000000000000000000 : ℝ) := by
    have hpowers : (6993/50000 : ℝ)^1029 ≤ (36820393224657267/100000000000000000000 : ℝ)^256 := by
      have hnat : (6993 : ℕ)^1029*100000000000000000000^256 ≤ 36820393224657267^256*50000^1029 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6993 50000 36820393224657267 100000000000000000000 1029 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6993/50000 : ℝ)) (X := (36820393224657267/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125947707174225327/3125000000000000000 : ℝ) ≤ (5000377197909691/5000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (3125947707174225327/3125000000000000000 : ℝ)^256 ≤ (5000377197909691/5000000000000000 : ℝ)^1029 := by
      have hnat : (3125947707174225327 : ℕ)^256*5000000000000000^1029 ≤ 5000377197909691^1029*3125000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125947707174225327 3125000000000000000 5000377197909691 5000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000377197909691/5000000000000000 : ℝ)) (X := (3125947707174225327/3125000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051983708012262499/100000000000000000000 : ℝ) ≤ (5000646512712529/5000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (100051983708012262499/100000000000000000000 : ℝ)^256 ≤ (5000646512712529/5000000000000000 : ℝ)^1029 := by
      have hnat : (100051983708012262499 : ℕ)^256*5000000000000000^1029 ≤ 5000646512712529^1029*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051983708012262499 100000000000000000000 5000646512712529 5000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000646512712529/5000000000000000 : ℝ)) (X := (100051983708012262499/100000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036820393224657267/50000000000000000000 : ℝ) ≤ (5000915827515367/5000000000000000 : ℝ) ^ (1029/256 : ℝ) := by
    have hpowers : (50036820393224657267/50000000000000000000 : ℝ)^256 ≤ (5000915827515367/5000000000000000 : ℝ)^1029 := by
      have hnat : (50036820393224657267 : ℕ)^256*5000000000000000^1029 ≤ 5000915827515367^1029*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036820393224657267 50000000000000000000 5000915827515367 5000000000000000 256 1029 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000915827515367/5000000000000000 : ℝ)) (X := (50036820393224657267/50000000000000000000 : ℝ)) (by norm_num) 1029 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(947707174225327/6250000000000000000 : ℝ) ≤ ((6922501784276291027/6925000000000000000 : ℝ)+2*(134657401419/69250000000000 : ℝ)*(701/6250 : ℝ))^(1029/256 : ℝ) := by
    rw [show (6922501784276291027/6925000000000000000 : ℝ)+2*(134657401419/69250000000000 : ℝ)*(701/6250 : ℝ)=(5000377197909691/5000000000000000 : ℝ) by norm_num, show 1+2*(947707174225327/6250000000000000000 : ℝ)=(3125947707174225327/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36820393224657267/100000000000000000000 : ℝ)+(947707174225327/6250000000000000000 : ℝ) ≤ ((6922501784276291027/6925000000000000000 : ℝ)+(134657401419/69250000000000 : ℝ)*((6993/50000 : ℝ)+(701/6250 : ℝ)))^(1029/256 : ℝ) := by
    rw [show (6922501784276291027/6925000000000000000 : ℝ)+(134657401419/69250000000000 : ℝ)*((6993/50000 : ℝ)+(701/6250 : ℝ))=(5000646512712529/5000000000000000 : ℝ) by norm_num, show 1+(36820393224657267/100000000000000000000 : ℝ)+(947707174225327/6250000000000000000 : ℝ)=(100051983708012262499/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36820393224657267/100000000000000000000 : ℝ) ≤ ((6922501784276291027/6925000000000000000 : ℝ)+2*(134657401419/69250000000000 : ℝ)*(6993/50000 : ℝ))^(1029/256 : ℝ) := by
    rw [show (6922501784276291027/6925000000000000000 : ℝ)+2*(134657401419/69250000000000 : ℝ)*(6993/50000 : ℝ)=(5000915827515367/5000000000000000 : ℝ) by norm_num, show 1+2*(36820393224657267/100000000000000000000 : ℝ)=(50036820393224657267/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6922501784276291027/6925000000000000000 : ℝ)*(X 1 0+X 2 0)+(134657401419/69250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (701/6250 : ℝ)) (hi := (6993/50000 : ℝ)) (c := (6922501784276291027/6925000000000000000 : ℝ)) (alpha := (134657401419/69250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6922501784276291027/6925000000000000000 : ℝ)*(X 0 1+X 2 1)+(134657401419/69250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (701/6250 : ℝ)) (hi := (6993/50000 : ℝ)) (c := (6922501784276291027/6925000000000000000 : ℝ)) (alpha := (134657401419/69250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6922501784276291027/6925000000000000000 : ℝ)*(X 0 2+X 1 2)+(134657401419/69250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1029/256 : ℝ)) (lo := (701/6250 : ℝ)) (hi := (6993/50000 : ℝ)) (c := (6922501784276291027/6925000000000000000 : ℝ)) (alpha := (134657401419/69250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2086271981/10000000000 : ℝ)*X 0 0+(2688857757/5000000000 : ℝ)*X 0 1+(2688857889/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5294902147/10000000000 : ℝ)*X 1 0+(-2198307383/10000000000 : ℝ)*X 1 1+(1344428957/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647450941/5000000000 : ℝ)*X 2 0+(5377716073/10000000000 : ℝ)*X 2 1+(-137394213/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4487932089/10000000000 : ℝ)*X 0 0+(4327084781/10000000000 : ℝ)*X 0 1+(865416943/2000000000 : ℝ)*X 0 2+(4487932089/10000000000 : ℝ)*X 1 0+(4327084781/10000000000 : ℝ)*X 1 1+(865416943/2000000000 : ℝ)*X 1 2+(4487932089/10000000000 : ℝ)*X 2 0+(4327084781/10000000000 : ℝ)*X 2 1+(865416943/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2348388411/10000000000 : ℝ)*X 0 0+(1319923577/2500000000 : ℝ)*X 0 1+(329980897/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2682157529/5000000000 : ℝ)*X 1 0+(-2236547101/10000000000 : ℝ)*X 1 1+(32998091/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2682157967/5000000000 : ℝ)*X 2 0+(5279693949/10000000000 : ℝ)*X 2 1+(-2236546743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4270243649/10000000000 : ℝ)*X 0 0+(2217953509/5000000000 : ℝ)*X 0 1+(4435907569/10000000000 : ℝ)*X 0 2+(4270243649/10000000000 : ℝ)*X 1 0+(2217953509/5000000000 : ℝ)*X 1 1+(4435907569/10000000000 : ℝ)*X 1 2+(4270243649/10000000000 : ℝ)*X 2 0+(2217953509/5000000000 : ℝ)*X 2 1+(4435907569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1146851159/5000000000 : ℝ)*X 0 0+(521323279/1000000000 : ℝ)*X 0 1+(5387312451/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288102289/10000000000 : ℝ)*X 1 0+(-274311617/1250000000 : ℝ)*X 1 1+(336707017/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288102609/10000000000 : ℝ)*X 2 0+(2693656191/5000000000 : ℝ)*X 2 1+(-2194492359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((901794173/2000000000 : ℝ)*X 0 0+(2158212367/5000000000 : ℝ)*X 0 1+(4316424973/10000000000 : ℝ)*X 0 2+(901794173/2000000000 : ℝ)*X 1 0+(2158212367/5000000000 : ℝ)*X 1 1+(4316424973/10000000000 : ℝ)*X 1 2+(901794173/2000000000 : ℝ)*X 2 0+(2158212367/5000000000 : ℝ)*X 2 1+(4316424973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2141343747/10000000000 : ℝ)*X 0 0+(5442820999/10000000000 : ℝ)*X 0 1+(2635854061/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369968339/10000000000 : ℝ)*X 1 0+(-2239603869/10000000000 : ℝ)*X 1 1+(5271707843/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1073993641/2000000000 : ℝ)*X 2 0+(1317926999/2500000000 : ℝ)*X 2 1+(-447920769/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4252276323/10000000000 : ℝ)*X 0 0+(4444769289/10000000000 : ℝ)*X 0 1+(1111192343/2500000000 : ℝ)*X 0 2+(4252276323/10000000000 : ℝ)*X 1 0+(4444769289/10000000000 : ℝ)*X 1 1+(1111192343/2500000000 : ℝ)*X 1 2+(4252276323/10000000000 : ℝ)*X 2 0+(4444769289/10000000000 : ℝ)*X 2 1+(1111192343/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1040_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-53859931791110595189085882601973/86562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8910041/12500000000000 : ℝ)*(upper0) + (97116899/50000000000000 : ℝ)*(lower1) + (349452257/100000000000000 : ℝ)*(lower2) + (1767227/2000000000000 : ℝ)*(lower3) + (24726047/100000000000000 : ℝ)*(upper5) + (1917311525001167/50000000000000 : ℝ)*(major0) + (1917311525001167/50000000000000 : ℝ)*(major1) + (1917311525001167/50000000000000 : ℝ)*(major2) + (13892525907/100000000000000 : ℝ)*(sp2) + (5090021786221089/100000000000000 : ℝ)*(sp4) + (5090021786221089/100000000000000 : ℝ)*(sp5) + (2545003946847591/50000000000000 : ℝ)*(sp6) + (2599892071082783/100000000000000 : ℝ)*(sp7) + (72529311063/100000000000000 : ℝ)*(sp15) + (1299982300196923/50000000000000 : ℝ)*(f.failure) + (5090021786221089/100000000000000 : ℝ)*(f.sum) + (9480285535167/6925000000000000000000000000 : ℝ)*base65 + (20234433129672321491/346250000000000000000000000000000 : ℝ)*base68 + (2488344883554821491/346250000000000000000000000000000 : ℝ)*base70 + (2208186525053571491/346250000000000000000000000000000 : ℝ)*base72 + (8764364703323/1731250000000000000000000000 : ℝ)*base73 + (20331987713334821491/346250000000000000000000000000000 : ℝ)*base76 + (1865339747053571491/346250000000000000000000000000000 : ℝ)*base78 + (19281072672566428509/346250000000000000000000000000000 : ℝ)*base79 + (468532234767033/6925000000000000000000000000 : ℝ)*base82 + (1706827/500000000000000000000 : ℝ)*base90 + (1706827/500000000000000000000 : ℝ)*base92 + (1706827/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29611/50000 : ℝ) ≤ (102531604666124172491725316565477/173125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29407549/50000000000000 : ℝ)*(lower0) + (15752843/25000000000000 : ℝ)*(upper2) + (846887/4000000000000 : ℝ)*(lower4) + (1948568163090117/50000000000000 : ℝ)*(major0) + (1948568163090117/50000000000000 : ℝ)*(major1) + (1948568163090117/50000000000000 : ℝ)*(major2) + (5132173684064843/100000000000000 : ℝ)*(sp0) + (320760653175177/6250000000000 : ℝ)*(sp1) + (5132162985739959/100000000000000 : ℝ)*(sp2) + (1321172146370437/50000000000000 : ℝ)*(sp3) + (10786035073/100000000000000 : ℝ)*(sp5) + (9125548973/50000000000000 : ℝ)*(sp6) + (288946149/5000000000000 : ℝ)*(sp7) + (3776386531/50000000000000 : ℝ)*(sp12) + (1321175035831927/50000000000000 : ℝ)*(f.failure) + (1026436247367581/20000000000000 : ℝ)*(f.sum) + (82184365920733/6925000000000000000000000000 : ℝ)*base66 + (54301015350719841/346250000000000000000000000000000 : ℝ)*base68 + (695231743223219841/346250000000000000000000000000000 : ℝ)*base70 + (7043168167838219841/346250000000000000000000000000000 : ℝ)*base72 + (15940961034467/6925000000000000000000000000 : ℝ)*base73 + (725596351569280159/346250000000000000000000000000000 : ℝ)*base75 + (11043624626998219841/346250000000000000000000000000000 : ℝ)*base78 + (2682117401753030159/346250000000000000000000000000000 : ℝ)*base79 + (70467482989/54101562500000000000000000 : ℝ)*base81 + (826823/500000000000000000000 : ℝ)*base90 + (826823/500000000000000000000 : ℝ)*base92 + (826823/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (7949/10000 : ℝ) ≤ (137621431686352192630472140540623/173125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (177058203/100000000000000 : ℝ)*(upper0) + (132427231/100000000000000 : ℝ)*(lower3) + (349032639/100000000000000 : ℝ)*(upper4) + (4365440875607017/100000000000000 : ℝ)*(major0) + (4365440875607017/100000000000000 : ℝ)*(major1) + (4365440875607017/100000000000000 : ℝ)*(major2) + (16461612463/12500000000000 : ℝ)*(sp1) + (374683490997/100000000000000 : ℝ)*(sp2) + (126084231427/100000000000000 : ℝ)*(sp3) + (8992715957/100000000000000 : ℝ)*(sp4) + (2872251841036441/50000000000000 : ℝ)*(sp8) + (1148876196377827/20000000000000 : ℝ)*(sp9) + (2872068995648921/50000000000000 : ℝ)*(sp10) + (739936371071961/25000000000000 : ℝ)*(sp11) + (2959871568519271/100000000000000 : ℝ)*(f.failure) + (5744512674788839/100000000000000 : ℝ)*(f.sum) + (4057503080627/3462500000000000000000000000 : ℝ)*base66 + (2884286768780136459/692500000000000000000000000000000 : ℝ)*base67 + (982767885310136459/692500000000000000000000000000000 : ℝ)*base69 + (5000657456267363541/692500000000000000000000000000000 : ℝ)*base72 + (194696985951571/6925000000000000000000000000 : ℝ)*base73 + (882320077505136459/692500000000000000000000000000000 : ℝ)*base75 + (387940140650136459/692500000000000000000000000000000 : ℝ)*base77 + (10135938403147636459/692500000000000000000000000000000 : ℝ)*base79 + (20610200567029/6925000000000000000000000000 : ℝ)*base82 + (3319479/1000000000000000000000 : ℝ)*base90 + (3319479/1000000000000000000000 : ℝ)*base92 + (3319479/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-82893/100000 : ℝ) ≤ (-28700774994418651507771943059563/34625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19929153/100000000000000 : ℝ)*(upper3) + (4220693/12500000000000 : ℝ)*(lower4) + (17323199/50000000000000 : ℝ)*(upper5) + (879965239812277/20000000000000 : ℝ)*(major0) + (879965239812277/20000000000000 : ℝ)*(major1) + (879965239812277/20000000000000 : ℝ)*(major2) + (659505169/100000000000000 : ℝ)*(sp4) + (229764185071/100000000000000 : ℝ)*(sp5) + (754977917/500000000000 : ℝ)*(sp6) + (78269797121/100000000000000 : ℝ)*(sp7) + (5844096220511321/100000000000000 : ℝ)*(sp12) + (5843867115831419/100000000000000 : ℝ)*(sp13) + (5843945884433089/100000000000000 : ℝ)*(sp14) + (298310735660703/10000000000000 : ℝ)*(sp15) + (2983185626404151/100000000000000 : ℝ)*(f.failure) + (584409688001649/10000000000000 : ℝ)*(f.sum) + (8493118714521/1385000000000000000000000000 : ℝ)*base65 + (1062482538785661521/138500000000000000000000000000000 : ℝ)*base68 + (95869443865661521/138500000000000000000000000000000 : ℝ)*base70 + (550991346447161521/138500000000000000000000000000000 : ℝ)*base72 + (198759366451/86562500000000000000000000 : ℝ)*base73 + (567777492155161521/138500000000000000000000000000000 : ℝ)*base76 + (200626329458161521/138500000000000000000000000000000 : ℝ)*base78 + (240633697163838479/138500000000000000000000000000000 : ℝ)*base79 + (2667964247207/692500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1534599/1000000000000000000000 : ℝ)*base90 + (1534599/1000000000000000000000 : ℝ)*base92 + (1534599/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1040_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6993/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29611/50000 : ℝ) else (7949/10000 : ℝ) ≤ X j i ∧ X j i ≤ (82893/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1040_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1040_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2243/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29611/50000 : ℝ) else (7949/10000 : ℝ) ≤ X j i ∧ X j i ≤ (82893/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1040_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1040_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1029/256 : ℝ) ≤ p) (hpb : p ≤ (8233/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14748751/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2243/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29611/50000 : ℝ) else (7949/10000 : ℝ) ≤ X j i ∧ X j i ≤ (82893/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1040_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

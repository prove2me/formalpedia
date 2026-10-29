-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1598_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:38:25.731+00:00
-- url     : https://prove2.me/submissions/5a581c63-88b2-4634-a0d0-e51cdd547f84

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
theorem support_rectangle_w1598_s0_0 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1588462643/10000000000 : ℝ)*x 0 + (2926793593/5000000000 : ℝ)*x 1 + (976779111/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1588462643/10000000000 : ℝ)^4711 ≤ (9529328377419/100000000000000 : ℝ)^3687 := by
    have hnat : (1588462643 : ℕ)^4711*100000000000000^3687 ≤ 9529328377419^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1588462643 10000000000 9529328377419 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2926793593/5000000000 : ℝ)^4711 ≤ (157644074713/312500000000 : ℝ)^3687 := by
    have hnat : (2926793593 : ℕ)^4711*312500000000^3687 ≤ 157644074713^3687*5000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2926793593 5000000000 157644074713 312500000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (976779111/2000000000 : ℝ)^4711 ≤ (8004913541647/20000000000000 : ℝ)^3687 := by
    have hnat : (976779111 : ℕ)^4711*20000000000000^3687 ≤ 8004913541647^3687*2000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976779111 2000000000 8004913541647 20000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1588462643/10000000000 : ℝ), (2926793593/5000000000 : ℝ), (976779111/2000000000 : ℝ)] ![(9529328377419/100000000000000 : ℝ), (157644074713/312500000000 : ℝ), (8004913541647/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1588462643/10000000000 : ℝ)|^4711 ≤ (9529328377419/100000000000000 : ℝ)^3687
        have hw : |(-1588462643/10000000000 : ℝ)|=(1588462643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2926793593/5000000000 : ℝ)|^4711 ≤ (157644074713/312500000000 : ℝ)^3687
        have hw : |(2926793593/5000000000 : ℝ)|=(2926793593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(976779111/2000000000 : ℝ)|^4711 ≤ (8004913541647/20000000000000 : ℝ)^3687
        have hw : |(976779111/2000000000 : ℝ)|=(976779111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1598_s0_1 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2729345193/5000000000 : ℝ)*x 0 + (-2126822207/10000000000 : ℝ)*x 1 + (2441947667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2729345193/5000000000 : ℝ)^4711 ≤ (11534781509571/25000000000000 : ℝ)^3687 := by
    have hnat : (2729345193 : ℕ)^4711*25000000000000^3687 ≤ 11534781509571^3687*5000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729345193 5000000000 11534781509571 25000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126822207/10000000000 : ℝ)^4711 ≤ (1729538569131/12500000000000 : ℝ)^3687 := by
    have hnat : (2126822207 : ℕ)^4711*12500000000000^3687 ≤ 1729538569131^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126822207 10000000000 1729538569131 12500000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2441947667/5000000000 : ℝ)^4711 ≤ (250153533713/625000000000 : ℝ)^3687 := by
    have hnat : (2441947667 : ℕ)^4711*625000000000^3687 ≤ 250153533713^3687*5000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2441947667 5000000000 250153533713 625000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2729345193/5000000000 : ℝ), (-2126822207/10000000000 : ℝ), (2441947667/5000000000 : ℝ)] ![(11534781509571/25000000000000 : ℝ), (1729538569131/12500000000000 : ℝ), (250153533713/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2729345193/5000000000 : ℝ)|^4711 ≤ (11534781509571/25000000000000 : ℝ)^3687
        have hw : |(2729345193/5000000000 : ℝ)|=(2729345193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2126822207/10000000000 : ℝ)|^4711 ≤ (1729538569131/12500000000000 : ℝ)^3687
        have hw : |(-2126822207/10000000000 : ℝ)|=(2126822207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2441947667/5000000000 : ℝ)|^4711 ≤ (250153533713/625000000000 : ℝ)^3687
        have hw : |(2441947667/5000000000 : ℝ)|=(2441947667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1598_s0_2 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (68233629/125000000 : ℝ)*x 0 + (976779069/2000000000 : ℝ)*x 1 + (-2126822279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68233629/125000000 : ℝ)^4711 ≤ (2883695332843/6250000000000 : ℝ)^3687 := by
    have hnat : (68233629 : ℕ)^4711*6250000000000^3687 ≤ 2883695332843^3687*125000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68233629 125000000 2883695332843 6250000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (976779069/2000000000 : ℝ)^4711 ≤ (2501535344329/6250000000000 : ℝ)^3687 := by
    have hnat : (976779069 : ℕ)^4711*6250000000000^3687 ≤ 2501535344329^3687*2000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976779069 2000000000 2501535344329 6250000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2126822279/10000000000 : ℝ)^4711 ≤ (1729538643943/12500000000000 : ℝ)^3687 := by
    have hnat : (2126822279 : ℕ)^4711*12500000000000^3687 ≤ 1729538643943^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126822279 10000000000 1729538643943 12500000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68233629/125000000 : ℝ), (976779069/2000000000 : ℝ), (-2126822279/10000000000 : ℝ)] ![(2883695332843/6250000000000 : ℝ), (2501535344329/6250000000000 : ℝ), (1729538643943/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68233629/125000000 : ℝ)|^4711 ≤ (2883695332843/6250000000000 : ℝ)^3687
        have hw : |(68233629/125000000 : ℝ)|=(68233629/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(976779069/2000000000 : ℝ)|^4711 ≤ (2501535344329/6250000000000 : ℝ)^3687
        have hw : |(976779069/2000000000 : ℝ)|=(976779069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2126822279/10000000000 : ℝ)|^4711 ≤ (1729538643943/12500000000000 : ℝ)^3687
        have hw : |(-2126822279/10000000000 : ℝ)|=(2126822279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1598_s0_3 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4115714889/10000000000 : ℝ)*x 0 + (1536256359/5000000000 : ℝ)*x 1 + (5417769049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4115714889/10000000000 : ℝ)^4711 ≤ (32163564842721/100000000000000 : ℝ)^3687 := by
    have hnat : (4115714889 : ℕ)^4711*100000000000000^3687 ≤ 32163564842721^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4115714889 10000000000 32163564842721 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1536256359/5000000000 : ℝ)^4711 ≤ (4427759138367/20000000000000 : ℝ)^3687 := by
    have hnat : (1536256359 : ℕ)^4711*20000000000000^3687 ≤ 4427759138367^3687*5000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1536256359 5000000000 4427759138367 20000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417769049/10000000000 : ℝ)^4711 ≤ (5712204930607/12500000000000 : ℝ)^3687 := by
    have hnat : (5417769049 : ℕ)^4711*12500000000000^3687 ≤ 5712204930607^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417769049 10000000000 5712204930607 12500000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4115714889/10000000000 : ℝ), (1536256359/5000000000 : ℝ), (5417769049/10000000000 : ℝ)] ![(32163564842721/100000000000000 : ℝ), (4427759138367/20000000000000 : ℝ), (5712204930607/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4115714889/10000000000 : ℝ)|^4711 ≤ (32163564842721/100000000000000 : ℝ)^3687
        have hw : |(4115714889/10000000000 : ℝ)|=(4115714889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1536256359/5000000000 : ℝ)|^4711 ≤ (4427759138367/20000000000000 : ℝ)^3687
        have hw : |(1536256359/5000000000 : ℝ)|=(1536256359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417769049/10000000000 : ℝ)|^4711 ≤ (5712204930607/12500000000000 : ℝ)^3687
        have hw : |(5417769049/10000000000 : ℝ)|=(5417769049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1598_s0_4 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-79571189/500000000 : ℝ)*x 0 + (4908575901/10000000000 : ℝ)*x 1 + (291401189/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (79571189/500000000 : ℝ)^4711 ≤ (149250500781/1562500000000 : ℝ)^3687 := by
    have hnat : (79571189 : ℕ)^4711*1562500000000^3687 ≤ 149250500781^3687*500000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79571189 500000000 149250500781 1562500000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4908575901/10000000000 : ℝ)^4711 ≤ (8056636788281/20000000000000 : ℝ)^3687 := by
    have hnat : (4908575901 : ℕ)^4711*20000000000000^3687 ≤ 8056636788281^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4908575901 10000000000 8056636788281 20000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (291401189/500000000 : ℝ)^4711 ≤ (50164783986017/100000000000000 : ℝ)^3687 := by
    have hnat : (291401189 : ℕ)^4711*100000000000000^3687 ≤ 50164783986017^3687*500000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291401189 500000000 50164783986017 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-79571189/500000000 : ℝ), (4908575901/10000000000 : ℝ), (291401189/500000000 : ℝ)] ![(149250500781/1562500000000 : ℝ), (8056636788281/20000000000000 : ℝ), (50164783986017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-79571189/500000000 : ℝ)|^4711 ≤ (149250500781/1562500000000 : ℝ)^3687
        have hw : |(-79571189/500000000 : ℝ)|=(79571189/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4908575901/10000000000 : ℝ)|^4711 ≤ (8056636788281/20000000000000 : ℝ)^3687
        have hw : |(4908575901/10000000000 : ℝ)|=(4908575901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(291401189/500000000 : ℝ)|^4711 ≤ (50164783986017/100000000000000 : ℝ)^3687
        have hw : |(291401189/500000000 : ℝ)|=(291401189/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1598_s0_5 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (519383529/1000000000 : ℝ)*x 0 + (-591346677/5000000000 : ℝ)*x 1 + (5828023973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519383529/1000000000 : ℝ)^4711 ≤ (43298212830529/100000000000000 : ℝ)^3687 := by
    have hnat : (519383529 : ℕ)^4711*100000000000000^3687 ≤ 43298212830529^3687*1000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519383529 1000000000 43298212830529 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (591346677/5000000000 : ℝ)^4711 ≤ (6537001039031/100000000000000 : ℝ)^3687 := by
    have hnat : (591346677 : ℕ)^4711*100000000000000^3687 ≤ 6537001039031^3687*5000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591346677 5000000000 6537001039031 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5828023973/10000000000 : ℝ)^4711 ≤ (1003295722173/2000000000000 : ℝ)^3687 := by
    have hnat : (5828023973 : ℕ)^4711*2000000000000^3687 ≤ 1003295722173^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5828023973 10000000000 1003295722173 2000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519383529/1000000000 : ℝ), (-591346677/5000000000 : ℝ), (5828023973/10000000000 : ℝ)] ![(43298212830529/100000000000000 : ℝ), (6537001039031/100000000000000 : ℝ), (1003295722173/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519383529/1000000000 : ℝ)|^4711 ≤ (43298212830529/100000000000000 : ℝ)^3687
        have hw : |(519383529/1000000000 : ℝ)|=(519383529/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-591346677/5000000000 : ℝ)|^4711 ≤ (6537001039031/100000000000000 : ℝ)^3687
        have hw : |(-591346677/5000000000 : ℝ)|=(591346677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5828023973/10000000000 : ℝ)|^4711 ≤ (1003295722173/2000000000000 : ℝ)^3687
        have hw : |(5828023973/10000000000 : ℝ)|=(5828023973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1598_s0_6 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (81153677/156250000 : ℝ)*x 0 + (5828023791/10000000000 : ℝ)*x 1 + (-1182693581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81153677/156250000 : ℝ)^4711 ≤ (43298213235297/100000000000000 : ℝ)^3687 := by
    have hnat : (81153677 : ℕ)^4711*100000000000000^3687 ≤ 43298213235297^3687*156250000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81153677 156250000 43298213235297 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5828023791/10000000000 : ℝ)^4711 ≤ (12541196026749/25000000000000 : ℝ)^3687 := by
    have hnat : (5828023791 : ℕ)^4711*25000000000000^3687 ≤ 12541196026749^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5828023791 10000000000 12541196026749 25000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1182693581/10000000000 : ℝ)^4711 ≤ (3268501321087/50000000000000 : ℝ)^3687 := by
    have hnat : (1182693581 : ℕ)^4711*50000000000000^3687 ≤ 3268501321087^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1182693581 10000000000 3268501321087 50000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(81153677/156250000 : ℝ), (5828023791/10000000000 : ℝ), (-1182693581/10000000000 : ℝ)] ![(43298213235297/100000000000000 : ℝ), (12541196026749/25000000000000 : ℝ), (3268501321087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(81153677/156250000 : ℝ)|^4711 ≤ (43298213235297/100000000000000 : ℝ)^3687
        have hw : |(81153677/156250000 : ℝ)|=(81153677/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5828023791/10000000000 : ℝ)|^4711 ≤ (12541196026749/25000000000000 : ℝ)^3687
        have hw : |(5828023791/10000000000 : ℝ)|=(5828023791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1182693581/10000000000 : ℝ)|^4711 ≤ (3268501321087/50000000000000 : ℝ)^3687
        have hw : |(-1182693581/10000000000 : ℝ)|=(1182693581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1598_s0_7 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4122877249/10000000000 : ℝ)*x 0 + (2679038927/5000000000 : ℝ)*x 1 + (3134338849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4122877249/10000000000 : ℝ)^4711 ≤ (16117550030293/50000000000000 : ℝ)^3687 := by
    have hnat : (4122877249 : ℕ)^4711*50000000000000^3687 ≤ 16117550030293^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4122877249 10000000000 16117550030293 50000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2679038927/5000000000 : ℝ)^4711 ≤ (45055311564073/100000000000000 : ℝ)^3687 := by
    have hnat : (2679038927 : ℕ)^4711*100000000000000^3687 ≤ 45055311564073^3687*5000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679038927 5000000000 45055311564073 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3134338849/10000000000 : ℝ)^4711 ≤ (2270958836499/10000000000000 : ℝ)^3687 := by
    have hnat : (3134338849 : ℕ)^4711*10000000000000^3687 ≤ 2270958836499^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3134338849 10000000000 2270958836499 10000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4122877249/10000000000 : ℝ), (2679038927/5000000000 : ℝ), (3134338849/10000000000 : ℝ)] ![(16117550030293/50000000000000 : ℝ), (45055311564073/100000000000000 : ℝ), (2270958836499/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4122877249/10000000000 : ℝ)|^4711 ≤ (16117550030293/50000000000000 : ℝ)^3687
        have hw : |(4122877249/10000000000 : ℝ)|=(4122877249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2679038927/5000000000 : ℝ)|^4711 ≤ (45055311564073/100000000000000 : ℝ)^3687
        have hw : |(2679038927/5000000000 : ℝ)|=(2679038927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3134338849/10000000000 : ℝ)|^4711 ≤ (2270958836499/10000000000000 : ℝ)^3687
        have hw : |(3134338849/10000000000 : ℝ)|=(3134338849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1598_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170927903/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3757/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12261/50000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4707/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4707 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4707*1^1024 ≤ 0^1024*1^4707 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4707 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4707 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4707/1024 : ℝ) ≤ (740913059171986767/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4707 ≤ (740913059171986767/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4707*50000000000000000000^1024 ≤ 740913059171986767^1024*5^4707 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 740913059171986767 50000000000000000000 4707 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (740913059171986767/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4707 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4707/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4707 := by
      have hnat : (1 : ℕ)^1024*1^4707 ≤ 1^4707*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4707 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4707 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50740913059171986767/50000000000000000000 : ℝ) ≤ (10032051622271267/10000000000000000 : ℝ) ^ (4707/1024 : ℝ) := by
    have hpowers : (50740913059171986767/50000000000000000000 : ℝ)^1024 ≤ (10032051622271267/10000000000000000 : ℝ)^4707 := by
      have hnat : (50740913059171986767 : ℕ)^1024*10000000000000000^4707 ≤ 10032051622271267^4707*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50740913059171986767 50000000000000000000 10032051622271267 10000000000000000 1024 4707 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10032051622271267/10000000000000000 : ℝ)) (X := (50740913059171986767/50000000000000000000 : ℝ)) (by norm_num) 4707 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25740913059171986767/25000000000000000000 : ℝ) ≤ (5032051622271267/5000000000000000 : ℝ) ^ (4707/1024 : ℝ) := by
    have hpowers : (25740913059171986767/25000000000000000000 : ℝ)^1024 ≤ (5032051622271267/5000000000000000 : ℝ)^4707 := by
      have hnat : (25740913059171986767 : ℕ)^1024*5000000000000000^4707 ≤ 5032051622271267^4707*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25740913059171986767 25000000000000000000 5032051622271267 5000000000000000 1024 4707 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5032051622271267/5000000000000000 : ℝ)) (X := (25740913059171986767/25000000000000000000 : ℝ)) (by norm_num) 4707 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(32051622271267/4000000000000000 : ℝ)*(0 : ℝ))^(4707/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(32051622271267/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(740913059171986767/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(32051622271267/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4707/1024 : ℝ) := by
    rw [show (1 : ℝ)+(32051622271267/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10032051622271267/10000000000000000 : ℝ) by norm_num, show 1+(740913059171986767/50000000000000000000 : ℝ)+(0 : ℝ)=(50740913059171986767/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(740913059171986767/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(32051622271267/4000000000000000 : ℝ)*(2/5 : ℝ))^(4707/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(32051622271267/4000000000000000 : ℝ)*(2/5 : ℝ)=(5032051622271267/5000000000000000 : ℝ) by norm_num, show 1+2*(740913059171986767/50000000000000000000 : ℝ)=(25740913059171986767/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(32051622271267/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4707/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (32051622271267/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(32051622271267/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4707/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (32051622271267/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(32051622271267/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4707/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (32051622271267/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1588462643/10000000000 : ℝ)*X 0 0+(2926793593/5000000000 : ℝ)*X 0 1+(976779111/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2729345193/5000000000 : ℝ)*X 1 0+(-2126822207/10000000000 : ℝ)*X 1 1+(2441947667/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((68233629/125000000 : ℝ)*X 2 0+(976779069/2000000000 : ℝ)*X 2 1+(-2126822279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4115714889/10000000000 : ℝ)*X 0 0+(1536256359/5000000000 : ℝ)*X 0 1+(5417769049/10000000000 : ℝ)*X 0 2+(4115714889/10000000000 : ℝ)*X 1 0+(1536256359/5000000000 : ℝ)*X 1 1+(5417769049/10000000000 : ℝ)*X 1 2+(4115714889/10000000000 : ℝ)*X 2 0+(1536256359/5000000000 : ℝ)*X 2 1+(5417769049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-79571189/500000000 : ℝ)*X 0 0+(4908575901/10000000000 : ℝ)*X 0 1+(291401189/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((519383529/1000000000 : ℝ)*X 1 0+(-591346677/5000000000 : ℝ)*X 1 1+(5828023973/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((81153677/156250000 : ℝ)*X 2 0+(5828023791/10000000000 : ℝ)*X 2 1+(-1182693581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4122877249/10000000000 : ℝ)*X 0 0+(2679038927/5000000000 : ℝ)*X 0 1+(3134338849/10000000000 : ℝ)*X 0 2+(4122877249/10000000000 : ℝ)*X 1 0+(2679038927/5000000000 : ℝ)*X 1 1+(3134338849/10000000000 : ℝ)*X 1 2+(4122877249/10000000000 : ℝ)*X 2 0+(2679038927/5000000000 : ℝ)*X 2 1+(3134338849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (153077669196546104595381/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30613689/100000000000000 : ℝ)*(base1) + (667104627/100000000000000 : ℝ)*(base19) + (327317931/50000000000000 : ℝ)*(base23) + (46979869/50000000000000 : ℝ)*(upper3) + (3421177/5000000000000 : ℝ)*(upper5) + (728827498257581/100000000000000 : ℝ)*(major0) + (728827498257581/100000000000000 : ℝ)*(major1) + (728827498257581/100000000000000 : ℝ)*(major2) + (1031257991831951/100000000000000 : ℝ)*(sp0) + (128907439263211/12500000000000 : ℝ)*(sp1) + (515629763287227/50000000000000 : ℝ)*(sp2) + (106598394872119/25000000000000 : ℝ)*(sp3) + (2219992053/100000000000000 : ℝ)*(sp4) + (16838093/1562500000000 : ℝ)*(sp7) + (213197343870059/50000000000000 : ℝ)*(f.failure) + (206252036242063/20000000000000 : ℝ)*(f.sum) + (63053054574873/200000000000000000000000000000 : ℝ)*base66 + (502922744774873/400000000000000000000000000000 : ℝ)*base68 + (596693665574873/400000000000000000000000000000 : ℝ)*base70 + (49660709225127/400000000000000000000000000000 : ℝ)*base71 + (446611650774873/200000000000000000000000000000 : ℝ)*base74 + (82758324374873/400000000000000000000000000000 : ℝ)*base76 + (1684567175574873/400000000000000000000000000000 : ℝ)*base78 + (3255011541174873/400000000000000000000000000000 : ℝ)*base80 + (169366959974873/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (39356277/5000000000000000000000 : ℝ)*base89 + (39356277/5000000000000000000000 : ℝ)*base91 + (39356277/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (201813606321293457899499/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1717872579/100000000000000 : ℝ)*(base19) + (870021891/50000000000000 : ℝ)*(base23) + (5324597/3125000000000 : ℝ)*(base32) + (145766899/50000000000000 : ℝ)*(upper3) + (14946079/10000000000000 : ℝ)*(upper5) + (192162655198299/25000000000000 : ℝ)*(major0) + (192162655198299/25000000000000 : ℝ)*(major1) + (192162655198299/25000000000000 : ℝ)*(major2) + (4725514529/100000000000000 : ℝ)*(sp1) + (5004252071/100000000000000 : ℝ)*(sp2) + (1087608086025813/100000000000000 : ℝ)*(sp4) + (217520328527741/20000000000000 : ℝ)*(sp5) + (1087601341729959/100000000000000 : ℝ)*(sp6) + (449692716088661/100000000000000 : ℝ)*(sp7) + (89938577295153/20000000000000 : ℝ)*(f.failure) + (1087608086025813/100000000000000 : ℝ)*(f.sum) + (8508367475167/50000000000000000000000000000 : ℝ)*base66 + (345544054274833/100000000000000000000000000000 : ℝ)*base67 + (534273777925167/100000000000000000000000000000 : ℝ)*base70 + (379250468325167/100000000000000000000000000000 : ℝ)*base72 + (361598583924833/50000000000000000000000000000 : ℝ)*base73 + (213488729025167/100000000000000000000000000000 : ℝ)*base76 + (118583131125167/100000000000000000000000000000 : ℝ)*base78 + (709820899174833/100000000000000000000000000000 : ℝ)*base79 + (59486755075167/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5645841/2000000000000000000000 : ℝ)*base90 + (5645841/2000000000000000000000 : ℝ)*base92 + (5645841/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1598_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170927903/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3757/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12261/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1598_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1598_s1_0 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-214689451/1250000000 : ℝ)*x 0 + (2770773599/5000000000 : ℝ)*x 1 + (5112585723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214689451/1250000000 : ℝ)^4711 ≤ (10529498630271/100000000000000 : ℝ)^3687 := by
    have hnat : (214689451 : ℕ)^4711*100000000000000^3687 ≤ 10529498630271^3687*1250000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214689451 1250000000 10529498630271 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2770773599/5000000000 : ℝ)^4711 ≤ (47035853002087/100000000000000 : ℝ)^3687 := by
    have hnat : (2770773599 : ℕ)^4711*100000000000000^3687 ≤ 47035853002087^3687*5000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2770773599 5000000000 47035853002087 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5112585723/10000000000 : ℝ)^4711 ≤ (42434648353987/100000000000000 : ℝ)^3687 := by
    have hnat : (5112585723 : ℕ)^4711*100000000000000^3687 ≤ 42434648353987^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5112585723 10000000000 42434648353987 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-214689451/1250000000 : ℝ), (2770773599/5000000000 : ℝ), (5112585723/10000000000 : ℝ)] ![(10529498630271/100000000000000 : ℝ), (47035853002087/100000000000000 : ℝ), (42434648353987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-214689451/1250000000 : ℝ)|^4711 ≤ (10529498630271/100000000000000 : ℝ)^3687
        have hw : |(-214689451/1250000000 : ℝ)|=(214689451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2770773599/5000000000 : ℝ)|^4711 ≤ (47035853002087/100000000000000 : ℝ)^3687
        have hw : |(2770773599/5000000000 : ℝ)|=(2770773599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5112585723/10000000000 : ℝ)|^4711 ≤ (42434648353987/100000000000000 : ℝ)^3687
        have hw : |(5112585723/10000000000 : ℝ)|=(5112585723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1598_s1_1 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671951171/1250000000 : ℝ)*x 0 + (-1942329/10000000 : ℝ)*x 1 + (5112585573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671951171/1250000000 : ℝ)^4711 ≤ (9048752083231/20000000000000 : ℝ)^3687 := by
    have hnat : (671951171 : ℕ)^4711*20000000000000^3687 ≤ 9048752083231^3687*1250000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671951171 1250000000 9048752083231 20000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1942329/10000000 : ℝ)^4711 ≤ (6160796401469/50000000000000 : ℝ)^3687 := by
    have hnat : (1942329 : ℕ)^4711*50000000000000^3687 ≤ 6160796401469^3687*10000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1942329 10000000 6160796401469 50000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5112585573/10000000000 : ℝ)^4711 ≤ (42434646763203/100000000000000 : ℝ)^3687 := by
    have hnat : (5112585573 : ℕ)^4711*100000000000000^3687 ≤ 42434646763203^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5112585573 10000000000 42434646763203 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671951171/1250000000 : ℝ), (-1942329/10000000 : ℝ), (5112585573/10000000000 : ℝ)] ![(9048752083231/20000000000000 : ℝ), (6160796401469/50000000000000 : ℝ), (42434646763203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671951171/1250000000 : ℝ)|^4711 ≤ (9048752083231/20000000000000 : ℝ)^3687
        have hw : |(671951171/1250000000 : ℝ)|=(671951171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1942329/10000000 : ℝ)|^4711 ≤ (6160796401469/50000000000000 : ℝ)^3687
        have hw : |(-1942329/10000000 : ℝ)|=(1942329/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5112585573/10000000000 : ℝ)|^4711 ≤ (42434646763203/100000000000000 : ℝ)^3687
        have hw : |(5112585573/10000000000 : ℝ)|=(5112585573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1598_s1_2 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5375609013/10000000000 : ℝ)*x 0 + (1278146469/2500000000 : ℝ)*x 1 + (-77693163/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375609013/10000000000 : ℝ)^4711 ≤ (45243756598477/100000000000000 : ℝ)^3687 := by
    have hnat : (5375609013 : ℕ)^4711*100000000000000^3687 ≤ 45243756598477^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375609013 10000000000 45243756598477 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1278146469/2500000000 : ℝ)^4711 ≤ (42434649976587/100000000000000 : ℝ)^3687 := by
    have hnat : (1278146469 : ℕ)^4711*100000000000000^3687 ≤ 42434649976587^3687*2500000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1278146469 2500000000 42434649976587 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (77693163/400000000 : ℝ)^4711 ≤ (12321593410857/100000000000000 : ℝ)^3687 := by
    have hnat : (77693163 : ℕ)^4711*100000000000000^3687 ≤ 12321593410857^3687*400000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77693163 400000000 12321593410857 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375609013/10000000000 : ℝ), (1278146469/2500000000 : ℝ), (-77693163/400000000 : ℝ)] ![(45243756598477/100000000000000 : ℝ), (42434649976587/100000000000000 : ℝ), (12321593410857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375609013/10000000000 : ℝ)|^4711 ≤ (45243756598477/100000000000000 : ℝ)^3687
        have hw : |(5375609013/10000000000 : ℝ)|=(5375609013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1278146469/2500000000 : ℝ)|^4711 ≤ (42434649976587/100000000000000 : ℝ)^3687
        have hw : |(1278146469/2500000000 : ℝ)|=(1278146469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-77693163/400000000 : ℝ)|^4711 ≤ (12321593410857/100000000000000 : ℝ)^3687
        have hw : |(-77693163/400000000 : ℝ)|=(77693163/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1598_s1_3 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4209849229/10000000000 : ℝ)*x 0 + (464513261/1250000000 : ℝ)*x 1 + (1188393603/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4209849229/10000000000 : ℝ)^4711 ≤ (33106488735581/100000000000000 : ℝ)^3687 := by
    have hnat : (4209849229 : ℕ)^4711*100000000000000^3687 ≤ 33106488735581^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4209849229 10000000000 33106488735581 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (464513261/1250000000 : ℝ)^4711 ≤ (3528560590767/12500000000000 : ℝ)^3687 := by
    have hnat : (464513261 : ℕ)^4711*12500000000000^3687 ≤ 3528560590767^3687*1250000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464513261 1250000000 3528560590767 12500000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1188393603/2500000000 : ℝ)^4711 ≤ (38665026519463/100000000000000 : ℝ)^3687 := by
    have hnat : (1188393603 : ℕ)^4711*100000000000000^3687 ≤ 38665026519463^3687*2500000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1188393603 2500000000 38665026519463 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4209849229/10000000000 : ℝ), (464513261/1250000000 : ℝ), (1188393603/2500000000 : ℝ)] ![(33106488735581/100000000000000 : ℝ), (3528560590767/12500000000000 : ℝ), (38665026519463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4209849229/10000000000 : ℝ)|^4711 ≤ (33106488735581/100000000000000 : ℝ)^3687
        have hw : |(4209849229/10000000000 : ℝ)|=(4209849229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(464513261/1250000000 : ℝ)|^4711 ≤ (3528560590767/12500000000000 : ℝ)^3687
        have hw : |(464513261/1250000000 : ℝ)|=(464513261/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1188393603/2500000000 : ℝ)|^4711 ≤ (38665026519463/100000000000000 : ℝ)^3687
        have hw : |(1188393603/2500000000 : ℝ)|=(1188393603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1598_s1_4 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-343553099/2000000000 : ℝ)*x 0 + (1279341037/2500000000 : ℝ)*x 1 + (5536692819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343553099/2000000000 : ℝ)^4711 ≤ (10531456119603/100000000000000 : ℝ)^3687 := by
    have hnat : (343553099 : ℕ)^4711*100000000000000^3687 ≤ 10531456119603^3687*2000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343553099 2000000000 10531456119603 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1279341037/2500000000 : ℝ)^4711 ≤ (42485331211901/100000000000000 : ℝ)^3687 := by
    have hnat : (1279341037 : ℕ)^4711*100000000000000^3687 ≤ 42485331211901^3687*2500000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279341037 2500000000 42485331211901 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5536692819/10000000000 : ℝ)^4711 ≤ (46983212649427/100000000000000 : ℝ)^3687 := by
    have hnat : (5536692819 : ℕ)^4711*100000000000000^3687 ≤ 46983212649427^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5536692819 10000000000 46983212649427 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-343553099/2000000000 : ℝ), (1279341037/2500000000 : ℝ), (5536692819/10000000000 : ℝ)] ![(10531456119603/100000000000000 : ℝ), (42485331211901/100000000000000 : ℝ), (46983212649427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-343553099/2000000000 : ℝ)|^4711 ≤ (10531456119603/100000000000000 : ℝ)^3687
        have hw : |(-343553099/2000000000 : ℝ)|=(343553099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1279341037/2500000000 : ℝ)|^4711 ≤ (42485331211901/100000000000000 : ℝ)^3687
        have hw : |(1279341037/2500000000 : ℝ)|=(1279341037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5536692819/10000000000 : ℝ)|^4711 ≤ (46983212649427/100000000000000 : ℝ)^3687
        have hw : |(5536692819/10000000000 : ℝ)|=(5536692819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1598_s1_5 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2630855947/5000000000 : ℝ)*x 0 + (-1518221733/10000000000 : ℝ)*x 1 + (5536693089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2630855947/5000000000 : ℝ)^4711 ≤ (44022526784403/100000000000000 : ℝ)^3687 := by
    have hnat : (2630855947 : ℕ)^4711*100000000000000^3687 ≤ 44022526784403^3687*5000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630855947 5000000000 44022526784403 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1518221733/10000000000 : ℝ)^4711 ≤ (2248564406057/25000000000000 : ℝ)^3687 := by
    have hnat : (1518221733 : ℕ)^4711*25000000000000^3687 ≤ 2248564406057^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1518221733 10000000000 2248564406057 25000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5536693089/10000000000 : ℝ)^4711 ≤ (46983215576921/100000000000000 : ℝ)^3687 := by
    have hnat : (5536693089 : ℕ)^4711*100000000000000^3687 ≤ 46983215576921^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5536693089 10000000000 46983215576921 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2630855947/5000000000 : ℝ), (-1518221733/10000000000 : ℝ), (5536693089/10000000000 : ℝ)] ![(44022526784403/100000000000000 : ℝ), (2248564406057/25000000000000 : ℝ), (46983215576921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2630855947/5000000000 : ℝ)|^4711 ≤ (44022526784403/100000000000000 : ℝ)^3687
        have hw : |(2630855947/5000000000 : ℝ)|=(2630855947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1518221733/10000000000 : ℝ)|^4711 ≤ (2248564406057/25000000000000 : ℝ)^3687
        have hw : |(-1518221733/10000000000 : ℝ)|=(1518221733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5536693089/10000000000 : ℝ)|^4711 ≤ (46983215576921/100000000000000 : ℝ)^3687
        have hw : |(5536693089/10000000000 : ℝ)|=(5536693089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1598_s1_6 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1315427843/2500000000 : ℝ)*x 0 + (34604333/62500000 : ℝ)*x 1 + (-1518222197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1315427843/2500000000 : ℝ)^4711 ≤ (44022521204093/100000000000000 : ℝ)^3687 := by
    have hnat : (1315427843 : ℕ)^4711*100000000000000^3687 ≤ 44022521204093^3687*2500000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315427843 2500000000 44022521204093 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34604333/62500000 : ℝ)^4711 ≤ (11745804411963/25000000000000 : ℝ)^3687 := by
    have hnat : (34604333 : ℕ)^4711*25000000000000^3687 ≤ 11745804411963^3687*62500000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34604333 62500000 11745804411963 25000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1518222197/10000000000 : ℝ)^4711 ≤ (17988522273/200000000000 : ℝ)^3687 := by
    have hnat : (1518222197 : ℕ)^4711*200000000000^3687 ≤ 17988522273^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1518222197 10000000000 17988522273 200000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1315427843/2500000000 : ℝ), (34604333/62500000 : ℝ), (-1518222197/10000000000 : ℝ)] ![(44022521204093/100000000000000 : ℝ), (11745804411963/25000000000000 : ℝ), (17988522273/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1315427843/2500000000 : ℝ)|^4711 ≤ (44022521204093/100000000000000 : ℝ)^3687
        have hw : |(1315427843/2500000000 : ℝ)|=(1315427843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34604333/62500000 : ℝ)|^4711 ≤ (11745804411963/25000000000000 : ℝ)^3687
        have hw : |(34604333/62500000 : ℝ)|=(34604333/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1518222197/10000000000 : ℝ)|^4711 ≤ (17988522273/200000000000 : ℝ)^3687
        have hw : |(-1518222197/10000000000 : ℝ)|=(1518222197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1598_s1_7 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2105226429/5000000000 : ℝ)*x 0 + (4742018267/10000000000 : ℝ)*x 1 + (3727845881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105226429/5000000000 : ℝ)^4711 ≤ (33112554217181/100000000000000 : ℝ)^3687 := by
    have hnat : (2105226429 : ℕ)^4711*100000000000000^3687 ≤ 33112554217181^3687*5000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105226429 5000000000 33112554217181 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4742018267/10000000000 : ℝ)^4711 ≤ (38544964887951/100000000000000 : ℝ)^3687 := by
    have hnat : (4742018267 : ℕ)^4711*100000000000000^3687 ≤ 38544964887951^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4742018267 10000000000 38544964887951 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3727845881/10000000000 : ℝ)^4711 ≤ (28342480882331/100000000000000 : ℝ)^3687 := by
    have hnat : (3727845881 : ℕ)^4711*100000000000000^3687 ≤ 28342480882331^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3727845881 10000000000 28342480882331 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2105226429/5000000000 : ℝ), (4742018267/10000000000 : ℝ), (3727845881/10000000000 : ℝ)] ![(33112554217181/100000000000000 : ℝ), (38544964887951/100000000000000 : ℝ), (28342480882331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2105226429/5000000000 : ℝ)|^4711 ≤ (33112554217181/100000000000000 : ℝ)^3687
        have hw : |(2105226429/5000000000 : ℝ)|=(2105226429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4742018267/10000000000 : ℝ)|^4711 ≤ (38544964887951/100000000000000 : ℝ)^3687
        have hw : |(4742018267/10000000000 : ℝ)|=(4742018267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3727845881/10000000000 : ℝ)|^4711 ≤ (28342480882331/100000000000000 : ℝ)^3687
        have hw : |(3727845881/10000000000 : ℝ)|=(3727845881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1598_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170927903/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12261/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3757/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8907/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17991/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12261/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3757/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12261/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3757/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12261/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3757/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12261/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3757/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12261/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3757/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12261/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3757/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3757/100000 : ℝ) ^ (4707/1024 : ℝ) ≤ (28119103473997/100000000000000000000 : ℝ) := by
    have hpowers : (3757/100000 : ℝ)^4707 ≤ (28119103473997/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3757 : ℕ)^4707*100000000000000000000^1024 ≤ 28119103473997^1024*100000^4707 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3757 100000 28119103473997 100000000000000000000 4707 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3757/100000 : ℝ)) (X := (28119103473997/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4707 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12261/50000 : ℝ) ^ (4707/1024 : ℝ) ≤ (625235950755547/400000000000000000 : ℝ) := by
    have hpowers : (12261/50000 : ℝ)^4707 ≤ (625235950755547/400000000000000000 : ℝ)^1024 := by
      have hnat : (12261 : ℕ)^4707*400000000000000000^1024 ≤ 625235950755547^1024*50000^4707 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12261 50000 625235950755547 400000000000000000 4707 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12261/50000 : ℝ)) (X := (625235950755547/400000000000000000 : ℝ)) (by norm_num) (by norm_num) 4707 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000028119103473997/50000000000000000000 : ℝ) ≤ (78125009558223/78125000000000 : ℝ) ^ (4707/1024 : ℝ) := by
    have hpowers : (50000028119103473997/50000000000000000000 : ℝ)^1024 ≤ (78125009558223/78125000000000 : ℝ)^4707 := by
      have hnat : (50000028119103473997 : ℕ)^1024*78125000000000^4707 ≤ 78125009558223^4707*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000028119103473997 50000000000000000000 78125009558223 78125000000000 1024 4707 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78125009558223/78125000000000 : ℝ)) (X := (50000028119103473997/50000000000000000000 : ℝ)) (by norm_num) 4707 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100156337106792360747/100000000000000000000 : ℝ) ≤ (10003399009404469/10000000000000000 : ℝ) ^ (4707/1024 : ℝ) := by
    have hpowers : (100156337106792360747/100000000000000000000 : ℝ)^1024 ≤ (10003399009404469/10000000000000000 : ℝ)^4707 := by
      have hnat : (100156337106792360747 : ℕ)^1024*10000000000000000^4707 ≤ 10003399009404469^4707*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100156337106792360747 100000000000000000000 10003399009404469 10000000000000000 1024 4707 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003399009404469/10000000000000000 : ℝ)) (X := (100156337106792360747/100000000000000000000 : ℝ)) (by norm_num) 4707 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (200625235950755547/200000000000000000 : ℝ) ≤ (5003398397678197/5000000000000000 : ℝ) ^ (4707/1024 : ℝ) := by
    have hpowers : (200625235950755547/200000000000000000 : ℝ)^1024 ≤ (5003398397678197/5000000000000000 : ℝ)^4707 := by
      have hnat : (200625235950755547 : ℕ)^1024*5000000000000000^4707 ≤ 5003398397678197^4707*200000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        200625235950755547 200000000000000000 5003398397678197 5000000000000000 1024 4707 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003398397678197/5000000000000000 : ℝ)) (X := (200625235950755547/200000000000000000 : ℝ)) (by norm_num) 4707 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(28119103473997/100000000000000000000 : ℝ) ≤ ((20762449444134931171/20765000000000000000 : ℝ)+2*(135911438077/83060000000000 : ℝ)*(3757/100000 : ℝ))^(4707/1024 : ℝ) := by
    rw [show (20762449444134931171/20765000000000000000 : ℝ)+2*(135911438077/83060000000000 : ℝ)*(3757/100000 : ℝ)=(78125009558223/78125000000000 : ℝ) by norm_num, show 1+2*(28119103473997/100000000000000000000 : ℝ)=(50000028119103473997/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(625235950755547/400000000000000000 : ℝ)+(28119103473997/100000000000000000000 : ℝ) ≤ ((20762449444134931171/20765000000000000000 : ℝ)+(135911438077/83060000000000 : ℝ)*((12261/50000 : ℝ)+(3757/100000 : ℝ)))^(4707/1024 : ℝ) := by
    rw [show (20762449444134931171/20765000000000000000 : ℝ)+(135911438077/83060000000000 : ℝ)*((12261/50000 : ℝ)+(3757/100000 : ℝ))=(10003399009404469/10000000000000000 : ℝ) by norm_num, show 1+(625235950755547/400000000000000000 : ℝ)+(28119103473997/100000000000000000000 : ℝ)=(100156337106792360747/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(625235950755547/400000000000000000 : ℝ) ≤ ((20762449444134931171/20765000000000000000 : ℝ)+2*(135911438077/83060000000000 : ℝ)*(12261/50000 : ℝ))^(4707/1024 : ℝ) := by
    rw [show (20762449444134931171/20765000000000000000 : ℝ)+2*(135911438077/83060000000000 : ℝ)*(12261/50000 : ℝ)=(5003398397678197/5000000000000000 : ℝ) by norm_num, show 1+2*(625235950755547/400000000000000000 : ℝ)=(200625235950755547/200000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20762449444134931171/20765000000000000000 : ℝ)*(X 1 0+X 2 0)+(135911438077/83060000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4707/1024 : ℝ)) (lo := (3757/100000 : ℝ)) (hi := (12261/50000 : ℝ)) (c := (20762449444134931171/20765000000000000000 : ℝ)) (alpha := (135911438077/83060000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20762449444134931171/20765000000000000000 : ℝ)*(X 0 1+X 2 1)+(135911438077/83060000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4707/1024 : ℝ)) (lo := (3757/100000 : ℝ)) (hi := (12261/50000 : ℝ)) (c := (20762449444134931171/20765000000000000000 : ℝ)) (alpha := (135911438077/83060000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20762449444134931171/20765000000000000000 : ℝ)*(X 0 2+X 1 2)+(135911438077/83060000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4707/1024 : ℝ)) (lo := (3757/100000 : ℝ)) (hi := (12261/50000 : ℝ)) (c := (20762449444134931171/20765000000000000000 : ℝ)) (alpha := (135911438077/83060000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-214689451/1250000000 : ℝ)*X 0 0+(2770773599/5000000000 : ℝ)*X 0 1+(5112585723/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((671951171/1250000000 : ℝ)*X 1 0+(-1942329/10000000 : ℝ)*X 1 1+(5112585573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5375609013/10000000000 : ℝ)*X 2 0+(1278146469/2500000000 : ℝ)*X 2 1+(-77693163/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4209849229/10000000000 : ℝ)*X 0 0+(464513261/1250000000 : ℝ)*X 0 1+(1188393603/2500000000 : ℝ)*X 0 2+(4209849229/10000000000 : ℝ)*X 1 0+(464513261/1250000000 : ℝ)*X 1 1+(1188393603/2500000000 : ℝ)*X 1 2+(4209849229/10000000000 : ℝ)*X 2 0+(464513261/1250000000 : ℝ)*X 2 1+(1188393603/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-343553099/2000000000 : ℝ)*X 0 0+(1279341037/2500000000 : ℝ)*X 0 1+(5536692819/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2630855947/5000000000 : ℝ)*X 1 0+(-1518221733/10000000000 : ℝ)*X 1 1+(5536693089/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1315427843/2500000000 : ℝ)*X 2 0+(34604333/62500000 : ℝ)*X 2 1+(-1518222197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2105226429/5000000000 : ℝ)*X 0 0+(4742018267/10000000000 : ℝ)*X 0 1+(3727845881/10000000000 : ℝ)*X 0 2+(2105226429/5000000000 : ℝ)*X 1 0+(4742018267/10000000000 : ℝ)*X 1 1+(3727845881/10000000000 : ℝ)*X 1 2+(2105226429/5000000000 : ℝ)*X 2 0+(4742018267/10000000000 : ℝ)*X 2 1+(3727845881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3532692056911334675666525949/1038250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8161029/25000000000000 : ℝ)*(base1) + (239349251/25000000000000 : ℝ)*(base19) + (160689017/20000000000000 : ℝ)*(base23) + (56969539/50000000000000 : ℝ)*(upper3) + (1802151/4000000000000 : ℝ)*(upper5) + (1647559385338427/100000000000000 : ℝ)*(major0) + (1647559385338427/100000000000000 : ℝ)*(major1) + (1647559385338427/100000000000000 : ℝ)*(major2) + (58280503625079/2500000000000 : ℝ)*(sp0) + (2331226283409671/100000000000000 : ℝ)*(sp1) + (233122643736159/10000000000000 : ℝ)*(sp2) + (481943987545347/50000000000000 : ℝ)*(sp3) + (7128447631/100000000000000 : ℝ)*(sp4) + (681743441/20000000000000 : ℝ)*(sp7) + (192778283290403/20000000000000 : ℝ)*(f.failure) + (93249089632267/4000000000000 : ℝ)*(f.sum) + (439611543291/259562500000000000000000000 : ℝ)*base65 + (16143545960968658017/2076500000000000000000000000000000 : ℝ)*base67 + (1438306357753158017/2076500000000000000000000000000000 : ℝ)*base69 + (1467638572509841983/2076500000000000000000000000000000 : ℝ)*base72 + (2271730934551/519125000000000000000000000 : ℝ)*base73 + (4714753383682158017/2076500000000000000000000000000000 : ℝ)*base75 + (13618938068727158017/2076500000000000000000000000000000 : ℝ)*base77 + (6624910601589341983/2076500000000000000000000000000000 : ℝ)*base80 + (207759753271/207650000000000000000000000 : ℝ)*base82 + (15185091/2000000000000000000000 : ℝ)*base90 + (15185091/2000000000000000000000 : ℝ)*base92 + (15185091/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8319279389569720191455675337/1038250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (196099099/12500000000000 : ℝ)*(base19) + (1359004333/100000000000000 : ℝ)*(base23) + (1348647/5000000000000 : ℝ)*(upper2) + (133815891/50000000000000 : ℝ)*(upper3) + (26675229/20000000000000 : ℝ)*(upper5) + (1685393658875483/100000000000000 : ℝ)*(major0) + (1685393658875483/100000000000000 : ℝ)*(major1) + (1685393658875483/100000000000000 : ℝ)*(major2) + (2343543169/20000000000000 : ℝ)*(sp1) + (5293730953/50000000000000 : ℝ)*(sp2) + (2384760995640197/100000000000000 : ℝ)*(sp4) + (59618692728289/2500000000000 : ℝ)*(sp5) + (1192374524586979/50000000000000 : ℝ)*(sp6) + (6162662843861/625000000000 : ℝ)*(sp7) + (6162662843861/625000000000 : ℝ)*(f.failure) + (2384760995640197/100000000000000 : ℝ)*(f.sum) + (3352469452373/2076500000000000000000000000 : ℝ)*base65 + (13488937314301869407/2076500000000000000000000000000000 : ℝ)*base68 + (9730498949567369407/2076500000000000000000000000000000 : ℝ)*base70 + (10089892877007869407/2076500000000000000000000000000000 : ℝ)*base72 + (529146019871/4153000000000000000000000000 : ℝ)*base73 + (7792392861240369407/2076500000000000000000000000000000 : ℝ)*base76 + (8212318574388869407/2076500000000000000000000000000000 : ℝ)*base78 + (8666857326911869407/2076500000000000000000000000000000 : ℝ)*base80 + (2643187295939/4153000000000000000000000000 : ℝ)*base81 + (278483/62500000000000000000 : ℝ)*base89 + (278483/62500000000000000000 : ℝ)*base91 + (278483/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1598_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170927903/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12261/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3757/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8907/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17991/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1598_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1598_s2_0 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-433291011/2500000000 : ℝ)*x 0 + (136802207/250000000 : ℝ)*x 1 + (1292956087/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433291011/2500000000 : ℝ)^4711 ≤ (2663058224627/25000000000000 : ℝ)^3687 := by
    have hnat : (433291011 : ℕ)^4711*25000000000000^3687 ≤ 2663058224627^3687*2500000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433291011 2500000000 2663058224627 25000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136802207/250000000 : ℝ)^4711 ≤ (46283871620133/100000000000000 : ℝ)^3687 := by
    have hnat : (136802207 : ℕ)^4711*100000000000000^3687 ≤ 46283871620133^3687*250000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136802207 250000000 46283871620133 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1292956087/2500000000 : ℝ)^4711 ≤ (43063895465689/100000000000000 : ℝ)^3687 := by
    have hnat : (1292956087 : ℕ)^4711*100000000000000^3687 ≤ 43063895465689^3687*2500000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292956087 2500000000 43063895465689 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-433291011/2500000000 : ℝ), (136802207/250000000 : ℝ), (1292956087/2500000000 : ℝ)] ![(2663058224627/25000000000000 : ℝ), (46283871620133/100000000000000 : ℝ), (43063895465689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-433291011/2500000000 : ℝ)|^4711 ≤ (2663058224627/25000000000000 : ℝ)^3687
        have hw : |(-433291011/2500000000 : ℝ)|=(433291011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136802207/250000000 : ℝ)|^4711 ≤ (46283871620133/100000000000000 : ℝ)^3687
        have hw : |(136802207/250000000 : ℝ)|=(136802207/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1292956087/2500000000 : ℝ)|^4711 ≤ (43063895465689/100000000000000 : ℝ)^3687
        have hw : |(1292956087/2500000000 : ℝ)|=(1292956087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1598_s2_1 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5357608187/10000000000 : ℝ)*x 0 + (-236044979/1250000000 : ℝ)*x 1 + (517182419/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5357608187/10000000000 : ℝ)^4711 ≤ (11262566349021/25000000000000 : ℝ)^3687 := by
    have hnat : (5357608187 : ℕ)^4711*25000000000000^3687 ≤ 11262566349021^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5357608187 10000000000 11262566349021 25000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (236044979/1250000000 : ℝ)^4711 ≤ (11885840806107/100000000000000 : ℝ)^3687 := by
    have hnat : (236044979 : ℕ)^4711*100000000000000^3687 ≤ 11885840806107^3687*1250000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236044979 1250000000 11885840806107 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517182419/1000000000 : ℝ)^4711 ≤ (21531946892347/50000000000000 : ℝ)^3687 := by
    have hnat : (517182419 : ℕ)^4711*50000000000000^3687 ≤ 21531946892347^3687*1000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517182419 1000000000 21531946892347 50000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5357608187/10000000000 : ℝ), (-236044979/1250000000 : ℝ), (517182419/1000000000 : ℝ)] ![(11262566349021/25000000000000 : ℝ), (11885840806107/100000000000000 : ℝ), (21531946892347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5357608187/10000000000 : ℝ)|^4711 ≤ (11262566349021/25000000000000 : ℝ)^3687
        have hw : |(5357608187/10000000000 : ℝ)|=(5357608187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-236044979/1250000000 : ℝ)|^4711 ≤ (11885840806107/100000000000000 : ℝ)^3687
        have hw : |(-236044979/1250000000 : ℝ)|=(236044979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(517182419/1000000000 : ℝ)|^4711 ≤ (21531946892347/50000000000000 : ℝ)^3687
        have hw : |(517182419/1000000000 : ℝ)|=(517182419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1598_s2_2 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071521581/2000000000 : ℝ)*x 0 + (2585912271/5000000000 : ℝ)*x 1 + (-944179871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071521581/2000000000 : ℝ)^4711 ≤ (22525131183137/50000000000000 : ℝ)^3687 := by
    have hnat : (1071521581 : ℕ)^4711*50000000000000^3687 ≤ 22525131183137^3687*2000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071521581 2000000000 22525131183137 50000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2585912271/5000000000 : ℝ)^4711 ≤ (43063897529697/100000000000000 : ℝ)^3687 := by
    have hnat : (2585912271 : ℕ)^4711*100000000000000^3687 ≤ 43063897529697^3687*5000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585912271 5000000000 43063897529697 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (944179871/5000000000 : ℝ)^4711 ≤ (2971460020573/25000000000000 : ℝ)^3687 := by
    have hnat : (944179871 : ℕ)^4711*25000000000000^3687 ≤ 2971460020573^3687*5000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944179871 5000000000 2971460020573 25000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071521581/2000000000 : ℝ), (2585912271/5000000000 : ℝ), (-944179871/5000000000 : ℝ)] ![(22525131183137/50000000000000 : ℝ), (43063897529697/100000000000000 : ℝ), (2971460020573/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071521581/2000000000 : ℝ)|^4711 ≤ (22525131183137/50000000000000 : ℝ)^3687
        have hw : |(1071521581/2000000000 : ℝ)|=(1071521581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2585912271/5000000000 : ℝ)|^4711 ≤ (43063897529697/100000000000000 : ℝ)^3687
        have hw : |(2585912271/5000000000 : ℝ)|=(2585912271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-944179871/5000000000 : ℝ)|^4711 ≤ (2971460020573/25000000000000 : ℝ)^3687
        have hw : |(-944179871/5000000000 : ℝ)|=(944179871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1598_s2_3 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4221356719/10000000000 : ℝ)*x 0 + (3870500869/10000000000 : ℝ)*x 1 + (287294151/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4221356719/10000000000 : ℝ)^4711 ≤ (332221616999/1000000000000 : ℝ)^3687 := by
    have hnat : (4221356719 : ℕ)^4711*1000000000000^3687 ≤ 332221616999^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221356719 10000000000 332221616999 1000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3870500869/10000000000 : ℝ)^4711 ≤ (5947119700579/20000000000000 : ℝ)^3687 := by
    have hnat : (3870500869 : ℕ)^4711*20000000000000^3687 ≤ 5947119700579^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3870500869 10000000000 5947119700579 20000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (287294151/625000000 : ℝ)^4711 ≤ (37042239785367/100000000000000 : ℝ)^3687 := by
    have hnat : (287294151 : ℕ)^4711*100000000000000^3687 ≤ 37042239785367^3687*625000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287294151 625000000 37042239785367 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4221356719/10000000000 : ℝ), (3870500869/10000000000 : ℝ), (287294151/625000000 : ℝ)] ![(332221616999/1000000000000 : ℝ), (5947119700579/20000000000000 : ℝ), (37042239785367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4221356719/10000000000 : ℝ)|^4711 ≤ (332221616999/1000000000000 : ℝ)^3687
        have hw : |(4221356719/10000000000 : ℝ)|=(4221356719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3870500869/10000000000 : ℝ)|^4711 ≤ (5947119700579/20000000000000 : ℝ)^3687
        have hw : |(3870500869/10000000000 : ℝ)|=(3870500869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(287294151/625000000 : ℝ)|^4711 ≤ (37042239785367/100000000000000 : ℝ)^3687
        have hw : |(287294151/625000000 : ℝ)|=(287294151/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1598_s2_4 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1733249613/10000000000 : ℝ)*x 0 + (5174173389/10000000000 : ℝ)*x 1 + (5469713303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1733249613/10000000000 : ℝ)^4711 ≤ (10652904884753/100000000000000 : ℝ)^3687 := by
    have hnat : (1733249613 : ℕ)^4711*100000000000000^3687 ≤ 10652904884753^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1733249613 10000000000 10652904884753 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5174173389/10000000000 : ℝ)^4711 ≤ (21544444494953/50000000000000 : ℝ)^3687 := by
    have hnat : (5174173389 : ℕ)^4711*50000000000000^3687 ≤ 21544444494953^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174173389 10000000000 21544444494953 50000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5469713303/10000000000 : ℝ)^4711 ≤ (2312910305853/5000000000000 : ℝ)^3687 := by
    have hnat : (5469713303 : ℕ)^4711*5000000000000^3687 ≤ 2312910305853^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469713303 10000000000 2312910305853 5000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1733249613/10000000000 : ℝ), (5174173389/10000000000 : ℝ), (5469713303/10000000000 : ℝ)] ![(10652904884753/100000000000000 : ℝ), (21544444494953/50000000000000 : ℝ), (2312910305853/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1733249613/10000000000 : ℝ)|^4711 ≤ (10652904884753/100000000000000 : ℝ)^3687
        have hw : |(-1733249613/10000000000 : ℝ)|=(1733249613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5174173389/10000000000 : ℝ)|^4711 ≤ (21544444494953/50000000000000 : ℝ)^3687
        have hw : |(5174173389/10000000000 : ℝ)|=(5174173389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5469713303/10000000000 : ℝ)|^4711 ≤ (2312910305853/5000000000000 : ℝ)^3687
        have hw : |(5469713303/10000000000 : ℝ)|=(5469713303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1598_s2_5 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278032043/10000000000 : ℝ)*x 0 + (-1590470909/10000000000 : ℝ)*x 1 + (5469713361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278032043/10000000000 : ℝ)^4711 ≤ (883941366999/2000000000000 : ℝ)^3687 := by
    have hnat : (5278032043 : ℕ)^4711*2000000000000^3687 ≤ 883941366999^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278032043 10000000000 883941366999 2000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1590470909/10000000000 : ℝ)^4711 ≤ (4772362451131/50000000000000 : ℝ)^3687 := by
    have hnat : (1590470909 : ℕ)^4711*50000000000000^3687 ≤ 4772362451131^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1590470909 10000000000 4772362451131 50000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5469713361/10000000000 : ℝ)^4711 ≤ (46258206743807/100000000000000 : ℝ)^3687 := by
    have hnat : (5469713361 : ℕ)^4711*100000000000000^3687 ≤ 46258206743807^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469713361 10000000000 46258206743807 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278032043/10000000000 : ℝ), (-1590470909/10000000000 : ℝ), (5469713361/10000000000 : ℝ)] ![(883941366999/2000000000000 : ℝ), (4772362451131/50000000000000 : ℝ), (46258206743807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278032043/10000000000 : ℝ)|^4711 ≤ (883941366999/2000000000000 : ℝ)^3687
        have hw : |(5278032043/10000000000 : ℝ)|=(5278032043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1590470909/10000000000 : ℝ)|^4711 ≤ (4772362451131/50000000000000 : ℝ)^3687
        have hw : |(-1590470909/10000000000 : ℝ)|=(1590470909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5469713361/10000000000 : ℝ)|^4711 ≤ (46258206743807/100000000000000 : ℝ)^3687
        have hw : |(5469713361/10000000000 : ℝ)|=(5469713361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1598_s2_6 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278032101/10000000000 : ℝ)*x 0 + (1367428293/2500000000 : ℝ)*x 1 + (-795235547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278032101/10000000000 : ℝ)^4711 ≤ (22098534485259/50000000000000 : ℝ)^3687 := by
    have hnat : (5278032101 : ℕ)^4711*50000000000000^3687 ≤ 22098534485259^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278032101 10000000000 22098534485259 50000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367428293/2500000000 : ℝ)^4711 ≤ (46258204701477/100000000000000 : ℝ)^3687 := by
    have hnat : (1367428293 : ℕ)^4711*100000000000000^3687 ≤ 46258204701477^3687*2500000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367428293 2500000000 46258204701477 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (795235547/5000000000 : ℝ)^4711 ≤ (2386181580207/25000000000000 : ℝ)^3687 := by
    have hnat : (795235547 : ℕ)^4711*25000000000000^3687 ≤ 2386181580207^3687*5000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795235547 5000000000 2386181580207 25000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278032101/10000000000 : ℝ), (1367428293/2500000000 : ℝ), (-795235547/5000000000 : ℝ)] ![(22098534485259/50000000000000 : ℝ), (46258204701477/100000000000000 : ℝ), (2386181580207/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278032101/10000000000 : ℝ)|^4711 ≤ (22098534485259/50000000000000 : ℝ)^3687
        have hw : |(5278032101/10000000000 : ℝ)|=(5278032101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367428293/2500000000 : ℝ)|^4711 ≤ (46258204701477/100000000000000 : ℝ)^3687
        have hw : |(1367428293/2500000000 : ℝ)|=(1367428293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-795235547/5000000000 : ℝ)|^4711 ≤ (2386181580207/25000000000000 : ℝ)^3687
        have hw : |(-795235547/5000000000 : ℝ)|=(795235547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1598_s2_7 (p : ℝ) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2110782073/5000000000 : ℝ)*x 0 + (1147756349/2500000000 : ℝ)*x 1 + (3876245091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2110782073/5000000000 : ℝ)^4711 ≤ (33224247554593/100000000000000 : ℝ)^3687 := by
    have hnat : (2110782073 : ℕ)^4711*100000000000000^3687 ≤ 33224247554593^3687*5000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110782073 5000000000 33224247554593 100000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1147756349/2500000000 : ℝ)^4711 ≤ (1479350203811/4000000000000 : ℝ)^3687 := by
    have hnat : (1147756349 : ℕ)^4711*4000000000000^3687 ≤ 1479350203811^3687*2500000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147756349 2500000000 1479350203811 4000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3876245091/10000000000 : ℝ)^4711 ≤ (14895998670751/50000000000000 : ℝ)^3687 := by
    have hnat : (3876245091 : ℕ)^4711*50000000000000^3687 ≤ 14895998670751^3687*10000000000^4711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3876245091 10000000000 14895998670751 50000000000000 4711 3687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4711/1024 : ℝ)) 4711 3687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2110782073/5000000000 : ℝ), (1147756349/2500000000 : ℝ), (3876245091/10000000000 : ℝ)] ![(33224247554593/100000000000000 : ℝ), (1479350203811/4000000000000 : ℝ), (14895998670751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2110782073/5000000000 : ℝ)|^4711 ≤ (33224247554593/100000000000000 : ℝ)^3687
        have hw : |(2110782073/5000000000 : ℝ)|=(2110782073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1147756349/2500000000 : ℝ)|^4711 ≤ (1479350203811/4000000000000 : ℝ)^3687
        have hw : |(1147756349/2500000000 : ℝ)|=(1147756349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3876245091/10000000000 : ℝ)|^4711 ≤ (14895998670751/50000000000000 : ℝ)^3687
        have hw : |(3876245091/10000000000 : ℝ)|=(3876245091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1598_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170927903/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17991/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8907/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5093/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16547/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17991/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8907/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17991/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8907/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17991/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8907/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17991/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8907/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17991/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8907/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17991/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8907/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8907/100000 : ℝ) ^ (4707/1024 : ℝ) ≤ (297359553588901/20000000000000000000 : ℝ) := by
    have hpowers : (8907/100000 : ℝ)^4707 ≤ (297359553588901/20000000000000000000 : ℝ)^1024 := by
      have hnat : (8907 : ℕ)^4707*20000000000000000000^1024 ≤ 297359553588901^1024*100000^4707 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8907 100000 297359553588901 20000000000000000000 4707 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8907/100000 : ℝ)) (X := (297359553588901/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4707 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17991/100000 : ℝ) ^ (4707/1024 : ℝ) ≤ (37646780819297603/100000000000000000000 : ℝ) := by
    have hpowers : (17991/100000 : ℝ)^4707 ≤ (37646780819297603/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17991 : ℕ)^4707*100000000000000000000^1024 ≤ 37646780819297603^1024*100000^4707 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17991 100000 37646780819297603 100000000000000000000 4707 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17991/100000 : ℝ)) (X := (37646780819297603/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4707 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000297359553588901/10000000000000000000 : ℝ) ≤ (2500016172330603/2500000000000000 : ℝ) ^ (4707/1024 : ℝ) := by
    have hpowers : (10000297359553588901/10000000000000000000 : ℝ)^1024 ≤ (2500016172330603/2500000000000000 : ℝ)^4707 := by
      have hnat : (10000297359553588901 : ℕ)^1024*2500000000000000^4707 ≤ 2500016172330603^4707*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000297359553588901 10000000000000000000 2500016172330603 2500000000000000 1024 4707 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500016172330603/2500000000000000 : ℝ)) (X := (10000297359553588901/10000000000000000000 : ℝ)) (by norm_num) 4707 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009783394646810527/25000000000000000000 : ℝ) ≤ (2000170242832927/2000000000000000 : ℝ) ^ (4707/1024 : ℝ) := by
    have hpowers : (25009783394646810527/25000000000000000000 : ℝ)^1024 ≤ (2000170242832927/2000000000000000 : ℝ)^4707 := by
      have hnat : (25009783394646810527 : ℕ)^1024*2000000000000000^4707 ≤ 2000170242832927^4707*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009783394646810527 25000000000000000000 2000170242832927 2000000000000000 1024 4707 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000170242832927/2000000000000000 : ℝ)) (X := (25009783394646810527/25000000000000000000 : ℝ)) (by norm_num) 4707 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037646780819297603/50000000000000000000 : ℝ) ≤ (5000818869503429/5000000000000000 : ℝ) ^ (4707/1024 : ℝ) := by
    have hpowers : (50037646780819297603/50000000000000000000 : ℝ)^1024 ≤ (5000818869503429/5000000000000000 : ℝ)^4707 := by
      have hnat : (50037646780819297603 : ℕ)^1024*5000000000000000^4707 ≤ 5000818869503429^4707*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037646780819297603 50000000000000000000 5000818869503429 5000000000000000 1024 4707 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000818869503429/5000000000000000 : ℝ)) (X := (50037646780819297603/50000000000000000000 : ℝ)) (by norm_num) 4707 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(297359553588901/20000000000000000000 : ℝ) ≤ ((15137762747377571681/15140000000000000000 : ℝ)+2*(786524842223/908400000000000 : ℝ)*(8907/100000 : ℝ))^(4707/1024 : ℝ) := by
    rw [show (15137762747377571681/15140000000000000000 : ℝ)+2*(786524842223/908400000000000 : ℝ)*(8907/100000 : ℝ)=(2500016172330603/2500000000000000 : ℝ) by norm_num, show 1+2*(297359553588901/20000000000000000000 : ℝ)=(10000297359553588901/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37646780819297603/100000000000000000000 : ℝ)+(297359553588901/20000000000000000000 : ℝ) ≤ ((15137762747377571681/15140000000000000000 : ℝ)+(786524842223/908400000000000 : ℝ)*((17991/100000 : ℝ)+(8907/100000 : ℝ)))^(4707/1024 : ℝ) := by
    rw [show (15137762747377571681/15140000000000000000 : ℝ)+(786524842223/908400000000000 : ℝ)*((17991/100000 : ℝ)+(8907/100000 : ℝ))=(2000170242832927/2000000000000000 : ℝ) by norm_num, show 1+(37646780819297603/100000000000000000000 : ℝ)+(297359553588901/20000000000000000000 : ℝ)=(25009783394646810527/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37646780819297603/100000000000000000000 : ℝ) ≤ ((15137762747377571681/15140000000000000000 : ℝ)+2*(786524842223/908400000000000 : ℝ)*(17991/100000 : ℝ))^(4707/1024 : ℝ) := by
    rw [show (15137762747377571681/15140000000000000000 : ℝ)+2*(786524842223/908400000000000 : ℝ)*(17991/100000 : ℝ)=(5000818869503429/5000000000000000 : ℝ) by norm_num, show 1+2*(37646780819297603/100000000000000000000 : ℝ)=(50037646780819297603/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15137762747377571681/15140000000000000000 : ℝ)*(X 1 0+X 2 0)+(786524842223/908400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4707/1024 : ℝ)) (lo := (8907/100000 : ℝ)) (hi := (17991/100000 : ℝ)) (c := (15137762747377571681/15140000000000000000 : ℝ)) (alpha := (786524842223/908400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15137762747377571681/15140000000000000000 : ℝ)*(X 0 1+X 2 1)+(786524842223/908400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4707/1024 : ℝ)) (lo := (8907/100000 : ℝ)) (hi := (17991/100000 : ℝ)) (c := (15137762747377571681/15140000000000000000 : ℝ)) (alpha := (786524842223/908400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15137762747377571681/15140000000000000000 : ℝ)*(X 0 2+X 1 2)+(786524842223/908400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4707/1024 : ℝ)) (lo := (8907/100000 : ℝ)) (hi := (17991/100000 : ℝ)) (c := (15137762747377571681/15140000000000000000 : ℝ)) (alpha := (786524842223/908400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-433291011/2500000000 : ℝ)*X 0 0+(136802207/250000000 : ℝ)*X 0 1+(1292956087/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5357608187/10000000000 : ℝ)*X 1 0+(-236044979/1250000000 : ℝ)*X 1 1+(517182419/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071521581/2000000000 : ℝ)*X 2 0+(2585912271/5000000000 : ℝ)*X 2 1+(-944179871/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4221356719/10000000000 : ℝ)*X 0 0+(3870500869/10000000000 : ℝ)*X 0 1+(287294151/625000000 : ℝ)*X 0 2+(4221356719/10000000000 : ℝ)*X 1 0+(3870500869/10000000000 : ℝ)*X 1 1+(287294151/625000000 : ℝ)*X 1 2+(4221356719/10000000000 : ℝ)*X 2 0+(3870500869/10000000000 : ℝ)*X 2 1+(287294151/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1733249613/10000000000 : ℝ)*X 0 0+(5174173389/10000000000 : ℝ)*X 0 1+(5469713303/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278032043/10000000000 : ℝ)*X 1 0+(-1590470909/10000000000 : ℝ)*X 1 1+(5469713361/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278032101/10000000000 : ℝ)*X 2 0+(1367428293/2500000000 : ℝ)*X 2 1+(-795235547/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2110782073/5000000000 : ℝ)*X 0 0+(1147756349/2500000000 : ℝ)*X 0 1+(3876245091/10000000000 : ℝ)*X 0 2+(2110782073/5000000000 : ℝ)*X 1 0+(1147756349/2500000000 : ℝ)*X 1 1+(3876245091/10000000000 : ℝ)*X 1 2+(2110782073/5000000000 : ℝ)*X 2 0+(1147756349/2500000000 : ℝ)*X 2 1+(3876245091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1598_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1074372798695043236929301373/94625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (373369543/20000000000000 : ℝ)*(base19) + (1629119163/100000000000000 : ℝ)*(base23) + (33447191/100000000000000 : ℝ)*(lower2) + (256829197/100000000000000 : ℝ)*(upper3) + (245261481/100000000000000 : ℝ)*(upper5) + (294217529320437/12500000000000 : ℝ)*(major0) + (294217529320437/12500000000000 : ℝ)*(major1) + (294217529320437/12500000000000 : ℝ)*(major2) + (832605839326703/25000000000000 : ℝ)*(sp0) + (832610340042127/25000000000000 : ℝ)*(sp1) + (166522079894853/5000000000000 : ℝ)*(sp2) + (344257172986417/25000000000000 : ℝ)*(sp3) + (19869709411/100000000000000 : ℝ)*(sp4) + (8171698237/100000000000000 : ℝ)*(sp7) + (275407372728781/20000000000000 : ℝ)*(f.failure) + (3330443227016223/100000000000000 : ℝ)*(f.sum) + (6773059533579/3785000000000000000000000000 : ℝ)*base65 + (1813063927706155403/189250000000000000000000000000000 : ℝ)*base68 + (143069691110405403/189250000000000000000000000000000 : ℝ)*base70 + (1780151329055905403/189250000000000000000000000000000 : ℝ)*base72 + (1873037090723/1892500000000000000000000000 : ℝ)*base74 + (1288364402642155403/189250000000000000000000000000000 : ℝ)*base76 + (998905433587905403/189250000000000000000000000000000 : ℝ)*base78 + (39643676635405403/189250000000000000000000000000000 : ℝ)*base80 + (13635364033659/3785000000000000000000000000 : ℝ)*base81 + (4076243/2000000000000000000000 : ℝ)*base89 + (4076243/2000000000000000000000 : ℝ)*base91 + (4076243/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (869574085764475050568332663/189250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (245769657/100000000000000 : ℝ)*(base19) + (190456373/50000000000000 : ℝ)*(base23) + (13657373/25000000000000 : ℝ)*(upper3) + (60117321/100000000000000 : ℝ)*(lower4) + (71463683/100000000000000 : ℝ)*(upper5) + (597833546221341/25000000000000 : ℝ)*(major0) + (597833546221341/25000000000000 : ℝ)*(major1) + (597833546221341/25000000000000 : ℝ)*(major2) + (1281286987/50000000000000 : ℝ)*(sp1) + (301059247/20000000000000 : ℝ)*(sp2) + (42295466419637/1250000000000 : ℝ)*(sp4) + (3383634505227329/100000000000000 : ℝ)*(sp5) + (169181771368099/5000000000000 : ℝ)*(sp6) + (17487886287979/1250000000000 : ℝ)*(sp7) + (17487886287979/1250000000000 : ℝ)*(f.failure) + (42295466419637/1250000000000 : ℝ)*(f.sum) + (3802963674719/3785000000000000000000000000 : ℝ)*base66 + (527164978956505779/378500000000000000000000000000000 : ℝ)*base68 + (2674335696603494221/378500000000000000000000000000000 : ℝ)*base69 + (191717402789005779/378500000000000000000000000000000 : ℝ)*base72 + (1246400371123/1892500000000000000000000000 : ℝ)*base73 + (2362151565406994221/378500000000000000000000000000000 : ℝ)*base75 + (2399443319334005779/378500000000000000000000000000000 : ℝ)*base78 + (1502187220421505779/378500000000000000000000000000000 : ℝ)*base80 + (30435868544131/3785000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (421963/125000000000000000000 : ℝ)*base90 + (421963/125000000000000000000 : ℝ)*base92 + (421963/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1598_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170927903/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17991/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8907/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5093/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16547/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1598_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1598_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170927903/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5093/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16547/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1598_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1598_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1598_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4707/1024 : ℝ) ≤ p) (hpb : p ≤ (4711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170927903/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5093/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16547/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1598_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

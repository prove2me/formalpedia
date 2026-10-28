-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1127_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:11:53.323861+00:00
-- url     : https://prove2.me/submissions/2c70b0b8-3000-4c8c-80fd-4abb0384e681

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
theorem support_rectangle_w1127_s3_0 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2170106797/10000000000 : ℝ)*x 0 + (5430749427/10000000000 : ℝ)*x 1 + (5230649033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170106797/10000000000 : ℝ)^65 ≤ (13177161749173/100000000000000 : ℝ)^49 := by
    have hnat : (2170106797 : ℕ)^65*100000000000000^49 ≤ 13177161749173^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170106797 10000000000 13177161749173 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430749427/10000000000 : ℝ)^65 ≤ (11123036707991/25000000000000 : ℝ)^49 := by
    have hnat : (5430749427 : ℕ)^65*25000000000000^49 ≤ 11123036707991^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430749427 10000000000 11123036707991 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230649033/10000000000 : ℝ)^65 ≤ (21165345703699/50000000000000 : ℝ)^49 := by
    have hnat : (5230649033 : ℕ)^65*50000000000000^49 ≤ 21165345703699^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230649033 10000000000 21165345703699 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2170106797/10000000000 : ℝ), (5430749427/10000000000 : ℝ), (5230649033/10000000000 : ℝ)] ![(13177161749173/100000000000000 : ℝ), (11123036707991/25000000000000 : ℝ), (21165345703699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2170106797/10000000000 : ℝ)|^65 ≤ (13177161749173/100000000000000 : ℝ)^49
        have hw : |(-2170106797/10000000000 : ℝ)|=(2170106797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430749427/10000000000 : ℝ)|^65 ≤ (11123036707991/25000000000000 : ℝ)^49
        have hw : |(5430749427/10000000000 : ℝ)|=(5430749427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230649033/10000000000 : ℝ)|^65 ≤ (21165345703699/50000000000000 : ℝ)^49
        have hw : |(5230649033/10000000000 : ℝ)|=(5230649033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s3_1 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5354159483/10000000000 : ℝ)*x 0 + (-1136212737/5000000000 : ℝ)*x 1 + (5230648937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354159483/10000000000 : ℝ)^65 ≤ (43661706749699/100000000000000 : ℝ)^49 := by
    have hnat : (5354159483 : ℕ)^65*100000000000000^49 ≤ 43661706749699^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354159483 10000000000 43661706749699 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1136212737/5000000000 : ℝ)^65 ≤ (14007602859507/100000000000000 : ℝ)^49 := by
    have hnat : (1136212737 : ℕ)^65*100000000000000^49 ≤ 14007602859507^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136212737 5000000000 14007602859507 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230648937/10000000000 : ℝ)^65 ≤ (42330690376803/100000000000000 : ℝ)^49 := by
    have hnat : (5230648937 : ℕ)^65*100000000000000^49 ≤ 42330690376803^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230648937 10000000000 42330690376803 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354159483/10000000000 : ℝ), (-1136212737/5000000000 : ℝ), (5230648937/10000000000 : ℝ)] ![(43661706749699/100000000000000 : ℝ), (14007602859507/100000000000000 : ℝ), (42330690376803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354159483/10000000000 : ℝ)|^65 ≤ (43661706749699/100000000000000 : ℝ)^49
        have hw : |(5354159483/10000000000 : ℝ)|=(5354159483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1136212737/5000000000 : ℝ)|^65 ≤ (14007602859507/100000000000000 : ℝ)^49
        have hw : |(-1136212737/5000000000 : ℝ)|=(1136212737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230648937/10000000000 : ℝ)|^65 ≤ (42330690376803/100000000000000 : ℝ)^49
        have hw : |(5230648937/10000000000 : ℝ)|=(5230648937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s3_2 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5354159579/10000000000 : ℝ)*x 0 + (5230649037/10000000000 : ℝ)*x 1 + (-454485043/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354159579/10000000000 : ℝ)^65 ≤ (43661707788179/100000000000000 : ℝ)^49 := by
    have hnat : (5354159579 : ℕ)^65*100000000000000^49 ≤ 43661707788179^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354159579 10000000000 43661707788179 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230649037/10000000000 : ℝ)^65 ≤ (2116534572517/5000000000000 : ℝ)^49 := by
    have hnat : (5230649037 : ℕ)^65*5000000000000^49 ≤ 2116534572517^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230649037 10000000000 2116534572517 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (454485043/2000000000 : ℝ)^65 ≤ (3501900185419/25000000000000 : ℝ)^49 := by
    have hnat : (454485043 : ℕ)^65*25000000000000^49 ≤ 3501900185419^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454485043 2000000000 3501900185419 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354159579/10000000000 : ℝ), (5230649037/10000000000 : ℝ), (-454485043/2000000000 : ℝ)] ![(43661707788179/100000000000000 : ℝ), (2116534572517/5000000000000 : ℝ), (3501900185419/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354159579/10000000000 : ℝ)|^65 ≤ (43661707788179/100000000000000 : ℝ)^49
        have hw : |(5354159579/10000000000 : ℝ)|=(5354159579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230649037/10000000000 : ℝ)|^65 ≤ (2116534572517/5000000000000 : ℝ)^49
        have hw : |(5230649037/10000000000 : ℝ)|=(5230649037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-454485043/2000000000 : ℝ)|^65 ≤ (3501900185419/25000000000000 : ℝ)^49
        have hw : |(-454485043/2000000000 : ℝ)|=(454485043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s3_3 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (436443453/1000000000 : ℝ)*x 0 + (4072727/9765625 : ℝ)*x 1 + (4567395611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436443453/1000000000 : ℝ)^65 ≤ (33293039572867/100000000000000 : ℝ)^49 := by
    have hnat : (436443453 : ℕ)^65*100000000000000^49 ≤ 33293039572867^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436443453 1000000000 33293039572867 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4072727/9765625 : ℝ)^65 ≤ (15672349930181/50000000000000 : ℝ)^49 := by
    have hnat : (4072727 : ℕ)^65*50000000000000^49 ≤ 15672349930181^49*9765625^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4072727 9765625 15672349930181 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4567395611/10000000000 : ℝ)^65 ≤ (35362260547523/100000000000000 : ℝ)^49 := by
    have hnat : (4567395611 : ℕ)^65*100000000000000^49 ≤ 35362260547523^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4567395611 10000000000 35362260547523 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436443453/1000000000 : ℝ), (4072727/9765625 : ℝ), (4567395611/10000000000 : ℝ)] ![(33293039572867/100000000000000 : ℝ), (15672349930181/50000000000000 : ℝ), (35362260547523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436443453/1000000000 : ℝ)|^65 ≤ (33293039572867/100000000000000 : ℝ)^49
        have hw : |(436443453/1000000000 : ℝ)|=(436443453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4072727/9765625 : ℝ)|^65 ≤ (15672349930181/50000000000000 : ℝ)^49
        have hw : |(4072727/9765625 : ℝ)|=(4072727/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4567395611/10000000000 : ℝ)|^65 ≤ (35362260547523/100000000000000 : ℝ)^49
        have hw : |(4567395611/10000000000 : ℝ)|=(4567395611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s3_4 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1085062821/5000000000 : ℝ)*x 0 + (5231433967/10000000000 : ℝ)*x 1 + (5429960051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085062821/5000000000 : ℝ)^65 ≤ (6588656771621/50000000000000 : ℝ)^49 := by
    have hnat : (1085062821 : ℕ)^65*50000000000000^49 ≤ 6588656771621^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085062821 5000000000 6588656771621 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231433967/10000000000 : ℝ)^65 ≤ (42339118171553/100000000000000 : ℝ)^49 := by
    have hnat : (5231433967 : ℕ)^65*100000000000000^49 ≤ 42339118171553^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231433967 10000000000 42339118171553 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429960051/10000000000 : ℝ)^65 ≤ (8896713654031/20000000000000 : ℝ)^49 := by
    have hnat : (5429960051 : ℕ)^65*20000000000000^49 ≤ 8896713654031^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429960051 10000000000 8896713654031 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1085062821/5000000000 : ℝ), (5231433967/10000000000 : ℝ), (5429960051/10000000000 : ℝ)] ![(6588656771621/50000000000000 : ℝ), (42339118171553/100000000000000 : ℝ), (8896713654031/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1085062821/5000000000 : ℝ)|^65 ≤ (6588656771621/50000000000000 : ℝ)^49
        have hw : |(-1085062821/5000000000 : ℝ)|=(1085062821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231433967/10000000000 : ℝ)|^65 ≤ (42339118171553/100000000000000 : ℝ)^49
        have hw : |(5231433967/10000000000 : ℝ)|=(5231433967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429960051/10000000000 : ℝ)|^65 ≤ (8896713654031/20000000000000 : ℝ)^49
        have hw : |(5429960051/10000000000 : ℝ)|=(5429960051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s3_5 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (165735023/312500000 : ℝ)*x 0 + (-2073114071/10000000000 : ℝ)*x 1 + (271498019/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165735023/312500000 : ℝ)^65 ≤ (43114770040797/100000000000000 : ℝ)^49 := by
    have hnat : (165735023 : ℕ)^65*100000000000000^49 ≤ 43114770040797^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165735023 312500000 43114770040797 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2073114071/10000000000 : ℝ)^65 ≤ (12401658102919/100000000000000 : ℝ)^49 := by
    have hnat : (2073114071 : ℕ)^65*100000000000000^49 ≤ 12401658102919^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073114071 10000000000 12401658102919 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271498019/500000000 : ℝ)^65 ≤ (22241785922743/50000000000000 : ℝ)^49 := by
    have hnat : (271498019 : ℕ)^65*50000000000000^49 ≤ 22241785922743^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271498019 500000000 22241785922743 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165735023/312500000 : ℝ), (-2073114071/10000000000 : ℝ), (271498019/500000000 : ℝ)] ![(43114770040797/100000000000000 : ℝ), (12401658102919/100000000000000 : ℝ), (22241785922743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165735023/312500000 : ℝ)|^65 ≤ (43114770040797/100000000000000 : ℝ)^49
        have hw : |(165735023/312500000 : ℝ)|=(165735023/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2073114071/10000000000 : ℝ)|^65 ≤ (12401658102919/100000000000000 : ℝ)^49
        have hw : |(-2073114071/10000000000 : ℝ)|=(2073114071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271498019/500000000 : ℝ)|^65 ≤ (22241785922743/50000000000000 : ℝ)^49
        have hw : |(271498019/500000000 : ℝ)|=(271498019/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s3_6 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1325880121/2500000000 : ℝ)*x 0 + (1357490157/2500000000 : ℝ)*x 1 + (-259139259/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325880121/2500000000 : ℝ)^65 ≤ (21557383661617/50000000000000 : ℝ)^49 := by
    have hnat : (1325880121 : ℕ)^65*50000000000000^49 ≤ 21557383661617^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325880121 2500000000 21557383661617 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357490157/2500000000 : ℝ)^65 ≤ (44483574540567/100000000000000 : ℝ)^49 := by
    have hnat : (1357490157 : ℕ)^65*100000000000000^49 ≤ 44483574540567^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357490157 2500000000 44483574540567 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259139259/1250000000 : ℝ)^65 ≤ (2480331622171/20000000000000 : ℝ)^49 := by
    have hnat : (259139259 : ℕ)^65*20000000000000^49 ≤ 2480331622171^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259139259 1250000000 2480331622171 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325880121/2500000000 : ℝ), (1357490157/2500000000 : ℝ), (-259139259/1250000000 : ℝ)] ![(21557383661617/50000000000000 : ℝ), (44483574540567/100000000000000 : ℝ), (2480331622171/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325880121/2500000000 : ℝ)|^65 ≤ (21557383661617/50000000000000 : ℝ)^49
        have hw : |(1325880121/2500000000 : ℝ)|=(1325880121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357490157/2500000000 : ℝ)|^65 ≤ (44483574540567/100000000000000 : ℝ)^49
        have hw : |(1357490157/2500000000 : ℝ)|=(1357490157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-259139259/1250000000 : ℝ)|^65 ≤ (2480331622171/20000000000000 : ℝ)^49
        have hw : |(-259139259/1250000000 : ℝ)|=(259139259/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s3_7 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4364471859/10000000000 : ℝ)*x 0 + (2282919623/5000000000 : ℝ)*x 1 + (1043009409/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364471859/10000000000 : ℝ)^65 ≤ (1664670865501/5000000000000 : ℝ)^49 := by
    have hnat : (4364471859 : ℕ)^65*5000000000000^49 ≤ 1664670865501^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364471859 10000000000 1664670865501 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282919623/5000000000 : ℝ)^65 ≤ (883656922441/2500000000000 : ℝ)^49 := by
    have hnat : (2282919623 : ℕ)^65*2500000000000^49 ≤ 883656922441^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282919623 5000000000 883656922441 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043009409/2500000000 : ℝ)^65 ≤ (15680152887971/50000000000000 : ℝ)^49 := by
    have hnat : (1043009409 : ℕ)^65*50000000000000^49 ≤ 15680152887971^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043009409 2500000000 15680152887971 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364471859/10000000000 : ℝ), (2282919623/5000000000 : ℝ), (1043009409/2500000000 : ℝ)] ![(1664670865501/5000000000000 : ℝ), (883656922441/2500000000000 : ℝ), (15680152887971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364471859/10000000000 : ℝ)|^65 ≤ (1664670865501/5000000000000 : ℝ)^49
        have hw : |(4364471859/10000000000 : ℝ)|=(4364471859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2282919623/5000000000 : ℝ)|^65 ≤ (883656922441/2500000000000 : ℝ)^49
        have hw : |(2282919623/5000000000 : ℝ)|=(2282919623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043009409/2500000000 : ℝ)|^65 ≤ (15680152887971/50000000000000 : ℝ)^49
        have hw : |(1043009409/2500000000 : ℝ)|=(1043009409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1127_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37295281/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4137/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4501/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1059/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1853/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4137/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4501/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4137/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4501/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4137/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4501/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4137/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4501/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4137/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4501/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4137/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4501/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4501/50000 : ℝ) ^ (8319/2048 : ℝ) ≤ (2828022128927973/50000000000000000000 : ℝ) := by
    have hpowers : (4501/50000 : ℝ)^8319 ≤ (2828022128927973/50000000000000000000 : ℝ)^2048 := by
      have hnat : (4501 : ℕ)^8319*50000000000000000000^2048 ≤ 2828022128927973^2048*50000^8319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4501 50000 2828022128927973 50000000000000000000 8319 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4501/50000 : ℝ)) (X := (2828022128927973/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (4137/25000 : ℝ) ^ (8319/2048 : ℝ) ≤ (67071051549646381/100000000000000000000 : ℝ) := by
    have hpowers : (4137/25000 : ℝ)^8319 ≤ (67071051549646381/100000000000000000000 : ℝ)^2048 := by
      have hnat : (4137 : ℕ)^8319*100000000000000000000^2048 ≤ 67071051549646381^2048*25000^8319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4137 25000 67071051549646381 100000000000000000000 8319 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4137/25000 : ℝ)) (X := (67071051549646381/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002828022128927973/25000000000000000000 : ℝ) ≤ (10000278473008607/10000000000000000 : ℝ) ^ (8319/2048 : ℝ) := by
    have hpowers : (25002828022128927973/25000000000000000000 : ℝ)^2048 ≤ (10000278473008607/10000000000000000 : ℝ)^8319 := by
      have hnat : (25002828022128927973 : ℕ)^2048*10000000000000000^8319 ≤ 10000278473008607^8319*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002828022128927973 25000000000000000000 10000278473008607 10000000000000000 2048 8319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000278473008607/10000000000000000 : ℝ)) (X := (25002828022128927973/25000000000000000000 : ℝ)) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100072727095807502327/100000000000000000000 : ℝ) ≤ (5000894965029223/5000000000000000 : ℝ) ^ (8319/2048 : ℝ) := by
    have hpowers : (100072727095807502327/100000000000000000000 : ℝ)^2048 ≤ (5000894965029223/5000000000000000 : ℝ)^8319 := by
      have hnat : (100072727095807502327 : ℕ)^2048*5000000000000000^8319 ≤ 5000894965029223^8319*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100072727095807502327 100000000000000000000 5000894965029223 5000000000000000 2048 8319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000894965029223/5000000000000000 : ℝ)) (X := (100072727095807502327/100000000000000000000 : ℝ)) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50067071051549646381/50000000000000000000 : ℝ) ≤ (2000660277421657/2000000000000000 : ℝ) ^ (8319/2048 : ℝ) := by
    have hpowers : (50067071051549646381/50000000000000000000 : ℝ)^2048 ≤ (2000660277421657/2000000000000000 : ℝ)^8319 := by
      have hnat : (50067071051549646381 : ℕ)^2048*2000000000000000^8319 ≤ 2000660277421657^8319*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50067071051549646381 50000000000000000000 2000660277421657 2000000000000000 2048 8319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000660277421657/2000000000000000 : ℝ)) (X := (50067071051549646381/50000000000000000000 : ℝ)) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2828022128927973/50000000000000000000 : ℝ) ≤ ((489836942107776929/490000000000000000 : ℝ)+2*(137405186349/68600000000000 : ℝ)*(4501/50000 : ℝ))^(8319/2048 : ℝ) := by
    rw [show (489836942107776929/490000000000000000 : ℝ)+2*(137405186349/68600000000000 : ℝ)*(4501/50000 : ℝ)=(10000278473008607/10000000000000000 : ℝ) by norm_num, show 1+2*(2828022128927973/50000000000000000000 : ℝ)=(25002828022128927973/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(67071051549646381/100000000000000000000 : ℝ)+(2828022128927973/50000000000000000000 : ℝ) ≤ ((489836942107776929/490000000000000000 : ℝ)+(137405186349/68600000000000 : ℝ)*((4137/25000 : ℝ)+(4501/50000 : ℝ)))^(8319/2048 : ℝ) := by
    rw [show (489836942107776929/490000000000000000 : ℝ)+(137405186349/68600000000000 : ℝ)*((4137/25000 : ℝ)+(4501/50000 : ℝ))=(5000894965029223/5000000000000000 : ℝ) by norm_num, show 1+(67071051549646381/100000000000000000000 : ℝ)+(2828022128927973/50000000000000000000 : ℝ)=(100072727095807502327/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(67071051549646381/100000000000000000000 : ℝ) ≤ ((489836942107776929/490000000000000000 : ℝ)+2*(137405186349/68600000000000 : ℝ)*(4137/25000 : ℝ))^(8319/2048 : ℝ) := by
    rw [show (489836942107776929/490000000000000000 : ℝ)+2*(137405186349/68600000000000 : ℝ)*(4137/25000 : ℝ)=(2000660277421657/2000000000000000 : ℝ) by norm_num, show 1+2*(67071051549646381/100000000000000000000 : ℝ)=(50067071051549646381/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (489836942107776929/490000000000000000 : ℝ)*(X 1 0+X 2 0)+(137405186349/68600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8319/2048 : ℝ)) (lo := (4501/50000 : ℝ)) (hi := (4137/25000 : ℝ)) (c := (489836942107776929/490000000000000000 : ℝ)) (alpha := (137405186349/68600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (489836942107776929/490000000000000000 : ℝ)*(X 0 1+X 2 1)+(137405186349/68600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8319/2048 : ℝ)) (lo := (4501/50000 : ℝ)) (hi := (4137/25000 : ℝ)) (c := (489836942107776929/490000000000000000 : ℝ)) (alpha := (137405186349/68600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (489836942107776929/490000000000000000 : ℝ)*(X 0 2+X 1 2)+(137405186349/68600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8319/2048 : ℝ)) (lo := (4501/50000 : ℝ)) (hi := (4137/25000 : ℝ)) (c := (489836942107776929/490000000000000000 : ℝ)) (alpha := (137405186349/68600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2170106797/10000000000 : ℝ)*X 0 0+(5430749427/10000000000 : ℝ)*X 0 1+(5230649033/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354159483/10000000000 : ℝ)*X 1 0+(-1136212737/5000000000 : ℝ)*X 1 1+(5230648937/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354159579/10000000000 : ℝ)*X 2 0+(5230649037/10000000000 : ℝ)*X 2 1+(-454485043/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((436443453/1000000000 : ℝ)*X 0 0+(4072727/9765625 : ℝ)*X 0 1+(4567395611/10000000000 : ℝ)*X 0 2+(436443453/1000000000 : ℝ)*X 1 0+(4072727/9765625 : ℝ)*X 1 1+(4567395611/10000000000 : ℝ)*X 1 2+(436443453/1000000000 : ℝ)*X 2 0+(4072727/9765625 : ℝ)*X 2 1+(4567395611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1085062821/5000000000 : ℝ)*X 0 0+(5231433967/10000000000 : ℝ)*X 0 1+(5429960051/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165735023/312500000 : ℝ)*X 1 0+(-2073114071/10000000000 : ℝ)*X 1 1+(271498019/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325880121/2500000000 : ℝ)*X 2 0+(1357490157/2500000000 : ℝ)*X 2 1+(-259139259/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4364471859/10000000000 : ℝ)*X 0 0+(2282919623/5000000000 : ℝ)*X 0 1+(1043009409/2500000000 : ℝ)*X 0 2+(4364471859/10000000000 : ℝ)*X 1 0+(2282919623/5000000000 : ℝ)*X 1 1+(1043009409/2500000000 : ℝ)*X 1 2+(4364471859/10000000000 : ℝ)*X 2 0+(2282919623/5000000000 : ℝ)*X 2 1+(1043009409/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (85550763697304523864509883/21437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1218957477/100000000000000 : ℝ)*(base19) + (9022471/781250000000 : ℝ)*(base23) + (4114321/5000000000000 : ℝ)*(lower2) + (17120083/100000000000000 : ℝ)*(upper3) + (186911539/100000000000000 : ℝ)*(upper5) + (469808387057829/12500000000000 : ℝ)*(major0) + (469808387057829/12500000000000 : ℝ)*(major1) + (469808387057829/12500000000000 : ℝ)*(major2) + (499750959287603/10000000000000 : ℝ)*(sp0) + (2498767138255077/50000000000000 : ℝ)*(sp1) + (4997534340591343/100000000000000 : ℝ)*(sp2) + (2519389588011201/100000000000000 : ℝ)*(sp3) + (25902591601/100000000000000 : ℝ)*(sp4) + (2244105721/25000000000000 : ℝ)*(sp7) + (503879712886817/20000000000000 : ℝ)*(f.failure) + (4997535495467631/100000000000000 : ℝ)*(f.sum) + (2453501965237/857500000000000000000000000 : ℝ)*base65 + (836348630939635013/42875000000000000000000000000000 : ℝ)*base68 + (628369302707260013/42875000000000000000000000000000 : ℝ)*base70 + (376370229339260013/42875000000000000000000000000000 : ℝ)*base72 + (516134094957/214375000000000000000000000 : ℝ)*base74 + (640515604001135013/42875000000000000000000000000000 : ℝ)*base76 + (481972821307385013/42875000000000000000000000000000 : ℝ)*base78 + (419116601552385013/42875000000000000000000000000000 : ℝ)*base80 + (554564651467/857500000000000000000000000 : ℝ)*base81 + (1210577/500000000000000000000 : ℝ)*base89 + (1210577/500000000000000000000 : ℝ)*base91 + (1210577/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (595796523488989223781661479/85750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1279569773/100000000000000 : ℝ)*(base19) + (1272765653/100000000000000 : ℝ)*(base23) + (249275493/100000000000000 : ℝ)*(upper3) + (22705117/25000000000000 : ℝ)*(lower4) + (15307047/20000000000000 : ℝ)*(upper5) + (1894116024330777/50000000000000 : ℝ)*(major0) + (1894116024330777/50000000000000 : ℝ)*(major1) + (1894116024330777/50000000000000 : ℝ)*(major2) + (12573637911/50000000000000 : ℝ)*(sp1) + (15783143807/50000000000000 : ℝ)*(sp2) + (5037113077171089/100000000000000 : ℝ)*(sp4) + (2518543325162747/50000000000000 : ℝ)*(sp5) + (2518540119058911/50000000000000 : ℝ)*(sp6) + (1269675394274933/50000000000000 : ℝ)*(sp7) + (1269675394274933/50000000000000 : ℝ)*(f.failure) + (5037113077171089/100000000000000 : ℝ)*(f.sum) + (4711964373367/1715000000000000000000000000 : ℝ)*base66 + (181053709343143169/171500000000000000000000000000000 : ℝ)*base68 + (786980567887143169/171500000000000000000000000000000 : ℝ)*base70 + (1050929733300643169/171500000000000000000000000000000 : ℝ)*base72 + (7057963015363/1715000000000000000000000000 : ℝ)*base73 + (778725140129643169/171500000000000000000000000000000 : ℝ)*base76 + (363773264896643169/171500000000000000000000000000000 : ℝ)*base78 + (327559277219643169/171500000000000000000000000000000 : ℝ)*base80 + (2519374304957/1715000000000000000000000000 : ℝ)*base82 + (7508827/1250000000000000000000 : ℝ)*base90 + (7508827/1250000000000000000000 : ℝ)*base92 + (7508827/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1127_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37295281/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4137/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4501/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1059/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1853/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1127_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1127_s4_0 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2173233917/10000000000 : ℝ)*x 0 + (2701311133/5000000000 : ℝ)*x 1 + (657091367/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173233917/10000000000 : ℝ)^65 ≤ (13202356189931/100000000000000 : ℝ)^49 := by
    have hnat : (2173233917 : ℕ)^65*100000000000000^49 ≤ 13202356189931^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173233917 10000000000 13202356189931 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701311133/5000000000 : ℝ)^65 ≤ (8837345158119/20000000000000 : ℝ)^49 := by
    have hnat : (2701311133 : ℕ)^65*20000000000000^49 ≤ 8837345158119^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701311133 5000000000 8837345158119 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657091367/1250000000 : ℝ)^65 ≤ (21305459002567/50000000000000 : ℝ)^49 := by
    have hnat : (657091367 : ℕ)^65*50000000000000^49 ≤ 21305459002567^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657091367 1250000000 21305459002567 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2173233917/10000000000 : ℝ), (2701311133/5000000000 : ℝ), (657091367/1250000000 : ℝ)] ![(13202356189931/100000000000000 : ℝ), (8837345158119/20000000000000 : ℝ), (21305459002567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2173233917/10000000000 : ℝ)|^65 ≤ (13202356189931/100000000000000 : ℝ)^49
        have hw : |(-2173233917/10000000000 : ℝ)|=(2173233917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701311133/5000000000 : ℝ)|^65 ≤ (8837345158119/20000000000000 : ℝ)^49
        have hw : |(2701311133/5000000000 : ℝ)|=(2701311133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657091367/1250000000 : ℝ)|^65 ≤ (21305459002567/50000000000000 : ℝ)^49
        have hw : |(657091367/1250000000 : ℝ)|=(657091367/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s4_1 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2673573207/5000000000 : ℝ)*x 0 + (-2247385579/10000000000 : ℝ)*x 1 + (1314182751/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673573207/5000000000 : ℝ)^65 ≤ (43585859142899/100000000000000 : ℝ)^49 := by
    have hnat : (2673573207 : ℕ)^65*100000000000000^49 ≤ 43585859142899^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673573207 5000000000 43585859142899 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247385579/10000000000 : ℝ)^65 ≤ (1725402763217/12500000000000 : ℝ)^49 := by
    have hnat : (2247385579 : ℕ)^65*12500000000000^49 ≤ 1725402763217^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247385579 10000000000 1725402763217 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314182751/2500000000 : ℝ)^65 ≤ (21305459368163/50000000000000 : ℝ)^49 := by
    have hnat : (1314182751 : ℕ)^65*50000000000000^49 ≤ 21305459368163^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314182751 2500000000 21305459368163 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673573207/5000000000 : ℝ), (-2247385579/10000000000 : ℝ), (1314182751/2500000000 : ℝ)] ![(43585859142899/100000000000000 : ℝ), (1725402763217/12500000000000 : ℝ), (21305459368163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673573207/5000000000 : ℝ)|^65 ≤ (43585859142899/100000000000000 : ℝ)^49
        have hw : |(2673573207/5000000000 : ℝ)|=(2673573207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2247385579/10000000000 : ℝ)|^65 ≤ (1725402763217/12500000000000 : ℝ)^49
        have hw : |(-2247385579/10000000000 : ℝ)|=(2247385579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1314182751/2500000000 : ℝ)|^65 ≤ (21305459368163/50000000000000 : ℝ)^49
        have hw : |(1314182751/2500000000 : ℝ)|=(1314182751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s4_2 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2673573033/5000000000 : ℝ)*x 0 + (2628365453/5000000000 : ℝ)*x 1 + (-224738617/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673573033/5000000000 : ℝ)^65 ≤ (21792927690011/50000000000000 : ℝ)^49 := by
    have hnat : (2673573033 : ℕ)^65*50000000000000^49 ≤ 21792927690011^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673573033 5000000000 21792927690011 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628365453/5000000000 : ℝ)^65 ≤ (42610917682549/100000000000000 : ℝ)^49 := by
    have hnat : (2628365453 : ℕ)^65*100000000000000^49 ≤ 42610917682549^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628365453 5000000000 42610917682549 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224738617/1000000000 : ℝ)^65 ≤ (6901613460431/50000000000000 : ℝ)^49 := by
    have hnat : (224738617 : ℕ)^65*50000000000000^49 ≤ 6901613460431^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224738617 1000000000 6901613460431 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673573033/5000000000 : ℝ), (2628365453/5000000000 : ℝ), (-224738617/1000000000 : ℝ)] ![(21792927690011/50000000000000 : ℝ), (42610917682549/100000000000000 : ℝ), (6901613460431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673573033/5000000000 : ℝ)|^65 ≤ (21792927690011/50000000000000 : ℝ)^49
        have hw : |(2673573033/5000000000 : ℝ)|=(2673573033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628365453/5000000000 : ℝ)|^65 ≤ (42610917682549/100000000000000 : ℝ)^49
        have hw : |(2628365453/5000000000 : ℝ)|=(2628365453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-224738617/1000000000 : ℝ)|^65 ≤ (6901613460431/50000000000000 : ℝ)^49
        have hw : |(-224738617/1000000000 : ℝ)|=(224738617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s4_3 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1091574593/2500000000 : ℝ)*x 0 + (211199747/500000000 : ℝ)*x 1 + (2256694521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091574593/2500000000 : ℝ)^65 ≤ (33311901328359/100000000000000 : ℝ)^49 := by
    have hnat : (1091574593 : ℕ)^65*100000000000000^49 ≤ 33311901328359^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091574593 2500000000 33311901328359 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211199747/500000000 : ℝ)^65 ≤ (6375887038873/20000000000000 : ℝ)^49 := by
    have hnat : (211199747 : ℕ)^65*20000000000000^49 ≤ 6375887038873^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211199747 500000000 6375887038873 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2256694521/5000000000 : ℝ)^65 ≤ (17404331732259/50000000000000 : ℝ)^49 := by
    have hnat : (2256694521 : ℕ)^65*50000000000000^49 ≤ 17404331732259^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256694521 5000000000 17404331732259 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091574593/2500000000 : ℝ), (211199747/500000000 : ℝ), (2256694521/5000000000 : ℝ)] ![(33311901328359/100000000000000 : ℝ), (6375887038873/20000000000000 : ℝ), (17404331732259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091574593/2500000000 : ℝ)|^65 ≤ (33311901328359/100000000000000 : ℝ)^49
        have hw : |(1091574593/2500000000 : ℝ)|=(1091574593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211199747/500000000 : ℝ)|^65 ≤ (6375887038873/20000000000000 : ℝ)^49
        have hw : |(211199747/500000000 : ℝ)|=(211199747/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2256694521/5000000000 : ℝ)|^65 ≤ (17404331732259/50000000000000 : ℝ)^49
        have hw : |(2256694521/5000000000 : ℝ)|=(2256694521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s4_4 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1086620551/5000000000 : ℝ)*x 0 + (1051429749/2000000000 : ℝ)*x 1 + (5402202827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086620551/5000000000 : ℝ)^65 ≤ (3300603522839/25000000000000 : ℝ)^49 := by
    have hnat : (1086620551 : ℕ)^65*25000000000000^49 ≤ 3300603522839^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086620551 5000000000 3300603522839 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051429749/2000000000 : ℝ)^65 ≤ (2663463168053/6250000000000 : ℝ)^49 := by
    have hnat : (1051429749 : ℕ)^65*6250000000000^49 ≤ 2663463168053^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051429749 2000000000 2663463168053 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402202827/10000000000 : ℝ)^65 ≤ (44182175199647/100000000000000 : ℝ)^49 := by
    have hnat : (5402202827 : ℕ)^65*100000000000000^49 ≤ 44182175199647^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402202827 10000000000 44182175199647 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1086620551/5000000000 : ℝ), (1051429749/2000000000 : ℝ), (5402202827/10000000000 : ℝ)] ![(3300603522839/25000000000000 : ℝ), (2663463168053/6250000000000 : ℝ), (44182175199647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1086620551/5000000000 : ℝ)|^65 ≤ (3300603522839/25000000000000 : ℝ)^49
        have hw : |(-1086620551/5000000000 : ℝ)|=(1086620551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051429749/2000000000 : ℝ)|^65 ≤ (2663463168053/6250000000000 : ℝ)^49
        have hw : |(1051429749/2000000000 : ℝ)|=(1051429749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402202827/10000000000 : ℝ)|^65 ≤ (44182175199647/100000000000000 : ℝ)^49
        have hw : |(5402202827/10000000000 : ℝ)|=(5402202827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s4_5 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (531022703/1000000000 : ℝ)*x 0 + (-2101914197/10000000000 : ℝ)*x 1 + (84409421/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531022703/1000000000 : ℝ)^65 ≤ (21593552754183/50000000000000 : ℝ)^49 := by
    have hnat : (531022703 : ℕ)^65*50000000000000^49 ≤ 21593552754183^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531022703 1000000000 21593552754183 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2101914197/10000000000 : ℝ)^65 ≤ (12630718013289/100000000000000 : ℝ)^49 := by
    have hnat : (2101914197 : ℕ)^65*100000000000000^49 ≤ 12630718013289^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101914197 10000000000 12630718013289 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84409421/156250000 : ℝ)^65 ≤ (44182176468991/100000000000000 : ℝ)^49 := by
    have hnat : (84409421 : ℕ)^65*100000000000000^49 ≤ 44182176468991^49*156250000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84409421 156250000 44182176468991 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531022703/1000000000 : ℝ), (-2101914197/10000000000 : ℝ), (84409421/156250000 : ℝ)] ![(21593552754183/50000000000000 : ℝ), (12630718013289/100000000000000 : ℝ), (44182176468991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531022703/1000000000 : ℝ)|^65 ≤ (21593552754183/50000000000000 : ℝ)^49
        have hw : |(531022703/1000000000 : ℝ)|=(531022703/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2101914197/10000000000 : ℝ)|^65 ≤ (12630718013289/100000000000000 : ℝ)^49
        have hw : |(-2101914197/10000000000 : ℝ)|=(2101914197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84409421/156250000 : ℝ)|^65 ≤ (44182176468991/100000000000000 : ℝ)^49
        have hw : |(84409421/156250000 : ℝ)|=(84409421/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s4_6 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1062045421/2000000000 : ℝ)*x 0 + (5402202963/10000000000 : ℝ)*x 1 + (-2101914069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062045421/2000000000 : ℝ)^65 ≤ (43187106317499/100000000000000 : ℝ)^49 := by
    have hnat : (1062045421 : ℕ)^65*100000000000000^49 ≤ 43187106317499^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062045421 2000000000 43187106317499 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402202963/10000000000 : ℝ)^65 ≤ (11045544168781/25000000000000 : ℝ)^49 := by
    have hnat : (5402202963 : ℕ)^65*25000000000000^49 ≤ 11045544168781^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402202963 10000000000 11045544168781 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2101914069/10000000000 : ℝ)^65 ≤ (39470990603/312500000000 : ℝ)^49 := by
    have hnat : (2101914069 : ℕ)^65*312500000000^49 ≤ 39470990603^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101914069 10000000000 39470990603 312500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062045421/2000000000 : ℝ), (5402202963/10000000000 : ℝ), (-2101914069/10000000000 : ℝ)] ![(43187106317499/100000000000000 : ℝ), (11045544168781/25000000000000 : ℝ), (39470990603/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062045421/2000000000 : ℝ)|^65 ≤ (43187106317499/100000000000000 : ℝ)^49
        have hw : |(1062045421/2000000000 : ℝ)|=(1062045421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402202963/10000000000 : ℝ)|^65 ≤ (11045544168781/25000000000000 : ℝ)^49
        have hw : |(5402202963/10000000000 : ℝ)|=(5402202963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2101914069/10000000000 : ℝ)|^65 ≤ (39470990603/312500000000 : ℝ)^49
        have hw : |(-2101914069/10000000000 : ℝ)|=(2101914069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s4_7 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1091578359/2500000000 : ℝ)*x 0 + (4512559667/10000000000 : ℝ)*x 1 + (4224827177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091578359/2500000000 : ℝ)^65 ≤ (832801344603/2500000000000 : ℝ)^49 := by
    have hnat : (1091578359 : ℕ)^65*2500000000000^49 ≤ 832801344603^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091578359 2500000000 832801344603 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4512559667/10000000000 : ℝ)^65 ≤ (34800178700567/100000000000000 : ℝ)^49 := by
    have hnat : (4512559667 : ℕ)^65*100000000000000^49 ≤ 34800178700567^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512559667 10000000000 34800178700567 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4224827177/10000000000 : ℝ)^65 ≤ (15943883752909/50000000000000 : ℝ)^49 := by
    have hnat : (4224827177 : ℕ)^65*50000000000000^49 ≤ 15943883752909^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224827177 10000000000 15943883752909 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091578359/2500000000 : ℝ), (4512559667/10000000000 : ℝ), (4224827177/10000000000 : ℝ)] ![(832801344603/2500000000000 : ℝ), (34800178700567/100000000000000 : ℝ), (15943883752909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091578359/2500000000 : ℝ)|^65 ≤ (832801344603/2500000000000 : ℝ)^49
        have hw : |(1091578359/2500000000 : ℝ)|=(1091578359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4512559667/10000000000 : ℝ)|^65 ≤ (34800178700567/100000000000000 : ℝ)^49
        have hw : |(4512559667/10000000000 : ℝ)|=(4512559667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4224827177/10000000000 : ℝ)|^65 ≤ (15943883752909/50000000000000 : ℝ)^49
        have hw : |(4224827177/10000000000 : ℝ)|=(4224827177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1127_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37295281/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1853/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1059/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11147/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1853/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1059/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1853/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1059/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1853/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1059/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1853/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1059/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1853/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1059/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1853/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1059/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1059/10000 : ℝ) ^ (8319/2048 : ℝ) ≤ (10942485075666173/100000000000000000000 : ℝ) := by
    have hpowers : (1059/10000 : ℝ)^8319 ≤ (10942485075666173/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1059 : ℕ)^8319*100000000000000000000^2048 ≤ 10942485075666173^2048*10000^8319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1059 10000 10942485075666173 100000000000000000000 8319 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1059/10000 : ℝ)) (X := (10942485075666173/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1853/12500 : ℝ) ^ (8319/2048 : ℝ) ≤ (42899454041512877/100000000000000000000 : ℝ) := by
    have hpowers : (1853/12500 : ℝ)^8319 ≤ (42899454041512877/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1853 : ℕ)^8319*100000000000000000000^2048 ≤ 42899454041512877^2048*12500^8319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1853 12500 42899454041512877 100000000000000000000 8319 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1853/12500 : ℝ)) (X := (42899454041512877/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010942485075666173/50000000000000000000 : ℝ) ≤ (5000269363639103/5000000000000000 : ℝ) ^ (8319/2048 : ℝ) := by
    have hpowers : (50010942485075666173/50000000000000000000 : ℝ)^2048 ≤ (5000269363639103/5000000000000000 : ℝ)^8319 := by
      have hnat : (50010942485075666173 : ℕ)^2048*5000000000000000^8319 ≤ 5000269363639103^8319*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010942485075666173 50000000000000000000 5000269363639103 5000000000000000 2048 8319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000269363639103/5000000000000000 : ℝ)) (X := (50010942485075666173/50000000000000000000 : ℝ)) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (2001076838782343581/2000000000000000000 : ℝ) ≤ (500066261522471/500000000000000 : ℝ) ^ (8319/2048 : ℝ) := by
    have hpowers : (2001076838782343581/2000000000000000000 : ℝ)^2048 ≤ (500066261522471/500000000000000 : ℝ)^8319 := by
      have hnat : (2001076838782343581 : ℕ)^2048*500000000000000^8319 ≤ 500066261522471^8319*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001076838782343581 2000000000000000000 500066261522471 500000000000000 2048 8319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500066261522471/500000000000000 : ℝ)) (X := (2001076838782343581/2000000000000000000 : ℝ)) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50042899454041512877/50000000000000000000 : ℝ) ≤ (5001055866810317/5000000000000000 : ℝ) ^ (8319/2048 : ℝ) := by
    have hpowers : (50042899454041512877/50000000000000000000 : ℝ)^2048 ≤ (5001055866810317/5000000000000000 : ℝ)^8319 := by
      have hnat : (50042899454041512877 : ℕ)^2048*5000000000000000^8319 ≤ 5001055866810317^8319*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50042899454041512877 50000000000000000000 5001055866810317 5000000000000000 2048 8319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001055866810317/5000000000000000 : ℝ)) (X := (50042899454041512877/50000000000000000000 : ℝ)) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10942485075666173/100000000000000000000 : ℝ) ≤ ((10581405708532402921/10585000000000000000 : ℝ)+2*(393251585607/211700000000000 : ℝ)*(1059/10000 : ℝ))^(8319/2048 : ℝ) := by
    rw [show (10581405708532402921/10585000000000000000 : ℝ)+2*(393251585607/211700000000000 : ℝ)*(1059/10000 : ℝ)=(5000269363639103/5000000000000000 : ℝ) by norm_num, show 1+2*(10942485075666173/100000000000000000000 : ℝ)=(50010942485075666173/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(42899454041512877/100000000000000000000 : ℝ)+(10942485075666173/100000000000000000000 : ℝ) ≤ ((10581405708532402921/10585000000000000000 : ℝ)+(393251585607/211700000000000 : ℝ)*((1853/12500 : ℝ)+(1059/10000 : ℝ)))^(8319/2048 : ℝ) := by
    rw [show (10581405708532402921/10585000000000000000 : ℝ)+(393251585607/211700000000000 : ℝ)*((1853/12500 : ℝ)+(1059/10000 : ℝ))=(500066261522471/500000000000000 : ℝ) by norm_num, show 1+(42899454041512877/100000000000000000000 : ℝ)+(10942485075666173/100000000000000000000 : ℝ)=(2001076838782343581/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(42899454041512877/100000000000000000000 : ℝ) ≤ ((10581405708532402921/10585000000000000000 : ℝ)+2*(393251585607/211700000000000 : ℝ)*(1853/12500 : ℝ))^(8319/2048 : ℝ) := by
    rw [show (10581405708532402921/10585000000000000000 : ℝ)+2*(393251585607/211700000000000 : ℝ)*(1853/12500 : ℝ)=(5001055866810317/5000000000000000 : ℝ) by norm_num, show 1+2*(42899454041512877/100000000000000000000 : ℝ)=(50042899454041512877/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10581405708532402921/10585000000000000000 : ℝ)*(X 1 0+X 2 0)+(393251585607/211700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8319/2048 : ℝ)) (lo := (1059/10000 : ℝ)) (hi := (1853/12500 : ℝ)) (c := (10581405708532402921/10585000000000000000 : ℝ)) (alpha := (393251585607/211700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10581405708532402921/10585000000000000000 : ℝ)*(X 0 1+X 2 1)+(393251585607/211700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8319/2048 : ℝ)) (lo := (1059/10000 : ℝ)) (hi := (1853/12500 : ℝ)) (c := (10581405708532402921/10585000000000000000 : ℝ)) (alpha := (393251585607/211700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10581405708532402921/10585000000000000000 : ℝ)*(X 0 2+X 1 2)+(393251585607/211700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8319/2048 : ℝ)) (lo := (1059/10000 : ℝ)) (hi := (1853/12500 : ℝ)) (c := (10581405708532402921/10585000000000000000 : ℝ)) (alpha := (393251585607/211700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2173233917/10000000000 : ℝ)*X 0 0+(2701311133/5000000000 : ℝ)*X 0 1+(657091367/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673573207/5000000000 : ℝ)*X 1 0+(-2247385579/10000000000 : ℝ)*X 1 1+(1314182751/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673573033/5000000000 : ℝ)*X 2 0+(2628365453/5000000000 : ℝ)*X 2 1+(-224738617/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1091574593/2500000000 : ℝ)*X 0 0+(211199747/500000000 : ℝ)*X 0 1+(2256694521/5000000000 : ℝ)*X 0 2+(1091574593/2500000000 : ℝ)*X 1 0+(211199747/500000000 : ℝ)*X 1 1+(2256694521/5000000000 : ℝ)*X 1 2+(1091574593/2500000000 : ℝ)*X 2 0+(211199747/500000000 : ℝ)*X 2 1+(2256694521/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1086620551/5000000000 : ℝ)*X 0 0+(1051429749/2000000000 : ℝ)*X 0 1+(5402202827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531022703/1000000000 : ℝ)*X 1 0+(-2101914197/10000000000 : ℝ)*X 1 1+(84409421/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062045421/2000000000 : ℝ)*X 2 0+(5402202963/10000000000 : ℝ)*X 2 1+(-2101914069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1091578359/2500000000 : ℝ)*X 0 0+(4512559667/10000000000 : ℝ)*X 0 1+(4224827177/10000000000 : ℝ)*X 0 2+(1091578359/2500000000 : ℝ)*X 1 0+(4512559667/10000000000 : ℝ)*X 1 1+(4224827177/10000000000 : ℝ)*X 1 2+(1091578359/2500000000 : ℝ)*X 2 0+(4512559667/10000000000 : ℝ)*X 2 1+(4224827177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16902177213821025119050509/33078125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (843006629/100000000000000 : ℝ)*(base19) + (37986949/5000000000000 : ℝ)*(base23) + (24585903/10000000000000 : ℝ)*(upper2) + (3717847/2000000000000 : ℝ)*(upper3) + (322187645562481/6250000000000 : ℝ)*(major0) + (322187645562481/6250000000000 : ℝ)*(major1) + (322187645562481/6250000000000 : ℝ)*(major2) + (274178166308667/4000000000000 : ℝ)*(sp0) + (6854471227365177/100000000000000 : ℝ)*(sp1) + (6854457266938333/100000000000000 : ℝ)*(sp2) + (215969658422361/6250000000000 : ℝ)*(sp3) + (1791265513/10000000000000 : ℝ)*(sp4) + (7021847247/50000000000000 : ℝ)*(sp6) + (4508959303/25000000000000 : ℝ)*(sp7) + (863883142648747/25000000000000 : ℝ)*(f.failure) + (3427236035185903/50000000000000 : ℝ)*(f.sum) + (80165530307893/10585000000000000000000000000 : ℝ)*base66 + (955368585740117999/66156250000000000000000000000000 : ℝ)*base68 + (983645896030555499/66156250000000000000000000000000 : ℝ)*base70 + (1605894049213430499/66156250000000000000000000000000 : ℝ)*base72 + (12261657739287/10585000000000000000000000000 : ℝ)*base73 + (865109601391992999/66156250000000000000000000000000 : ℝ)*base76 + (989290183609992999/66156250000000000000000000000000 : ℝ)*base78 + (1858997335063242999/66156250000000000000000000000000 : ℝ)*base80 + (17000334705057/2646250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (3662907/625000000000000000000 : ℝ)*base89 + (3662907/625000000000000000000 : ℝ)*base91 + (3662907/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (125317144568352495775143213/18250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1318741229/100000000000000 : ℝ)*(base19) + (327531973/20000000000000 : ℝ)*(base23) + (66417467/25000000000000 : ℝ)*(upper3) + (80822539/100000000000000 : ℝ)*(lower4) + (7118047/2500000000000 : ℝ)*(upper5) + (5184715523195207/100000000000000 : ℝ)*(major0) + (5184715523195207/100000000000000 : ℝ)*(major1) + (5184715523195207/100000000000000 : ℝ)*(major2) + (28962297627/100000000000000 : ℝ)*(sp1) + (38937356087/100000000000000 : ℝ)*(sp2) + (1723495179382519/25000000000000 : ℝ)*(sp4) + (344697521824561/5000000000000 : ℝ)*(sp5) + (1723485035628531/25000000000000 : ℝ)*(sp6) + (1357597695301/39062500000 : ℝ)*(sp7) + (1357597695301/39062500000 : ℝ)*(f.failure) + (1723495179382519/25000000000000 : ℝ)*(f.sum) + (2705310798861/365000000000000000000000000 : ℝ)*base65 + (369543639739643/36500000000000000000000000000000 : ℝ)*base67 + (199722475771739643/36500000000000000000000000000000 : ℝ)*base69 + (424334483412739643/36500000000000000000000000000000 : ℝ)*base71 + (96002057063/182500000000000000000000000 : ℝ)*base73 + (870740142507739643/36500000000000000000000000000000 : ℝ)*base75 + (317101185096739643/36500000000000000000000000000000 : ℝ)*base77 + (188011677728739643/36500000000000000000000000000000 : ℝ)*base79 + (1251179500271/365000000000000000000000000 : ℝ)*base81 + (150227/7812500000000000000 : ℝ)*base90 + (150227/7812500000000000000 : ℝ)*base92 + (150227/7812500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1127_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37295281/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1853/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1059/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11147/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1127_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1127_s5_0 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2173904021/10000000000 : ℝ)*x 0 + (5395308809/10000000000 : ℝ)*x 1 + (526360473/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173904021/10000000000 : ℝ)^65 ≤ (13207756594789/100000000000000 : ℝ)^49 := by
    have hnat : (2173904021 : ℕ)^65*100000000000000^49 ≤ 13207756594789^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173904021 10000000000 13207756594789 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395308809/10000000000 : ℝ)^65 ≤ (11026849234017/25000000000000 : ℝ)^49 := by
    have hnat : (5395308809 : ℕ)^65*25000000000000^49 ≤ 11026849234017^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395308809 10000000000 11026849234017 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526360473/1000000000 : ℝ)^65 ≤ (10671211614237/25000000000000 : ℝ)^49 := by
    have hnat : (526360473 : ℕ)^65*25000000000000^49 ≤ 10671211614237^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526360473 1000000000 10671211614237 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2173904021/10000000000 : ℝ), (5395308809/10000000000 : ℝ), (526360473/1000000000 : ℝ)] ![(13207756594789/100000000000000 : ℝ), (11026849234017/25000000000000 : ℝ), (10671211614237/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2173904021/10000000000 : ℝ)|^65 ≤ (13207756594789/100000000000000 : ℝ)^49
        have hw : |(-2173904021/10000000000 : ℝ)|=(2173904021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395308809/10000000000 : ℝ)|^65 ≤ (11026849234017/25000000000000 : ℝ)^49
        have hw : |(5395308809/10000000000 : ℝ)|=(5395308809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526360473/1000000000 : ℝ)|^65 ≤ (10671211614237/25000000000000 : ℝ)^49
        have hw : |(526360473/1000000000 : ℝ)|=(526360473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s5_1 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (213812591/400000000 : ℝ)*x 0 + (-560184861/2500000000 : ℝ)*x 1 + (5263604649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213812591/400000000 : ℝ)^65 ≤ (43566054983967/100000000000000 : ℝ)^49 := by
    have hnat : (213812591 : ℕ)^65*100000000000000^49 ≤ 43566054983967^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213812591 400000000 43566054983967 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560184861/2500000000 : ℝ)^65 ≤ (13749099406793/100000000000000 : ℝ)^49 := by
    have hnat : (560184861 : ℕ)^65*100000000000000^49 ≤ 13749099406793^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560184861 2500000000 13749099406793 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263604649/10000000000 : ℝ)^65 ≤ (21342422792799/50000000000000 : ℝ)^49 := by
    have hnat : (5263604649 : ℕ)^65*50000000000000^49 ≤ 21342422792799^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263604649 10000000000 21342422792799 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213812591/400000000 : ℝ), (-560184861/2500000000 : ℝ), (5263604649/10000000000 : ℝ)] ![(43566054983967/100000000000000 : ℝ), (13749099406793/100000000000000 : ℝ), (21342422792799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213812591/400000000 : ℝ)|^65 ≤ (43566054983967/100000000000000 : ℝ)^49
        have hw : |(213812591/400000000 : ℝ)|=(213812591/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-560184861/2500000000 : ℝ)|^65 ≤ (13749099406793/100000000000000 : ℝ)^49
        have hw : |(-560184861/2500000000 : ℝ)|=(560184861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263604649/10000000000 : ℝ)|^65 ≤ (21342422792799/50000000000000 : ℝ)^49
        have hw : |(5263604649/10000000000 : ℝ)|=(5263604649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s5_2 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5345314603/10000000000 : ℝ)*x 0 + (1052720959/2000000000 : ℝ)*x 1 + (-2240739481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345314603/10000000000 : ℝ)^65 ≤ (21783026562181/50000000000000 : ℝ)^49 := by
    have hnat : (5345314603 : ℕ)^65*50000000000000^49 ≤ 21783026562181^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345314603 10000000000 21783026562181 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052720959/2000000000 : ℝ)^65 ≤ (2134242357809/5000000000000 : ℝ)^49 := by
    have hnat : (1052720959 : ℕ)^65*5000000000000^49 ≤ 2134242357809^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052720959 2000000000 2134242357809 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2240739481/10000000000 : ℝ)^65 ≤ (3437274926989/25000000000000 : ℝ)^49 := by
    have hnat : (2240739481 : ℕ)^65*25000000000000^49 ≤ 3437274926989^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240739481 10000000000 3437274926989 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345314603/10000000000 : ℝ), (1052720959/2000000000 : ℝ), (-2240739481/10000000000 : ℝ)] ![(21783026562181/50000000000000 : ℝ), (2134242357809/5000000000000 : ℝ), (3437274926989/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345314603/10000000000 : ℝ)|^65 ≤ (21783026562181/50000000000000 : ℝ)^49
        have hw : |(5345314603/10000000000 : ℝ)|=(5345314603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052720959/2000000000 : ℝ)|^65 ≤ (2134242357809/5000000000000 : ℝ)^49
        have hw : |(1052720959/2000000000 : ℝ)|=(1052720959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2240739481/10000000000 : ℝ)|^65 ≤ (3437274926989/25000000000000 : ℝ)^49
        have hw : |(-2240739481/10000000000 : ℝ)|=(2240739481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s5_3 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1091672491/2500000000 : ℝ)*x 0 + (4238015473/10000000000 : ℝ)*x 1 + (1124816649/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091672491/2500000000 : ℝ)^65 ≤ (16657932252629/50000000000000 : ℝ)^49 := by
    have hnat : (1091672491 : ℕ)^65*50000000000000^49 ≤ 16657932252629^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091672491 2500000000 16657932252629 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4238015473/10000000000 : ℝ)^65 ≤ (8004969875683/25000000000000 : ℝ)^49 := by
    have hnat : (4238015473 : ℕ)^65*25000000000000^49 ≤ 8004969875683^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238015473 10000000000 8004969875683 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124816649/2500000000 : ℝ)^65 ≤ (1386570239221/4000000000000 : ℝ)^49 := by
    have hnat : (1124816649 : ℕ)^65*4000000000000^49 ≤ 1386570239221^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124816649 2500000000 1386570239221 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091672491/2500000000 : ℝ), (4238015473/10000000000 : ℝ), (1124816649/2500000000 : ℝ)] ![(16657932252629/50000000000000 : ℝ), (8004969875683/25000000000000 : ℝ), (1386570239221/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091672491/2500000000 : ℝ)|^65 ≤ (16657932252629/50000000000000 : ℝ)^49
        have hw : |(1091672491/2500000000 : ℝ)|=(1091672491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4238015473/10000000000 : ℝ)|^65 ≤ (8004969875683/25000000000000 : ℝ)^49
        have hw : |(4238015473/10000000000 : ℝ)|=(4238015473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124816649/2500000000 : ℝ)|^65 ≤ (1386570239221/4000000000000 : ℝ)^49
        have hw : |(1124816649/2500000000 : ℝ)|=(1124816649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s5_4 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2173908869/10000000000 : ℝ)*x 0 + (2631972869/5000000000 : ℝ)*x 1 + (5394966931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173908869/10000000000 : ℝ)^65 ≤ (13207795667067/100000000000000 : ℝ)^49 := by
    have hnat : (2173908869 : ℕ)^65*100000000000000^49 ≤ 13207795667067^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173908869 10000000000 13207795667067 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631972869/5000000000 : ℝ)^65 ≤ (8537702971741/20000000000000 : ℝ)^49 := by
    have hnat : (2631972869 : ℕ)^65*20000000000000^49 ≤ 8537702971741^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631972869 5000000000 8537702971741 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394966931/10000000000 : ℝ)^65 ≤ (22051844727001/50000000000000 : ℝ)^49 := by
    have hnat : (5394966931 : ℕ)^65*50000000000000^49 ≤ 22051844727001^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394966931 10000000000 22051844727001 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2173908869/10000000000 : ℝ), (2631972869/5000000000 : ℝ), (5394966931/10000000000 : ℝ)] ![(13207795667067/100000000000000 : ℝ), (8537702971741/20000000000000 : ℝ), (22051844727001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2173908869/10000000000 : ℝ)|^65 ≤ (13207795667067/100000000000000 : ℝ)^49
        have hw : |(-2173908869/10000000000 : ℝ)|=(2173908869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631972869/5000000000 : ℝ)|^65 ≤ (8537702971741/20000000000000 : ℝ)^49
        have hw : |(2631972869/5000000000 : ℝ)|=(2631972869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394966931/10000000000 : ℝ)|^65 ≤ (22051844727001/50000000000000 : ℝ)^49
        have hw : |(5394966931/10000000000 : ℝ)|=(5394966931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s5_5 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1062396923/2000000000 : ℝ)*x 0 + (-2109377319/10000000000 : ℝ)*x 1 + (2697483419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062396923/2000000000 : ℝ)^65 ≤ (43206068117299/100000000000000 : ℝ)^49 := by
    have hnat : (1062396923 : ℕ)^65*100000000000000^49 ≤ 43206068117299^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062396923 2000000000 43206068117299 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109377319/10000000000 : ℝ)^65 ≤ (12690243418251/100000000000000 : ℝ)^49 := by
    have hnat : (2109377319 : ℕ)^65*100000000000000^49 ≤ 12690243418251^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109377319 10000000000 12690243418251 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697483419/5000000000 : ℝ)^65 ≤ (22051844222739/50000000000000 : ℝ)^49 := by
    have hnat : (2697483419 : ℕ)^65*50000000000000^49 ≤ 22051844222739^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697483419 5000000000 22051844222739 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062396923/2000000000 : ℝ), (-2109377319/10000000000 : ℝ), (2697483419/5000000000 : ℝ)] ![(43206068117299/100000000000000 : ℝ), (12690243418251/100000000000000 : ℝ), (22051844222739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062396923/2000000000 : ℝ)|^65 ≤ (43206068117299/100000000000000 : ℝ)^49
        have hw : |(1062396923/2000000000 : ℝ)|=(1062396923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2109377319/10000000000 : ℝ)|^65 ≤ (12690243418251/100000000000000 : ℝ)^49
        have hw : |(-2109377319/10000000000 : ℝ)|=(2109377319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697483419/5000000000 : ℝ)|^65 ≤ (22051844222739/50000000000000 : ℝ)^49
        have hw : |(2697483419/5000000000 : ℝ)|=(2697483419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s5_6 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5311984363/10000000000 : ℝ)*x 0 + (2107409/3906250 : ℝ)*x 1 + (-1054688693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311984363/10000000000 : ℝ)^65 ≤ (43206065398321/100000000000000 : ℝ)^49 := by
    have hnat : (5311984363 : ℕ)^65*100000000000000^49 ≤ 43206065398321^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311984363 10000000000 43206065398321 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107409/3906250 : ℝ)^65 ≤ (11025922659009/25000000000000 : ℝ)^49 := by
    have hnat : (2107409 : ℕ)^65*25000000000000^49 ≤ 11025922659009^49*3906250^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107409 3906250 11025922659009 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054688693/5000000000 : ℝ)^65 ≤ (3172560988237/25000000000000 : ℝ)^49 := by
    have hnat : (1054688693 : ℕ)^65*25000000000000^49 ≤ 3172560988237^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054688693 5000000000 3172560988237 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311984363/10000000000 : ℝ), (2107409/3906250 : ℝ), (-1054688693/5000000000 : ℝ)] ![(43206065398321/100000000000000 : ℝ), (11025922659009/25000000000000 : ℝ), (3172560988237/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311984363/10000000000 : ℝ)|^65 ≤ (43206065398321/100000000000000 : ℝ)^49
        have hw : |(5311984363/10000000000 : ℝ)|=(5311984363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2107409/3906250 : ℝ)|^65 ≤ (11025922659009/25000000000000 : ℝ)^49
        have hw : |(2107409/3906250 : ℝ)|=(2107409/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1054688693/5000000000 : ℝ)|^65 ≤ (3172560988237/25000000000000 : ℝ)^49
        have hw : |(-1054688693/5000000000 : ℝ)|=(1054688693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1127_s5_7 (p : ℝ) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1091675061/2500000000 : ℝ)*x 0 + (899718187/2000000000 : ℝ)*x 1 + (2119347023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091675061/2500000000 : ℝ)^65 ≤ (33315968547401/100000000000000 : ℝ)^49 := by
    have hnat : (1091675061 : ℕ)^65*100000000000000^49 ≤ 33315968547401^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091675061 2500000000 33315968547401 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899718187/2000000000 : ℝ)^65 ≤ (17328675395241/50000000000000 : ℝ)^49 := by
    have hnat : (899718187 : ℕ)^65*50000000000000^49 ≤ 17328675395241^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899718187 2000000000 17328675395241 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119347023/5000000000 : ℝ)^65 ≤ (32026680652831/100000000000000 : ℝ)^49 := by
    have hnat : (2119347023 : ℕ)^65*100000000000000^49 ≤ 32026680652831^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119347023 5000000000 32026680652831 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091675061/2500000000 : ℝ), (899718187/2000000000 : ℝ), (2119347023/5000000000 : ℝ)] ![(33315968547401/100000000000000 : ℝ), (17328675395241/50000000000000 : ℝ), (32026680652831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091675061/2500000000 : ℝ)|^65 ≤ (33315968547401/100000000000000 : ℝ)^49
        have hw : |(1091675061/2500000000 : ℝ)|=(1091675061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899718187/2000000000 : ℝ)|^65 ≤ (17328675395241/50000000000000 : ℝ)^49
        have hw : |(899718187/2000000000 : ℝ)|=(899718187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2119347023/5000000000 : ℝ)|^65 ≤ (32026680652831/100000000000000 : ℝ)^49
        have hw : |(2119347023/5000000000 : ℝ)|=(2119347023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1127_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37295281/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11147/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11293/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14083/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11147/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11147/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11147/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11147/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11147/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11147/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11147/100000 : ℝ) ^ (8319/2048 : ℝ) ≤ (1347549212134651/10000000000000000000 : ℝ) := by
    have hpowers : (11147/100000 : ℝ)^8319 ≤ (1347549212134651/10000000000000000000 : ℝ)^2048 := by
      have hnat : (11147 : ℕ)^8319*10000000000000000000^2048 ≤ 1347549212134651^2048*100000^8319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11147 100000 1347549212134651 10000000000000000000 8319 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11147/100000 : ℝ)) (X := (1347549212134651/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (8319/2048 : ℝ) ≤ (18197932723777667/50000000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^8319 ≤ (18197932723777667/50000000000000000000 : ℝ)^2048 := by
      have hnat : (3559 : ℕ)^8319*50000000000000000000^2048 ≤ 18197932723777667^2048*25000^8319 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 18197932723777667 50000000000000000000 8319 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (18197932723777667/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001347549212134651/5000000000000000000 : ℝ) ≤ (5000331710601121/5000000000000000 : ℝ) ^ (8319/2048 : ℝ) := by
    have hpowers : (5001347549212134651/5000000000000000000 : ℝ)^2048 ≤ (5000331710601121/5000000000000000 : ℝ)^8319 := by
      have hnat : (5001347549212134651 : ℕ)^2048*5000000000000000^8319 ≤ 5000331710601121^8319*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001347549212134651 5000000000000000000 5000331710601121 5000000000000000 2048 8319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000331710601121/5000000000000000 : ℝ)) (X := (5001347549212134651/5000000000000000000 : ℝ)) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012467839392225461/25000000000000000000 : ℝ) ≤ (5000613759750961/5000000000000000 : ℝ) ^ (8319/2048 : ℝ) := by
    have hpowers : (25012467839392225461/25000000000000000000 : ℝ)^2048 ≤ (5000613759750961/5000000000000000 : ℝ)^8319 := by
      have hnat : (25012467839392225461 : ℕ)^2048*5000000000000000^8319 ≤ 5000613759750961^8319*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012467839392225461 25000000000000000000 5000613759750961 5000000000000000 2048 8319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000613759750961/5000000000000000 : ℝ)) (X := (25012467839392225461/25000000000000000000 : ℝ)) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018197932723777667/25000000000000000000 : ℝ) ≤ (5000895808900801/5000000000000000 : ℝ) ^ (8319/2048 : ℝ) := by
    have hpowers : (25018197932723777667/25000000000000000000 : ℝ)^2048 ≤ (5000895808900801/5000000000000000 : ℝ)^8319 := by
      have hnat : (25018197932723777667 : ℕ)^2048*5000000000000000^8319 ≤ 5000895808900801^8319*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018197932723777667 25000000000000000000 5000895808900801 5000000000000000 2048 8319 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000895808900801/5000000000000000 : ℝ)) (X := (25018197932723777667/25000000000000000000 : ℝ)) (by norm_num) 8319 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1347549212134651/10000000000000000000 : ℝ) ≤ ((15439736650300329809/15445000000000000000 : ℝ)+2*(3525614373/1930625000000 : ℝ)*(11147/100000 : ℝ))^(8319/2048 : ℝ) := by
    rw [show (15439736650300329809/15445000000000000000 : ℝ)+2*(3525614373/1930625000000 : ℝ)*(11147/100000 : ℝ)=(5000331710601121/5000000000000000 : ℝ) by norm_num, show 1+2*(1347549212134651/10000000000000000000 : ℝ)=(5001347549212134651/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18197932723777667/50000000000000000000 : ℝ)+(1347549212134651/10000000000000000000 : ℝ) ≤ ((15439736650300329809/15445000000000000000 : ℝ)+(3525614373/1930625000000 : ℝ)*((3559/25000 : ℝ)+(11147/100000 : ℝ)))^(8319/2048 : ℝ) := by
    rw [show (15439736650300329809/15445000000000000000 : ℝ)+(3525614373/1930625000000 : ℝ)*((3559/25000 : ℝ)+(11147/100000 : ℝ))=(5000613759750961/5000000000000000 : ℝ) by norm_num, show 1+(18197932723777667/50000000000000000000 : ℝ)+(1347549212134651/10000000000000000000 : ℝ)=(25012467839392225461/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18197932723777667/50000000000000000000 : ℝ) ≤ ((15439736650300329809/15445000000000000000 : ℝ)+2*(3525614373/1930625000000 : ℝ)*(3559/25000 : ℝ))^(8319/2048 : ℝ) := by
    rw [show (15439736650300329809/15445000000000000000 : ℝ)+2*(3525614373/1930625000000 : ℝ)*(3559/25000 : ℝ)=(5000895808900801/5000000000000000 : ℝ) by norm_num, show 1+2*(18197932723777667/50000000000000000000 : ℝ)=(25018197932723777667/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15439736650300329809/15445000000000000000 : ℝ)*(X 1 0+X 2 0)+(3525614373/1930625000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8319/2048 : ℝ)) (lo := (11147/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (15439736650300329809/15445000000000000000 : ℝ)) (alpha := (3525614373/1930625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15439736650300329809/15445000000000000000 : ℝ)*(X 0 1+X 2 1)+(3525614373/1930625000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8319/2048 : ℝ)) (lo := (11147/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (15439736650300329809/15445000000000000000 : ℝ)) (alpha := (3525614373/1930625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15439736650300329809/15445000000000000000 : ℝ)*(X 0 2+X 1 2)+(3525614373/1930625000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8319/2048 : ℝ)) (lo := (11147/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (15439736650300329809/15445000000000000000 : ℝ)) (alpha := (3525614373/1930625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2173904021/10000000000 : ℝ)*X 0 0+(5395308809/10000000000 : ℝ)*X 0 1+(526360473/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213812591/400000000 : ℝ)*X 1 0+(-560184861/2500000000 : ℝ)*X 1 1+(5263604649/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345314603/10000000000 : ℝ)*X 2 0+(1052720959/2000000000 : ℝ)*X 2 1+(-2240739481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1091672491/2500000000 : ℝ)*X 0 0+(4238015473/10000000000 : ℝ)*X 0 1+(1124816649/2500000000 : ℝ)*X 0 2+(1091672491/2500000000 : ℝ)*X 1 0+(4238015473/10000000000 : ℝ)*X 1 1+(1124816649/2500000000 : ℝ)*X 1 2+(1091672491/2500000000 : ℝ)*X 2 0+(4238015473/10000000000 : ℝ)*X 2 1+(1124816649/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2173908869/10000000000 : ℝ)*X 0 0+(2631972869/5000000000 : ℝ)*X 0 1+(5394966931/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062396923/2000000000 : ℝ)*X 1 0+(-2109377319/10000000000 : ℝ)*X 1 1+(2697483419/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311984363/10000000000 : ℝ)*X 2 0+(2107409/3906250 : ℝ)*X 2 1+(-1054688693/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1091675061/2500000000 : ℝ)*X 0 0+(899718187/2000000000 : ℝ)*X 0 1+(2119347023/5000000000 : ℝ)*X 0 2+(1091675061/2500000000 : ℝ)*X 1 0+(899718187/2000000000 : ℝ)*X 1 1+(2119347023/5000000000 : ℝ)*X 1 2+(1091675061/2500000000 : ℝ)*X 2 0+(899718187/2000000000 : ℝ)*X 2 1+(2119347023/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1127_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2445405132762320390834557983/386125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1701167257/100000000000000 : ℝ)*(base19) + (314448327/25000000000000 : ℝ)*(base23) + (140041/48828125000 : ℝ)*(upper3) + (106400163/100000000000000 : ℝ)*(upper4) + (20134241/50000000000000 : ℝ)*(upper5) + (2855158731125057/50000000000000 : ℝ)*(major0) + (2855158731125057/50000000000000 : ℝ)*(major1) + (2855158731125057/50000000000000 : ℝ)*(major2) + (7592825096803297/100000000000000 : ℝ)*(sp0) + (303714328719077/4000000000000 : ℝ)*(sp1) + (3796429330675437/50000000000000 : ℝ)*(sp2) + (29904315867797/781250000000 : ℝ)*(sp3) + (17411170443/50000000000000 : ℝ)*(sp4) + (22363171499/100000000000000 : ℝ)*(sp7) + (1913887397124757/50000000000000 : ℝ)*(f.failure) + (3796429959572091/50000000000000 : ℝ)*(f.sum) + (24247518326903/3089000000000000000000000000 : ℝ)*base65 + (3530478510715424113/772250000000000000000000000000000 : ℝ)*base67 + (4533867652618424113/772250000000000000000000000000000 : ℝ)*base69 + (2831859628338174113/772250000000000000000000000000000 : ℝ)*base71 + (15146485898167/3089000000000000000000000000 : ℝ)*base73 + (11039843428174113/772250000000000000000000000000000 : ℝ)*base75 + (2300979341317424113/772250000000000000000000000000000 : ℝ)*base77 + (2390132699385174113/772250000000000000000000000000000 : ℝ)*base79 + (778629647/2413281250000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (20628283/1250000000000000000000 : ℝ)*base90 + (20628283/1250000000000000000000 : ℝ)*base92 + (20628283/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1999004208644189929229301549/154450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1032731311/100000000000000 : ℝ)*(base19) + (535114171/50000000000000 : ℝ)*(base23) + (5162729/20000000000000 : ℝ)*(upper3) + (39189977/20000000000000 : ℝ)*(lower4) + (1148002269568287/20000000000000 : ℝ)*(major0) + (1148002269568287/20000000000000 : ℝ)*(major1) + (1148002269568287/20000000000000 : ℝ)*(major2) + (28834915227/100000000000000 : ℝ)*(sp1) + (33726348761/100000000000000 : ℝ)*(sp2) + (1376885529/100000000000000 : ℝ)*(sp3) + (3816171441847367/50000000000000 : ℝ)*(sp4) + (7632313016048197/100000000000000 : ℝ)*(sp5) + (119254813861213/1562500000000 : ℝ)*(sp6) + (240479875229897/6250000000000 : ℝ)*(sp7) + (96191984514097/2500000000000 : ℝ)*(f.failure) + (3816171441847367/50000000000000 : ℝ)*(f.sum) + (7049414831331/1544500000000000000000000000 : ℝ)*base66 + (650252013897067183/308900000000000000000000000000000 : ℝ)*base67 + (2942212850368167183/308900000000000000000000000000000 : ℝ)*base69 + (1150648545268432817/308900000000000000000000000000000 : ℝ)*base72 + (4286487675837/1544500000000000000000000000 : ℝ)*base74 + (2603759232621332817/308900000000000000000000000000000 : ℝ)*base76 + (7838882528217532817/308900000000000000000000000000000 : ℝ)*base78 + (6995768850791632817/308900000000000000000000000000000 : ℝ)*base80 + (9002985085827/3089000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (798743/62500000000000000000 : ℝ)*base90 + (798743/62500000000000000000 : ℝ)*base92 + (798743/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1127_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37295281/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11147/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11293/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1127_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1127_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37295281/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4137/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4501/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11293/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1127_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1127_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1127_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8319/2048 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37295281/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4137/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4501/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11293/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1127_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
